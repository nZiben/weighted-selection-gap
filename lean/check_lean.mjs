import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

const filename = path.resolve(process.argv[2] ?? 'work/lean_audit/Scalar.lean');
const code = fs.readFileSync(filename, 'utf8');
if (/\b(?:sorry|admit|axiom|native_decide)\b/.test(code)) {
  throw new Error('Source contains a prohibited proof placeholder or axiom declaration');
}
const project = process.argv[3] ?? 'mathlib-stable';
const logname = process.argv[4] ?? filename + '.lsp.jsonl';
const summaryname = logname + '.summary.json';
const uri = 'file:///MathlibStable.lean';
const logs = [];
let latestDiagnostics = null;
let initialized = false;
let complete = false;
let timeout;
const socket = new WebSocket('wss://live.lean-lang.org/websocket/' + project);
const send = x => { logs.push({direction:'sent',message:x});socket.send(JSON.stringify(x)); };
const finish = (result) => {
  if (complete) return;
  complete = true;
  clearTimeout(timeout);
  const summary = {endpoint:'https://live.lean-lang.org',project,filename:path.basename(filename),
    source_sha256:crypto.createHash('sha256').update(code).digest('hex'),
    checked_at:new Date().toISOString(),result,diagnostics:latestDiagnostics};
  fs.writeFileSync(logname,logs.map(x=>JSON.stringify(x)).join('\n')+'\n');
  fs.writeFileSync(summaryname,JSON.stringify(summary,null,2)+'\n');
  console.log(JSON.stringify({...summary,diagnostics:latestDiagnostics?.diagnostics?.map(d=>({line:d.range.start.line+1,severity:d.severity,message:d.message}))},null,2));
  socket.close();
  setTimeout(()=>process.exit(result==='success'?0:1),500);
};
socket.addEventListener('open',()=>{
  send({jsonrpc:'2.0',id:1,method:'initialize',params:{processId:null,rootUri:'file:///',capabilities:{textDocument:{publishDiagnostics:{versionSupport:true}}},initializationOptions:{hasWidgets:false},workspaceFolders:null}});
});
socket.addEventListener('message',ev=>{
  const message=JSON.parse(ev.data);
  logs.push({direction:'received',message});
  if(message.id===1 && message.result && !initialized){
    initialized=true;
    send({jsonrpc:'2.0',method:'initialized',params:{}});
    send({jsonrpc:'2.0',method:'textDocument/didOpen',params:{textDocument:{uri,languageId:'lean4',version:1,text:code}}});
  }
  if(message.method==='textDocument/publishDiagnostics'){
    latestDiagnostics=message.params;
    // A command at EOF prints a marker; its presence proves the whole document was processed.
    if(message.params.diagnostics.some(d=>d.message.includes('SCALAR_CHECK_COMPLETE'))){
      const diagnostics=message.params.diagnostics;
      const badAxiom=diagnostics.some(d=>d.message.includes('sorryAx') ||
        (/depends on axioms:/.test(d.message) &&
          (d.message.match(/\[([^\]]*)\]/s)?.[1] ?? '').split(',')
            .some(a=>!['propext','Classical.choice','Quot.sound'].includes(a.trim()))));
      const axiomChecks=diagnostics.filter(d=>d.message.includes('depends on axioms:')).length;
      finish(diagnostics.some(d=>d.severity===1)?'lean_errors':
        badAxiom?'unexpected_axiom':axiomChecks!==16?'missing_axiom_audit':'success');
    }
  }
});
socket.addEventListener('error',e=>{
  console.error(e);
  logs.push({direction:'error',message:String(e.message??e)});
  finish('websocket_error');
});
socket.addEventListener('close',ev=>{
  if(!complete){logs.push({direction:'close',message:{code:ev.code,reason:ev.reason}});finish('premature_close');}
});
timeout=setTimeout(()=>finish('timeout'),150000);
