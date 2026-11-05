"""Recheck the compiled source and its printed axiom dependencies locally."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent
source = root / 'Scalar.lean'
code = source.read_bytes()
assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b', code)
check = subprocess.run(['lake', 'env', 'lean', 'Scalar.lean'], cwd=root,
                       text=True, capture_output=True)
output = check.stdout + check.stderr
print(output)
assert check.returncode == 0, 'Lean compilation failed'
assert 'SCALAR_CHECK_COMPLETE' in output, 'Missing completion marker'
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)
assert len(reports) == 11, 'Missing axiom reports'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, values in reports:
    assert set(a.strip() for a in values.split(',') if a.strip()) <= allowed, name
record = {'result':'success', 'method':'lake build and lake env lean',
          'source_sha256':hashlib.sha256(code).hexdigest(),
          'toolchain':(root/'lean-toolchain').read_text().strip(),
          'axiom_reports':{name:[a.strip() for a in values.split(',')] for name,values in reports}}
(root/'lean-check.json').write_text(json.dumps(record,indent=2)+'\n')
(root/'lean-output.txt').write_text(output)
