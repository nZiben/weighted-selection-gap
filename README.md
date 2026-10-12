# An explicit gap for three-point weighted selection

**Volkov Sergey.** Preprint, 10 October 2026.

The paper proves `T₃ ≤ (5/6 − 10⁻²⁰) E` for finite planar residual frames and derives
`F_weighted(2,2,3) ≤ 11/6 − 10⁻²⁰` for minimum-Frobenius-norm regression.
It does not determine the conjectured sharp value 13/8.

- [Preprint PDF](preprint.pdf)
- [Standalone LaTeX source](preprint.tex)
- [Lean source](lean/Scalar.lean)
- [Compiler/axiom audit](verification/lean-check.json)

## Exact formalized scope and noncircularity

This is **partial formal verification**, not a Lean proof of the full geometric/regression theorem.
There is no formal definition of `T₃` or regression learners in the Lean package.
The paper supplies the geometric arguments separately.

| Lean theorem | Assumptions | Proven conclusion / role |
| --- | --- | --- |
| `certificate_identity`, `cost_identity` | Arbitrary real parameters; nonnegative `a,b` for the cost conversion | Exact polynomial/rational identities in the scalar proof |
| `scalar_moment_selection` | Finite nonnegative `p,a,b`; sum `p=1`; `0≤r≤1`; means `a=r`, `b=1−r` | A positive-weight atom has scalar cost at most 5/6 |
| `scalar_anisotropy_selection` | Exactly the same finite moment assumptions | A positive-weight atom has cost at most `5/6−(11/60)(2r−1)²` |
| `scalar_relaxation_optimal` | Arbitrary real proposed bound `c` | Universal scalar bound holds iff `5/6≤c`; the sharpness witness is a valid scalar distribution, not a frame |
| `isotropic_ratio_bound` | `c²≤1/4`; arbitrary real `d` | The unit-output comparison ratio is at most 26/9 |
| `quantitative_numeric_contradiction` | Bounds on `δ,ζ`, a nonnegative `t` with `t²=ζ`, and the stability deficit inequality | These numerical estimates are inconsistent at `ε=10⁻²⁰`; **the geometric estimates are not derived in Lean** |

The finite scalar selection theorems assume neither the desired selection bound nor the existence of a selected atom.
The conditional numerical lemma is not presented as a proof of the frame theorem.
No conclusion-equivalent frame bound is hidden in a formalized geometric theorem: no such theorem is claimed here.
The source contains no `sorry`, `admit`, custom axiom or `native_decide`.
All 16 audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

The source was checked as one file using the Lean community web server's `mathlib-stable` project.
The record includes the SHA-256 of the exact source, Lean version, all compiler diagnostics and all 16 axiom reports.
The captured remote dependency manifest is included for provenance; it is not the local package manifest.
No local `lake build` was performed on the authoring machine because Lean was not installed there.

Local reproduction with Lean/Elan installed:

```sh
cd lean
lake update
lake exe cache get
lake build
```

The toolchain is Lean 4.34.0 and Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`.

Alternatively, with Node.js 22 or later:

```sh
node lean/check_lean.mjs lean/Scalar.lean mathlib-stable lean-check.jsonl
```

The checker waits for an end-of-file compiler marker, rejects compiler errors and nonstandard audited axioms,
and checks that all 16 axiom reports were received. The remote stable project may change in the future;
use the pinned local toolchain for exact reproduction.

Exact supplementary algebra checks:

```sh
python -m pip install -r requirements.txt
python verify_exact.py
```

These symbolic checks supplement the proof and do not establish its geometric steps.

## Primary references

- Hanneke, Moran, Shlimovich and Yehudayoff, [Open Problem: Data Selection for Regression Tasks](https://proceedings.mlr.press/v291/hanneke25e.html), COLT 2025.
- Hanneke, Moran, Shlimovich and Yehudayoff, [Data Selection for ERMs](https://arxiv.org/abs/2504.14572), 2025.
- Zhang, [Exact Recovery Thresholds for Weighted Data Selection in Vector-Valued Linear Regression](https://arxiv.org/abs/2608.30254v2), version 2, 2026.
