# A strict upper bound for three-point weighted selection

**Volkov Sergey.** Preprint, 5 November 2026. Six pages.

The paper proves the existence of a universal constant `ε₀ > 0` such that
`T₃ ≤ (5/6 − ε₀) E` for finite planar residual frames. It derives
`13/8 ≤ F_weighted(2,2,3) ≤ 11/6 − ε₀ < 11/6` for minimum-Frobenius-norm regression.
This revision does not specify a numerical value of `ε₀` or determine the sharp value.
It supersedes the earlier numerical version in this repository's history.

- [Preprint PDF](preprint.pdf)
- [Standalone LaTeX source](preprint.tex)
- [Lean source](lean/Scalar.lean)
- [Compiler and axiom audit](verification/lean-check.json)
- [Revision audit and limitations](verification/revision-audit.txt)
- [Continuous verification](https://github.com/nZiben/weighted-selection-gap/actions/workflows/lean.yml)

## Formalized scope and noncircularity

This is **partial formal verification**. The Lean package does not define `T₃`
or regression learners and does not prove the full frame or regression theorem.
The planar lemma, equality rigidity, support reduction, compactness and regression
bridge are supplied by the written proof.

| Lean theorem | Assumptions | Conclusion |
| --- | --- | --- |
| `certificate_identity`, `cost_identity` | Real parameters; nonnegative `a,b` for the rational identity | Exact identities used in the scalar proof |
| `scalar_moment_selection` | Finite nonnegative `p,a,b`; sum `p=1`; `0≤r≤1`; means `a=r`, `b=1−r` | A positive-weight atom has scalar cost at most `5/6` |
| `scalar_anisotropy_selection` | The same scalar moment assumptions | A positive-weight atom has cost at most `5/6−(11/60)(2r−1)²` |
| `scalar_relaxation_optimal` | A real proposed bound `c` | A universal scalar bound holds exactly when `5/6≤c` |
| `isotropic_equality_impossible` | `c²≤1/4`; arbitrary real `d` | `7c²−2cd−3d²<2`, the algebraic obstruction to equality |

The selection theorems assume neither the desired selection bound nor the existence
of the selected atom. Their moment hypotheses are derived from the frame in the paper.
The one-atom sharpness example concerns the scalar relaxation, not an extremal frame.
The source contains no `sorry`, `admit`, custom axiom or `native_decide`.
The 11 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
their transitive dependencies are included in these axiom reports.

## Reproduction

Install Lean/Elan, then run from the repository root:

```sh
cd lean
lake exe cache get
lake build
cd ..
python lean/check_local.py
```

The toolchain is Lean 4.34.0. Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`; the complete dependency lockfile is
`lean/lake-manifest.json`. The GitHub Actions workflow performs the build and axiom audit.
The checked source hash, CI run, and compiler output are recorded in `verification/`.
The checker requires successful compilation, an end-of-file marker, exactly 11 axiom
reports, and no audited axioms outside the three listed above.

Supplementary exact algebra checks:

```sh
python -m pip install -r requirements.txt
python verify_exact.py
```

These symbolic checks do not establish the geometric or compactness arguments.
The LaTeX source has an embedded bibliography and can be compiled twice with `pdflatex`.

## Primary references

- Hanneke, Moran, Shlimovich and Yehudayoff, [Open Problem: Data Selection for Regression Tasks](https://proceedings.mlr.press/v291/hanneke25e.html), COLT 2025.
- Hanneke, Moran, Shlimovich and Yehudayoff, [Data Selection for ERMs](https://arxiv.org/abs/2504.14572), 2025.
- Zhang, [Exact Recovery Thresholds for Weighted Data Selection in Vector-Valued Linear Regression](https://arxiv.org/abs/2608.30254v2), version 2, 2026.
