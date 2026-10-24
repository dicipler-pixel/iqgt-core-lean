# MATHLIB_STATE — where IQGT core and the older libraries sit against current Mathlib

Jeromie Beasley · ORCID 0009-0006-4645-5643 ·
X [@d1c1pler](https://x.com/d1c1pler) · GitHub [dicipler-pixel](https://github.com/dicipler-pixel) ·
YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) ·
[atlas-memoriae.dicipler.workers.dev](https://atlas-memoriae.dicipler.workers.dev)

Checked 2026-10-24 (America/Chicago). Every Mathlib name below was found by `grep` in the
Mathlib source tree this repo builds against and, where marked ✓, also confirmed with `#check`
in a live Lean session. Anything not checked that way is marked **UNVERIFIED**.

## 1. Versions

| Item | Value |
|---|---|
| Lean used here | `leanprover/lean4:v4.35.0` |
| Mathlib used here | tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (newest stable tag on 2026-10-24) |
| Mathlib master on 2026-10-24 | `0b57f692…` on `v4.36.0-rc1` (release candidate; deliberately not used) |

Toolchain pins of the existing repos (read from each `lean-toolchain`, not changed):

| Pin | Repos |
|---|---|
| v4.34.1 | iqgt-grassmannian-lean (main and PR #1 branch), dirac-time-lean, nonnormality-connection-energy-lean, relational-atlas-lean, coboundary-k3, electron-screening, emergent-transport, event-horizon, filament-fracture, foft, matter-at-a-scale, price-of-a-direction, ramanujan-challenge, spectral-stability, spectral-stress, suns, three-body, votkp, what-russell-saw, what-tesla-saw, what-transport-keeps |
| v4.33.0 | light-ledger-lean, gravity-ledger-lean, upg-lean, yang-mills-lean, arithmetic-kakeya-finite-bridges, coxeter-rank2, elemental-peeling, offset, small-diophantine, square-case |
| v4.29.1 | acwindow-lean (private) |
| v4.28.0 | sqrt-lower-bound-lean |

So every library is 1–7 minor versions behind the current stable Mathlib.

## 2. Does the old code still compile on v4.35.0?

Method: each `.lean` file of each repo was compiled with `lean` against Mathlib v4.35.0, in
import order (`/workspace/iqgt_port/compile_all.py` on the build box). **Caveat:** this is a
single-file compile, not `lake build`, so lakefile options (e.g. `autoImplicit`, custom
`srcDir`, extra packages) are not applied. Failures marked *(setup)* come from that, not from
Mathlib drift. Nothing was pushed to any of these repos.

| Repo | Real files OK | False controls rejected | Notes |
|---|---|---|---|
| iqgt-grassmannian-lean main `5dec080` | 1/1 | 3/3 | |
| iqgt-grassmannian-lean PR #1 branch `e52db89` | 3/3 | 6/6 | uses `push_neg` (deprecated) |
| upg-lean `79cd730` | 12/12 | 1/1 | |
| dirac-time-lean `e8a4c86` | 16/18 | 13/13 | `UnitaryEntropy` needs the external `QuantumInfo` package *(setup)*; root file skipped as a result |
| gravity-ledger-lean `885932f` | 2/2 | 4/4 | |
| light-ledger-lean `885794f` | 13/13 | 6/6 | uses deprecated `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` |
| nonnormality-connection-energy-lean `a66bfe4` | 15/15 | 17/17 | |
| arithmetic-kakeya, coboundary-k3, coxeter-rank2, electron-screening, elemental-peeling, emergent-transport, event-horizon, filament-fracture, foft, matter-at-a-scale, price-of-a-direction, ramanujan-challenge, small-diophantine, spectral-stability, spectral-stress, square-case, suns, three-body, votkp, what-tesla-saw, what-transport-keeps, relational-atlas, yang-mills | all OK | all rejected | deprecation warnings in several (ramanujan 18, arithmetic-kakeya 14, square-case 10, three-body 6) |
| offset-lean | 9/13 | 13/15 (2 skipped) | **genuine break:** `OperatorFirst/EndpointTransfer.lean` lines 161/183, `rfl` now fails; `OffsetLean` root *(setup)* |
| sqrt-lower-bound-lean (pinned v4.28) | 6/30 | 1/1 | **genuine breaks:** `RectangularCore.lean` (rewrite at 75, type mismatch at 397–398) and `EntropyLaw.lean:71`; the remaining failures cascade from those; 164 deprecation mentions |
| what-russell-saw-lean | 2/4 | 3/3 | `Audit` and `RussellPhyslib` need other packages (`RussellRebuild`, `Physlib`) *(setup)* |
| acwindow-lean | 1/3 | – | `AC` module prefix *(setup)* |
| -connection-energy-lean | see map doc | | compiled separately |

No file in any repo produced a `sorry` warning in this run.

## 3. What IQGT core takes from Mathlib (all ✓ by `#check` or by building)

* Idempotents / projectors: `IsIdempotentElem`, `IsIdempotentElem.one_sub`,
  `IsIdempotentElem.mul_one_sub_self`, `IsIdempotentElem.one_sub_mul_self`,
  `IsStarProjection` (Algebra/Star/StarProjection.lean).
* Positivity: `Matrix.posSemidef_conjTranspose_mul_self`, `Matrix.PosSemidef.det_nonneg`,
  `Matrix.PosSemidef.trace_nonneg`, `Matrix.trace_conjTranspose_mul_self_eq_zero_iff`,
  `Complex.nonneg_iff` (with `open scoped ComplexOrder`).
* Blocks: `Matrix.fromBlocks_multiply`, `Matrix.fromBlocks_conjTranspose`, `Matrix.fromBlocks_add`, …
* Trace: `Matrix.trace_mul_comm`, `Matrix.trace_conjTranspose`, `Matrix.trace_sub`, …
* Inequalities: `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` (the `_eq_mul` form is deprecated
  since 2026-05-12), `zpow_add_one₀`, `zpow_sub_one₀`.

## 4. Where the older libraries re-prove Mathlib (exact names both sides)

| His declaration | Repo | Mathlib already has |
|---|---|---|
| `proj_mul_compl`, `compl_mul_proj` | upg-lean `UPGAlgebra`, iqgt PR #1 `Core`, `Rebuild` | `IsIdempotentElem.mul_one_sub_self`, `IsIdempotentElem.one_sub_mul_self` |
| `compl_idempotent` | upg-lean `UPGAlgebra` | `IsIdempotentElem.one_sub` |
| Hermitian + idempotent hypothesis pairs (`P*P=P`, `Pᴴ=P`) | upg, dirac-time, gravity, iqgt | `IsStarProjection` (bundles both) |
| `two_level_population_gap` (tanh as exp quotient) | dirac-time `FrictionMetric` | `Real.tanh_eq` (`tanh x = (exp x - exp (-x)) / (exp x + exp (-x))`) — a short `rw` away (judgement, not re-proved here) |
| `tanh_exp` (`tanh t = (exp 2t - 1)/(exp 2t + 1)`) | votkp `Smith` | follows from `Real.tanh_eq`; no direct Mathlib lemma of that exact form (ABSENT, searched `tanh_exp`, `tanh_eq`) |
| `constant_of_silent` | iqgt PR #1 `Rebuild` | thin wrapper around `is_const_of_deriv_eq_zero` |
| `saturation_iff_complex_line` | iqgt PR #1 `Rebuild` | thin wrapper around `norm_inner_eq_norm_iff` |
| `frobenius_norm_sq` | nonnormality `Frobenius` | **not** in Mathlib in squared form; Mathlib has `Matrix.frobenius_norm_def` (with `^ (1/2)`) |
| `frob_eq_sum` with own `frob` | -connection-energy-lean | could be stated through `Matrix.frobenius_norm_def` / `Matrix.frobeniusNormedAddCommGroup` |
| `trace_proj_mul` (`trace(uuᵀ vvᵀ) = (u⬝v)²`) | price-of-a-direction | `Matrix.trace_vecMulVec` + `Matrix.vecMulVec_mul_vecMulVec` |
| Gram constructions (`gram_entries`, `gram_det_nonneg` via an explicit 2×2 matrix) | iqgt main / PR #1 `Basic` | `Matrix.gram`, `Matrix.posSemidef_gram` (InnerProductSpace/GramMatrix.lean) |
| tangent law, 6 separate copies (`tangent_offdiag`, `tangent_of_blocks`, `tangent_iff_blocks_zero`, `tangent_split`, `mul_mul_eq_zero_of_tangent`, …) | iqgt main, PR #1 (`Basic`, `Core`, `Rebuild`), dirac-time `ProjectorTangent`, gravity `Gravity`, nonnormality `Admissible` | not in Mathlib; **IQGT core now holds one copy** (`IQGT.tangent_iff_blocks`, `IQGT.IsTangent.eq_offdiag`) that the others could import |

ramanujan-challenge already reuses `hasSum_zeta_two` correctly.

## 5. Mathlib gaps (checked absent by grep and by searching all constant names)

| Gap | Search terms used | Status | His candidate |
|---|---|---|---|
| `trace (fromBlocks A B C D) = trace A + trace D` | `trace_fromBlocks` | ABSENT | `IQGT.trace_fromBlocks'`, upg `trace_fromBlocks_diag` |
| Hilbert–Schmidt / Frobenius inner product on matrices | `frobenius_inner`, `Matrix.inner` | ABSENT, open PR #41477 ("add Hilbert-Schmidt inner product and norm", last updated 2026-08-03) | wait for #41477; don't duplicate |
| Unitary invariance of the Frobenius norm | `frobenius_norm_unitary`, `unitary.*frobenius` | ABSENT | nonnormality `frobenius_norm_unitary_mul`, `frobenius_norm_mul_unitary` |
| Squared Frobenius norm as a double sum | `frobenius_norm_sq` | ABSENT | nonnormality `frobenius_norm_sq` |
| Quantum geometric tensor / Fubini–Study form on projectors, SLD, quantum Fisher information | `QGT`, `Fisher`, `symmetricLogarithmic` | ABSENT | IQGT core `Form` / `Tangent` (research-level, not upstream-ready) |
| Riesz (contour-integral) spectral projection | `rieszProj`, `spectralProj`, `igenproj`, `contour` | ABSENT (only Riesz lemma / Riesz–Markov–Kakutani / Herglotz–Riesz kernel exist) | none; the Sylvester hypothesis in `IQGT.Spectral` stays a hypothesis |
| Grassmannian ↔ projector matrices | `Grassmannian` with `proj`, `idempot`, `starProj`, `Matrix` | ABSENT. `Module.Grassmannian R M k` is the algebraic quotient-module Grassmannian; Mathlib links submodules to projections only via `Submodule.starProjection` | IQGT core states everything on projectors, no manifold |
| tanh addition formula | `tanh_add` | ABSENT (only `Complex.tanh_add_pi_mul_I`) | votkp `tanh_add'` |
| `(z-1)/(z+1) = tanh (log z / 2)` | `tanh_log`, `log.*tanh` | ABSENT (nearest: `Real.artanh_eq_half_log`, `Real.tanh_artanh`) | votkp `smith_identity` |
| Davis–Kahan sin θ | `DavisKahan`, `sin_theta` | ABSENT | none in Lean yet |
| Rank-2 Coxeter group = dihedral group | `Dihedral` in GroupTheory/Coxeter | ABSENT | coxeter-rank2-lean |

Present, so **not** gaps: PSD Schur complement `Matrix.PosDef.fromBlocks₁₁` / `Matrix.PosDef.fromBlocks₂₂`
✓ (note: Mathlib's own module docstring calls them `Matrix.PosSemidef.fromBlocks₁₁`, which does
not exist as a constant), `Matrix.schur_complement_eq₁₁` ✓, `Matrix.det_fromBlocks₁₁` ✓,
`Matrix.IsHermitian.spectral_theorem` ✓, `Matrix.IsHermitian.eigenvectorUnitary` ✓,
`Real.tanh_eq` ✓, `Real.tanh_eq_sinh_div_cosh` ✓, `IsStarProjection`,
`LinearMap.IsIdempotentElem.trace_eq_zero_iff` ✓.

## 6. Mathlib PRs by dicipler-pixel

| PR | Title | State | Closed |
|---|---|---|---|
| #43703 | feat(GroupTheory/Coxeter): identify rank-two Coxeter groups with dihedral groups | **closed, not merged** | 2026-10-07 07:51 CDT, by `mathlib-triage` with the message that it "does not meet community standards for the use of AI" |
| #43951 | feat(Matrix/Trace): trace identity for idempotent differences | closed, not merged | 2026-09-18 14:02 CDT (reason not stated in the last comments; UNVERIFIED) |

His fork `dicipler-pixel/mathlib4` also has prepared branches (names read via the GitHub API,
contents not reviewed, UNVERIFIED): `feat/idempotent-tangent-decomposition`,
`feat/matrix-trace-idempotent-difference`, `feat/matrix-psd-weighted-sum-mono`,
`feat/laurent-degree-add-mul`, `feat/laurent-matrix-det-degree`, `feat/coxeter-i2-dihedral`.

**Practical consequence.** Mathlib's AI-use policy
(<https://leanprover-community.github.io/contribute/#use-of-ai>) is now the binding constraint
for any upstream contribution, more than the mathematics. Any of the gaps above should go
upstream only as a small PR he can explain and defend line by line himself, with review
comments answered in his own words.

## 7. Deprecations to fix when the old repos are bumped

* `push_neg` → `push Not` (iqgt PR #1, filament-fracture, matter-at-a-scale, sqrt-lower-bound,
  square-case, votkp).
* `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` → `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`
  (light-ledger).
* `orthogonalProjection` → `Submodule.starProjection` (deprecated 2026-05-05; no current
  use found in his repos).
* `Data.Matrix.Notation` import moved to `LinearAlgebra.Matrix.Notation`.
