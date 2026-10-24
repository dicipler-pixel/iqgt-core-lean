# IQGT core — Lean 4 + Mathlib

**The intrinsic quantum geometric tensor `Q_P(V,W) = Tr(PVW)` as the primitive geometry, and
Jeromie Beasley's operator-first libraries read through it.**

Jeromie Beasley · ORCID [0009-0006-4645-5643](https://orcid.org/0009-0006-4645-5643)

- X: [@d1c1pler](https://x.com/d1c1pler)
- GitHub: [dicipler-pixel](https://github.com/dicipler-pixel)
- YouTube: [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae)
- Web: [atlas-memoriae.dicipler.workers.dev](https://atlas-memoriae.dicipler.workers.dev)

Status: **private, in development.** Toolchain `leanprover/lean4:v4.35.0`, Mathlib tag `v4.35.0`
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, the newest stable Mathlib release on
2026-10-24). No `sorry`, no new axioms; CI audits every declaration's axioms.

## Not a standard metric

This library deliberately does **not** route anything through a Riemannian or spacetime metric
(no `Mathlib.Geometry.Manifold` Riemannian API). The geometry is the intrinsic
Hilbert–Schmidt / Fisher form on projector tangents:

* a tangent at an orthogonal projector `P` is a Hermitian `V` with `V = PV + VP`;
  every such `V` is purely **cross-gap** (`PVP = 0`, `(1-P)V(1-P) = 0`);
* `Q_P(V,W) = Tr(PVW)`; metric `g = Re Q`, curvature `Ω = 2 Im Q`;
* other libraries' quantities are stated as consequences or reweightings of this form, and
  only where that is honestly provable (see `LIMITATIONS.md` for what is not).

## Modules

| Module | What it proves |
|---|---|
| `IQGTCore.Tangent` | Ring-level tangent law (`tangent_iff_blocks`, `IsTangent.eq_offdiag`), redistribution operator (`redist_isTangent`, `redist_eq_zero_iff`), SLD core, silent second order, gap/Sylvester identity, second resolvent identity. |
| `IQGTCore.Form` | `Q`, `metric`, `curvature`; Frobenius form `Q_eq_frobenius`; Hermitian symmetry `Q_swap`; positive definiteness `metric_pos`; `metric_eq_half_re_trace` (g = ½ Re Tr VW); **Gram inequality** `metric_control`, `curvature_sq_le` (Ω² ≤ 4 det g); `rigidity`; unitary invariance `Q_unitary_conj`. |
| `IQGTCore.Blocks` | Adapted blocks: tangent space = cross-gap blocks (`isTangent_iff_eq_offDiag`), `Q_offDiag` (Q = Tr XYᴴ = Σ X_ij conj Y_ij), **two-level saturation** (`two_level_saturation`), sharpness of the constant 4 (`curvature_factor_four_sharp`). |
| `IQGTCore.Spectral` | Inverse-gap-squared form of Q and g from the Sylvester response equation (`Q_sylvester`, `metric_sylvester`), partial-fraction residue step, **one cross-gap pair sum at gap powers** `pairSum` with log-convexity `pairSum_sq_le` (polarisability² ≤ metric·spread, spread² ≤ polarisability·f-sum), gap ladder, single-gap equality. |
| `IQGTCore.Bounds` | Scalar bounds and equality cases from the IQGT paper (ported from the PR #1 branch): friction band, length form and constant-speed equality, HS gap step and its equality case, Cauchy–Schwarz block bound and complex-line equality, principal-angle sandwich. |
| `IQGTCore.Bridge.UPG` | UPG coupling energy = IQGT metric of the redistribution tangent (`metric_redist`, `metric_redist_real`), decoupling iff zero speed, interface persistence, commutator energy = 2Q. |
| `IQGTCore.Bridge.ConnectionEnergy` | Two books of a projector field: budget and difference; chordal distance = twice the squared cross-gap block (`connection_book_eq_two_cross`); unitary edge form; tangent form. |
| `IQGTCore.Bridge.DiracTime` | Friction on projector rotations = spectrally reweighted IQGT pair sum (band, same null directions); ported Gibbs/tanh pair algebra. |
| `IQGTCore.Bridge.GravityLedger` | IQGT Gram determinant ≥ 0 vs. the ledger's indefinite reciprocal determinant; the curvature-proxy hypothesis is exactly the IQGT bound; non-Hermitian false control (`Q_nonHermitian_negative`); moving-wall chart is idempotent. |
| `IQGTCore.Bridge.LightLedger` | Light-ledger's transition metric is the IQGT metric of the response tangent (`metric_eq_sum_transitionMetric`); polarisability = response weight × IQGT metric at a single gap; static polarisability² ≤ 4·metric·spread. |

The "meeting point" with the Galilean-Variance comparison note (extinction length / refraction
as one cross-gap pair sum read at gap powers ω⁻² metric, ω⁻¹ polarisability, ω⁰ spread, ω⁺¹
f-sum) appears here only as the exact finite algebra of `pairSum`; no propagation law is claimed.

## Build

```
lake exe cache get
lake build
lake env lean verification/AxiomAudit.lean
```

See `MATHLIB_STATE.md` for how this sits against current Mathlib and where the older libraries
duplicate Mathlib or need updates.

## Credits

**Jeromie Beasley (author).** The research program, the papers, the IQGT construction, the
choice of the projector as primitive, every statement's mathematical content, and the original
Lean libraries this repository ports from: `iqgt-grassmannian-lean` (including the PR #1 branch
`claude-rebuild-sections-2-6`), `upg-lean`, `dirac-time-lean`, `gravity-ledger-lean`,
`light-ledger-lean`, `nonnormality-connection-energy-lean`. Papers: IQGT
(doi:10.5281/zenodo.20768258), Light Keeps the Ledger (10.5281/zenodo.22123115), The Ledger
Outlives the Metric (10.5281/zenodo.22023237), Universal Projector Geometry
(10.5281/zenodo.21305024), The Dirac Time of the Gigantefermion (10.5281/zenodo.22978630),
Non-Normality Is Connection Energy (10.5281/zenodo.22803572).

**Prior published work (standard background, not claimed as new here).** The quantum geometric
tensor (Provost & Vallée 1980) and Berry curvature (Berry 1984); Kato's perturbation theory of
spectral projectors; the Davis–Kahan sin θ theorem (1970); quantum Fisher information and the
symmetric logarithmic derivative (Helstrom; Braunstein & Caves 1994); thermodynamic length and
friction tensors (Salamon & Berry 1983; Sivak & Crooks 2012); Cauchy–Schwarz and Lagrange's
identity. The formal library builds on **Mathlib** (the Mathlib community, Apache-2.0), which
supplies `IsIdempotentElem`, `IsStarProjection`, `Matrix.PosSemidef`, `Matrix.trace`,
`norm_inner_le_norm`, `norm_inner_eq_norm_iff`, `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`,
and the tactics used.

**AI assistance.** This repository was assembled, ported to Mathlib v4.35.0 and extended by
Grok Bot (an AI assistant acting for Jeromie Beasley) on 2026-10-24. Several ported proofs
were originally written with AI help in the source repositories (their `AI_USE.md` files name
Claude and ChatGPT). No statement rests on an AI's say-so: every theorem is checked by the Lean
kernel, and the axiom audit runs on every push. What the statements mean and do not mean is in
`LIMITATIONS.md`.

## License

MIT OR Apache-2.0 (see `LICENSE`), matching the author's other Lean libraries.
