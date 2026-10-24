# Limitations — what is and is not proved here

Grades: **[LEAN]** kernel-checked in this repository; **[HYP]** proved, but under a hypothesis
that is itself not derived here; **[NOT PROVED]** stated in the papers, not formalized here;
**[OUT OF SCOPE]** not a mathematical claim of this library.

## Setting

* [LEAN] Everything is finite-dimensional: complex square matrices (`Matrix n n ℂ`, `Fintype n`)
  or an arbitrary ring for the purely algebraic tangent law. Infinite-dimensional Hilbert
  spaces, unbounded operators and trace-class conditions are **not** covered.
* [LEAN] The "Grassmannian" is represented pointwise: a projector `P` with `IsStarProjection P`
  and its tangent vectors `V` (Hermitian, `V = PV + VP`). The manifold structure of
  `Gr(k, ℂⁿ)` (charts, smoothness, the tangent bundle as a bundle) is **not** built. Mathlib's
  `Module.Grassmannian` is an algebraic (quotient-module) Grassmannian and is not used.
* No Riemannian/spacetime metric API is used on purpose; the IQGT form is the primitive.

## Core

* [LEAN] Tangent law, off-diagonal decomposition, redistribution operator, Sylvester/gap
  identity, second resolvent identity (`IQGTCore.Tangent`).
* [LEAN] Hermitian form, positivity, `g = ½ Re Tr(VW)`, Gram inequality
  `(Im Q)² ≤ g_VV g_WW − g_VW²`, `Ω² ≤ 4 det g`, rigidity, unitary invariance (`IQGTCore.Form`).
* [LEAN] Block form, tangent space = cross-gap blocks, two-level saturation, sharpness of 4
  (`IQGTCore.Blocks`).
* [LEAN] Equality in the Gram inequality *in general* is only covered in vector form:
  `saturation_iff_complex_line` (a restatement of Mathlib's `norm_inner_eq_norm_iff` for
  vectors in a complex inner product space). It is **not** yet transported to the matrix
  statement `metric_control` (i.e. "equality iff `WP` is a complex multiple of `VP`" for
  matrices is [NOT PROVED] here).
* Sign convention: `curvature = 2 Im Q` (as in `IqgtGrassmannian/Basic.lean`); the PR #1
  block-form file used `Ω = −2 Im Q`. All inequalities involve `Ω²`, so they are unaffected;
  signed statements (`curvature_antisymm`) use this file's convention.

## Spectral reading

* [HYP] `Q_sylvester`, `metric_sylvester`, `metric_sylvester_eq_pairSum`: the cross-gap block `X`
  of the tangent is *assumed* to satisfy the first-order response (Sylvester) equation
  `X_ij (e_i − f_j) = A_ij`. That the derivative of a spectral (Riesz) projector satisfies this
  equation — the analytic Kato/Riesz contour-integral step — is [NOT PROVED]. Mathlib has
  `spectrum.resolvent` and the resolvent set but no Riesz projection / contour-integral
  projector API that this could be built on today.
* [LEAN] `pairSum` log-convexity, gap ladder, single-gap equality. The *equality case* of
  log-convexity for several distinct gaps (equality iff all coupled gaps are equal) is
  [NOT PROVED]; only the single-gap direction (`pairSum_sq_eq_of_single_gap`) is.
* [OUT OF SCOPE] The physical identification of `pairSum` at powers −2, −1, 0, +1 with metric,
  polarisability, spread and f-sum budget, and any statement about extinction length,
  refraction or a propagation law (including the Galilean-Variance comparison). Only the
  finite algebra is formalized.

## Bridges

* UPG [LEAN]: coupling energy = IQGT metric of the redistribution tangent; decoupling iff zero
  speed; interface persistence; commutator energy = 2Q. The UPG library's real-matrix lemmas
  are **re-proved** in the complex setting, not imported; the remaining UPG files (torus
  anchor, Dirac refraction, resolvent feedback, obstruction, spectrum) are not bridged.
* Connection energy [LEAN, single edge only]: two books for a projector field, budget,
  difference, chordal distance = 2 × squared cross-gap block (equal ranks), unitary edge form.
  The **graph-level** identity `⅛‖[H,H*]‖² = Σ_edges ‖D_i − U D_j U*‖²` and the opposite-book
  identity are in `nonnormality-connection-energy-lean` and are [NOT RE-PROVED] here. There is
  **no** proof that the self-commutator energy of a general `H = D + A` equals an IQGT metric;
  that would be an overclaim.
* Dirac time [LEAN/HYP]: friction as a spectrally reweighted IQGT pair sum, band and null
  directions. The derivation of the pairwise friction formula from a bath/relaxation model is
  [NOT PROVED] (also not in `dirac-time-lean`). The excess-work bound (thermodynamic length² /
  time) appears only in its discrete Cauchy–Schwarz form `length_sq_le`.
* Gravity ledger [LEAN]: the ledger's reciprocal (signed) determinant is indefinite and is
  **not** a pullback of the IQGT form — the bridge records the contrast, it does not unify
  them. The projector-overlap Taylor bridge and the local overlap cap of `GravityOverlap.lean`
  are [NOT BRIDGED].
* Light ledger [LEAN/HYP]: the summed transition metric equals the IQGT metric of the response
  tangent (under the Sylvester hypothesis); polarisability = response weight × IQGT metric at
  a single gap. Boundary elimination (Schur lift, Smith transform), census, coherence and the
  Edition 7.2 spectral bounds are [NOT BRIDGED].

## Not included at all

* Mixed states beyond the SLD algebraic core; non-abelian (Wilczek–Zee) curvature; the exact
  gap-closing case; Davis–Kahan as an inequality (only its Sylvester identity is here);
  data-analysis claims (transmon readout, BEC images) — those are numerical and live in the
  papers' scripts.
