/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scalar bounds and equality cases of the IQGT paper

Ported, with proofs essentially unchanged, from `iqgt-grassmannian-lean` PR #1 branch
`claude-rebuild-sections-2-6` (`IqgtGrassmannian/Rebuild.lean`, commit `e52db89`), re-checked on
Mathlib `v4.35.0`. These are the scalar steps the matrix statements in `IQGTCore.Form` /
`IQGTCore.Spectral` reduce to:

* friction band and length form (`friction_band`, `length_sq_le`, `constant_speed_iff`);
* Hilbert–Schmidt step of the gap bound and its equality case (`gap_bound_hs_step`,
  `gap_bound_hs_step_eq_iff`);
* the block-form curvature bound via Cauchy–Schwarz in `EuclideanSpace ℂ ι`
  (`curvature_bound`) and its equality case on the complex line
  (`saturation_iff_complex_line`, a restatement of Mathlib's `norm_inner_eq_norm_iff`);
* principal-angle sandwich (`sofic_sandwich`, `sandwich_upper_eq_iff`).

Several of these are thin wrappers of Mathlib lemmas (`Finset.sum_mul_sq_le_sq_mul_sq`,
`norm_inner_le_norm`, `norm_inner_eq_norm_iff`, `Real.sin_le`, `Real.mul_le_sin`,
`is_const_of_deriv_eq_zero`); they are kept so the paper's numbering has a Lean anchor.
-/

namespace IQGT

open BigOperators

section Friction
variable {ι : Type*}

/-- Theorem 5.3(ii), the zero-temperature band: a reweighting of the metric by weights in `[lo, hi]`. -/
theorem friction_band (s : Finset ι) (w g : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i)
    (lo hi : ℝ) (hlo : ∀ i ∈ s, lo ≤ w i) (hhi : ∀ i ∈ s, w i ≤ hi) :
    lo * ∑ i ∈ s, g i ≤ ∑ i ∈ s, w i * g i ∧ ∑ i ∈ s, w i * g i ≤ hi * ∑ i ∈ s, g i := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_right (hlo i hi') (hg i hi')
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_right (hhi i hi') (hg i hi')

/-- Theorem 5.3, length form (discretised): `(Σ √gᵢ)² ≤ N · Σ gᵢ`, the step `ℒ² ≤ T ∫ g`. -/
theorem length_sq_le (s : Finset ι) (g : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, Real.sqrt (g i)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, g i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (g i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  calc (∑ i ∈ s, Real.sqrt (g i)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, Real.sqrt (g i) ^ 2 := h
    _ = (s.card : ℝ) * ∑ i ∈ s, g i := by
        congr 1; exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hg i hi)

end Friction

section Transport
/-- §7.2: friction read from the response function, one pair at a time:
`2Δg·τ/(1+τ²Δ²) = τ·[2Δg − 2Δ³g/(Δ² + 1/τ²)]`, i.e. `ζ_rot = τ[α(0) − α(i/τ)]`. -/
theorem friction_response_pair (Δ g τ : ℝ) (hτ : 0 < τ) :
    2 * Δ * g * τ / (1 + τ ^ 2 * Δ ^ 2) = τ * (2 * Δ * g - 2 * Δ ^ 3 * g / (Δ ^ 2 + 1 / τ ^ 2)) := by
  have h1 : (0 : ℝ) < 1 + τ ^ 2 * Δ ^ 2 := by positivity
  have h2 : (0 : ℝ) < Δ ^ 2 + 1 / τ ^ 2 := by positivity
  field_simp
  ring

/-- §7.5: the regularised pair metric is bounded at a closed gap: `a/(Δ² + η²) ≤ a/η²` for `a ≥ 0`. -/
theorem eta_regularised_bound (a Δ η : ℝ) (ha : 0 ≤ a) (hη : 0 < η) :
    a / (Δ ^ 2 + η ^ 2) ≤ a / η ^ 2 := by
  apply div_le_div_of_nonneg_left ha (by positivity)
  nlinarith [sq_nonneg Δ]

/-- §8.3, total internal reflection: if `C = g∥ sin²θ` with `sin²θ ≤ 1` and `g∥ ≥ 0`, then the
trajectory only visits `g∥ ≥ C`; at a stratum `g∥ = 0` it would need `C = 0`. -/
theorem reflection_bound (gpar s2 : ℝ) (hg : 0 ≤ gpar) (hs1 : s2 ≤ 1) :
    gpar * s2 ≤ gpar := by
  nlinarith

end Transport

section Bounds
variable {ι : Type*}

/-- §3, Proposition 3.5, the Hilbert–Schmidt step of the gap bound: dividing each entry of
`Π δΣ (1-Π)` by a gap of modulus at least `Δ` divides the sum of squared entries by at least `Δ²`.
This is the step that bounds the Hilbert–Schmidt norm (dividing entries does not, in general,
bound the operator norm). -/
theorem gap_bound_hs_step (s : Finset ι) (a d : ι → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hd : ∀ i ∈ s, Δ ≤ |d i|) :
    ∑ i ∈ s, a i ^ 2 / d i ^ 2 ≤ (∑ i ∈ s, a i ^ 2) / Δ ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hdi := hd i hi
  have hm := mul_le_mul hdi hdi hΔ.le (abs_nonneg (d i))
  have h1 : Δ ^ 2 ≤ d i ^ 2 := by nlinarith [sq_abs (d i)]
  have h2 : 0 < Δ ^ 2 := by positivity
  exact div_le_div_of_nonneg_left (sq_nonneg (a i)) h2 h1

/-- §12.4, lower half of the sandwich, one principal angle: `sin² θ ≤ θ²` on `[0, π/2]`. -/
theorem sin_sq_le_angle_sq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Real.sin x ^ 2 ≤ x ^ 2 := by
  have hs : Real.sin x ≤ x := Real.sin_le h0
  have hpos : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  nlinarith [mul_le_mul hs hs hpos h0]

/-- §12.4, upper half of the sandwich, one principal angle (Jordan's inequality):
`θ² ≤ (π/2)² sin² θ` on `[0, π/2]`. -/
theorem angle_sq_le_jordan (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    x ^ 2 ≤ (Real.pi / 2) ^ 2 * Real.sin x ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hj : 2 / Real.pi * x ≤ Real.sin x := by
    exact Real.mul_le_sin h0 h1
  have hpi' : Real.pi ≠ 0 := hpi.ne'
  have he : Real.pi / 2 * (2 / Real.pi * x) = x := by
    field_simp
  have hx : x ≤ Real.pi / 2 * Real.sin x := by
    calc x = Real.pi / 2 * (2 / Real.pi * x) := he.symm
      _ ≤ Real.pi / 2 * Real.sin x := mul_le_mul_of_nonneg_left hj (by positivity)
  calc x ^ 2 = x * x := sq x
    _ ≤ (Real.pi / 2 * Real.sin x) * (Real.pi / 2 * Real.sin x) :=
        mul_le_mul hx hx h0 (le_trans h0 hx)
    _ = (Real.pi / 2) ^ 2 * Real.sin x ^ 2 := by ring

/-- §12.4, the sandwich between the Hamming count and the intrinsic length: over principal
angles in `[0, π/2]`, `Σ sin² θ ≤ Σ θ² ≤ (π/2)² Σ sin² θ`. With `d_H = (2/n) Σ sin² θ` this is
`d_H / 2 ≤ (1/n) Σ θ² ≤ (π²/8) d_H`. -/
theorem sofic_sandwich (s : Finset ι) (θ : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ θ i)
    (h1 : ∀ i ∈ s, θ i ≤ Real.pi / 2) :
    ∑ i ∈ s, Real.sin (θ i) ^ 2 ≤ ∑ i ∈ s, θ i ^ 2 ∧
    ∑ i ∈ s, θ i ^ 2 ≤ (Real.pi / 2) ^ 2 * ∑ i ∈ s, Real.sin (θ i) ^ 2 := by
  refine ⟨Finset.sum_le_sum fun i hi => sin_sq_le_angle_sq _ (h0 i hi) (h1 i hi), ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => angle_sq_le_jordan _ (h0 i hi) (h1 i hi)

/-- §12.4, the displacement Gram eigenvalues of an `ℓ`-cycle come in pairs:
`2 sin²(π(ℓ-j)/ℓ) = 2 sin²(πj/ℓ)`, the sine and cosine of one cyclic motion. -/
theorem cycle_gram_pair (l j : ℝ) (hl : l ≠ 0) :
    2 * Real.sin (Real.pi * (l - j) / l) ^ 2 = 2 * Real.sin (Real.pi * j / l) ^ 2 := by
  have h : Real.pi * (l - j) / l = Real.pi - Real.pi * j / l := by
    field_simp
  rw [h, Real.sin_pi_sub]

end Bounds

section Curvature
variable {ι : Type*} [Fintype ι]

/-- Theorem 6.1 in block form. For the cross-gap blocks `x, y` of two tangent vectors,
`Q(V,W) = ⟪y, x⟫`, `g_VV = ‖x‖²`, `g_WW = ‖y‖²`, `g_VW = Re Q` and `Ω = −2 Im Q`. Then
`Ω² ≤ 4 (g_VV g_WW − g_VW²)`, which is Cauchy–Schwarz for the blocks. -/
theorem curvature_bound (x y : EuclideanSpace ℂ ι) :
    (2 * (inner ℂ y x).im) ^ 2 ≤ 4 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℂ y x).re ^ 2) := by
  have h1 : ‖inner ℂ y x‖ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm y x
  have h2 : ‖inner ℂ y x‖ ^ 2 = (inner ℂ y x).re ^ 2 + (inner ℂ y x).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h3 : ‖inner ℂ y x‖ ^ 2 ≤ (‖y‖ * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [h2, h3]

end Curvature

section Rigidity
variable {ι : Type*}

/-- §6.3 (i), one term of the gap bound: dividing by a gap at least `Δ` loses nothing exactly when
the entry vanishes or its gap is exactly `Δ`. -/
theorem gap_term_eq_iff (a d Δ : ℝ) (hΔ : 0 < Δ) (hd : Δ ≤ |d|) :
    a ^ 2 / d ^ 2 = a ^ 2 / Δ ^ 2 ↔ a = 0 ∨ |d| = Δ := by
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, abs_zero] at hd
    linarith
  have hdsq : d ^ 2 = |d| ^ 2 := (sq_abs d).symm
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
      have hΔ2 : Δ ^ 2 ≠ 0 := pow_ne_zero 2 hΔ.ne'
      rw [div_eq_div_iff hd2 hΔ2] at h
      have hsq : Δ ^ 2 = d ^ 2 := mul_left_cancel₀ ha2 h
      rw [hdsq] at hsq
      have habs : 0 ≤ |d| := abs_nonneg d
      nlinarith
  · rintro (h | h)
    · rw [h]; simp
    · rw [hdsq, h]

/-- §6.3 (i): equality in the Hilbert–Schmidt step of the gap bound holds exactly when every
coupled pair sits at gap exactly `Δ`. -/
theorem gap_bound_hs_step_eq_iff (s : Finset ι) (a d : ι → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hd : ∀ i ∈ s, Δ ≤ |d i|) :
    ∑ i ∈ s, a i ^ 2 / d i ^ 2 = (∑ i ∈ s, a i ^ 2) / Δ ^ 2 ↔
      ∀ i ∈ s, a i = 0 ∨ |d i| = Δ := by
  rw [Finset.sum_div]
  have hle : ∀ i ∈ s, a i ^ 2 / d i ^ 2 ≤ a i ^ 2 / Δ ^ 2 := by
    intro i hi
    have h := gap_bound_hs_step {i} a d Δ hΔ (by simpa using hd i hi)
    simpa using h
  rw [Finset.sum_eq_sum_iff_of_le hle]
  exact forall₂_congr fun i hi => gap_term_eq_iff (a i) (d i) Δ hΔ (hd i hi)

/-- §6.3 (iii) and (v), the two-number arithmetic–geometric mean step: `(a+b)² = 4ab` exactly
when `a = b` (the metric is conformal to the reference metric). -/
theorem am_gm_eq_iff (a b : ℝ) : (a + b) ^ 2 = 4 * a * b ↔ a = b := by
  constructor
  · intro h
    have h2 : (a - b) ^ 2 = 0 := by nlinarith
    have h3 : a - b = 0 := by
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    linarith
  · intro h; rw [h]; ring

/-- §6.3 (iii), constant speed: for the discrete length form `(Σ xᵢ)² ≤ N Σ xᵢ²`, the gap
`N Σ xᵢ² - (Σ xᵢ)²` is half the sum of all squared differences. -/
theorem length_gap_identity (s : Finset ι) (x : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (x i - x j) ^ 2 =
      2 * ((s.card : ℝ) * ∑ i ∈ s, x i ^ 2 - (∑ i ∈ s, x i) ^ 2) := by
  have e : ∀ i j, (x i - x j) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * (x i * x j) := fun i j => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  ring

/-- §6.3 (iii): the length form `(Σ xᵢ)² ≤ N Σ xᵢ²` is an equality exactly when the speed is
constant. -/
theorem constant_speed_iff (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, x i) ^ 2 = (s.card : ℝ) * ∑ i ∈ s, x i ^ 2 ↔
      ∀ i ∈ s, ∀ j ∈ s, x i = x j := by
  have hid := length_gap_identity s x
  have hnn : ∀ i ∈ s, 0 ≤ ∑ j ∈ s, (x i - x j) ^ 2 :=
    fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor
  · intro h i hi j hj
    have h0 : ∑ i ∈ s, ∑ j ∈ s, (x i - x j) ^ 2 = 0 := by rw [hid, h]; ring
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 i hi
    have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x i - x j)).mp hi0 j hj
    have : x i - x j = 0 := by
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hij
    linarith
  · intro h
    have h0 : ∑ i ∈ s, ∑ j ∈ s, (x i - x j) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => by rw [h i hi j hj]; ring
    rw [hid] at h0
    linarith

/-- §6.3 (iv), Corollary 6.2: the curvature bound is met exactly on the complex line of `V`.
This is equality in Cauchy–Schwarz over `ℂ` (Mathlib's `norm_inner_eq_norm_iff`), restated. -/
theorem saturation_iff_complex_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖inner ℂ x y‖ = ‖x‖ * ‖y‖ ↔ ∃ r : ℂ, r ≠ 0 ∧ y = r • x :=
  norm_inner_eq_norm_iff hx hy

/-- §8.5, Lemma 8.5: a curve of projectors whose derivative vanishes everywhere is constant
(on a connected parameter line the whole stratum is one projector). -/
theorem constant_of_silent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : Differentiable ℝ f) (h0 : ∀ t, deriv f t = 0) : ∀ s t, f s = f t :=
  is_const_of_deriv_eq_zero hf h0

/-- §12.4, Proposition 12.3, one angle: `sin² θ = θ²` on `[0, π/2]` only at `θ = 0`. -/
theorem sin_sq_eq_angle_sq_iff (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    Real.sin x ^ 2 = x ^ 2 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hpos : 0 < x := lt_of_le_of_ne h0 (Ne.symm hx)
    have hs : Real.sin x < x := Real.sin_lt hpos
    have hsn : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
    nlinarith
  · intro h; rw [h]; simp

/-- §12.4, Proposition 12.3, one angle: Jordan's inequality `θ² ≤ (π/2)² sin² θ` is an equality
on `[0, π/2]` only at the two ends. -/
theorem jordan_eq_iff (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    x ^ 2 = (Real.pi / 2) ^ 2 * Real.sin x ^ 2 ↔ x = 0 ∨ x = Real.pi / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · intro h
    by_contra hx
    push Not at hx
    have hpos : 0 < x := lt_of_le_of_ne h0 (Ne.symm hx.1)
    have hlt : x < Real.pi / 2 := lt_of_le_of_ne h1 hx.2
    have hj : 2 / Real.pi * x < Real.sin x := Real.mul_lt_sin hpos hlt
    have he : Real.pi / 2 * (2 / Real.pi * x) = x := by
      field_simp
    have hx2 : x < Real.pi / 2 * Real.sin x := by
      calc x = Real.pi / 2 * (2 / Real.pi * x) := he.symm
        _ < Real.pi / 2 * Real.sin x := mul_lt_mul_of_pos_left hj (by positivity)
    have : x ^ 2 < (Real.pi / 2) ^ 2 * Real.sin x ^ 2 := by
      calc x ^ 2 = x * x := sq x
        _ < (Real.pi / 2 * Real.sin x) * (Real.pi / 2 * Real.sin x) :=
            mul_self_lt_mul_self h0 hx2
        _ = (Real.pi / 2) ^ 2 * Real.sin x ^ 2 := by ring
    linarith
  · rintro (h | h)
    · rw [h]; simp
    · rw [h, Real.sin_pi_div_two]; ring

/-- §12.4, Proposition 12.3: the upper half of the sandwich is an equality exactly when every
principal angle is `0` or `π/2`. -/
theorem sandwich_upper_eq_iff (s : Finset ι) (θ : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ θ i)
    (h1 : ∀ i ∈ s, θ i ≤ Real.pi / 2) :
    ∑ i ∈ s, θ i ^ 2 = (Real.pi / 2) ^ 2 * ∑ i ∈ s, Real.sin (θ i) ^ 2 ↔
      ∀ i ∈ s, θ i = 0 ∨ θ i = Real.pi / 2 := by
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_sum_iff_of_le fun i hi => angle_sq_le_jordan _ (h0 i hi) (h1 i hi)]
  exact forall₂_congr fun i hi => jordan_eq_iff _ (h0 i hi) (h1 i hi)

/-- §12.4, Proposition 12.3: a principal angle `|φ|/2` with `φ ∈ (-π, π]` is a right angle
exactly when the eigenphase is `π`. -/
theorem half_phase_right_iff (φ : ℝ) (h1 : -Real.pi < φ) (h2 : φ ≤ Real.pi) :
    |φ| / 2 = Real.pi / 2 ↔ φ = Real.pi := by
  constructor
  · intro h
    have ha : |φ| = Real.pi := by linarith
    rcases abs_cases φ with ⟨hc, _⟩ | ⟨hc, _⟩
    · linarith
    · linarith
  · intro h; rw [h, abs_of_pos Real.pi_pos]

end Rigidity

end IQGT
