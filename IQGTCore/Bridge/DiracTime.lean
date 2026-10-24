/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Spectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Bridge: Dirac-time friction is the IQGT pair sum reweighted by the spectrum

`dirac-time-lean` (`DiracTime/FrictionMetric.lean`) proves the pairwise algebra of friction on
projector rotations: each pair's friction is its intrinsic metric `|Ḣ_mn|²/(E_n−E_m)²` times a
spectral weight; Gibbs weights are nonnegative; the two-level population gap is `tanh`; at zero
temperature the weighted sum lies in a band. Here:

* `pair_friction_eq_weighted_metric`, `gibbs_pair_weight_nonneg`, `two_level_population_gap`
  are ported (statements unchanged).
* `friction s w a Δ := Σ wᵢ aᵢ² Δᵢ⁻²` – the IQGT pair sum at gap power `-2`, reweighted.
* `friction_band_pairSum` : `lo · pairSum (-2) ≤ friction ≤ hi · pairSum (-2)`.
* `friction_eq_zero_iff` : with positive weights and gaps, friction vanishes iff every
  cross-gap amplitude does (the friction and the IQGT metric have the same null directions).
* `friction_const_weight` : a constant weight `c` gives exactly `c · pairSum (-2)`, which by
  `IQGT.metric_sylvester_eq_pairSum` is `c · g_IQGT` of the response tangent.

The derivation of the pairwise friction formula from a relaxation/bath model is **not**
formalized (as in `dirac-time-lean`).
-/

namespace IQGT

/-- Ported: pair friction (both orders) = intrinsic pair metric × spectral weight. -/
theorem pair_friction_eq_weighted_metric (c h2 pm pn Em En : ℝ) (hE : En ≠ Em) :
    2 * (c * h2 * ((pm - pn) / (En - Em))) =
      2 * c * (pm - pn) * (En - Em) * (h2 / (En - Em) ^ 2) := by
  have h : En - Em ≠ 0 := sub_ne_zero.mpr hE
  field_simp

/-- Ported: Gibbs weights give nonnegative pair weights. -/
theorem gibbs_pair_weight_nonneg (β Em En : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (Real.exp (-β * Em) - Real.exp (-β * En)) * (En - Em) := by
  rcases le_total Em En with h | h
  · apply mul_nonneg
    · have hle : -β * En ≤ -β * Em := by nlinarith
      linarith [Real.exp_le_exp.mpr hle]
    · linarith
  · apply mul_nonneg_of_nonpos_of_nonpos
    · have hle : -β * Em ≤ -β * En := by nlinarith
      linarith [Real.exp_le_exp.mpr hle]
    · linarith

/-- Ported: two-level Gibbs population gap is `tanh x` (`x = βΔ/2`). -/
theorem two_level_population_gap (x : ℝ) :
    Real.exp x / (Real.exp x + Real.exp (-x)) - Real.exp (-x) / (Real.exp x + Real.exp (-x)) =
      Real.tanh x := by
  have h : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  field_simp

variable {ι : Type*}

/-- Friction on projector rotations: the IQGT pair sum at gap power `-2`, reweighted. -/
noncomputable def friction (s : Finset ι) (w a Δ : ι → ℝ) : ℝ := ∑ i ∈ s, w i * (a i ^ 2 * Δ i ^ (-2 : ℤ))

/-- **Friction band.** Weights in `[lo, hi]` put the friction between `lo · g` and `hi · g`. -/
theorem friction_band_pairSum (s : Finset ι) (w a Δ : ι → ℝ) (lo hi : ℝ)
    (hw : ∀ i ∈ s, lo ≤ w i ∧ w i ≤ hi) :
    lo * pairSum s a Δ (-2) ≤ friction s w a Δ ∧ friction s w a Δ ≤ hi * pairSum s a Δ (-2) := by
  have hg : ∀ i ∈ s, 0 ≤ a i ^ 2 * Δ i ^ (-2 : ℤ) := fun i _ =>
    mul_nonneg (sq_nonneg _) (by rw [_root_.zpow_neg, zpow_ofNat]; positivity)
  unfold friction pairSum
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_right (hw i hi').1 (hg i hi')
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_right (hw i hi').2 (hg i hi')

/-- A constant weight gives exactly `c ·` the IQGT pair sum. -/
theorem friction_const_weight (s : Finset ι) (c : ℝ) (a Δ : ι → ℝ) :
    friction s (fun _ => c) a Δ = c * pairSum s a Δ (-2) := by
  unfold friction pairSum; rw [Finset.mul_sum]

/-- **Same null directions.** With positive weights and nonzero gaps, friction vanishes iff
every amplitude vanishes. -/
theorem friction_eq_zero_iff (s : Finset ι) (w a Δ : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hΔ : ∀ i ∈ s, Δ i ≠ 0) : friction s w a Δ = 0 ↔ ∀ i ∈ s, a i = 0 := by
  have hpos : ∀ i ∈ s, 0 < Δ i ^ (-2 : ℤ) := fun i hi => by
    rw [_root_.zpow_neg, zpow_ofNat]; exact inv_pos.mpr (pow_pos (abs_pos.mpr (hΔ i hi)) 2 |>.trans_eq (sq_abs _))
  unfold friction
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
    mul_nonneg (hw i hi).le (mul_nonneg (sq_nonneg _) (hpos i hi).le)]
  refine forall₂_congr fun i hi => ?_
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (hw i hi).ne'
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
      · exact absurd h2 (hpos i hi).ne'
  · intro h; rw [h]; ring

end IQGT
