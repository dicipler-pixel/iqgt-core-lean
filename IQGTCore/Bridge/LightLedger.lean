/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Spectral

/-!
# Bridge: light-ledger's optical response is a reweighting of the IQGT metric

`light-ledger-lean` (`OpticalMetric.lean`) defines, per transition, the metric `a²/Δ²`, the
lossless polarisability `2Δa²/(Δ² − ω²)` and the response weight `2Δ³/(Δ² − ω²)`, and proves
`polarisability = weight × metric`. The definitions are re-stated here verbatim (same names,
namespace `IQGT.Light`) and connected to the IQGT form:

* `sum_transitionMetric_eq_pairSum` : `Σ a²/Δ² = pairSum (-2)`.
* `sum_static_polarizability` : `Σ α_i(0) = 2 · pairSum (-1)`.
* `static_polarizability_sq_le` : `(Σ α_i(0))² ≤ 4 · (Σ a²/Δ²) · Σ a²` – the metric (ω⁻²),
  static polarisability (ω⁻¹) and spread (ω⁰) readings of one pair sum are tied by
  log-convexity (`IQGT.pairSum_sq_le`).
* `metric_eq_sum_transitionMetric` : the IQGT metric of the response tangent
  (Sylvester hypothesis, see `IQGT.metric_sylvester`) equals light-ledger's summed transition
  metric over cross-gap pairs.
* `polarizability_single_gap` : at a single gap `d`, the summed polarisability is
  `responseWeight d ω · g_IQGT`.
* `weighted_zero_iff`, `peel_null_persists` : positive reweighting never creates or removes a
  null direction; lowering weights keeps nulls.
-/

namespace IQGT.Light

open Matrix

/-- Single-transition metric `a²/Δ²` (light-ledger `transitionMetric`). -/
noncomputable def transitionMetric (amplitude gap : ℝ) : ℝ := amplitude ^ 2 / gap ^ 2

/-- Lossless polarisability `2Δa²/(Δ² − ω²)` (light-ledger `polarizability`). -/
noncomputable def polarizability (amplitude gap photonEnergy : ℝ) : ℝ :=
  2 * gap * amplitude ^ 2 / (gap ^ 2 - photonEnergy ^ 2)

/-- Response weight `2Δ³/(Δ² − ω²)` (light-ledger `responseWeight`). -/
noncomputable def responseWeight (gap photonEnergy : ℝ) : ℝ :=
  2 * gap ^ 3 / (gap ^ 2 - photonEnergy ^ 2)

/-- Ported: `polarisability = responseWeight × transitionMetric`. -/
theorem response_is_weighted_metric (a gap x : ℝ) (hg : gap ≠ 0) (hd : gap ^ 2 - x ^ 2 ≠ 0) :
    polarizability a gap x = responseWeight gap x * transitionMetric a gap := by
  unfold polarizability responseWeight transitionMetric
  field_simp

/-- Ported: below resonance the response weight is positive. -/
theorem response_weight_positive (gap x : ℝ) (hg : 0 < gap) (hx : x ^ 2 < gap ^ 2) :
    0 < responseWeight gap x := by
  unfold responseWeight
  exact div_pos (mul_pos (by norm_num) (pow_pos hg 3)) (sub_pos.mpr hx)

theorem transitionMetric_eq_zpow (a gap : ℝ) :
    transitionMetric a gap = a ^ 2 * gap ^ (-2 : ℤ) := by
  unfold transitionMetric
  rw [_root_.zpow_neg, zpow_ofNat, div_eq_mul_inv]

variable {ι : Type*}

/-- `Σ a²/Δ² = pairSum (-2)` (the ω⁻² reading is the IQGT metric reading). -/
theorem sum_transitionMetric_eq_pairSum (s : Finset ι) (a Δ : ι → ℝ) :
    ∑ i ∈ s, transitionMetric (a i) (Δ i) = pairSum s a Δ (-2) := by
  unfold pairSum
  exact Finset.sum_congr rfl fun i _ => transitionMetric_eq_zpow _ _

/-- `Σ α_i(0) = 2 · pairSum (-1)` (the ω⁻¹ reading). -/
theorem sum_static_polarizability (s : Finset ι) (a Δ : ι → ℝ) (hΔ : ∀ i ∈ s, Δ i ≠ 0) :
    ∑ i ∈ s, polarizability (a i) (Δ i) 0 = 2 * pairSum s a Δ (-1) := by
  unfold pairSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold polarizability
  have h := hΔ i hi
  rw [_root_.zpow_neg_one]
  field_simp
  ring

/-- **Polarisability is controlled by metric and spread**:
`(Σ α_i(0))² ≤ 4 (Σ a²/Δ²)(Σ a²)` for positive gaps. -/
theorem static_polarizability_sq_le (s : Finset ι) (a Δ : ι → ℝ) (hΔ : ∀ i ∈ s, 0 < Δ i) :
    (∑ i ∈ s, polarizability (a i) (Δ i) 0) ^ 2 ≤
      4 * (∑ i ∈ s, transitionMetric (a i) (Δ i)) * ∑ i ∈ s, a i ^ 2 := by
  rw [sum_static_polarizability s a Δ fun i hi => (hΔ i hi).ne',
    sum_transitionMetric_eq_pairSum]
  have h := polarisability_sq_le s a Δ hΔ
  have h0 : pairSum s a Δ 0 = ∑ i ∈ s, a i ^ 2 := by
    unfold pairSum; simp
  rw [← h0]
  nlinarith [h]

/-- **Light-ledger's transition metric is the IQGT metric.** For the response tangent
(Sylvester hypothesis), the IQGT metric equals the summed light-ledger transition metric over
cross-gap pairs. -/
theorem metric_eq_sum_transitionMetric {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    (e : k → ℝ) (f : m → ℝ) (hgap : ∀ i j, e i - f j ≠ 0)
    (A X : Matrix k m ℂ) (hX : ∀ i j, X i j * ((e i - f j : ℝ) : ℂ) = A i j) :
    metric P0 (offDiag X) (offDiag X) =
      ∑ i, ∑ j, transitionMetric ‖A i j‖ (e i - f j) := by
  rw [metric_sylvester e f hgap A X hX]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold transitionMetric
  rw [Complex.normSq_eq_norm_sq]

/-- At a single gap `d`, the summed polarisability of the cross-gap pairs is
`responseWeight d ω` times the IQGT metric of the response tangent. -/
theorem polarizability_single_gap {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    (e : k → ℝ) (f : m → ℝ) (d x : ℝ) (hd : d ≠ 0) (hdx : d ^ 2 - x ^ 2 ≠ 0)
    (hgap : ∀ i j, e i - f j = d)
    (A X : Matrix k m ℂ) (hX : ∀ i j, X i j * ((e i - f j : ℝ) : ℂ) = A i j) :
    ∑ i, ∑ j, polarizability ‖A i j‖ (e i - f j) x =
      responseWeight d x * metric P0 (offDiag X) (offDiag X) := by
  rw [metric_eq_sum_transitionMetric e f (fun i j => by rw [hgap]; exact hd) A X hX,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hgap, response_is_weighted_metric _ _ _ hd hdx]

section Channels

variable [Fintype ι]

/-- Weighted channel form `Σ wᵢ qᵢ²` (light-ledger `weightedForm`). -/
def weightedForm (w q : ι → ℝ) : ℝ := ∑ i, w i * q i ^ 2

/-- Ported: a positive reweighting cannot create a null direction. -/
theorem weighted_zero_iff (w q : ι → ℝ) (hw : ∀ i, 0 < w i) :
    weightedForm w q = 0 ↔ ∀ i, q i = 0 := by
  unfold weightedForm
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hw i).le (sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero, (hw _).ne', false_or, pow_eq_zero_iff,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

/-- Peel: lowering nonnegative weights keeps a null direction null. -/
theorem peel_null_persists (after before q : ι → ℝ) (ha : ∀ i, 0 ≤ after i)
    (hab : ∀ i, after i ≤ before i) (hz : weightedForm before q = 0) :
    weightedForm after q = 0 := by
  apply le_antisymm
  · rw [← hz]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hab i) (sq_nonneg _)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (sq_nonneg _)

end Channels

end IQGT.Light
