/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Blocks
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Spectral reading of the IQGT: one cross-gap pair sum at different gap powers

* `IQGT.Q_sylvester` / `IQGT.metric_sylvester` : if the cross-gap blocks solve the Sylvester
  (first-order response) equation `X_ij (e_i − f_j) = A_ij` with nonzero real gaps, then
  `Q = Σ A_ij conj(B_ij) / (e_i − f_j)²` and `g = Σ |A_ij|² / (e_i − f_j)²`: the inverse-gap-squared
  (Kubo / Riesz) form of the metric, as an exact finite statement.
* `IQGT.partial_fraction` : the residue step behind the inverse-gap weight.
* `IQGT.pairSum s a Δ p = Σ aᵢ² Δᵢ^p` : one cross-gap pair sum read at gap power `p`
  (`p = -2` metric, `p = -1` static polarisability up to the factor 2, `p = 0` spread,
  `p = 1` f-sum budget – the reading used in the Galilean-Variance comparison note).
* `IQGT.pairSum_sq_le` : **log-convexity in the gap power**,
  `pairSum p ² ≤ pairSum (p-1) · pairSum (p+1)` for positive gaps; consequences
  `polarisability_sq_le` and `spread_sq_le`.
* `IQGT.pairSum_ladder` : a gap floor `Δ₀ ≤ Δᵢ` gives `Δ₀ · pairSum p ≤ pairSum (p+1)`.
* `IQGT.pairSum_single_gap` : at a single gap every reading is a power of that gap times the spread.

What is *not* proved here: that the derivative of a spectral projector satisfies the Sylvester
equation (the analytic Riesz/Kato step) – it is taken as a hypothesis. See `LIMITATIONS.md`.
-/

namespace IQGT

open Matrix ComplexConjugate

section Sylvester

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]

omit [Fintype k] [Fintype m] [DecidableEq k] in
/-- Solving the Sylvester equation entrywise divides by the gap. -/
theorem sylvester_entry {x a : ℂ} {d : ℝ} (hd : d ≠ 0) (h : x * d = a) : x = a / d := by
  rw [← h, mul_div_assoc, div_self (Complex.ofReal_ne_zero.mpr hd), mul_one]

/-- **IQGT as an inverse-gap-squared pair sum.** If `X_ij (e_i − f_j) = A_ij` and
`Y_ij (e_i − f_j) = B_ij` with nonzero real gaps, then
`Q_{P₀}(V_X, V_Y) = Σ_ij A_ij conj(B_ij) / (e_i − f_j)²`. -/
theorem Q_sylvester (e : k → ℝ) (f : m → ℝ) (hgap : ∀ i j, e i - f j ≠ 0)
    (A B X Y : Matrix k m ℂ) (hX : ∀ i j, X i j * ((e i - f j : ℝ) : ℂ) = A i j)
    (hY : ∀ i j, Y i j * ((e i - f j : ℝ) : ℂ) = B i j) :
    Q P0 (offDiag X) (offDiag Y) =
      ∑ i, ∑ j, A i j * conj (B i j) / (((e i - f j) ^ 2 : ℝ) : ℂ) := by
  rw [Q_offDiag_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sylvester_entry (hgap i j) (hX i j), sylvester_entry (hgap i j) (hY i j), map_div₀,
    Complex.conj_ofReal]
  have h0 : ((e i - f j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hgap i j)
  push_cast
  field_simp

/-- **Metric as inverse-gap-squared pair sum**: `g(V_X,V_X) = Σ |A_ij|² / (e_i − f_j)²`. -/
theorem metric_sylvester (e : k → ℝ) (f : m → ℝ) (hgap : ∀ i j, e i - f j ≠ 0)
    (A X : Matrix k m ℂ) (hX : ∀ i j, X i j * ((e i - f j : ℝ) : ℂ) = A i j) :
    metric P0 (offDiag X) (offDiag X) =
      ∑ i, ∑ j, Complex.normSq (A i j) / (e i - f j) ^ 2 := by
  unfold metric
  rw [Q_sylvester e f hgap A A X X hX hX, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re]

end Sylvester

/-- **Residue step.** `1/((z−a)(z−b)) = (1/(z−a) − 1/(z−b))/(a−b)`; the residue at `z = a`
is the inverse-gap weight `1/(a−b)`. -/
theorem partial_fraction (z a b : ℂ) (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) :
    1 / ((z - a) * (z - b)) = (1 / (z - a) - 1 / (z - b)) / (a - b) := by
  have h1 : z - a ≠ 0 := sub_ne_zero.mpr hza
  have h2 : z - b ≠ 0 := sub_ne_zero.mpr hzb
  have h3 : a - b ≠ 0 := sub_ne_zero.mpr hab
  field_simp
  ring

section PairSum

variable {ι : Type*}

/-- One cross-gap pair sum read at gap power `p`: `Σ_{i ∈ s} aᵢ² Δᵢ^p`. -/
noncomputable def pairSum (s : Finset ι) (a Δ : ι → ℝ) (p : ℤ) : ℝ := ∑ i ∈ s, a i ^ 2 * Δ i ^ p

theorem pairSum_nonneg (s : Finset ι) (a Δ : ι → ℝ) (p : ℤ) (hΔ : ∀ i ∈ s, 0 < Δ i) :
    0 ≤ pairSum s a Δ p :=
  Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (zpow_nonneg (hΔ i hi).le _)

/-- **Log-convexity in the gap power.** For positive gaps,
`(Σ aᵢ² Δᵢ^p)² ≤ (Σ aᵢ² Δᵢ^(p-1)) (Σ aᵢ² Δᵢ^(p+1))`. -/
theorem pairSum_sq_le (s : Finset ι) (a Δ : ι → ℝ) (p : ℤ) (hΔ : ∀ i ∈ s, 0 < Δ i) :
    pairSum s a Δ p ^ 2 ≤ pairSum s a Δ (p - 1) * pairSum s a Δ (p + 1) := by
  unfold pairSum
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun i hi => mul_nonneg (sq_nonneg _) (zpow_nonneg (hΔ i hi).le _)
  · exact fun i hi => mul_nonneg (sq_nonneg _) (zpow_nonneg (hΔ i hi).le _)
  · intro i hi
    apply le_of_eq
    have h0 : Δ i ≠ 0 := (hΔ i hi).ne'
    rw [zpow_sub_one₀ h0, zpow_add_one₀ h0]
    field_simp

/-- Static polarisability (`p = -1`) is controlled by metric (`p = -2`) and spread (`p = 0`). -/
theorem polarisability_sq_le (s : Finset ι) (a Δ : ι → ℝ) (hΔ : ∀ i ∈ s, 0 < Δ i) :
    pairSum s a Δ (-1) ^ 2 ≤ pairSum s a Δ (-2) * pairSum s a Δ 0 := by
  have h := pairSum_sq_le s a Δ (-1) hΔ
  norm_num at h
  exact h

/-- Spread (`p = 0`) is controlled by polarisability (`p = -1`) and the f-sum budget (`p = 1`). -/
theorem spread_sq_le (s : Finset ι) (a Δ : ι → ℝ) (hΔ : ∀ i ∈ s, 0 < Δ i) :
    pairSum s a Δ 0 ^ 2 ≤ pairSum s a Δ (-1) * pairSum s a Δ 1 := by
  have h := pairSum_sq_le s a Δ 0 hΔ
  norm_num at h
  exact h

/-- **Gap ladder.** A gap floor `0 < Δ₀ ≤ Δᵢ` gives `Δ₀ · pairSum p ≤ pairSum (p+1)`. -/
theorem pairSum_ladder (s : Finset ι) (a Δ : ι → ℝ) (p : ℤ) (Δ₀ : ℝ) (h0 : 0 < Δ₀)
    (hΔ : ∀ i ∈ s, Δ₀ ≤ Δ i) : Δ₀ * pairSum s a Δ p ≤ pairSum s a Δ (p + 1) := by
  unfold pairSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hpos : 0 < Δ i := lt_of_lt_of_le h0 (hΔ i hi)
  rw [zpow_add_one₀ hpos.ne']
  have hz : 0 ≤ a i ^ 2 * Δ i ^ p := mul_nonneg (sq_nonneg _) (zpow_nonneg hpos.le _)
  nlinarith [mul_le_mul_of_nonneg_left (hΔ i hi) hz]

/-- At a single gap `d`, every reading is `d^p` times the spread. -/
theorem pairSum_single_gap (s : Finset ι) (a Δ : ι → ℝ) (p : ℤ) (d : ℝ)
    (hΔ : ∀ i ∈ s, Δ i = d) : pairSum s a Δ p = d ^ p * pairSum s a Δ 0 := by
  unfold pairSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hΔ i hi, zpow_zero, mul_one, mul_comm]

/-- At a single gap the log-convexity bound is an equality. -/
theorem pairSum_sq_eq_of_single_gap (s : Finset ι) (a Δ : ι → ℝ) (p : ℤ) (d : ℝ) (hd : 0 < d)
    (hΔ : ∀ i ∈ s, Δ i = d) :
    pairSum s a Δ p ^ 2 = pairSum s a Δ (p - 1) * pairSum s a Δ (p + 1) := by
  rw [pairSum_single_gap s a Δ p d hΔ, pairSum_single_gap s a Δ (p - 1) d hΔ,
    pairSum_single_gap s a Δ (p + 1) d hΔ, zpow_sub_one₀ hd.ne', zpow_add_one₀ hd.ne']
  field_simp

/-- **The IQGT metric of the response tangent is the gap-power `-2` pair sum** over
(occupied, empty) pairs, with amplitudes `‖A_ij‖` and gaps `|e_i − f_j|`. -/
theorem metric_sylvester_eq_pairSum {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    (e : k → ℝ) (f : m → ℝ) (hgap : ∀ i j, e i - f j ≠ 0)
    (A X : Matrix k m ℂ) (hX : ∀ i j, X i j * ((e i - f j : ℝ) : ℂ) = A i j) :
    metric P0 (offDiag X) (offDiag X) =
      pairSum Finset.univ (fun p : k × m => ‖A p.1 p.2‖) (fun p => |e p.1 - f p.2|) (-2) := by
  rw [metric_sylvester e f hgap A X hX]
  unfold pairSum
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show Complex.normSq (A i j) / (e i - f j) ^ 2 = ‖A i j‖ ^ 2 * |e i - f j| ^ (-2 : ℤ)
  rw [Complex.normSq_eq_norm_sq, _root_.zpow_neg, zpow_ofNat, sq_abs, div_eq_mul_inv]

end PairSum

end IQGT
