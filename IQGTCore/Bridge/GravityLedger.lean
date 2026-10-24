/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Form
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Bridge: gravity-ledger tangents and signed metrics, against the IQGT form

`gravity-ledger-lean` (`Gravity.lean`) proves the tangent split at an idempotent (here
`IQGT.IsTangent.eq_offdiag`, one shared copy), a curvature-proxy determinant step, the reciprocal
(signed) determinant, a non-self-adjoint negative tangent, and a rank-one moving-wall chart.
Here these are placed relative to the IQGT form:

* `iqgt_det_nonneg` : on Hermitian tangents the IQGT Gram determinant
  `g_VV g_WW − g_VW²` is `≥ (Im Q)² ≥ 0` – the "Hermitian slice" is nonnegative.
* `reciprocal_determinant` / `reciprocal_not_definite` (ported) : the signed (reciprocal)
  slice has determinant `−(ad − bc)² ≤ 0` – a different, indefinite form. The two are not the
  same metric; the ledger's signed metric is **not** a pullback of the IQGT form.
* `proxy_second_diagonal` (ported) and `proxy_holds_for_iqgt` : gravity-ledger's
  curvature-proxy hypothesis `Ω² ≤ 4(ac − b²)` is exactly `IQGT.curvature_sq_le` with
  `a = g_VV`, `b = g_VW`, `c = g_WW`.
* `Q_nonHermitian_negative` : the false control – for the non-Hermitian tangent
  `D = [[0,1],[-1,0]]` at `P = [[1,0],[0,0]]` one gets `Q(D,D) = −1`; so the Hermitian
  hypothesis in `IQGT.metric_self_nonneg` cannot be dropped (complex form of
  gravity-ledger's `selfadjoint_point_negative_tangent`).
* `chartP_isIdempotentElem`, `chart_trace_one` (ported) : the moving-wall chart is an
  idempotent family, so the tangent law applies along it.
-/

namespace IQGT

open Matrix

/-- On Hermitian tangents the IQGT Gram determinant is nonnegative. -/
theorem iqgt_det_nonneg {n : Type*} [Fintype n] {P V W : Matrix n n ℂ}
    (hP : IsStarProjection P) (hV : Vᴴ = V) (hW : Wᴴ = W) :
    0 ≤ metric P V V * metric P W W - metric P V W ^ 2 :=
  le_trans (sq_nonneg _) (metric_control hP hV hW)

/-- Ported: the reciprocal single-partner determinant is a negative square. -/
theorem reciprocal_determinant (a b c d : ℝ) :
    (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) - (a * c - b * d) ^ 2 = -(a * d - b * c) ^ 2 := by ring

theorem reciprocal_not_definite (a b c d : ℝ) :
    (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) - (a * c - b * d) ^ 2 ≤ 0 := by
  rw [reciprocal_determinant]; exact neg_nonpos.mpr (sq_nonneg _)

/-- Ported: with a positive first diagonal, the curvature-proxy bound forces `c ≥ 0`. -/
theorem proxy_second_diagonal (a b c omega : ℝ) (ha : 0 < a) (h : omega ^ 2 ≤ 4 * (a * c - b ^ 2)) :
    0 ≤ c := by
  have hac : 0 ≤ a * c := by nlinarith [sq_nonneg omega, sq_nonneg b]
  exact nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using hac) ha

/-- Gravity-ledger's proxy hypothesis is satisfied by IQGT data. -/
theorem proxy_holds_for_iqgt {n : Type*} [Fintype n] {P V W : Matrix n n ℂ}
    (hP : IsStarProjection P) (hV : Vᴴ = V) (hW : Wᴴ = W) :
    curvature P V W ^ 2 ≤ 4 * (metric P V V * metric P W W - metric P V W ^ 2) :=
  curvature_sq_le hP hV hW

/-- The adapted 2×2 projector and the non-Hermitian tangent of gravity-ledger, over `ℂ`. -/
def pointP : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
def pointD : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem pointP_isStarProjection : IsStarProjection pointP where
  isIdempotentElem := by
    unfold IsIdempotentElem pointP; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  isSelfAdjoint := by
    unfold IsSelfAdjoint pointP
    rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem pointD_isTangent : IsTangent pointP pointD := by
  unfold IsTangent pointP pointD; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem pointD_not_hermitian : pointDᴴ ≠ pointD := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [pointD] at this
  norm_num at this

/-- **False control.** A non-Hermitian tangent can have negative `Q(D,D)`; the Hermitian
hypothesis of `metric_self_nonneg` is necessary. -/
theorem Q_nonHermitian_negative : Q pointP pointD pointD = -1 := by
  unfold Q pointP pointD
  simp [Matrix.trace, Fin.sum_univ_two]

/-- Ported: the rank-one moving-wall chart. -/
noncomputable def chartP (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / (1 + z * w), w / (1 + z * w); z / (1 + z * w), z * w / (1 + z * w)]

theorem chartP_isIdempotentElem (z w : ℂ) (h : 1 + z * w ≠ 0) :
    IsIdempotentElem (chartP z w) := by
  unfold IsIdempotentElem
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [chartP, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem chart_trace_one (z w : ℂ) (h : 1 + z * w ≠ 0) : (chartP z w).trace = 1 := by
  simp [chartP, Matrix.trace, Fin.sum_univ_two]
  field_simp

end IQGT
