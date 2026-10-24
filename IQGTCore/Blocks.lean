/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Form
import Mathlib.Data.Matrix.Block

/-!
# Cross-gap block form of the IQGT

In an adapted basis `ℂ^(k ⊕ m)` (occupied `k`, empty `m`) the projector is
`P₀ = [[1,0],[0,0]]`. This file shows:

* `isTangent_iff_eq_offDiag` : a Hermitian `V` is tangent at `P₀` iff `V = [[0,X],[Xᴴ,0]]`
  for a (unique) cross-gap block `X : Matrix k m ℂ` – the tangent space *is* the space of
  cross-gap transition amplitudes.
* `Q_offDiag` : `Q_{P₀}(V_X, V_Y) = Tr(X Yᴴ) = Σ_{i occupied, j empty} X_ij conj(Y_ij)` – the
  IQGT is a sum over cross-gap pairs only.
* `two_level_saturation` : for one occupied and one empty level the Gram inequality is an
  equality (`Ω² = 4 det g`): the two-level saturation step.
* `trace_offDiag_sq` : `Tr V² = 2 Tr(XXᴴ)`.
-/

namespace IQGT

open Matrix ComplexConjugate

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

omit [DecidableEq k] [DecidableEq m] in
/-- Trace of a block matrix: `Tr [[A,B],[C,D]] = Tr A + Tr D`. -/
theorem trace_fromBlocks' (A : Matrix k k ℂ) (B : Matrix k m ℂ) (C : Matrix m k ℂ)
    (D : Matrix m m ℂ) : trace (fromBlocks A B C D) = trace A + trace D := by
  simp only [trace, diag, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₂]

/-- The adapted projector `P₀ = [[1,0],[0,0]]` onto the occupied block. -/
def P0 : Matrix (k ⊕ m) (k ⊕ m) ℂ := fromBlocks 1 0 0 0

/-- The Hermitian off-diagonal tangent built from a cross-gap block `X`. -/
def offDiag (X : Matrix k m ℂ) : Matrix (k ⊕ m) (k ⊕ m) ℂ := fromBlocks 0 X Xᴴ 0

theorem isStarProjection_P0 : IsStarProjection (P0 : Matrix (k ⊕ m) (k ⊕ m) ℂ) where
  isIdempotentElem := by
    unfold IsIdempotentElem P0; rw [fromBlocks_multiply]; simp
  isSelfAdjoint := by
    unfold IsSelfAdjoint P0; rw [star_eq_conjTranspose, fromBlocks_conjTranspose]; simp

omit [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m] in
theorem offDiag_conjTranspose (X : Matrix k m ℂ) : (offDiag X)ᴴ = offDiag X := by
  unfold offDiag; rw [fromBlocks_conjTranspose]; simp

theorem offDiag_isTangent (X : Matrix k m ℂ) : IsTangent P0 (offDiag X) := by
  unfold IsTangent P0 offDiag
  simp [fromBlocks_multiply, fromBlocks_add]

/-- **Tangent space = cross-gap blocks.** A Hermitian `V` is tangent at `P₀` iff it is
`offDiag X` for some `X`. -/
theorem isTangent_iff_eq_offDiag {V : Matrix (k ⊕ m) (k ⊕ m) ℂ} (hV : Vᴴ = V) :
    IsTangent P0 V ↔ ∃ X : Matrix k m ℂ, V = offDiag X := by
  constructor
  · intro hT
    have hb := (tangent_iff_blocks isStarProjection_P0.isIdempotentElem).mp hT
    rw [← fromBlocks_toBlocks V] at hb hV
    obtain ⟨h1, h2⟩ := hb
    unfold P0 at h1 h2
    have hPc : (1 : Matrix (k ⊕ m) (k ⊕ m) ℂ) - fromBlocks 1 0 0 0 = fromBlocks 0 0 0 1 := by
      rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]; simp
    rw [hPc] at h2
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add] at h1 h2
    rw [← fromBlocks_zero, fromBlocks_inj] at h1 h2
    rw [fromBlocks_conjTranspose, fromBlocks_inj] at hV
    refine ⟨V.toBlocks₁₂, ?_⟩
    conv_lhs => rw [← fromBlocks_toBlocks V]
    unfold offDiag
    rw [h1.1, h2.2.2.2, ← hV.2.2.1]
  · rintro ⟨X, rfl⟩; exact offDiag_isTangent X

omit [DecidableEq k] [DecidableEq m] in
/-- `Tr V² = 2 Tr(XXᴴ)` for `V = offDiag X`. -/
theorem trace_offDiag_sq (X : Matrix k m ℂ) :
    trace (offDiag X * offDiag X) = 2 * trace (X * Xᴴ) := by
  unfold offDiag
  rw [fromBlocks_multiply]
  simp only [Matrix.zero_mul, zero_add, Matrix.mul_zero, add_zero, trace_fromBlocks']
  rw [trace_mul_comm Xᴴ X]; ring

omit [DecidableEq m] in
/-- **Cross-gap formula.** `Q_{P₀}(V_X, V_Y) = Tr(X Yᴴ)`. -/
theorem Q_offDiag (X Y : Matrix k m ℂ) : Q P0 (offDiag X) (offDiag Y) = trace (X * Yᴴ) := by
  unfold Q P0 offDiag
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, trace_fromBlocks', trace_zero]

omit [DecidableEq m] in
/-- The cross-gap formula as an explicit sum over (occupied, empty) pairs. -/
theorem Q_offDiag_eq_sum (X Y : Matrix k m ℂ) :
    Q P0 (offDiag X) (offDiag Y) = ∑ i, ∑ j, X i j * conj (Y i j) := by
  rw [Q_offDiag]
  simp [trace, mul_apply, conjTranspose_apply]

/-- **Two-level saturation.** With one occupied and one empty level, the Gram inequality
`(Im Q)² ≤ g_VV g_WW − g_VW²` holds with equality (so `Ω² = 4 det g`). -/
theorem two_level_saturation (X Y : Matrix Unit Unit ℂ) :
    (Q P0 (offDiag X) (offDiag Y)).im ^ 2 =
      metric P0 (offDiag X) (offDiag X) * metric P0 (offDiag Y) (offDiag Y) -
        metric P0 (offDiag X) (offDiag Y) ^ 2 := by
  unfold metric
  simp only [Q_offDiag_eq_sum, Fintype.univ_unit, Finset.sum_singleton, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Lagrange's identity in `ℝ³` (`|A|²|B|² − (A·B)² = |A×B|²`): the real-coordinate form of
two-level saturation used in the paper (Bloch-sphere picture). -/
theorem lagrange_identity (a1 a2 a3 b1 b2 b3 : ℝ) :
    (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) - (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 =
      (a2 * b3 - a3 * b2) ^ 2 + (a3 * b1 - a1 * b3) ^ 2 + (a1 * b2 - a2 * b1) ^ 2 := by
  ring

/-- **Sharpness of the constant 4.** For `X = 1`, `Y = i` (one occupied, one empty level),
`Ω² = 4` while `g_VV g_WW − g_VW² = 1`; so `Ω² ≤ 4 det g` cannot be improved to `Ω² ≤ det g`. -/
theorem curvature_factor_four_sharp :
    curvature P0 (offDiag (of fun _ _ => (1 : ℂ) : Matrix Unit Unit ℂ))
        (offDiag (of fun _ _ => Complex.I)) ^ 2 = 4 ∧
      metric P0 (offDiag (of fun _ _ => (1 : ℂ) : Matrix Unit Unit ℂ))
          (offDiag (of fun _ _ => (1 : ℂ) : Matrix Unit Unit ℂ)) *
        metric P0 (offDiag (of fun _ _ => Complex.I : Matrix Unit Unit ℂ))
          (offDiag (of fun _ _ => Complex.I)) -
        metric P0 (offDiag (of fun _ _ => (1 : ℂ) : Matrix Unit Unit ℂ))
          (offDiag (of fun _ _ => Complex.I)) ^ 2 = 1 := by
  unfold curvature metric
  simp only [Q_offDiag_eq_sum, Fintype.univ_unit, Finset.sum_singleton, of_apply]
  simp
  norm_num

end IQGT
