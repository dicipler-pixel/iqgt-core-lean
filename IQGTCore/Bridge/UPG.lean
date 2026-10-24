/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Blocks

/-!
# Bridge: UPG coupling energy is the IQGT metric of the redistribution tangent

`upg-lean` (Universal Projector Geometry) proves, for real block Hamiltonians
`H = [[A,B],[Bᵀ,D]]`, that `[H,P] = 0 ↔ F(H,P) = 0 ↔ B = 0` and that the half cross energy of
`[H,P]` is the coupling energy `Σ B_ij²`. Here the same facts are read through the IQGT form:

* `redist_conjTranspose` : for Hermitian `H` and an orthogonal projector `P`, the
  redistribution operator `F = F(H,P)` is a Hermitian tangent at `P`.
* `metric_redist` : `g_P(F,F) = Re Tr(((1-P)HP)ᴴ (1-P)HP)` – the squared cross-gap block of `H`.
* `metric_redist_eq_zero_iff` : `g_P(F,F) = 0 ↔ HP = PH` (sector decouples iff the IQGT speed
  of the redistribution vanishes).
* `redist_blockHam` : in adapted blocks, `F(H,P₀) = offDiag B`.
* `metric_redist_blockHam` : `g(F,F) = Re Tr(B Bᴴ)`; independent of `A`, `D`
  (`metric_redist_blockHam_indep`, the interface-persistence statement).
* `metric_redist_real` : for a real coupling block, `g(F,F) = Σ B_ij²`, literally UPG's
  `couplingEnergy`.
* `commutator_energy_eq_two_metric` : `Tr([H,P₀]ᴴ[H,P₀]) = 2 · Q(F,F)`.
-/

namespace IQGT

open Matrix ComplexConjugate
open scoped ComplexOrder

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem redist_conjTranspose {H P : Matrix n n ℂ} (hH : Hᴴ = H) (hP : IsStarProjection P) :
    (redist H P)ᴴ = redist H P := by
  have hPc := conjTranspose_eq_of_isStarProjection hP
  unfold redist
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, hPc,
    Matrix.mul_assoc]
  rw [add_comm]

/-- **UPG ↦ IQGT.** The IQGT metric of the redistribution tangent is the squared cross-gap block
`(1-P)HP` of the Hamiltonian. -/
theorem metric_redist {H P : Matrix n n ℂ} (hH : Hᴴ = H) (hP : IsStarProjection P) :
    metric P (redist H P) (redist H P) =
      (trace (((1 - P) * H * P)ᴴ * ((1 - P) * H * P))).re := by
  unfold metric
  rw [Q_eq_frobenius hP (redist_conjTranspose hH hP), redist_mul_proj H P hP.isIdempotentElem]

/-- The redistribution speed vanishes exactly when the sector decouples, `HP = PH`. -/
theorem metric_redist_eq_zero_iff {H P : Matrix n n ℂ} (hH : Hᴴ = H) (hP : IsStarProjection P) :
    metric P (redist H P) (redist H P) = 0 ↔ H * P = P * H := by
  rw [metric_self_eq_zero_iff hP (redist_conjTranspose hH hP),
    redist_mul_proj H P hP.isIdempotentElem]
  constructor
  · intro h0
    have hF : redist H P = 0 :=
      eq_zero_of_mul_proj_eq_zero hP (redist_conjTranspose hH hP)
        (redist_isTangent H P hP.isIdempotentElem) (by rw [redist_mul_proj H P hP.isIdempotentElem, h0])
    exact (redist_eq_zero_iff H P hP.isIdempotentElem).mp hF
  · intro hc
    rw [← redist_mul_proj H P hP.isIdempotentElem,
      (redist_eq_zero_iff H P hP.isIdempotentElem).mpr hc, Matrix.zero_mul]

end General

section Block

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

/-- The Hermitian block Hamiltonian `[[A,B],[Bᴴ,D]]`. -/
def blockHam (A : Matrix k k ℂ) (B : Matrix k m ℂ) (D : Matrix m m ℂ) :
    Matrix (k ⊕ m) (k ⊕ m) ℂ := fromBlocks A B Bᴴ D

omit [Fintype k] [Fintype m] in
lemma one_sub_P0 : (1 : Matrix (k ⊕ m) (k ⊕ m) ℂ) - P0 = fromBlocks 0 0 0 1 := by
  unfold P0
  rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]; simp

/-- In adapted blocks the redistribution operator is the off-diagonal coupling: `F = offDiag B`. -/
theorem redist_blockHam (A : Matrix k k ℂ) (B : Matrix k m ℂ) (D : Matrix m m ℂ) :
    redist (blockHam A B D) P0 = offDiag B := by
  unfold redist
  rw [one_sub_P0]
  unfold P0 blockHam offDiag
  simp [fromBlocks_multiply, fromBlocks_add]

theorem metric_redist_blockHam (A : Matrix k k ℂ) (B : Matrix k m ℂ) (D : Matrix m m ℂ) :
    metric P0 (redist (blockHam A B D) P0) (redist (blockHam A B D) P0) =
      (trace (B * Bᴴ)).re := by
  rw [redist_blockHam]; unfold metric; rw [Q_offDiag]

/-- **Interface persistence.** Changing the diagonal sectors at fixed coupling leaves the IQGT
speed of the redistribution unchanged. -/
theorem metric_redist_blockHam_indep (A A' : Matrix k k ℂ) (B : Matrix k m ℂ)
    (D D' : Matrix m m ℂ) :
    metric P0 (redist (blockHam A B D) P0) (redist (blockHam A B D) P0) =
      metric P0 (redist (blockHam A' B D') P0) (redist (blockHam A' B D') P0) := by
  rw [metric_redist_blockHam, metric_redist_blockHam]

/-- For a real coupling block the IQGT metric of the redistribution is UPG's coupling energy
`Σ B_ij²`. -/
theorem metric_redist_real (A : Matrix k k ℂ) (B : Matrix k m ℝ) (D : Matrix m m ℂ) :
    metric P0 (redist (blockHam A (B.map (↑)) D) P0) (redist (blockHam A (B.map (↑)) D) P0) =
      ∑ i, ∑ j, B i j ^ 2 := by
  rw [redist_blockHam]
  unfold metric
  rw [Q_offDiag_eq_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply, sq]

/-- `[H,P₀] = [[0,-B],[Bᴴ,0]]`. -/
theorem commutator_blockHam (A : Matrix k k ℂ) (B : Matrix k m ℂ) (D : Matrix m m ℂ) :
    blockHam A B D * P0 - P0 * blockHam A B D = fromBlocks 0 (-B) Bᴴ 0 := by
  unfold blockHam P0
  simp [fromBlocks_multiply, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]

/-- **Commutator energy is twice the IQGT metric:** `Tr([H,P₀]ᴴ[H,P₀]) = 2 Q(F,F)`. -/
theorem commutator_energy_eq_two_Q (A : Matrix k k ℂ) (B : Matrix k m ℂ) (D : Matrix m m ℂ) :
    trace ((blockHam A B D * P0 - P0 * blockHam A B D)ᴴ * (blockHam A B D * P0 - P0 * blockHam A B D))
      = 2 * Q P0 (redist (blockHam A B D) P0) (redist (blockHam A B D) P0) := by
  rw [commutator_blockHam, redist_blockHam, Q_offDiag, fromBlocks_conjTranspose,
    fromBlocks_multiply]
  simp only [conjTranspose_zero, conjTranspose_neg, conjTranspose_conjTranspose, Matrix.zero_mul,
    zero_add, Matrix.mul_zero, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    trace_fromBlocks']
  rw [trace_mul_comm Bᴴ B]; ring

/-- `B = 0` iff the coupling decouples: the UPG equivalence `[H,P₀] = 0 ↔ B = 0`, through the
IQGT metric. -/
theorem metric_redist_blockHam_eq_zero_iff (A : Matrix k k ℂ) (B : Matrix k m ℂ)
    (D : Matrix m m ℂ) :
    metric P0 (redist (blockHam A B D) P0) (redist (blockHam A B D) P0) = 0 ↔ B = 0 := by
  rw [metric_redist_blockHam]
  constructor
  · intro h
    have h' : trace (B * Bᴴ) = 0 := by
      apply Complex.ext h
      have : (trace (B * Bᴴ)) = trace (Bᴴᴴ * Bᴴ) := by rw [conjTranspose_conjTranspose]
      rw [this]
      exact (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self Bᴴ).trace_nonneg).2.symm
    exact trace_mul_conjTranspose_self_eq_zero_iff.mp h'
  · rintro rfl; simp

end Block

end IQGT
