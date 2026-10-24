/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Form

/-!
# Bridge: the two books of a projector field, read through the IQGT

`nonnormality-connection-energy-lean` proves that the Frobenius self-commutator energy of
`H = D + A` on a graph is the connection energy `Σ_edges ‖D_i − U D_j U*‖²`, that the opposite
energy is `Σ ‖D_i + U D_j U*‖²`, and that the two books share the budget `2 Σ deg(i) ‖D_i‖²`.
That graph-level identity is **not** re-proved here (it lives in that repository). What is
proved here is the single-edge algebra for a *projector* field and its exact relation to the
IQGT cross-gap block:

* `connection_book` : `Tr((P−R)²) = Tr P + Tr R − 2 Tr(PR)` for idempotents (chordal distance).
* `opposite_book` : `Tr((P+R)²) = Tr P + Tr R + 2 Tr(PR)`.
* `books_budget` : the two books sum to `2(Tr P + Tr R)`; `books_difference` : they differ by
  `4 Tr(PR)` (the indefinite form).
* `connection_book_eq_two_cross` : for orthogonal projectors of equal rank,
  `Tr((P−R)²) = 2 Tr(((1−R)P)ᴴ((1−R)P))` – the finite chordal distance is twice the squared
  cross-gap block, the finite counterpart of `Tr(V²) = 2 g(V,V)` (`IQGT.two_Q_self`).
* `connection_book_edge` : the same with a unitary edge transport `R = U P_j Uᴴ`.
* `connection_book_tangent` : along a tangent direction, the book of the displacement `tV` is
  `2 t² Q(V,V)`.
-/

namespace IQGT

open Matrix

section Comm

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [CommRing 𝕜]

/-- Connection book (chordal distance): `Tr((P−R)²) = Tr P + Tr R − 2 Tr(PR)`. -/
theorem connection_book {P R : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R) :
    trace ((P - R) * (P - R)) = trace P + trace R - 2 * trace (P * R) := by
  have e : (P - R) * (P - R) = P * P - P * R - R * P + R * R := by noncomm_ring
  rw [e, hP.eq, hR.eq, trace_add, trace_sub, trace_sub, trace_mul_comm R P]; ring

/-- Opposite book: `Tr((P+R)²) = Tr P + Tr R + 2 Tr(PR)`. -/
theorem opposite_book {P R : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R) :
    trace ((P + R) * (P + R)) = trace P + trace R + 2 * trace (P * R) := by
  have e : (P + R) * (P + R) = P * P + P * R + R * P + R * R := by noncomm_ring
  rw [e, hP.eq, hR.eq, trace_add, trace_add, trace_add, trace_mul_comm R P]; ring

/-- **Budget.** The two books of one edge sum to `2(Tr P + Tr R)`. -/
theorem books_budget {P R : Matrix n n 𝕜} (hP : IsIdempotentElem P) (hR : IsIdempotentElem R) :
    trace ((P - R) * (P - R)) + trace ((P + R) * (P + R)) = 2 * (trace P + trace R) := by
  rw [connection_book hP hR, opposite_book hP hR]; ring

/-- The books differ by the indefinite form `4 Tr(PR)`. -/
theorem books_difference {P R : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (hR : IsIdempotentElem R) :
    trace ((P + R) * (P + R)) - trace ((P - R) * (P - R)) = 4 * trace (P * R) := by
  rw [connection_book hP hR, opposite_book hP hR]; ring

end Comm

section Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Chordal distance = twice the cross-gap energy.** For orthogonal projectors of equal trace,
`Tr((P−R)²) = 2 Tr(((1−R)P)ᴴ((1−R)P))`. -/
theorem connection_book_eq_two_cross {P R : Matrix n n ℂ} (hP : IsStarProjection P)
    (hR : IsStarProjection R) (htr : trace P = trace R) :
    trace ((P - R) * (P - R)) = 2 * trace (((1 - R) * P)ᴴ * ((1 - R) * P)) := by
  have hPc := conjTranspose_eq_of_isStarProjection hP
  have hRc := conjTranspose_eq_of_isStarProjection hR
  have hRi := hR.isIdempotentElem.one_sub
  have e : ((1 - R) * P)ᴴ * ((1 - R) * P) = P * ((1 - R) * (1 - R)) * P := by
    rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPc, hRc]; noncomm_ring
  rw [e, hRi.eq, connection_book hP.isIdempotentElem hR.isIdempotentElem, ← htr]
  have e2 : P * (1 - R) * P = P * P - P * R * P := by noncomm_ring
  rw [e2, hP.isIdempotentElem.eq, trace_sub, trace_mul_cycle P R P, hP.isIdempotentElem.eq]
  ring

/-- Conjugating a projector by a unitary gives a projector. -/
theorem isIdempotentElem_unitary_conj {U P : Matrix n n ℂ} (hU : star U * U = 1)
    (hP : IsIdempotentElem P) : IsIdempotentElem (U * P * star U) := by
  unfold IsIdempotentElem
  have e : U * P * star U * (U * P * star U) = U * (P * (star U * U) * P) * star U := by
    simp only [Matrix.mul_assoc]
  rw [e, hU, Matrix.mul_one, hP.eq]

theorem trace_unitary_conj {U : Matrix n n ℂ} (hU : star U * U = 1) (X : Matrix n n ℂ) :
    trace (U * X * star U) = trace X := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **Edge form.** With a unitary transport `U` on the edge `i — j`, the connection book of a
projector field is `Tr P_i + Tr P_j − 2 Tr(P_i U P_j Uᴴ)`. -/
theorem connection_book_edge {U Pi Pj : Matrix n n ℂ} (hU : star U * U = 1)
    (hi : IsIdempotentElem Pi) (hj : IsIdempotentElem Pj) :
    trace ((Pi - U * Pj * star U) * (Pi - U * Pj * star U)) =
      trace Pi + trace Pj - 2 * trace (Pi * (U * Pj * star U)) := by
  rw [connection_book hi (isIdempotentElem_unitary_conj hU hj), trace_unitary_conj hU]

/-- Along a tangent direction the book of the displacement `tV` is `2 t² Q(V,V)`. -/
theorem connection_book_tangent {P V : Matrix n n ℂ} (hT : IsTangent P V) (t : ℂ) :
    trace ((P + t • V - P) * (P + t • V - P)) = 2 * t ^ 2 * Q P V V := by
  rw [add_sub_cancel_left, smul_mul_smul_comm, trace_smul, ← two_Q_self hT, smul_eq_mul]; ring

end Complex

end IQGT
