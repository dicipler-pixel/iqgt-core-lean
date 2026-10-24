/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# The tangent law at a projector (ring level)

Everything here holds in an arbitrary (noncommutative) ring `R`, so it applies to matrices,
bounded operators, or any other algebra. The projector hypothesis is Mathlib's
`IsIdempotentElem`.

* `IQGT.IsTangent P V` : the linearised constraint `V = PV + VP` (derivative of `P² = P`).
* `IQGT.tangent_iff_blocks` : `V` is tangent iff both diagonal blocks vanish,
  `PVP = 0` and `(1-P)V(1-P) = 0` (every tangent is purely cross-gap).
* `IQGT.tangent_eq_offdiag` : `V = PV(1-P) + (1-P)VP`.
* `IQGT.redist` : the redistribution operator `F(Ω,P) = (1-P)ΩP + PΩ(1-P)`;
  `redist_tangent`, `redist_eq_zero_iff` (`F = 0 ↔ ΩP = PΩ`).
* `IQGT.gap_identity` : the Sylvester identity behind the finite Davis–Kahan rule.

Provenance: ported from `iqgt-grassmannian-lean` (PR #1 branch `claude-rebuild-sections-2-6`,
`IqgtGrassmannian/Rebuild.lean`), `dirac-time-lean` (`DiracTime/ProjectorTangent.lean`),
`gravity-ledger-lean` (`Gravity.lean`) and `upg-lean` (`UPGAlgebra.lean`), which each carried
their own copy. Here there is one copy, phrased with Mathlib's `IsIdempotentElem` API
(`IsIdempotentElem.mul_one_sub_self`, `IsIdempotentElem.one_sub_mul_self`,
`IsIdempotentElem.one_sub`).
-/

namespace IQGT

variable {R : Type*} [Ring R]

/-- The linearised projector constraint `V = PV + VP` (the derivative of `P² = P`). -/
def IsTangent (P V : R) : Prop := V = P * V + V * P

/-- Expansion used repeatedly: `(1-P)X(1-P) = X - (PX + XP) + PXP`. -/
theorem compl_sandwich (P X : R) :
    (1 - P) * X * (1 - P) = X - (P * X + X * P) + P * X * P := by
  noncomm_ring

/-- A tangent vector has zero occupied–occupied block: `PVP = 0`. -/
theorem IsTangent.occupied_block {P V : R} (hP : IsIdempotentElem P) (hV : IsTangent P V) :
    P * V * P = 0 := by
  have h : P * V * P = P * V * P + P * V * P := by
    calc P * V * P = P * (P * V + V * P) * P := by rw [← hV]
      _ = (P * P) * V * P + P * V * (P * P) := by noncomm_ring
      _ = P * V * P + P * V * P := by rw [hP.eq]
  simpa using h

/-- A tangent vector has zero empty–empty block: `(1-P)V(1-P) = 0`. -/
theorem IsTangent.empty_block {P V : R} (hP : IsIdempotentElem P) (hV : IsTangent P V) :
    (1 - P) * V * (1 - P) = 0 := by
  rw [compl_sandwich, ← hV, hV.occupied_block hP, sub_self, add_zero]

/-- Converse: both diagonal blocks vanishing makes `V` tangent (no idempotence needed). -/
theorem isTangent_of_blocks {P V : R} (h1 : P * V * P = 0) (h2 : (1 - P) * V * (1 - P) = 0) :
    IsTangent P V := by
  rw [compl_sandwich, h1, add_zero, sub_eq_zero] at h2
  exact h2

/-- **Tangent law.** At an idempotent, `V` is tangent iff it is purely off-diagonal. -/
theorem tangent_iff_blocks {P V : R} (hP : IsIdempotentElem P) :
    IsTangent P V ↔ P * V * P = 0 ∧ (1 - P) * V * (1 - P) = 0 :=
  ⟨fun h => ⟨h.occupied_block hP, h.empty_block hP⟩, fun h => isTangent_of_blocks h.1 h.2⟩

/-- A tangent is the sum of its two cross-gap blocks: `V = PV(1-P) + (1-P)VP`. -/
theorem IsTangent.eq_offdiag {P V : R} (hP : IsIdempotentElem P) (hV : IsTangent P V) :
    V = P * V * (1 - P) + (1 - P) * V * P := by
  have e : V = P * V * (1 - P) + (1 - P) * V * P + P * V * P + (1 - P) * V * (1 - P) := by
    noncomm_ring
  rw [hV.occupied_block hP, hV.empty_block hP, add_zero, add_zero] at e
  exact e

/-- `-V` is tangent at the complementary projector `1 - P`. -/
theorem IsTangent.compl {P V : R} (hV : IsTangent P V) : IsTangent (1 - P) (-V) := by
  unfold IsTangent at *
  have e : (1 - P) * -V + -V * (1 - P) = -V - V + (P * V + V * P) := by noncomm_ring
  rw [e, ← hV]; abel

/-- Tangent vectors at `P` form an additive subgroup (closed under `+`). -/
theorem IsTangent.add {P V W : R} (hV : IsTangent P V) (hW : IsTangent P W) :
    IsTangent P (V + W) := by
  unfold IsTangent at *
  conv_lhs => rw [hV, hW]
  noncomm_ring

/-- Tangent vectors at `P` are closed under negation. -/
theorem IsTangent.neg {P V : R} (hV : IsTangent P V) : IsTangent P (-V) := by
  unfold IsTangent at *
  conv_lhs => rw [hV]
  noncomm_ring

/-- The redistribution operator `F(Ω,P) = (1-P)ΩP + PΩ(1-P)`. -/
def redist (Ω P : R) : R := (1 - P) * Ω * P + P * Ω * (1 - P)

theorem redist_eq_sum_form (Ω P : R) : redist Ω P = Ω * P + P * Ω - 2 * (P * Ω * P) := by
  unfold redist; noncomm_ring

/-- `F(Ω,P) = [[Ω,P],P]` for an idempotent `P`. -/
theorem redist_double_bracket (Ω P : R) (hP : IsIdempotentElem P) :
    redist Ω P = (Ω * P - P * Ω) * P - P * (Ω * P - P * Ω) := by
  calc redist Ω P = Ω * P + P * Ω - P * Ω * P - P * Ω * P := by unfold redist; noncomm_ring
    _ = Ω * (P * P) + (P * P) * Ω - P * Ω * P - P * Ω * P := by rw [hP.eq]
    _ = (Ω * P - P * Ω) * P - P * (Ω * P - P * Ω) := by noncomm_ring

theorem proj_mul_redist (Ω P : R) (hP : IsIdempotentElem P) :
    P * redist Ω P = P * Ω * (1 - P) := by
  have a : P * redist Ω P = (P * (1 - P)) * Ω * P + (P * P) * Ω * (1 - P) := by
    unfold redist; noncomm_ring
  rw [a, hP.mul_one_sub_self, hP.eq, zero_mul, zero_mul, zero_add]

theorem redist_mul_proj (Ω P : R) (hP : IsIdempotentElem P) :
    redist Ω P * P = (1 - P) * Ω * P := by
  have b : redist Ω P * P = (1 - P) * Ω * (P * P) + P * Ω * ((1 - P) * P) := by
    unfold redist; noncomm_ring
  rw [b, hP.one_sub_mul_self, hP.eq, mul_zero, add_zero]

/-- The redistribution operator is a tangent vector at `P`. -/
theorem redist_isTangent (Ω P : R) (hP : IsIdempotentElem P) : IsTangent P (redist Ω P) := by
  unfold IsTangent
  rw [proj_mul_redist Ω P hP, redist_mul_proj Ω P hP]
  unfold redist; exact add_comm _ _

/-- `F(Ω,P) = 0` exactly when `Ω` commutes with `P`. -/
theorem redist_eq_zero_iff (Ω P : R) (hP : IsIdempotentElem P) :
    redist Ω P = 0 ↔ Ω * P = P * Ω := by
  constructor
  · intro hF
    have a := proj_mul_redist Ω P hP
    have b := redist_mul_proj Ω P hP
    rw [hF, mul_zero, mul_sub, mul_one] at a
    rw [hF, zero_mul, sub_mul, one_mul, sub_mul] at b
    have e1 : P * Ω = P * Ω * P := sub_eq_zero.mp a.symm
    have e2 : Ω * P = P * Ω * P := sub_eq_zero.mp b.symm
    rw [e2, ← e1]
  · intro hc
    rw [redist_double_bracket Ω P hP, hc, sub_self, zero_mul, mul_zero, sub_self]

/-- An operator that commutes with `P` and is tangent at `P` is zero: commuting directions
do not move the subspace. -/
theorem IsTangent.eq_zero_of_commute {P V : R} (hP : IsIdempotentElem P) (hV : IsTangent P V)
    (hc : V * P = P * V) : V = 0 := by
  have h := hV.eq_offdiag hP
  have e1 : P * V * (1 - P) = V * (P * (1 - P)) := by rw [← hc]; noncomm_ring
  have e2 : (1 - P) * V * P = ((1 - P) * P) * V := by
    rw [mul_assoc, hc]; noncomm_ring
  rw [e1, e2, hP.mul_one_sub_self, hP.one_sub_mul_self, mul_zero, zero_mul, add_zero] at h
  exact h

/-- Symmetric-logarithmic-derivative core: `L = 2V` solves `LP + PL = 2V` for a tangent `V`
(for `ρ = P/k` the factor `1/k` cancels on both sides). -/
theorem IsTangent.sld {P V : R} (hV : IsTangent P V) : (2 * V) * P + P * (2 * V) = 2 * V := by
  have e : (2 * V) * P + P * (2 * V) = 2 * (P * V + V * P) := by
    simp only [two_mul, add_mul, mul_add]; abel
  rw [e, ← hV]

/-- Anything of the form `LP + PL` has no empty–empty block, so a variation with such a block
never solves the SLD equation. -/
theorem sld_empty_block {P L : R} (hP : IsIdempotentElem P) :
    (1 - P) * (L * P + P * L) * (1 - P) = 0 := by
  have e : (1 - P) * (L * P + P * L) * (1 - P)
      = (1 - P) * L * (P * (1 - P)) + ((1 - P) * P) * L * (1 - P) := by noncomm_ring
  rw [e, hP.mul_one_sub_self, hP.one_sub_mul_self]; simp

/-- Along a silent direction (`P' = 0`) the second derivative is again off-diagonal.
`A = P''`, `B = P'`; `P'' = P''P + 2P'P' + PP''` is `P² = P` differentiated twice. -/
theorem silent_second_order {P A B : R} (hP : IsIdempotentElem P)
    (h : A = A * P + 2 * (B * B) + P * A) (hB : B = 0) :
    P * A * P = 0 ∧ (1 - P) * A * (1 - P) = 0 := by
  have hT : IsTangent P A := by
    unfold IsTangent
    rw [hB] at h
    simpa [add_comm] using h
  exact (tangent_iff_blocks hP).mp hT

/-- **Gap (Sylvester) identity.** If `P` is a spectral projector of `A` and `Q` one of `A'`
(each commuting with its operator), then `(QA'Q)(QP) - (QP)(PAP) = Q(A'-A)P`. With `Q` the
complementary spectral projector of `A' = A + E`, the block `QP` measures how far the subspace
moved; this is the identity a gap turns into the finite Davis–Kahan bound. -/
theorem gap_identity {P Q A A' : R} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hA : A * P = P * A) (hA' : A' * Q = Q * A') :
    (Q * A' * Q) * (Q * P) - (Q * P) * (P * A * P) = Q * (A' - A) * P := by
  have e1 : Q * A' * Q * (Q * P) = Q * A' * P := by
    calc Q * A' * Q * (Q * P) = Q * A' * (Q * Q) * P := by noncomm_ring
      _ = Q * (A' * Q) * P := by rw [hQ.eq]; noncomm_ring
      _ = (Q * Q) * A' * P := by rw [hA']; noncomm_ring
      _ = Q * A' * P := by rw [hQ.eq]
  have e2 : Q * P * (P * A * P) = Q * A * P := by
    calc Q * P * (P * A * P) = Q * (P * P) * A * P := by noncomm_ring
      _ = Q * (P * A) * P := by rw [hP.eq]; noncomm_ring
      _ = Q * A * (P * P) := by rw [← hA]; noncomm_ring
      _ = Q * A * P := by rw [hP.eq]
  rw [e1, e2]; noncomm_ring

/-- The second resolvent identity: `a⁻¹ - b⁻¹ = a⁻¹ (b - a) b⁻¹` for units. -/
theorem second_resolvent (a b : Rˣ) :
    ((a⁻¹ : Rˣ) : R) - ((b⁻¹ : Rˣ) : R) =
      ((a⁻¹ : Rˣ) : R) * ((b : R) - (a : R)) * ((b⁻¹ : Rˣ) : R) := by
  rw [mul_sub, sub_mul, mul_assoc, Units.mul_inv, mul_one, Units.inv_mul, one_mul]

end IQGT
