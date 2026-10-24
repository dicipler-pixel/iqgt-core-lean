/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import IQGTCore.Tangent
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The intrinsic quantum geometric tensor `Q_P(V,W) = Tr(PVW)`

This is the primitive geometric object of the library. **No Riemannian or spacetime metric
from Mathlib's manifold library is used.** The geometry is the intrinsic Hilbert–Schmidt
(Fisher) form on projector tangents:

* `IQGT.Q P V W = trace (P * V * W)` for complex square matrices;
* `IQGT.metric P V W = re (Q P V W)` (the quantum metric `g`);
* `IQGT.curvature P V W = 2 * im (Q P V W)` (the Berry curvature `Ω`; sign convention of
  `IqgtGrassmannian/Basic.lean`. Every inequality below involves only `Ω²`, so it does not
  depend on that sign choice).

The projector hypothesis is Mathlib's `IsStarProjection P` (`P * P = P`, `star P = P`), tangent
vectors are Hermitian (`Vᴴ = V`) and satisfy `IQGT.IsTangent P V`.

Main results:
* `Q_eq_frobenius` : `Q P V W = Tr((VP)ᴴ (WP))` – the form is a Frobenius/Gram pairing of the
  cross-gap blocks.
* `Q_swap` : `Q P W V = conj (Q P V W)` – Hermitian; hence `metric_symm`, `curvature_antisymm`.
* `metric_self_nonneg`, `metric_self_eq_zero_iff`, `metric_pos` – `g` is positive definite on
  Hermitian tangents.
* `Q_add_Q_swap` / `metric_eq_half_re_trace` – `g(V,W) = ½ Re Tr(VW)` on tangents (the
  Hilbert–Schmidt metric, independent of `P` once `V` is tangent).
* `two_Q_self` – `2 Q(V,V) = Tr(V²)`, the trace step of `F_Q = 4g/k`.
* `metric_control` / `curvature_sq_le` – **Gram inequality** `(Im Q)² ≤ g_VV g_WW − g_VW²`,
  equivalently `Ω² ≤ 4 (g_VV g_WW − g_VW²)` (operator form of `4 det g ≥ Ω²`).
* `rigidity` – `g(V,V) = 0` forces `Ω(V,W) = 0`.
* `Q_unitary_conj` – unitary frame changes leave `Q` unchanged.
-/

namespace IQGT

open Matrix ComplexConjugate
open scoped ComplexOrder

variable {n : Type*} [Fintype n]

/-- The intrinsic quantum geometric tensor `Q_P(V,W) = Tr(PVW)`. -/
def Q (P V W : Matrix n n ℂ) : ℂ := trace (P * V * W)

/-- The quantum metric `g = Re Q`. -/
noncomputable def metric (P V W : Matrix n n ℂ) : ℝ := (Q P V W).re

/-- The Berry curvature `Ω = 2 Im Q`. -/
noncomputable def curvature (P V W : Matrix n n ℂ) : ℝ := 2 * (Q P V W).im

lemma conjTranspose_eq_of_isStarProjection {P : Matrix n n ℂ} (hP : IsStarProjection P) :
    Pᴴ = P := by
  have := hP.isSelfAdjoint
  rwa [IsSelfAdjoint, star_eq_conjTranspose] at this

/-- `Q(V,W) = Tr((VP)ᴴ(WP))` for Hermitian `V` and an orthogonal projector `P`. -/
theorem Q_eq_frobenius {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (W : Matrix n n ℂ) : Q P V W = trace ((V * P)ᴴ * (W * P)) := by
  unfold Q
  rw [conjTranspose_mul, hV, conjTranspose_eq_of_isStarProjection hP, ← Matrix.mul_assoc,
    trace_mul_comm (P * V * W) P, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.isIdempotentElem.eq]

/-- The Frobenius pairing is Hermitian: `Tr(Bᴴ A) = conj Tr(Aᴴ B)`. -/
theorem frob_herm (A B : Matrix n n ℂ) : trace (Bᴴ * A) = conj (trace (Aᴴ * B)) := by
  rw [← Complex.star_def, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- **Hermitian symmetry** `Q(W,V) = conj Q(V,W)`. -/
theorem Q_swap {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) (hW : Wᴴ = W) :
    Q P W V = conj (Q P V W) := by
  rw [Q_eq_frobenius hP hW, Q_eq_frobenius hP hV, frob_herm]

theorem metric_symm {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (hW : Wᴴ = W) : metric P W V = metric P V W := by
  unfold metric; rw [Q_swap hP hV hW, Complex.conj_re]

theorem curvature_antisymm {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (hW : Wᴴ = W) : curvature P W V = -curvature P V W := by
  unfold curvature; rw [Q_swap hP hV hW, Complex.conj_im]; ring

theorem Q_self_im {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) :
    (Q P V V).im = 0 := by
  have h := Q_swap hP hV hV
  exact Complex.conj_eq_iff_im.mp h.symm

theorem curvature_self {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) :
    curvature P V V = 0 := by
  unfold curvature; rw [Q_self_im hP hV, mul_zero]

theorem Q_self_nonneg {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) :
    0 ≤ Q P V V := by
  rw [Q_eq_frobenius hP hV]
  exact (posSemidef_conjTranspose_mul_self (V * P)).trace_nonneg

theorem metric_self_nonneg {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) :
    0 ≤ metric P V V :=
  (Complex.nonneg_iff.mp (Q_self_nonneg hP hV)).1

/-- `g(V,V) = 0` iff the cross-gap block `VP` vanishes. -/
theorem metric_self_eq_zero_iff {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) :
    metric P V V = 0 ↔ V * P = 0 := by
  rw [← trace_conjTranspose_mul_self_eq_zero_iff, ← Q_eq_frobenius hP hV]
  constructor
  · intro h; exact Complex.ext h (Q_self_im hP hV)
  · intro h; unfold metric; rw [h, Complex.zero_re]

/-- A Hermitian tangent with `VP = 0` is zero. -/
theorem eq_zero_of_mul_proj_eq_zero [DecidableEq n] {P V : Matrix n n ℂ} (hP : IsStarProjection P)
    (hV : Vᴴ = V) (hT : IsTangent P V) (h0 : V * P = 0) : V = 0 := by
  have hPV : P * V = 0 := by
    have := congrArg conjTranspose h0
    rwa [conjTranspose_mul, hV, conjTranspose_eq_of_isStarProjection hP,
      conjTranspose_zero] at this
  have e := hT
  unfold IsTangent at e
  rw [hPV, h0, add_zero] at e
  exact e

/-- **Positive definiteness**: `g(V,V) > 0` for every nonzero Hermitian tangent `V`. -/
theorem metric_pos [DecidableEq n] {P V : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (hT : IsTangent P V) (hne : V ≠ 0) : 0 < metric P V V := by
  rcases (metric_self_nonneg hP hV).lt_or_eq with h | h
  · exact h
  · exact absurd (eq_zero_of_mul_proj_eq_zero hP hV hT ((metric_self_eq_zero_iff hP hV).mp h.symm))
      hne

/-- Remark 2.3: `Q(V,W) + Q(W,V) = Tr(VW)` as soon as `V` is tangent (any `W`). -/
theorem Q_add_Q_swap [DecidableEq n] {P V : Matrix n n ℂ} (hT : IsTangent P V) (W : Matrix n n ℂ) :
    Q P V W + Q P W V = trace (V * W) := by
  unfold Q
  have h : V * W = (P * V + V * P) * W := by rw [← hT]
  rw [h, add_mul, trace_add, trace_mul_cycle V P W, trace_mul_cycle W V P]

/-- `Q(V,W) − Q(W,V) = Tr(P[V,W])`: the curvature is the trace of the projected commutator. -/
theorem Q_sub_Q_swap (P V W : Matrix n n ℂ) :
    Q P V W - Q P W V = trace (P * (V * W - W * V)) := by
  unfold Q; rw [Matrix.mul_sub, trace_sub, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **The metric is the Hilbert–Schmidt metric**: `g(V,W) = ½ Re Tr(VW)` on tangents. -/
theorem metric_eq_half_re_trace [DecidableEq n] {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (hW : Wᴴ = W) (hT : IsTangent P V) : metric P V W = (trace (V * W)).re / 2 := by
  have h := congrArg Complex.re (Q_add_Q_swap hT W)
  rw [Complex.add_re] at h
  have hs : (Q P W V).re = (Q P V W).re := by rw [Q_swap hP hV hW, Complex.conj_re]
  unfold metric; rw [hs] at h; linarith

/-- Trace step of Lemma 5.1: `2 Q(V,V) = Tr(V²)` for tangent `V` (so `F_Q = 4 g / k`). -/
theorem two_Q_self [DecidableEq n] {P V : Matrix n n ℂ} (hT : IsTangent P V) :
    2 * Q P V V = trace (V * V) := by
  rw [two_mul]; exact Q_add_Q_swap hT V

/-! ### The Gram inequality -/

/-- Two matrices as the two columns of one matrix (indexed by matrix entries). -/
def cols (A B : Matrix n n ℂ) : Matrix (n × n) (Fin 2) ℂ := of fun p a => ![A, B] a p.1 p.2

theorem frob_sum (A B : Matrix n n ℂ) :
    ∑ p : n × n, conj (A p.1 p.2) * B p.1 p.2 = trace (Aᴴ * B) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Complex.star_def]
  exact Finset.sum_comm

theorem gram_entries (A B : Matrix n n ℂ) :
    ((cols A B)ᴴ * cols A B) 0 0 = trace (Aᴴ * A) ∧
      ((cols A B)ᴴ * cols A B) 0 1 = trace (Aᴴ * B) ∧
      ((cols A B)ᴴ * cols A B) 1 0 = trace (Bᴴ * A) ∧
      ((cols A B)ᴴ * cols A B) 1 1 = trace (Bᴴ * B) := by
  simp only [mul_apply, conjTranspose_apply, cols, of_apply]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [frob_sum]

/-- The Gram determinant of two Frobenius vectors is nonnegative. -/
theorem gram_det_nonneg (A B : Matrix n n ℂ) :
    0 ≤ trace (Aᴴ * A) * trace (Bᴴ * B) - trace (Aᴴ * B) * trace (Bᴴ * A) := by
  have h := (posSemidef_conjTranspose_mul_self (cols A B)).det_nonneg
  rw [det_fin_two] at h
  obtain ⟨h00, h01, h10, h11⟩ := gram_entries A B
  rwa [h00, h01, h10, h11] at h

/-- **Metric control of curvature (Gram inequality).**
`(Im Q(V,W))² ≤ g(V,V) g(W,W) − g(V,W)²`. -/
theorem metric_control {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (hW : Wᴴ = W) :
    (Q P V W).im ^ 2 ≤ metric P V V * metric P W W - metric P V W ^ 2 := by
  set A := V * P
  set B := W * P
  have eVV : Q P V V = trace (Aᴴ * A) := Q_eq_frobenius hP hV V
  have eWW : Q P W W = trace (Bᴴ * B) := Q_eq_frobenius hP hW W
  have eVW : Q P V W = trace (Aᴴ * B) := Q_eq_frobenius hP hV W
  have hBA : trace (Bᴴ * A) = conj (trace (Aᴴ * B)) := frob_herm A B
  have hAA : (trace (Aᴴ * A)).im = 0 := by rw [← eVV]; exact Q_self_im hP hV
  have hBB : (trace (Bᴴ * B)).im = 0 := by rw [← eWW]; exact Q_self_im hP hW
  have hd := gram_det_nonneg A B
  rw [hBA] at hd
  have hre := (Complex.nonneg_iff.mp hd).1
  unfold metric
  rw [eVV, eWW, eVW]
  simp only [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, hAA, hBB,
    mul_zero, sub_zero] at hre
  nlinarith [hre]

/-- **`4 det g ≥ Ω²`** in operator form: `Ω(V,W)² ≤ 4 (g_VV g_WW − g_VW²)`. -/
theorem curvature_sq_le {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V)
    (hW : Wᴴ = W) :
    curvature P V W ^ 2 ≤ 4 * (metric P V V * metric P W W - metric P V W ^ 2) := by
  have h := metric_control hP hV hW
  unfold curvature; nlinarith [h]

/-- **Rigidity**: `g(V,V) = 0` forces `Ω(V,W) = 0`. -/
theorem rigidity {P V W : Matrix n n ℂ} (hP : IsStarProjection P) (hV : Vᴴ = V) (hW : Wᴴ = W)
    (h0 : metric P V V = 0) : curvature P V W = 0 := by
  have h := metric_control hP hV hW
  rw [h0, zero_mul, zero_sub] at h
  have : (Q P V W).im = 0 := by nlinarith [sq_nonneg (metric P V W), sq_nonneg (Q P V W).im]
  unfold curvature; rw [this, mul_zero]

/-! ### Frame independence -/

/-- Unitary frame changes leave `Q` invariant: `Q(UPU⁻¹, UVU⁻¹, UWU⁻¹) = Q(P,V,W)`. -/
theorem Q_unitary_conj [DecidableEq n] {U : Matrix n n ℂ} (hU : star U * U = 1) (P V W : Matrix n n ℂ) :
    Q (U * P * star U) (U * V * star U) (U * W * star U) = Q P V W := by
  unfold Q
  have e : U * P * star U * (U * V * star U) * (U * W * star U)
      = U * (P * (star U * U) * V * (star U * U) * W) * star U := by
    simp only [Matrix.mul_assoc]
  rw [e, hU, Matrix.mul_one, Matrix.mul_one, trace_mul_comm, ← Matrix.mul_assoc, hU,
    Matrix.one_mul]

end IQGT
