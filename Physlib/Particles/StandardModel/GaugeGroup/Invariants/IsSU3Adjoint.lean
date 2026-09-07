/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
/-!
# Gauge tensors carrying one `su(3)` adjoint index

A single gluon field strength `F^a` carries one colour index, running over the eight
Gell-Mann directions of `su(3)`, and transforms in the adjoint representation `8`. That
representation contains no singlet: no linear combination of the eight components is left
alone by every colour rotation, which is why a Lagrangian never contains a term linear in a
field strength. This file proves that fact in the form the Standard Model files consume,
modulo a colour-stable submodule in which other families are parked.

`IsSU3Adjoint B repGauge T` records the hypothesis. `T` is a family indexed by one colour
index and valued in a module `B` carrying a representation of the gauge group, and a colour
rotation `U ∈ SU(3)` moves its components by the adjoint matrix of `U`. Nothing is asked of
the isospin and hypercharge factors.

The argument is the one of `IsSU3BiAdjoint` with one index instead of two. A colour
invariant of the span is the contraction of an invariant coefficient vector, by
`Family.exists_invariant_coeff`, since the adjoint matrix is orthogonal. Two colour
rotations then kill the coefficient vector. The colour parities, diagonal sign matrices of
`SU(3)`, reverse the six Gell-Mann directions that mix two colours and fix the two Cartan
directions `λ₃` and `λ₈`, so an invariant coefficient lives in the Cartan plane. The cyclic
permutation of the colours rotates that plane through a third of a turn, and a rotation of a
plane fixes no nonzero vector.

Section A gives the transformation law and the span, section B the action on coefficient
vectors, section C the vanishing of an invariant coefficient vector, and section D the
vanishing of the invariants of the span and its form modulo a stable submodule.
-/

@[expose] public section

namespace StandardModel

open Matrix IsSU3BiAdjoint

/-!

## A. The transformation law and the span of the components

The law carries one factor of the adjoint matrix, with the summed index in the row slot,
exactly as each of the two indices of a bi-adjoint family does.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with one
  adjoint index. -/
def IsSU3AdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B) (T : Fin 8 → B) : Prop :=
  ∀ l : Fin 8, f (T l) = ∑ a : Fin 8, ((su3AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T` of elements of `B`, indexed by one `su(3)` adjoint index, transforms as a
  tensor `T^a` under the colour factor of the gauge group. Nothing is asked of the isospin
  and hypercharge factors. -/
structure IsSU3Adjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 8 → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3AdjointMat g (repGauge (g, 1, 1)) T

namespace IsSU3Adjoint

/- `span` takes the hypothesis `hT` only to hang off it by dot notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : Fin 8 → B}

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU3Adjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff (hT : IsSU3Adjoint B repGauge T) (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 8 → ℂ, x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-!

## B. The action on coefficient vectors

A vector of the span is a contraction `∑ a, c a • T a` against a coefficient vector
`c : Fin 8 → ℂ`, and the law says that a colour rotation moves it by the row action
`IsSU3BiAdjoint.rowAct U` on `c`, which is the adjoint matrix itself as a linear map. It is
unitary for the standard inner product, the matrix being real and orthogonal.

-/

/-- The row action of the adjoint matrix, as a linear map on coefficient vectors. -/
noncomputable def act (U : specialUnitaryGroup (Fin 3) ℂ) : (Fin 8 → ℂ) →ₗ[ℂ] (Fin 8 → ℂ) :=
  Matrix.toLin' (Matrix.of fun a x => ((su3AdjointMatrix U a x : ℝ) : ℂ))

/-- The action on coefficient vectors is the row action. -/
lemma act_apply (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 8 → ℂ) :
    act U c = rowAct U c := by
  funext a
  simp [act, rowAct, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form. -/
lemma map_sum_smul {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3AdjointMat U f T) (c : Fin 8 → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, rowAct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The action of `U⁻¹` is the transpose of the action of `U`. -/
lemma sum_act_mul (U : specialUnitaryGroup (Fin 3) ℂ) (c d : Fin 8 → ℂ) :
    ∑ a, act U c a * d a = ∑ l, c l * act U⁻¹ d l := by
  simp only [act_apply, rowAct, su3AdjointMatrix_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The action on coefficient vectors commutes with complex conjugation. -/
lemma act_star (U : specialUnitaryGroup (Fin 3) ℂ) (c : Fin 8 → ℂ) :
    act U (star c) = star (act U c) := by
  funext a
  simp [act_apply, rowAct, star_sum, star_mul', Complex.conj_ofReal]

/-!

## C. An invariant coefficient vector vanishes

-/

/-- A colour parity scales each coordinate by the sign of its Gell-Mann direction. -/
lemma rowAct_su3Parity_apply (k : Fin 3) (c : Fin 8 → ℂ) (a : Fin 8) :
    rowAct (su3Parity k) c a = ((paritySign k a : ℤ) : ℂ) * c a := by
  simp only [rowAct, su3AdjointMatrix_su3Parity, apply_ite (fun r : ℝ => (r : ℂ)),
    Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Complex.ofReal_intCast]

/-- A coefficient vector fixed by every colour rotation is zero: the parities confine it to
  the Cartan plane, which the cyclic rotation turns through a third of a turn. -/
theorem eq_zero_of_rowAct_eq {c : Fin 8 → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, rowAct U c = c) : c = 0 := by
  -- the parities: every direction outside the Cartan plane carries a sign `-1`
  have hpar : ∀ (k : Fin 3) (a : Fin 8), paritySign k a = -1 → c a = 0 := by
    intro k a hk
    have h := congrFun (hc (su3Parity k)) a
    rw [rowAct_su3Parity_apply, hk] at h
    push_cast at h
    linear_combination (-1 / 2 : ℂ) * h
  have hroot : ∀ a : Fin 8, a ≠ 2 → a ≠ 7 → c a = 0 := by
    intro a h2 h7
    have key : paritySign 0 a = -1 ∨ paritySign 1 a = -1 := by
      revert a
      decide
    rcases key with h | h
    · exact hpar 0 a h
    · exact hpar 1 a h
  -- the Cartan plane: the cyclic rotation turns it, fixing nothing
  have hcart : c = c 2 • unitVec 2 + c 7 • unitVec 7 := by
    funext a
    have ha : a = 2 ∨ a = 7 ∨ (a ≠ 2 ∧ a ≠ 7) := by
      revert a
      decide
    rcases ha with rfl | rfl | ⟨h2, h7⟩
    · simp [unitVec]
    · simp [unitVec]
    · simp [unitVec, h2, h7, hroot a h2 h7]
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h := hc su3Perm
  rw [hcart, rowAct_add, rowAct_smul, rowAct_smul, rowAct_su3Perm_unitVec,
    rowAct_su3Perm_unitVec] at h
  have h2 := congrFun h 2
  have h7 := congrFun h 7
  simp [permCol, unitVec] at h2 h7
  have hc7 : c 7 = 0 := by
    linear_combination (-((Real.sqrt 3 : ℝ) : ℂ) / 6) * h2 + (-(1 : ℂ) / 2) * h7
      + (-(c 7) / 12) * h3
  have hc2 : c 2 = 0 := by
    linear_combination (-(2 : ℂ) / 3) * h2 - (((Real.sqrt 3 : ℝ) : ℂ) / 3) * hc7
  rw [hcart, hc2, hc7]
  simp

/-!

## D. A single adjoint index carries no invariant

The action on coefficients is unitary, so `Family.exists_invariant_coeff` writes an
invariant of the span as the contraction of an invariant coefficient vector, which section C
makes zero. The statement is made for any family of linear maps obeying the law, so that
it applies in a quotient, and `Family.exists_smul_add_of_mem_sup` then gives the form
modulo a stable submodule: an invariant of the span joined with `S` lies in `S`.

-/

/-- An invariant of the span of a family obeying the law for a family of linear maps
  `φ U` is zero: the adjoint representation of `SU(3)` contains no singlet. -/
theorem eq_zero_of_invariant' {φ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU3AdjointMat U (φ U) T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ U, φ U x = x) : x = 0 := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c)
    (Family.sum_star_mul_of_transpose act sum_act_mul act_star) hx hinv
  have hc0 : c = 0 := eq_zero_of_rowAct_eq fun U => by rw [← act_apply, hc U]
  simp [hc0]

/-- A colour invariant in the span of the components is zero. -/
theorem eq_zero_of_su3_invariant (hT : IsSU3Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) : x = 0 :=
  eq_zero_of_invariant' hT.repGauge_T hx hinv

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU3AdjointMat_mapQ {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3AdjointMat U f T) (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU3AdjointMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- A colour invariant of the span of the components joined with a colour-stable submodule
  `S` lies in `S`: an `su(3)` adjoint index contributes nothing to the invariants. -/
theorem mem_of_mem_span_sup_su3_invariant (hT : IsSU3Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    x ∈ S := by
  obtain ⟨c, y, hyS, hxy, -⟩ := Family.exists_smul_add_of_mem_sup T
    (fun U => repGauge (U, 1, 1)) S hS 0 (fun U => map_zero _)
    (fun x hx hinv => ⟨0, by
      rw [eq_zero_of_invariant' (fun U => isSU3AdjointMat_mapQ (hT.repGauge_T U) S (hS U))
        hx hinv, zero_smul]⟩) hx hinv
  rwa [hxy, smul_zero, zero_add]

/-- The colour invariants of the span of the components joined with a colour-stable
  submodule are exactly the colour invariants of the submodule. -/
theorem mem_span_sup_su3_invariant_iff (hT : IsSU3Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x)
      ↔ x ∈ S ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x :=
  ⟨fun ⟨hx, hinv⟩ => ⟨hT.mem_of_mem_span_sup_su3_invariant x S hS hx hinv, hinv⟩,
    fun ⟨hx, hinv⟩ => ⟨Submodule.mem_sup_right hx, hinv⟩⟩

end IsSU3Adjoint

end StandardModel
