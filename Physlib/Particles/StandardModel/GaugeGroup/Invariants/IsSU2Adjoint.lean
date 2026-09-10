/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
/-!
# Gauge tensors carrying one `su(2)` adjoint index

A single `W`-boson field strength `W^a` carries one isospin index, running over the three
Pauli directions of `su(2)`, and transforms in the adjoint representation, which is the vector
representation `3` of the rotation group. That representation contains no singlet: no linear
combination of the three components is left alone by every isospin rotation, which is why a
Lagrangian never contains a term linear in a field strength. This file proves that fact in
the form the Standard Model files consume, modulo an isospin-stable submodule in which other
families are parked.

`IsSU2Adjoint B repGauge T` records the hypothesis. `T` is a family indexed by one isospin
index and valued in a module `B` carrying a representation of the gauge group, and an isospin
rotation `U ∈ SU(2)` moves its components by the adjoint matrix of `U`. Nothing is asked of
the colour and hypercharge factors.

The argument is the one of `IsSU2BiAdjoint` with one index instead of two. An isospin
invariant of the span is the contraction of an invariant coefficient vector, by
`Family.exists_invariant_coeff`, since the adjoint matrix is orthogonal. The three isospin
flips then kill the coefficient vector: the half turn about the axis `a + 1` reverses the
direction `a`, so an invariant coefficient vector is its own negative in every coordinate.

Section A gives the transformation law and the span, section B the action on coefficient
vectors, section C the vanishing of an invariant coefficient vector, and section D the
vanishing of the invariants of the span and its form modulo a stable submodule.
-/

@[expose] public section

namespace StandardModel

open Matrix IsSU2BiAdjoint

/-!

## A. The transformation law and the span of the components

The law carries one factor of the adjoint matrix, with the summed index in the row slot,
exactly as each of the two indices of a bi-adjoint family does.

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with one
  adjoint index. -/
def IsSU2AdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B) (T : Fin 3 → B) : Prop :=
  ∀ l : Fin 3, f (T l) = ∑ a : Fin 3, ((su2AdjointMatrix U a l : ℝ) : ℂ) • T a

/-- A family `T` of elements of `B`, indexed by one `su(2)` adjoint index, transforms as a
  tensor `T^a` under the isospin factor of the gauge group. Nothing is asked of the colour
  and hypercharge factors. -/
structure IsSU2Adjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) (T : Fin 3 → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2AdjointMat g (repGauge (1, g, 1)) T

namespace IsSU2Adjoint

/- `span` takes the hypothesis `hT` only to hang off it by dot notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : Fin 3 → B}

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU2Adjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff (hT : IsSU2Adjoint B repGauge T) (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 3 → ℂ, x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-!

## B. The action on coefficient vectors

A vector of the span is a contraction `∑ a, c a • T a` against a coefficient vector
`c : Fin 3 → ℂ`, and the law says that an isospin rotation moves it by the adjoint matrix
acting on `c`. That action is unitary for the standard inner product, the matrix being real
and orthogonal.

-/

/-- The adjoint matrix as a linear map on coefficient vectors. -/
noncomputable def act (U : specialUnitaryGroup (Fin 2) ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  Matrix.toLin' (Matrix.of fun a x => ((su2AdjointMatrix U a x : ℝ) : ℂ))

/-- The action on coefficient vectors, written out. -/
lemma act_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : Fin 3 → ℂ) (a : Fin 3) :
    act U c a = ∑ x, ((su2AdjointMatrix U a x : ℝ) : ℂ) * c x := by
  simp [act, Matrix.mulVec, dotProduct]

/-- The transformation law in coefficient form. -/
lemma map_sum_smul {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2AdjointMat U f T) (c : Fin 3 → ℂ) :
    f (∑ l, c l • T l) = ∑ a, act U c a • T a := by
  simp only [map_sum, map_smul, act_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hf l, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]

/-- The action of `U⁻¹` is the transpose of the action of `U`. -/
lemma sum_act_mul (U : specialUnitaryGroup (Fin 2) ℂ) (c d : Fin 3 → ℂ) :
    ∑ a, act U c a * d a = ∑ l, c l * act U⁻¹ d l := by
  simp only [act_apply, su2AdjointMatrix_inv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring

/-- The action on coefficient vectors commutes with complex conjugation. -/
lemma act_star (U : specialUnitaryGroup (Fin 2) ℂ) (c : Fin 3 → ℂ) :
    act U (star c) = star (act U c) := by
  funext a
  simp [act_apply, star_sum, star_mul', Complex.conj_ofReal]

/-!

## C. An invariant coefficient vector vanishes

-/

/-- An isospin flip scales each coordinate by the sign of its Pauli direction. -/
lemma act_su2Flip (k : Fin 3) (c : Fin 3 → ℂ) (a : Fin 3) :
    act (su2Flip k) c a = ((su2FlipSign k a : ℤ) : ℂ) * c a := by
  rw [act_apply]
  simp only [su2AdjointMatrix_su2Flip, apply_ite (fun r : ℝ => (r : ℂ)),
    Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Complex.ofReal_intCast]

/-- A coefficient vector fixed by every isospin rotation is zero: the flip about the axis
  `a + 1` reverses the direction `a`. -/
theorem eq_zero_of_act_eq {c : Fin 3 → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, act U c = c) : c = 0 := by
  funext a
  have hs : su2FlipSign (a + 1) a = -1 := by
    revert a
    decide
  have h := congrFun (hc (su2Flip (a + 1))) a
  rw [act_su2Flip, hs] at h
  push_cast at h
  rw [Pi.zero_apply]
  linear_combination (-1 / 2 : ℂ) * h

/-!

## D. A single adjoint index carries no invariant

The action on coefficients is unitary, so `Family.exists_invariant_coeff` writes an
invariant of the span as the contraction of an invariant coefficient vector, which section C
makes zero. The statement is made for any family of linear maps obeying the law, so that it
applies in a quotient, and `Family.exists_smul_add_of_mem_sup` then gives the form modulo a
stable submodule: an invariant of the span joined with `S` lies in `S`.

-/

/-- An invariant of the span of a family obeying the law for a family of linear maps
  `φ U` is zero: the adjoint representation of `SU(2)` contains no singlet. -/
theorem eq_zero_of_invariant' {φ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU2AdjointMat U (φ U) T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ U, φ U x = x) : x = 0 := by
  obtain ⟨c, rfl, hc⟩ := Family.exists_invariant_coeff T φ act
    (fun U c => map_sum_smul (hT U) c)
    (Family.sum_star_mul_of_transpose act sum_act_mul act_star) hx hinv
  simp [eq_zero_of_act_eq hc]

/-- An isospin invariant in the span of the components is zero. -/
theorem eq_zero_of_su2_invariant (hT : IsSU2Adjoint B repGauge T) {x : B}
    (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) : x = 0 :=
  eq_zero_of_invariant' hT.repGauge_T hx hinv

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU2AdjointMat_mapQ {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2AdjointMat U f T) (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU2AdjointMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- An isospin invariant of the span of the components joined with an isospin-stable
  submodule `S` lies in `S`: an `su(2)` adjoint index contributes nothing to the
  invariants. -/
theorem mem_of_mem_span_sup_su2_invariant (hT : IsSU2Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    x ∈ S := by
  obtain ⟨c, y, hyS, hxy, -⟩ := Family.exists_smul_add_of_mem_sup T
    (fun U => repGauge (1, U, 1)) S hS 0 (fun U => map_zero _)
    (fun x hx hinv => ⟨0, by
      rw [eq_zero_of_invariant' (fun U => isSU2AdjointMat_mapQ (hT.repGauge_T U) S (hS U))
        hx hinv, zero_smul]⟩) hx hinv
  rwa [hxy, smul_zero, zero_add]

/-- The isospin invariants of the span of the components joined with an isospin-stable
  submodule are exactly the isospin invariants of the submodule. -/
theorem mem_span_sup_su2_invariant_iff (hT : IsSU2Adjoint B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x)
      ↔ x ∈ S ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x :=
  ⟨fun ⟨hx, hinv⟩ => ⟨hT.mem_of_mem_span_sup_su2_invariant x S hS hx hinv, hinv⟩,
    fun ⟨hx, hinv⟩ => ⟨Submodule.mem_sup_right hx, hinv⟩⟩

end IsSU2Adjoint

end StandardModel
