/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
/-!
# Families with two `u(1)` adjoint indices

The hypercharge factor is abelian, so its adjoint action on `u(1)` is trivial. A family
`T : (Fin 2 → Fin 1) → B` obeys the `u(1)` bi-adjoint law when a hypercharge rotation moves
it by one factor of the `1 × 1` adjoint matrix `1` per index, which is to say not at all
(`isU1BiAdjointMat_iff`). The law has the same shape as `IsSU2BiAdjoint` and
`IsSU3BiAdjoint`, so that the three factors can be treated alike. The trace contraction is the
one component of the family, and every map obeying the law fixes it.

- A. The adjoint matrix and the transformation law
- B. The trace contraction
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint matrix and the transformation law

-/

/-- The adjoint matrix of an element of `U(1)`: the one by one matrix `1`, the `u(1)`
  factor being abelian and so acting trivially on its own algebra. -/
def u1AdjointMatrix (_u : unitary ℂ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The single entry of the adjoint matrix of an element of `U(1)` is `1`. -/
@[simp]
lemma u1AdjointMatrix_apply (u : unitary ℂ) (i j : Fin 1) :
    u1AdjointMatrix u i j = 1 := rfl

/-- The linear map `f` moves the components of `T` as `u ∈ U(1)` moves a tensor with two
  adjoint indices: one factor of `u1AdjointMatrix u` per index, with the summed index in
  the row slot. -/
def IsU1BiAdjointMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (u : unitary ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 1) → B) : Prop :=
  ∀ l : Fin 2 → Fin 1,
    f (T l) = ∑ a : Fin 2 → Fin 1,
      (∏ i : Fin 2, ((u1AdjointMatrix u (a i) (l i) : ℝ) : ℂ)) • T a

/-- The `u(1)` transformation law says exactly that the map fixes every component: the
  adjoint matrix is `1`, and there is a single family of two `u(1)` indices to sum over. -/
lemma isU1BiAdjointMat_iff {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (u : unitary ℂ) (f : B →ₗ[ℂ] B) (T : (Fin 2 → Fin 1) → B) :
    IsU1BiAdjointMat u f T ↔ ∀ l : Fin 2 → Fin 1, f (T l) = T l := by
  refine forall_congr' fun l => ?_
  rw [Fintype.sum_unique, Subsingleton.elim (default : Fin 2 → Fin 1) l]
  simp

/-- A linear map obeying the `u(1)` transformation law fixes every component. -/
lemma IsU1BiAdjointMat.map_T {B : Type*} [AddCommMonoid B] [Module ℂ B] {u : unitary ℂ}
    {f : B →ₗ[ℂ] B} {T : (Fin 2 → Fin 1) → B} (hf : IsU1BiAdjointMat u f T)
    (l : Fin 2 → Fin 1) : f (T l) = T l :=
  (isU1BiAdjointMat_iff u f T).1 hf l

/-- A family `T` of elements of `B`, indexed by two `u(1)` adjoint indices, transforms as a
  tensor `T^{a b}` under the hypercharge factor of the gauge group. Nothing is asked of the
  colour and isospin factors. -/
structure IsU1BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 1) → B) : Prop where
  repGauge_T : ∀ g : unitary ℂ, IsU1BiAdjointMat g (repGauge (1, 1, g)) T

namespace IsU1BiAdjoint

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 1) → B}

/-!

## B. The trace contraction

-/

/-- The trace contraction: the Kronecker contraction of the two `u(1)` indices, which is
  the one component of the family. -/
def traceContraction (T : (Fin 2 → Fin 1) → B) : B := ∑ a : Fin 1, T ![a, a]

/-- Any map obeying the `u(1)` law fixes the trace contraction. -/
lemma map_traceContraction {u : unitary ℂ} {f : B →ₗ[ℂ] B} (hf : IsU1BiAdjointMat u f T) :
    f (traceContraction T) = traceContraction T := by
  rw [traceContraction, map_sum]
  exact Finset.sum_congr rfl fun a _ => hf.map_T _

end IsU1BiAdjoint

end StandardModel
