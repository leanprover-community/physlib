/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import Mathlib.RepresentationTheory.Invariants
/-!
# Gauge tensors carrying two `u(1)` adjoint indices

The hypercharge field strength `B` carries one `u(1)` adjoint index, and a product of two
field strengths carries two. The `u(1)` factor of the gauge group is abelian, so its adjoint
action on its own Lie algebra is trivial: a hypercharge rotation leaves every component of
such a product alone, and every combination of the components is a hypercharge invariant.
This is the companion of `IsSU2BiAdjoint` and `IsSU3BiAdjoint` for the third factor of the
gauge group, and it is the degenerate case: the index takes a single value, the adjoint
matrix is the one by one matrix `1`, and the trace contraction is the one component.

`IsU1BiAdjoint B repGauge T` records the hypothesis, in the same shape as its companions so
that the three factors can be treated alike: `T` is a family indexed by two `u(1)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group, and a
hypercharge rotation `u ∈ U(1)` moves its components by two copies of the adjoint matrix of
`u`, which is to say not at all. Nothing is asked of the colour and isospin factors.

The theorem, `span_le_invariants`, says that the span of the components consists of gauge
invariants once the law is known at every gauge element and not only at the hypercharge
ones. That hypothesis cannot be dropped: `IsU1BiAdjoint` says nothing about the colour and
isospin factors, which may move the components. Where they do not, as for the hypercharge
field strengths of `IsGaugeSector`, the hypothesis is supplied by the transformation law of
the underlying field.

Section A gives the adjoint matrix and the transformation law, section B the span and the
trace contraction, and section C the invariance of the span.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint action of `U(1)` on a hypercharge index

The `u(1)` factor is abelian, so it acts trivially on its own algebra and the adjoint matrix
is the one by one matrix `1`, whatever the element of `U(1)`. The transformation law is
recorded with one factor of that matrix per index, exactly as for the other two factors, and
`isU1BiAdjointMat_iff` reads it as the statement that the map fixes every component.

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

/- `span` and `traceContraction` take the hypothesis `hT` only to hang off it by dot
notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 1) → B}

/-!

## B. The span and the trace contraction

-/

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsU1BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff (hT : IsU1BiAdjoint B repGauge T) (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 1) → ℂ), x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-- The trace contraction: the Kronecker contraction of the two `u(1)` indices, which is
  the one component of the family. -/
@[nolint unusedArguments]
def traceContraction (hT : IsU1BiAdjoint B repGauge T) : B := ∑ a : Fin 1, T ![a, a]

/-- Any map obeying the `u(1)` law fixes the trace contraction. -/
lemma map_traceContraction (hT : IsU1BiAdjoint B repGauge T)
    {u : unitary ℂ} {f : B →ₗ[ℂ] B} (hf : IsU1BiAdjointMat u f T) :
    f hT.traceContraction = hT.traceContraction := by
  rw [traceContraction, map_sum]
  exact Finset.sum_congr rfl fun a _ => hf.map_T _

/-- The trace contraction is fixed by the hypercharge factor. -/
lemma repGauge_traceContraction (hT : IsU1BiAdjoint B repGauge T) (u : unitary ℂ) :
    repGauge (1, 1, u) hT.traceContraction = hT.traceContraction :=
  hT.map_traceContraction (hT.repGauge_T u)

/-!

## C. The whole span is invariant

-/

/-- Every vector of the span is fixed by any map obeying the `u(1)` law. -/
lemma map_of_mem_span (hT : IsU1BiAdjoint B repGauge T) {u : unitary ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsU1BiAdjointMat u f T) {x : B} (hx : x ∈ hT.span) : f x = x := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff x).1 hx
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul, hf.map_T d]

/-- The span of the components consists of gauge invariants, once the law is known to hold
  at every gauge element and not only at the hypercharge ones. -/
theorem span_le_invariants (hT : IsU1BiAdjoint B repGauge T)
    (hmat : ∀ g : GaugeGroupI, IsU1BiAdjointMat (GaugeGroupI.toU1 g) (repGauge g) T) :
    hT.span ≤ repGauge.invariants :=
  fun _ hx => (Representation.mem_invariants _ _).2 fun g => hT.map_of_mem_span (hmat g) hx

end IsU1BiAdjoint

end StandardModel
