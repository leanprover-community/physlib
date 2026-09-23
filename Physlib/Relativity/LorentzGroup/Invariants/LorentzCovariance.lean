/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.Basic
/-!
# Lorentz covariance of component families

A family `T` of vectors of a complex module `B`, indexed by `n` spacetime directions and moved
by a representation of `SL(2,ℂ)` with one factor of the Lorentz matrix per index, is what the
rank-specific files of this folder classify the invariants of. This file holds the predicate
saying so, at an arbitrary number of indices, together with the part of its interface that does
not depend on that number.

The transformation law is

`repLorentz g (T l) = ∑_a (∏ i, Λ(g)_{a i, l i}) • T a`,

with `l` free and `a` summed, and the summed index first in each factor of the Lorentz matrix
`Λ(g)` of `g`. That is how the basis vectors of a tensor power of the vector representation
move, and `Invariants.act` is the matching action on coefficients.

Nothing here assumes the components independent or `B` finite dimensional: the span of the
components is taken as it is, and a vector of it is written as a combination in a way that need
not be unique. The rank-zero case is admitted and says that every component is invariant.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants

/-!

## A. The span of a family of components

The span exists for any family, with no transformation law in sight, so it is defined on the
family alone. Its elements are exactly the combinations of the components, which is what
`mem_componentSpan_iff` records and what everything below reads it through.

-/

section Span

variable {ι B : Type*} [AddCommMonoid B] [Module ℂ B]

/-- The span of the components of a family `T`. -/
def componentSpan (T : ι → B) : Submodule ℂ B := ⨆ i, ℂ ∙ T i

/-- Every component lies in the component span. -/
lemma mem_componentSpan_self (T : ι → B) (i : ι) : T i ∈ componentSpan T :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_span_singleton_self _)

/-- The component span lies in a submodule exactly when every component does. -/
lemma componentSpan_le_iff (T : ι → B) (N : Submodule ℂ B) :
    componentSpan T ≤ N ↔ ∀ i, T i ∈ N :=
  iSup_le_iff.trans (forall_congr' fun _ => Submodule.span_singleton_le_iff_mem _ _)

variable [Fintype ι]

/-- A vector lies in the component span exactly when it is a combination `∑ i, c i • T i`. -/
lemma mem_componentSpan_iff (T : ι → B) (x : B) :
    x ∈ componentSpan T ↔ ∃ c : ι → ℂ, x = ∑ i, c i • T i := by
  classical
  rw [componentSpan, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

/-- Every combination of the components lies in their span. -/
lemma sum_smul_mem_componentSpan (T : ι → B) (c : ι → ℂ) : ∑ i, c i • T i ∈ componentSpan T :=
  (mem_componentSpan_iff T _).2 ⟨c, rfl⟩

end Span

section SpanQuotient

variable {ι B : Type*} [Fintype ι] [AddCommGroup B] [Module ℂ B]

/-- Taking classes modulo a submodule `S` carries `componentSpan T ⊔ S` into the span of the
  classes of the components. -/
lemma mkQ_mem_componentSpan (T : ι → B) (S : Submodule ℂ B) {x : B}
    (hx : x ∈ componentSpan T ⊔ S) : S.mkQ x ∈ componentSpan fun i => S.mkQ (T i) := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := (mem_componentSpan_iff T u).1 hu
  refine (mem_componentSpan_iff _ _).2 ⟨c, ?_⟩
  rw [map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz, add_zero, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

end SpanQuotient

/-!

## B. Families transforming with one Lorentz matrix per index

-/

/-- A family `T` of vectors of `B`, one per index vector `l : Fin n → Fin 1 ⊕ Fin 3`, which
  `repLorentz` moves the way the components of a rank-`n` tensor `T^{μ₁ ⋯ μₙ}` transform: one
  factor of the Lorentz matrix per slot, the moved index second in each factor and the summed
  one first. -/
structure IsLorentzCovariant (n : ℕ) (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin n → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin n → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin n), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsLorentzCovariant

section Monoid

variable {n : ℕ} {B : Type*} [AddCommMonoid B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin n → (Fin 1 ⊕ Fin 3)) → B}

/-- The image of the family under a linear map intertwining the two representations is again
  such a family. The map is not assumed injective or surjective. -/
lemma map {B' : Type*} [AddCommMonoid B'] [Module ℂ B'] {rep' : Representation ℂ SL(2,ℂ) B'}
    (hT : IsLorentzCovariant n B repLorentz T) (f : B →ₗ[ℂ] B')
    (hf : ∀ (g : SL(2,ℂ)) (y : B), f (repLorentz g y) = rep' g (f y)) :
    IsLorentzCovariant n B' rep' fun l => f (T l) where
  repLorentz_T g l := by
    rw [← hf, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The span of the components is Lorentz stable: each component goes to a combination of the
  components. -/
lemma repLorentz_mem_componentSpan (hT : IsLorentzCovariant n B repLorentz T) (g : SL(2,ℂ))
    {x : B} (hx : x ∈ componentSpan T) : repLorentz g x ∈ componentSpan T := by
  obtain ⟨c, rfl⟩ := (mem_componentSpan_iff T x).1 hx
  exact (mem_componentSpan_iff T _).2 ⟨_, repLorentz_sum_smul hT.repLorentz_T g c⟩

end Monoid

section Group

variable {n : ℕ} {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin n → (Fin 1 ⊕ Fin 3)) → B}

/-- The classes of the components in the quotient by a Lorentz-stable submodule again form a
  Lorentz tensor family of the same rank, for Mathlib's quotient representation. -/
lemma quotient (hT : IsLorentzCovariant n B repLorentz T) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsLorentzCovariant n (B ⧸ S) (repLorentz.quotient S fun g y hy => hS g y hy)
      fun l => S.mkQ (T l) :=
  hT.map S.mkQ fun _ _ => rfl

/-- A Lorentz invariant lying in the span of the components is the contraction of a coefficient
  tensor that the Lorentz matrices themselves fix. -/
theorem exists_isInvariantCoeff_of_mem_componentSpan
    (hT : IsLorentzCovariant n B repLorentz T) {x : B} (hx : x ∈ componentSpan T)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c ∧ x = ∑ d, c d • T d :=
  Invariants.exists_isInvariantCoeff_of_mem_span hT.repLorentz_T hx hinv

/-- Contracting the components with an invariant coefficient tensor gives a Lorentz
  invariant. -/
lemma isInvariant_sum_smul (hT : IsLorentzCovariant n B repLorentz T)
    {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) (g : SL(2,ℂ)) :
    repLorentz g (∑ d, c d • T d) = ∑ d, c d • T d :=
  repLorentz_sum_smul_of_isInvariantCoeff hT.repLorentz_T hc g

end Group

end IsLorentzCovariant

/-!

## C. The quotient representation on classes

Dividing out a Lorentz-stable submodule `S` uses Mathlib's `Representation.quotient`. The
stability hypothesis is kept in the membership form the rest of the library uses, and converted
where Mathlib asks for the `comap` form.

-/

/-- The quotient representation on `B ⧸ S` moves the class of `y` by moving `y`. -/
lemma quotient_apply_mkQ {B : Type*} [AddCommGroup B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (g : SL(2,ℂ)) (y : B) :
    repLorentz.quotient S (fun g y hy => hS g y hy) g (S.mkQ y) = S.mkQ (repLorentz g y) := rfl

end Lorentz
