/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The underlying module of a subrepresentation

Mathlib's `Subrepresentation` API records how `toSubmodule` interacts with the lattice
operations — `Subrepresentation.toSubmodule_sup` and `Subrepresentation.toSubmodule_inf`, both
`@[simp]` and both true by `rfl` — but not how it interacts with the bounded-lattice structure,
nor how it interacts with the order relations themselves, nor how it interacts with membership.
This file adds the five missing counterparts, in the same shape. It also records that the
representation action on a subrepresentation is the restriction of the original action, when an
intertwining map is zero and when it is surjective in terms of the subrepresentation its range is,
the inclusion of a subrepresentation as an intertwining map, that the group-algebra action on a
subrepresentation coerces to the original action, the canonical equivalence between the module of
the restricted representation and the corresponding submodule, and that a subrepresentation is
minimal exactly when the `A[G]`-submodule it carries is simple.

They are stated at the typeclasses `Subrepresentation` itself asks for, so they apply wherever
the abstraction does. The `⊥` and `⊤` lemmas let proofs about extreme subrepresentations avoid
asserting the definitional unfolding of the `BoundedOrder` instance by hand; the `≤` and `<`
lemmas move an order statement between the two lattices, which is what lets a submodule-level
argument — a dimension count, say, or an orthogonal complement — settle a question about
subrepresentations; and the membership lemma does the same for a single element, so that a
carrier computed by a `toSubmodule` lemma answers a `SetLike` membership goal without unfolding
the `SetLike` instance by hand. `Representation.IntertwiningMap.eq_zero_iff_range_eq_bot` and
`Representation.IntertwiningMap.surjective_iff_range_eq_top` are the first consumers of the `⊥` and
`⊤` lemmas, and belong here because `⊥` and `⊤` of `Subrepresentation` have no other API: they are
`LinearMap.range_eq_bot` and `LinearMap.range_eq_top` moved up to the subrepresentation lattice,
and `Subrepresentation.subtype_eq_zero_iff` and `Subrepresentation.subtype_surjective_iff` below
are what they are proved for. In the same spirit,
`Subrepresentation.isSimpleModule_asSubmodule_iff` moves the notion of an irreducible constituent
across `Subrepresentation.subrepresentationSubmoduleOrderIso`, so that Mathlib's simple- and
semisimple-module API applies to minimal subrepresentations; being about `asSubmodule` it asks for
the coefficients to be a commutative ring, as `Subrepresentation.asSubmodule` and
`IsSimpleModule` between them do.

## Main results

* `Subrepresentation.mem_toSubmodule`
* `Subrepresentation.toSubmodule_bot`
* `Subrepresentation.toSubmodule_top`
* `Subrepresentation.toSubmodule_le_toSubmodule`
* `Subrepresentation.toSubmodule_lt_toSubmodule`
* `Subrepresentation.toRepresentation_apply`
* `Representation.IntertwiningMap.eq_zero_iff_range_eq_bot`
* `Representation.IntertwiningMap.surjective_iff_range_eq_top`
* `Subrepresentation.subtype`
* `Subrepresentation.coe_subtype`
* `Subrepresentation.toLinearMap_subtype`
* `Subrepresentation.subtype_injective`
* `Subrepresentation.range_subtype`
* `Subrepresentation.ker_subtype`
* `Subrepresentation.subtype_eq_zero_iff`
* `Subrepresentation.subtype_surjective_iff`
* `Subrepresentation.coe_toRepresentation_asAlgebraHom_apply`
* `Subrepresentation.asModuleEquivAsSubmodule`
* `Subrepresentation.isSimpleModule_asSubmodule_iff`
-/

public section

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- A vector lies in the subspace a subrepresentation carries exactly when it lies in the
subrepresentation. This is the `SetLike` instance of `Subrepresentation`, whose coercion is
`toSubmodule`, stated as a lemma so that proofs need not unfold it. -/
@[simp]
lemma mem_toSubmodule {ρ' : Subrepresentation ρ} {v : W} : v ∈ ρ'.toSubmodule ↔ v ∈ ρ' := Iff.rfl

/-- The bottom subrepresentation carries the bottom subspace. -/
@[simp]
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

/-- The top subrepresentation carries the top subspace. -/
@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

/-- One subrepresentation is contained in another exactly when the subspace it carries is. -/
@[simp]
lemma toSubmodule_le_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule ≤ ρ₂.toSubmodule ↔ ρ₁ ≤ ρ₂ := Iff.rfl

/-- One subrepresentation is strictly contained in another exactly when the subspace it carries
is. -/
@[simp]
lemma toSubmodule_lt_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule < ρ₂.toSubmodule ↔ ρ₁ < ρ₂ := by
  simp only [lt_iff_le_not_ge, toSubmodule_le_toSubmodule]

/-- The action on a subrepresentation is the restriction of the original action. -/
theorem toRepresentation_apply (S : Subrepresentation ρ) (g : G) :
    S.toRepresentation g = (ρ g).restrict (S.apply_mem_toSubmodule g) :=
  rfl

/-- An intertwining map is zero exactly when its range is the bottom subrepresentation. -/
theorem _root_.Representation.IntertwiningMap.eq_zero_iff_range_eq_bot
    {V : Type*} [AddCommMonoid V] [Module A V] {τ : Representation A G V}
    (f : Representation.IntertwiningMap ρ τ) : f = 0 ↔ f.range = ⊥ := by
  rw [← (Representation.IntertwiningMap.toLinearMap_injective ρ τ).eq_iff,
    Representation.IntertwiningMap.zero_toLinearMap, ← LinearMap.range_eq_bot,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    Representation.IntertwiningMap.range_toSubmodule, Subrepresentation.toSubmodule_bot]

/-- An intertwining map is surjective exactly when its range is the top subrepresentation. -/
theorem _root_.Representation.IntertwiningMap.surjective_iff_range_eq_top
    {V : Type*} [AddCommMonoid V] [Module A V] {τ : Representation A G V}
    (f : Representation.IntertwiningMap ρ τ) : Function.Surjective f ↔ f.range = ⊤ := by
  rw [← Representation.IntertwiningMap.coe_toLinearMap, ← LinearMap.range_eq_top,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    Representation.IntertwiningMap.range_toSubmodule, Subrepresentation.toSubmodule_top]

/-- **The inclusion of a subrepresentation**, as an intertwining map: the analogue of
`Submodule.subtype`, which is the linear map underlying it. -/
def subtype (ρ' : Subrepresentation ρ) :
    Representation.IntertwiningMap ρ'.toRepresentation ρ where
  toLinearMap := ρ'.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

/-- The inclusion of a subrepresentation acts by the subtype coercion. -/
@[simp]
lemma coe_subtype (ρ' : Subrepresentation ρ) : ⇑ρ'.subtype = Subtype.val := by rfl

/-- The linear map underlying the inclusion is the submodule subtype map. -/
@[simp]
lemma toLinearMap_subtype (ρ' : Subrepresentation ρ) :
    ρ'.subtype.toLinearMap = ρ'.toSubmodule.subtype := by rfl

/-- The range of the inclusion of a subrepresentation is that subrepresentation. -/
@[simp]
theorem range_subtype (ρ' : Subrepresentation ρ) : ρ'.subtype.range = ρ' := by
  apply toSubmodule_injective
  rw [Representation.IntertwiningMap.range_toSubmodule, toLinearMap_subtype,
    Submodule.range_subtype]

/-- The kernel of the inclusion of a subrepresentation is zero. -/
@[simp]
theorem ker_subtype (ρ' : Subrepresentation ρ) : ρ'.subtype.ker = ⊥ := by
  apply toSubmodule_injective
  rw [Representation.IntertwiningMap.ker_toSubmodule, toLinearMap_subtype, Submodule.ker_subtype,
    toSubmodule_bot]

/-- The inclusion of a subrepresentation is injective. -/
theorem subtype_injective (ρ' : Subrepresentation ρ) : Function.Injective ρ'.subtype := by
  simpa only [coe_subtype] using Subtype.val_injective

/-- The inclusion of a subrepresentation is zero exactly when the subrepresentation is zero. -/
@[simp]
theorem subtype_eq_zero_iff (ρ' : Subrepresentation ρ) : ρ'.subtype = 0 ↔ ρ' = ⊥ := by
  rw [Representation.IntertwiningMap.eq_zero_iff_range_eq_bot, range_subtype]

/-- The inclusion of a subrepresentation is surjective exactly when the subrepresentation is the
whole representation. -/
theorem subtype_surjective_iff (ρ' : Subrepresentation ρ) :
    Function.Surjective ρ'.subtype ↔ ρ' = ⊤ := by
  rw [Representation.IntertwiningMap.surjective_iff_range_eq_top, range_subtype]

/-- The group-algebra action on a subrepresentation, coerced to the ambient module, is the
original group-algebra action. -/
@[simp]
theorem coe_toRepresentation_asAlgebraHom_apply {k H V : Type*} [CommSemiring k] [Monoid H]
    [AddCommMonoid V] [Module k V] {σ : Representation k H V} (S : Subrepresentation σ)
    (a : MonoidAlgebra k H) (x : S.toSubmodule) :
    ((S.toRepresentation.asAlgebraHom a x : S.toSubmodule) : V) =
      σ.asAlgebraHom a (x : V) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
        congrArg₂ (fun u v => u + v) ha hb
  | single g r =>
      simp only [Representation.asAlgebraHom_single]
      congr 1

section AsSubmoduleEquiv

open scoped MonoidAlgebra

variable {A G W : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- **The module carried by a subrepresentation is canonically its associated submodule.**
The equivalence identifies both with the same invariant subset of the ambient representation. -/
noncomputable def asModuleEquivAsSubmodule (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule ≃ₗ[A[G]] σ.asSubmodule where
  toFun x := ⟨(_root_.Representation.asModuleEquiv ρ).symm
      (σ.toRepresentation.asModuleEquiv x : W),
    (Subrepresentation.mem_asSubmodule_iff
      (v := (σ.toRepresentation.asModuleEquiv x : W))).mpr
        (σ.toRepresentation.asModuleEquiv x).2⟩
  invFun x := σ.toRepresentation.asModuleEquiv.symm
    ⟨_root_.Representation.asModuleEquiv ρ x.1,
      (Subrepresentation.mem_asSubmodule_iff
        (v := _root_.Representation.asModuleEquiv ρ x.1)).mp x.2⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' a x := by
    apply Subtype.ext
    apply (_root_.Representation.asModuleEquiv ρ).injective
    simp only [LinearEquiv.apply_symm_apply, RingHom.id_apply,
      _root_.Representation.asModuleEquiv_map_smul]
    exact coe_toRepresentation_asAlgebraHom_apply σ a
      (σ.toRepresentation.asModuleEquiv x)

@[simp]
theorem coe_asModuleEquivAsSubmodule_apply (σ : Subrepresentation ρ)
    (x : σ.toRepresentation.asModule) :
    _root_.Representation.asModuleEquiv ρ (σ.asModuleEquivAsSubmodule x).1 =
      (σ.toRepresentation.asModuleEquiv x).1 :=
  (rfl)

@[simp]
theorem coe_asModuleEquivAsSubmodule_symm_apply (σ : Subrepresentation ρ)
    (x : σ.asSubmodule) :
    (σ.toRepresentation.asModuleEquiv (σ.asModuleEquivAsSubmodule.symm x)).1 =
      _root_.Representation.asModuleEquiv ρ x.1 :=
  (rfl)

end AsSubmoduleEquiv

section AsSubmodule

open scoped MonoidAlgebra

variable {A G W : Type*} [CommRing A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

/-- A minimal subrepresentation is the same thing as a simple `A[G]`-submodule of the associated
module: the dictionary between the two ways of saying "irreducible constituent".  It is
`isSimpleModule_iff_isAtom` read across `Subrepresentation.subrepresentationSubmoduleOrderIso`. -/
@[simp]
theorem isSimpleModule_asSubmodule_iff {σ : Subrepresentation ρ} :
    IsSimpleModule A[G] σ.asSubmodule ↔ IsAtom σ :=
  isSimpleModule_iff_isAtom.trans (subrepresentationSubmoduleOrderIso.isAtom_iff σ)

end AsSubmodule

end Subrepresentation
