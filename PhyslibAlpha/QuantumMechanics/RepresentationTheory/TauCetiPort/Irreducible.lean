/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Rank
import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.RingTheory.Semisimple.DoubleCentralizer
import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.RingTheory.Semisimple.Schur

/-!
# Criteria for irreducibility

This file collects three ways of recognising an irreducible representation from outside, without
inspecting its subrepresentations one by one, and the finite-dimensional existence statement that
makes the second of them usable.

A representation on a one-dimensional vector space is irreducible, whatever the group and however
it acts: a subrepresentation is in particular a subspace, and a line has only the two trivial
subspaces.  Nontriviality, the other half of irreducibility, is the same dimension count.  This is
how the smallest representations of a group are recognised as irreducible without knowing anything
about the group -- the trivial representation, a character, a sign.

The second criterion turns a lattice-theoretic statement about a fixed ambient representation into
a statement about a subrepresentation on its own: a subrepresentation that is an **atom** of the
lattice of subrepresentations carries an irreducible representation.  Irreducibility of a
subrepresentation `σ` of `ρ` is a statement about the subrepresentations of `σ.toRepresentation`,
one level down from `ρ`, whereas minimality is a statement inside the lattice attached to `ρ`; the
translation between them is the correspondence sending a subrepresentation of `σ.toRepresentation`
to its image in `ρ` under the inclusion of `σ.toSubmodule`.  In practice the atom form is the one
that gets proved -- one exhibits an invariant subspace of the ambient representation and shows it
has no proper nonzero invariant subspace -- and the irreducibility form is the one that gets used.

At the other extreme, a representation whose algebra map exhausts `End k V` is irreducible, because
a vector space is a simple module over its own endomorphism ring, so a nonzero vector can be carried
to any other.  This is the criterion a matrix block of a semisimple group algebra is recognised as
irreducible by.

## Main results

* `TauCeti.Representation.IsIrreducible.nontrivial`: an irreducible representation has a nonzero
  carrier.
* `Representation.IsIrreducible.finrank_pos`: a finite-dimensional irreducible
  representation has positive dimension.
* `Representation.IsIrreducible.natCast_finrank_ne_zero`: in characteristic zero that
  dimension is nonzero, hence invertible, in the base field.
* `Representation.IsIrreducible.finiteDimensional`: an irreducible representation of a finite
  monoid is finite-dimensional.
* `TauCeti.Representation.isIrreducible_of_finrank_eq_one`: a line is irreducible.
* `TauCeti.Representation.isIrreducible_of_linearEquiv`: irreducibility transports along an
  equivariant linear equivalence.
* `TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom`: an atom of the lattice of
  subrepresentations carries an irreducible representation.
* `TauCeti.Representation.isIrreducible_of_asAlgebraHom_surjective`: a representation whose
  algebra map exhausts the endomorphisms is irreducible.
* `Representation.asAlgebraHom_surjective_of_isIrreducible`: over an algebraically closed
  field, every finite-dimensional irreducible representation exhausts the endomorphisms.
* `TauCeti.Representation.exists_isAtom_le`: every nonzero finite-dimensional subrepresentation
  contains an atom, so the atom criterion always has something to apply to.
* `TauCeti.Representation.exists_isAtom`: in particular a nonzero finite-dimensional
  representation has an atom.
* `TauCeti.Representation.exists_isIrreducible_subrepresentation`: consequently every nonzero
  finite-dimensional representation contains an irreducible subrepresentation.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles".
-/

public section

namespace TauCeti

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

open scoped MonoidAlgebra in
/-- **An irreducible representation has a nonzero carrier.** This is `IsSimpleModule.nontrivial`
for `ρ.asModule`, read back on `V` along `ρ.asModuleEquiv`; the Mathlib statement is not an
instance, so nothing supplies `Nontrivial V` without naming it. -/
theorem IsIrreducible.nontrivial {ρ : Representation k G V} (h : ρ.IsIrreducible) :
    Nontrivial V :=
  have _ : ρ.IsIrreducible := h
  have _ := IsSimpleModule.nontrivial k[G] ρ.asModule
  ρ.asModuleEquiv.symm.toEquiv.nontrivial

/-- **A finite-dimensional irreducible representation has positive dimension.** This is what makes
the degree of an irreducible character positive, and, cast into the base field by
`Representation.IsIrreducible.natCast_finrank_ne_zero`, what lets the orthogonality relations and
the integrated operator divide by that degree. -/
theorem _root_.Representation.IsIrreducible.finrank_pos [FiniteDimensional k V]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) : 0 < Module.finrank k V :=
  have := IsIrreducible.nontrivial h
  Module.finrank_pos

/-- **The dimension of an irreducible representation is nonzero in the base field.** In
characteristic zero it is therefore invertible there: this is the scalar the orthogonality
relations and the integrated operator of an irreducible representation are normalised by. -/
theorem _root_.Representation.IsIrreducible.natCast_finrank_ne_zero [CharZero k]
    [FiniteDimensional k V] {ρ : Representation k G V} (h : ρ.IsIrreducible) :
    (Module.finrank k V : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Representation.IsIrreducible.finrank_pos h).ne'

open scoped MonoidAlgebra in
/-- **An irreducible representation of a finite monoid is finite-dimensional.** A simple module is
cyclic -- it is generated by any one of its nonzero elements -- so `ρ.asModule` is a quotient of
`k[G]`, which is finite-dimensional over `k` when `G` is finite.  No finiteness has to be assumed
of `V`, which is what makes the hypothesis `[FiniteDimensional k V]` redundant on statements that
already assume irreducibility over a finite monoid. -/
theorem _root_.Representation.IsIrreducible.finiteDimensional [Finite G]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) : FiniteDimensional k V := by
  have _ : ρ.IsIrreducible := h
  have _ := IsSimpleModule.nontrivial k[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  have _ : Module.Finite k[G] ρ.asModule :=
    .of_surjective _ (IsSimpleModule.toSpanSingleton_surjective k[G] hv)
  have _ : Module.Finite k ρ.asModule := Module.Finite.trans k[G] ρ.asModule
  exact Module.Finite.equiv ρ.asModuleEquiv

/-- A representation on a one-dimensional vector space is irreducible. -/
theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V)
    (h : Module.finrank k V = 1) : ρ.IsIrreducible := by
  have hsimple : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k V) (by
      rw [← Subrepresentation.toSubmodule_bot (ρ := ρ), ← Subrepresentation.toSubmodule_top
        (ρ := ρ), hc])
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hne⟩
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_top.symm)

/-- The trivial representation of a monoid on the base field is irreducible, being a line. -/
instance isIrreducible_trivial_self : (_root_.Representation.trivial k G k).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- **Irreducibility transports along an equivariant linear equivalence.** A linear equivalence
intertwining two representations matches their lattices of subrepresentations, by taking preimages
of invariant subspaces, so one is irreducible exactly when the other is.

Only one direction is stated; the reverse is this one applied to `e.symm`. -/
theorem isIrreducible_of_linearEquiv {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  have _ : ρ.IsIrreducible := h
  have hV : Nontrivial V := IsIrreducible.nontrivial h
  have : Nontrivial W := e.symm.toEquiv.nontrivial
  have hne : (⊥ : Subrepresentation σ) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k W) (by
      rw [← Subrepresentation.toSubmodule_bot (ρ := σ), ← Subrepresentation.toSubmodule_top
        (ρ := σ), hc])
  have : Nontrivial (Subrepresentation σ) := ⟨⊥, ⊤, hne⟩
  refine ⟨fun τ => ?_⟩
  -- pull `τ` back along `e` to a subrepresentation of `ρ`
  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.comap (e : V →ₗ[k] W)
      apply_mem_toSubmodule g v hv := by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [he]
        exact τ.apply_mem_toSubmodule g hv }
  have hmap : (τ'.toSubmodule).map (e : V →ₗ[k] W) = τ.toSubmodule :=
    Submodule.map_comap_eq_of_surjective e.surjective _
  refine (eq_bot_or_eq_top τ').imp (fun hτ => ?_) fun hτ => ?_
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_bot, Submodule.map_bot,
      Subrepresentation.toSubmodule_bot]
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_top, Submodule.map_top, LinearEquiv.range,
      Subrepresentation.toSubmodule_top]

/-- A subrepresentation that is an **atom** of the lattice of subrepresentations -- nonzero, with
no subrepresentation strictly between it and zero -- carries an irreducible representation.  The
translation is the correspondence between the subrepresentations of `σ.toRepresentation` and the
subrepresentations of `ρ` contained in `σ`, given by pushing forward along the inclusion. -/
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (h : IsAtom σ) : σ.toRepresentation.IsIrreducible := by
  have hσ : σ.toSubmodule ≠ ⊥ := fun hc =>
    h.1 (Subrepresentation.toSubmodule_injective (hc.trans Subrepresentation.toSubmodule_bot.symm))
  have : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hσ
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k σ.toSubmodule) (by
      rw [← Subrepresentation.toSubmodule_bot (ρ := σ.toRepresentation),
        ← Subrepresentation.toSubmodule_top (ρ := σ.toRepresentation), hc])
  have : Nontrivial (Subrepresentation σ.toRepresentation) := ⟨⊥, ⊤, hne⟩
  refine ⟨fun τ => ?_⟩
  -- push `τ` forward to a subrepresentation of `ρ` contained in `σ`
  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.map σ.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩ }
  have hmap : τ'.toSubmodule = τ.toSubmodule.map σ.toSubmodule.subtype := rfl
  have hle : τ' ≤ σ := Submodule.map_subtype_le _ _
  rcases eq_or_ne τ' ⊥ with hτ | hτ
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊥ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_bot]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule hτ)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      Subrepresentation.toSubmodule_bot.symm
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    have heq : τ' = σ := by
      by_contra hne'
      exact hτ (h.2 _ (lt_of_le_of_ne hle hne'))
    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊤ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_subtype_top]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule heq)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      Subrepresentation.toSubmodule_top.symm

/-- **A representation whose algebra map exhausts the endomorphisms is irreducible.** Every nonzero
vector then generates, because a vector space is a simple module over its endomorphism ring. -/
theorem isIrreducible_of_asAlgebraHom_surjective [Nontrivial V] (ρ : Representation k G V)
    (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule,
    isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨ρ.asModuleEquiv.toEquiv.nontrivial, fun x hx y => ?_⟩
  obtain ⟨T, hT⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End k V)
    (m := ρ.asModuleEquiv x) (by simpa using hx) (ρ.asModuleEquiv y)
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hT
  obtain ⟨r, rfl⟩ := h T
  refine ⟨r, ρ.asModuleEquiv.injective ?_⟩
  rw [LinearMap.toSpanSingleton_apply, _root_.Representation.asModuleEquiv_map_smul, hT]

open scoped MonoidAlgebra in
/-- **Burnside density theorem.** The monoid algebra of a finite-dimensional irreducible
representation over an algebraically closed field exhausts the full endomorphism algebra.

Jacobson density gives all endomorphisms linear over the representation's commuting endomorphism
ring. Schur's lemma identifies that ring with the base field, so these are exactly the
`k`-linear endomorphisms. -/
theorem _root_.Representation.asAlgebraHom_surjective_of_isIrreducible
    [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ρ.IsIrreducible) :
    Function.Surjective ρ.asAlgebraHom := by
  have : ρ.IsIrreducible := hρ
  have : IsSimpleModule k[G] ρ.asModule := inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  have : Nontrivial V := IsIrreducible.nontrivial hρ
  have : Module.Finite (Module.End k[G] ρ.asModule) ρ.asModule :=
    finite_end_of_smulCommClass (R := k[G]) (M := ρ.asModule) k
  intro T
  let T' : Module.End (Module.End k[G] ρ.asModule) ρ.asModule :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x ↦ by
        -- `T` acts on `V`, while `f` acts on the definitionally equal type synonym
        -- `ρ.asModule`; exposing function application is required before Schur's scalar
        -- description is type-correct.
        change T (f x) = f (T x)
        rw [← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f x,
          ← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f (T x)]
        exact T.map_smul _ _ }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := k[G]) (M := ρ.asModule) T'
  refine ⟨a, LinearMap.ext fun x ↦ ?_⟩
  have hT' (y : ρ.asModule) : T' y = T y := rfl
  have hx := LinearMap.congr_fun ha (ρ.asModuleEquiv.symm x)
  rw [hT'] at hx
  have hx' := congrArg ρ.asModuleEquiv hx
  have hT_equiv : ρ.asModuleEquiv (T (ρ.asModuleEquiv.symm x)) = T x := rfl
  rw [hT_equiv] at hx'
  simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply,
    _root_.Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using hx'

/-! ### Atoms exist in finite dimensions -/

/-- **Atoms exist.** Every nonzero finite-dimensional subrepresentation contains an atom of the
lattice of subrepresentations.

Finite-dimensionality is what makes a minimal nonzero subrepresentation exist, and only the
subrepresentation being minimised inside has to be finite-dimensional: the ambient representation
may be infinite-dimensional, and the acting monoid stays arbitrary.  Combined with
`TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom` it exhibits an irreducible
subrepresentation inside any nonzero one. -/
theorem exists_isAtom_le {ρ : Representation k G V} {σ : Subrepresentation ρ}
    [FiniteDimensional k σ.toSubmodule] (hσ : σ ≠ ⊥) :
    ∃ τ : Subrepresentation ρ, τ ≤ σ ∧ IsAtom τ := by
  -- Among the nonzero subrepresentations contained in `σ`, pick one whose subspace has least
  -- dimension; the dimensions are natural numbers, so such a one exists.
  obtain ⟨τ, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT (fun τ : Subrepresentation ρ => τ ≠ ⊥ ∧ τ ≤ σ)
      (fun τ => Module.finrank k τ.toSubmodule) ⟨σ, hσ, le_rfl⟩
  obtain ⟨hτ, hτσ⟩ := hmin.1
  have : FiniteDimensional k τ.toSubmodule :=
    Submodule.finiteDimensional_of_le (Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ)
  -- Anything strictly inside `τ` is again inside `σ` and of strictly smaller dimension, so
  -- minimality forces it to be zero.
  refine ⟨τ, hτσ, hτ, fun υ hυ => ?_⟩
  by_contra hυ0
  exact hmin.not_prop_of_lt
    (Submodule.finrank_lt_finrank_of_lt (Subrepresentation.toSubmodule_lt_toSubmodule.mpr hυ))
    ⟨hυ0, hυ.le.trans hτσ⟩

/-- **A nonzero finite-dimensional representation has a minimal nonzero subrepresentation.**  This
is `TauCeti.Representation.exists_isAtom_le` applied to the whole space, which is nonzero exactly
because `V` is; the acting monoid stays arbitrary. -/
theorem exists_isAtom [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, IsAtom σ := by
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := fun hc =>
    top_ne_bot (α := Submodule k V) (by
      rw [← Subrepresentation.toSubmodule_top (ρ := ρ), ← Subrepresentation.toSubmodule_bot
        (ρ := ρ), hc])
  obtain ⟨σ, -, hσ⟩ := exists_isAtom_le htop
  exact ⟨σ, hσ⟩

/-- **Every nonzero finite-dimensional representation contains an irreducible subrepresentation.**
Finite-dimensionality alone suffices; no semisimplicity is assumed.  This produces a single
irreducible subrepresentation, not a decomposition: a representation that is not semisimple need
not be the sum of its irreducible subrepresentations. -/
theorem exists_isIrreducible_subrepresentation [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, σ ≠ ⊥ ∧ σ.toRepresentation.IsIrreducible := by
  obtain ⟨σ, hσ⟩ := exists_isAtom ρ
  exact ⟨σ, hσ.1, isIrreducible_toRepresentation_of_isAtom hσ⟩

end Representation

end TauCeti
