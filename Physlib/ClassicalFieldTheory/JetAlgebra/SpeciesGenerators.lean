/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.JetAlgebra.JetComponentSpace.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.LocalFieldAlgebra
public import Mathlib.Algebra.DirectSum.Module
/-!
# The generator spaces of a family of species

## i. Overview

A field theory carries several species of field, each with its own value space, its own
Lorentz representation and its own mass weight. The local field algebra of
`Physlib.ClassicalFieldTheory.JetAlgebra.LocalFieldAlgebra` takes one complex space of
fermionic generators and one of bosonic generators, so a multi-species theory has to
present its species as a single generator space.

This file does that with a direct sum of component spaces. For a family `V : ι → Type` of
value spaces the total generator space is

`SpeciesComponentSpace V = ⨁ i, JetComponentSpace (V i)`,

one `JetComponentSpace` per species, each with its conjugate summand. The alternative, a
single `JetComponentSpace (∀ i, V i)` on the product of the value spaces, is available but
carries only one mass weight, since its scaling commutes with `JetComponentSpace.comap`
and so cannot distinguish the species. The direct sum records one weight per species.

Nothing here is finite. Neither the index type `ι` nor any of the value spaces `V i` is
assumed finite, and the component spaces are infinite-dimensional in any case, since a
derivative label ranges over all multisets of directions. Only `DecidableEq ι` is used,
and only to have the summand inclusions.

The subtle point is Fermi statistics. `LocalFieldAlgebra.Assignment` asks for
`fermion v * fermion v = 0` on the whole fermionic generator space, and imposing it on
each species separately is strictly weaker. By `DirectSum.mul_self_iff_lof`, square-zero
on the total space is equivalent to square-zero on each species together with
anticommutation between the images of any two species. So a species assignment must carry
the cross-species anticommutation as data, and `SpeciesAssignment.fermion_mul_swap` is
that field.

## ii. Key results

- `DirectSum.mul_self_iff_lof` : square-zero on a direct sum is square-zero on each
  summand plus anticommutation across summands.
- `SpeciesComponentSpace` : the total component space of a family of species.
- `SpeciesComponentSpace.incl`, `SpeciesComponentSpace.assemble`,
  `SpeciesComponentSpace.hom_ext`, `SpeciesComponentSpace.existsUnique_linearMap` : the
  species inclusions and the mapping-out property of the total component space.
- `SpeciesComponentSpace.comap` : functoriality, contravariant in the family of value
  spaces.
- `SpeciesComponentSpace.rep` : the species-diagonal assembly of a family of
  representations on the individual component spaces.
- `SpeciesComponentSpace.massWeightScale` : the mass-weight scaling of a family with one
  weight per species.
- `JetComponentSpace.comap_comp_massWeightScale` : the scaling of a single component
  space is natural in the value space, hence species-blind, which is the reason for the
  direct sum.
- `SpeciesLocalFieldAlgebra` : the local field algebra of a family of fermionic and a
  family of bosonic species.
- `SpeciesLocalFieldAlgebra.ιFermionSpecies_mul_swap` : the generators of two different
  fermionic species anticommute.
- `SpeciesAssignment`, `SpeciesAssignment.lift`,
  `SpeciesAssignment.existsUnique_algHom` : the universal property in species form.

## iii. Table of contents

- A. Maps out of a direct sum into a ring
  - A.1. Commutation
  - A.2. Anticommutation and the square-zero condition
- B. The component space of a family of species
  - B.1. The species inclusions and the assembly of linear maps
  - B.2. Functoriality in the family of value spaces
  - B.3. The species-diagonal representation
  - B.4. Unequal mass weights
  - B.5. Why the weights are recorded per species
- C. The local field algebra of a family of species
  - C.1. The species generators
  - C.2. Cross-species statistics
- D. Species assignments and the universal property
  - D.1. The assembled assignment
  - D.2. The induced algebra homomorphism and its computation rules
  - D.3. Uniqueness

-/

@[expose] public section

open TensorProduct DirectSum

/-!

## A. Maps out of a direct sum into a ring

A linear map out of a direct sum is determined by its restrictions to the summands, so a
relation between the images of two such maps which is stable under addition in each
argument need only be checked on the summands. The lemmas below are the instances of that
principle used later, and carry no physics.

-/

namespace DirectSum

section OfLof

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  {N : κ → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
  {B : Type*} [Ring B] [Algebra ℂ B]

/-!

### A.1. Commutation

-/

/-- If the image of every summand commutes with a fixed element, so does the whole
  image. -/
lemma commute_of_lof_left {F : (⨁ i, M i) →ₗ[ℂ] B} {b : B}
    (h : ∀ i x, Commute (F (lof ℂ ι M i x)) b) (v : ⨁ i, M i) : Commute (F v) b := by
  induction v using DirectSum.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left b
  | of i x => exact h i x
  | add v w hv hw => rw [map_add]; exact hv.add_left hw

/-- Commutation extends from the summands. If the image of every summand of one direct
  sum commutes with the image of every summand of another, then the two images commute
  elementwise. -/
lemma commute_of_lof {F : (⨁ i, M i) →ₗ[ℂ] B} {G : (⨁ j, N j) →ₗ[ℂ] B}
    (h : ∀ i j x y, Commute (F (lof ℂ ι M i x)) (G (lof ℂ κ N j y)))
    (v : ⨁ i, M i) (w : ⨁ j, N j) : Commute (F v) (G w) :=
  commute_of_lof_left (fun i x =>
    (commute_of_lof_left (fun j y => (h i j x y).symm) w).symm) v

/-!

### A.2. Anticommutation and the square-zero condition

-/

/-- Anticommutation extends from the summands. -/
lemma mul_swap_of_lof {F : (⨁ i, M i) →ₗ[ℂ] B}
    (h : ∀ i j x y, F (lof ℂ ι M i x) * F (lof ℂ ι M j y)
      = -(F (lof ℂ ι M j y) * F (lof ℂ ι M i x)))
    (v w : ⨁ i, M i) : F v * F w = -(F w * F v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction w using DirectSum.induction_on with
    | zero => simp
    | of j y => exact h i j x y
    | add w₁ w₂ h₁ h₂ => rw [map_add, mul_add, add_mul, h₁, h₂, neg_add]
  | add v₁ v₂ h₁ h₂ => rw [map_add, add_mul, mul_add, h₁, h₂, neg_add]

/-- Square-zero extends from the summands, given anticommutation across them. The
  cross terms of `(x + y) * (x + y)` cancel exactly because the two images anticommute;
  square-zero on each summand alone would leave them. -/
lemma mul_self_of_lof {F : (⨁ i, M i) →ₗ[ℂ] B}
    (hsq : ∀ i x, F (lof ℂ ι M i x) * F (lof ℂ ι M i x) = 0)
    (hswap : ∀ i j x y, F (lof ℂ ι M i x) * F (lof ℂ ι M j y)
      = -(F (lof ℂ ι M j y) * F (lof ℂ ι M i x)))
    (v : ⨁ i, M i) : F v * F v = 0 := by
  have key := mul_swap_of_lof hswap
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x => exact hsq i x
  | add v w hv hw =>
    have h : F (v + w) * F (v + w)
        = F v * F v + (F v * F w + F w * F v) + F w * F w := by
      rw [map_add]; noncomm_ring
    rw [h, hv, hw, key v w]
    abel

/-- Square-zero on a direct sum is not square-zero summand by summand. It is equivalent to
  square-zero on each summand together with anticommutation between the images of any two
  summands, the second condition being vacuous only when there is at most one summand.
  This is the precise sense in which Fermi statistics for a family of species is more than
  the Fermi statistics of the individual species. -/
lemma mul_self_iff_lof {F : (⨁ i, M i) →ₗ[ℂ] B} :
    (∀ v, F v * F v = 0) ↔
      ((∀ i x, F (lof ℂ ι M i x) * F (lof ℂ ι M i x) = 0) ∧
        ∀ i j x y, F (lof ℂ ι M i x) * F (lof ℂ ι M j y)
          = -(F (lof ℂ ι M j y) * F (lof ℂ ι M i x))) :=
  ⟨fun h => ⟨fun _ _ => h _, fun _ _ _ _ => F.mul_swap_of_mul_self h _ _⟩,
    fun h v => mul_self_of_lof h.1 h.2 v⟩

end OfLof

end DirectSum

/-!

## B. The component space of a family of species

-/

section ComponentSpace

variable {ι : Type*} [DecidableEq ι] (V : ι → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The component space of a family of species, with one `JetComponentSpace` per species,
  each carrying its own conjugate summand, combined by a direct sum. A component function
  of the theory is a finitely supported family of component functions of the species. -/
abbrev SpeciesComponentSpace : Type _ := ⨁ i, JetComponentSpace (V i)

namespace SpeciesComponentSpace

/-!

### B.1. The species inclusions and the assembly of linear maps

-/

/-- The inclusion of a species into the total component space. -/
abbrev incl (i : ι) : JetComponentSpace (V i) →ₗ[ℂ] SpeciesComponentSpace V :=
  DirectSum.lof ℂ ι (fun i => JetComponentSpace (V i)) i

variable {N : Type*} [AddCommMonoid N] [Module ℂ N]

/-- The assembly of a species-wise family of linear maps into a common target. -/
abbrev assemble (f : ∀ i, JetComponentSpace (V i) →ₗ[ℂ] N) :
    SpeciesComponentSpace V →ₗ[ℂ] N :=
  DirectSum.toModule ℂ ι N f

variable {V}

@[simp]
lemma assemble_incl (f : ∀ i, JetComponentSpace (V i) →ₗ[ℂ] N) (i : ι)
    (x : JetComponentSpace (V i)) : assemble V f (incl V i x) = f i x :=
  DirectSum.toModule_lof (M := fun i => JetComponentSpace (V i)) ℂ i x

/-- Two linear maps out of the total component space agreeing on every species are
  equal. -/
lemma hom_ext {F G : SpeciesComponentSpace V →ₗ[ℂ] N}
    (h : ∀ i x, F (incl V i x) = G (incl V i x)) : F = G :=
  DirectSum.linearMap_ext ℂ fun i => LinearMap.ext (h i)

variable (V)

/-- The mapping-out property of the total component space. A species-wise family of linear
  maps into a common target extends to one and only one linear map out of the total
  component space. -/
lemma existsUnique_linearMap (f : ∀ i, JetComponentSpace (V i) →ₗ[ℂ] N) :
    ∃! F : SpeciesComponentSpace V →ₗ[ℂ] N, ∀ i x, F (incl V i x) = f i x :=
  ⟨assemble V f, assemble_incl f, fun _ hF =>
    hom_ext fun i x => (hF i x).trans (assemble_incl f i x).symm⟩

/-!

### B.2. Functoriality in the family of value spaces

Component functions are covectors on the value space, so the total component space is
contravariant in the family of value spaces, exactly as a single one is. The species-wise
pullbacks are the existing `JetComponentSpace.comap`; only the assembly is new.

-/

variable (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The total component space is contravariant in the family of value spaces. Applied
  to the projections out of a larger family, this is the inclusion of a subfamily of
  species. -/
noncomputable def comap (f : ∀ i, V i →ₗ[ℂ] W i) :
    SpeciesComponentSpace W →ₗ[ℂ] SpeciesComponentSpace V :=
  assemble W fun i => (incl V i).comp (JetComponentSpace.comap (f i))

variable {V W}

@[simp]
lemma comap_incl (f : ∀ i, V i →ₗ[ℂ] W i) (i : ι) (x : JetComponentSpace (W i)) :
    comap V W f (incl W i x) = incl V i (JetComponentSpace.comap (f i) x) :=
  assemble_incl _ i x

@[simp]
lemma comap_id : comap V V (fun _ => LinearMap.id) = LinearMap.id :=
  hom_ext fun i x => by
    rw [comap_incl, JetComponentSpace.comap_id, LinearMap.id_apply, LinearMap.id_apply]

/-- Functoriality, with the order reversing as a contravariant construction demands. -/
lemma comap_comp (U : ι → Type*) [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
    (f : ∀ i, V i →ₗ[ℂ] W i) (g : ∀ i, W i →ₗ[ℂ] U i) :
    comap V U (fun i => (g i).comp (f i)) = (comap V W f).comp (comap W U g) :=
  hom_ext fun i x => by
    rw [comap_incl, JetComponentSpace.comap_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, comap_incl, comap_incl]

/-!

### B.3. The species-diagonal representation

A symmetry of a field theory acts on each species separately, a Lorentz transformation
through that species' Lorentz representation and a gauge jet through that species' jet
action. On the total component space the action is therefore the direct sum of the
species-wise actions, and the representation laws follow from the mapping-out property of
the direct sum alone, with no relation between the species used.

-/

variable (V)

/-- The species-diagonal representation on the total component space assembled from a
  representation on each species' component space. The summands are preserved, so `map_one`
  and `map_mul` reduce by `hom_ext` to the corresponding laws of the species-wise
  representations.

  Both transformation laws a matter species carries are of this form, namely the Lorentz
  action `JetComponentSpace.repLorentzGroup` and the jet gauge action
  `JetComponentSpace.repJet`. Nothing here asks the two to commute, and nothing asks the
  monoid `H` to be related to the species. -/
noncomputable def rep {H : Type*} [Monoid H]
    (ρ : ∀ i, Representation ℂ H (JetComponentSpace (V i))) :
    Representation ℂ H (SpeciesComponentSpace V) where
  toFun g := assemble V fun i => (incl V i).comp (ρ i g)
  map_one' := hom_ext fun i x => by simp
  map_mul' g h := hom_ext fun i x => by simp

variable {V}

/-- The species-diagonal representation acts on the summand of a species through that
  species' representation. -/
@[simp]
lemma rep_incl {H : Type*} [Monoid H] (ρ : ∀ i, Representation ℂ H (JetComponentSpace (V i)))
    (g : H) (i : ι) (x : JetComponentSpace (V i)) :
    rep V ρ g (incl V i x) = incl V i (ρ i g x) :=
  assemble_incl _ i x

/-!

### B.4. Unequal mass weights

The mass weight is a property of a species, not of the theory, a fermion carrying weight
`3` and a scalar weight `2`. The total component space records one weight per species,
and the scaling acts on the summand of a species through that species' weight alone.

-/

variable (V)

/-- The mass-weight scaling of a family of species, with the weight `w i` of each
  species acting on that species' component functions. -/
noncomputable def massWeightScale (w : ι → ℕ) (c : ℂ) :
    SpeciesComponentSpace V →ₗ[ℂ] SpeciesComponentSpace V :=
  assemble V fun i => (incl V i).comp (JetComponentSpace.massWeightScale (w i) c)

variable {V}

@[simp]
lemma massWeightScale_incl (w : ι → ℕ) (c : ℂ) (i : ι) (x : JetComponentSpace (V i)) :
    massWeightScale V w c (incl V i x)
      = incl V i (JetComponentSpace.massWeightScale (w i) c x) :=
  assemble_incl _ i x

/-- On a homogeneous component function `∂_s φ_α` of the species `i` the scaling is
  multiplication by `c ^ (w i + 2 |s|)`, the weight being the weight of that species. -/
lemma massWeightScale_incl_basis_tmul (w : ι → ℕ) (c : ℂ) (i : ι)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (V i)) :
    massWeightScale V w c
        (incl V i ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (V i)))
      = c ^ (w i + 2 * Multiset.card s) •
        incl V i ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (V i)) := by
  rw [massWeightScale_incl, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · exact JetComponentSpace.massWeightScale_fst_basis_tmul (w i) c s φ 0
  · simp

/-- The conjugate component functions of a species scale with the same weight as its
  unconjugated ones. -/
lemma massWeightScale_incl_basis_tmul_conj (w : ι → ℕ) (c : ℂ) (i : ι)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (V i))) :
    massWeightScale V w c
        (incl V i ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (V i)))
      = c ^ (w i + 2 * Multiset.card s) •
        incl V i ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (V i)) := by
  rw [massWeightScale_incl, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · simp
  · simp only [JetComponentSpace.massWeightScale_snd, Prod.smul_snd,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      DerivAlgebraComplex.gradeScale_basis, LinearMap.id_apply, TensorProduct.smul_tmul',
      ← pow_mul, ← smul_assoc, smul_eq_mul, ← pow_add, mul_comm 2 (Multiset.card s)]

end SpeciesComponentSpace

end ComponentSpace

/-!

### B.5. Why the weights are recorded per species

-/

/-- The mass-weight scaling of a single component space is natural in the value space. It
  therefore cannot see which species a component function came from, so in the alternative
  encoding `JetComponentSpace (∀ i, V i)`, where a species enters through
  `JetComponentSpace.comap (LinearMap.proj i)`, every species is scaled by the same weight.
  That is why the total generator space of this file is a direct sum, with one weight per
  summand.

  The statement is about a single `JetComponentSpace` and would sit more naturally with the
  rest of that API in `Physlib.ClassicalFieldTheory.JetAlgebra.JetComponentSpace.Basic`; it
  is here because it justifies the choice this file makes. -/
lemma JetComponentSpace.comap_comp_massWeightScale {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (w : ℕ) (c : ℂ) :
    (JetComponentSpace.comap f).comp (JetComponentSpace.massWeightScale w c)
      = (JetComponentSpace.massWeightScale w c).comp (JetComponentSpace.comap f) := by
  simp only [JetComponentSpace.comap, JetComponentSpace.massWeightScale,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.prodMap_comp,
    ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

/-!

## C. The local field algebra of a family of species

-/

section SpeciesAlgebra

variable {ιf ιb : Type*} [DecidableEq ιf] [DecidableEq ιb]
  (Vf : ιf → Type*) [∀ i, AddCommGroup (Vf i)] [∀ i, Module ℂ (Vf i)]
  (Vb : ιb → Type*) [∀ j, AddCommGroup (Vb j)] [∀ j, Module ℂ (Vb j)]
  (EA : Type*) [AddCommGroup EA] [Module ℝ EA]

/-- The local field algebra of a family of species. Its fermionic generators are the
  component functions of a family of fermionic species, its bosonic generators those of a
  family of bosonic species, and its connection generator space is left abstract. All the
  fermionic species share one exterior algebra, so their generators anticommute across
  species and not merely within one. -/
abbrev SpeciesLocalFieldAlgebra : Type _ :=
  LocalFieldAlgebra (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA

namespace SpeciesLocalFieldAlgebra

open LocalFieldAlgebra

/-!

### C.1. The species generators

-/

/-- The fermionic generators contributed by one species. -/
noncomputable def ιFermionSpecies (i : ιf) :
    JetComponentSpace (Vf i) →ₗ[ℂ] SpeciesLocalFieldAlgebra Vf Vb EA :=
  (ιFermion (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA).comp
    (SpeciesComponentSpace.incl Vf i)

/-- The bosonic generators contributed by one species. -/
noncomputable def ιBosonSpecies (j : ιb) :
    JetComponentSpace (Vb j) →ₗ[ℂ] SpeciesLocalFieldAlgebra Vf Vb EA :=
  (ιBoson (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA).comp
    (SpeciesComponentSpace.incl Vb j)

variable {Vf Vb EA}

omit [DecidableEq ιb] in
lemma ιFermionSpecies_apply (i : ιf) (x : JetComponentSpace (Vf i)) :
    ιFermionSpecies Vf Vb EA i x
      = ιFermion (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA
          (SpeciesComponentSpace.incl Vf i x) := rfl

omit [DecidableEq ιf] in
lemma ιBosonSpecies_apply (j : ιb) (y : JetComponentSpace (Vb j)) :
    ιBosonSpecies Vf Vb EA j y
      = ιBoson (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA
          (SpeciesComponentSpace.incl Vb j y) := rfl

/-!

### C.2. Cross-species statistics

The five relations of `LocalFieldAlgebra`, read one species at a time. Each is the
corresponding relation of the total generator space evaluated at the images of the species
inclusions, so none is new mathematical content; what they record is that the inclusions
do not disturb the statistics.

-/

omit [DecidableEq ιb] in
/-- A fermionic generator squares to zero. -/
@[simp]
lemma ιFermionSpecies_mul_self (i : ιf) (x : JetComponentSpace (Vf i)) :
    ιFermionSpecies Vf Vb EA i x * ιFermionSpecies Vf Vb EA i x = 0 :=
  ιFermion_mul_self (Ef := SpeciesComponentSpace Vf) (Eb := SpeciesComponentSpace Vb)
    (EA := EA) (SpeciesComponentSpace.incl Vf i x)

omit [DecidableEq ιb] in
/-- Fermionic generators of two different species anticommute. The two species enter
  the same exterior algebra through different summands of the total component space, so
  this is the ordinary exterior anticommutation, not an extra relation; it is what
  separate exterior algebras joined by an ordinary tensor product would lose. -/
lemma ιFermionSpecies_mul_swap (i j : ιf) (x : JetComponentSpace (Vf i))
    (y : JetComponentSpace (Vf j)) :
    ιFermionSpecies Vf Vb EA i x * ιFermionSpecies Vf Vb EA j y
      = -(ιFermionSpecies Vf Vb EA j y * ιFermionSpecies Vf Vb EA i x) :=
  ιFermion_mul_swap (Ef := SpeciesComponentSpace Vf) (Eb := SpeciesComponentSpace Vb)
    (EA := EA) (SpeciesComponentSpace.incl Vf i x) (SpeciesComponentSpace.incl Vf j y)

omit [DecidableEq ιf] in
/-- Bosonic generators commute, across species as well as within one. -/
lemma ιBosonSpecies_commute (i j : ιb) (x : JetComponentSpace (Vb i))
    (y : JetComponentSpace (Vb j)) :
    Commute (ιBosonSpecies Vf Vb EA i x) (ιBosonSpecies Vf Vb EA j y) :=
  ιBoson_commute (Ef := SpeciesComponentSpace Vf) (Eb := SpeciesComponentSpace Vb)
    (EA := EA) (SpeciesComponentSpace.incl Vb i x) (SpeciesComponentSpace.incl Vb j y)

/-- A bosonic generator commutes with a fermionic one, bosons being even. -/
lemma ιBosonSpecies_commute_ιFermionSpecies (j : ιb) (i : ιf)
    (y : JetComponentSpace (Vb j)) (x : JetComponentSpace (Vf i)) :
    Commute (ιBosonSpecies Vf Vb EA j y) (ιFermionSpecies Vf Vb EA i x) :=
  ιBoson_commute_ιFermion (Ef := SpeciesComponentSpace Vf) (Eb := SpeciesComponentSpace Vb)
    (EA := EA) (SpeciesComponentSpace.incl Vb j y) (SpeciesComponentSpace.incl Vf i x)

omit [DecidableEq ιf] in
/-- A bosonic generator commutes with a connection generator. -/
lemma ιBosonSpecies_commute_ιConnection (j : ιb) (y : JetComponentSpace (Vb j)) (v : EA) :
    Commute (ιBosonSpecies Vf Vb EA j y)
      (ιConnection (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA v) :=
  ιBoson_commute_ιConnection (Ef := SpeciesComponentSpace Vf)
    (Eb := SpeciesComponentSpace Vb) (EA := EA) (SpeciesComponentSpace.incl Vb j y) v

omit [DecidableEq ιb] in
/-- A connection generator commutes with a fermionic one, the connection being even. -/
lemma ιConnection_commute_ιFermionSpecies (v : EA) (i : ιf)
    (x : JetComponentSpace (Vf i)) :
    Commute (ιConnection (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA v)
      (ιFermionSpecies Vf Vb EA i x) :=
  ιConnection_commute_ιFermion (Ef := SpeciesComponentSpace Vf)
    (Eb := SpeciesComponentSpace Vb) (EA := EA) v (SpeciesComponentSpace.incl Vf i x)

end SpeciesLocalFieldAlgebra

/-!

## D. Species assignments and the universal property

-/

open SpeciesLocalFieldAlgebra in
/-- A compatible assignment for a family of species in a complex algebra `B`, which is not
  assumed commutative. It consists of one linear map per fermionic species, one per
  bosonic species, and one real-linear map on the connection generator space, subject to
  the relations of section C.2 read species by species.

  `fermion_mul_swap` is not redundant. `LocalFieldAlgebra.Assignment` demands
  `fermion v * fermion v = 0` on the whole fermionic generator space, and by
  `DirectSum.mul_self_iff_lof` that condition is equivalent to `fermion_mul_self` together
  with `fermion_mul_swap`, since species-wise square-zero alone leaves the cross terms of
  `(x + y) * (x + y)` for `x` and `y` in different species. -/
structure SpeciesAssignment (B : Type*) [Ring B] [Algebra ℂ B] where
  /-- The images of the generators of each fermionic species. -/
  fermion : ∀ i, JetComponentSpace (Vf i) →ₗ[ℂ] B
  /-- The images of the generators of each bosonic species. -/
  boson : ∀ j, JetComponentSpace (Vb j) →ₗ[ℂ] B
  /-- The images of the connection generators; only real-linear. -/
  connection : EA →ₗ[ℝ] B
  /-- Fermi statistics within a species. -/
  fermion_mul_self : ∀ i x, fermion i x * fermion i x = 0
  /-- Fermi statistics across species, which does not follow from `fermion_mul_self`. -/
  fermion_mul_swap : ∀ i j x y, fermion i x * fermion j y = -(fermion j y * fermion i x)
  /-- Bosonic images commute, across species as well as within one. -/
  boson_commute : ∀ i j x y, Commute (boson i x) (boson j y)
  /-- Connection images commute pairwise. -/
  connection_commute : ∀ v w, Commute (connection v) (connection w)
  /-- Bosonic and connection images commute with each other. -/
  boson_commute_connection : ∀ j y w, Commute (boson j y) (connection w)
  /-- Bosonic images commute with fermionic images. -/
  boson_commute_fermion : ∀ j i y x, Commute (boson j y) (fermion i x)
  /-- Connection images commute with fermionic images. -/
  connection_commute_fermion : ∀ v i x, Commute (connection v) (fermion i x)

namespace SpeciesAssignment

open SpeciesLocalFieldAlgebra

variable {Vf Vb EA}
variable {B : Type*} [Ring B] [Algebra ℂ B]

/-!

### D.1. The assembled assignment

-/

/-- Species-wise square-zero is not square-zero. The condition
  `LocalFieldAlgebra.Assignment` imposes on the assembled fermionic map is equivalent to
  the two fields `fermion_mul_self` and `fermion_mul_swap` of `SpeciesAssignment`
  together; the second is vacuous only for a family with at most one species. -/
lemma assemble_mul_self_iff (f : ∀ i, JetComponentSpace (Vf i) →ₗ[ℂ] B) :
    (∀ v, SpeciesComponentSpace.assemble Vf f v * SpeciesComponentSpace.assemble Vf f v = 0)
      ↔ ((∀ i x, f i x * f i x = 0) ∧
        ∀ i j x y, f i x * f j y = -(f j y * f i x)) := by
  rw [DirectSum.mul_self_iff_lof]
  simp

variable (d : SpeciesAssignment Vf Vb EA B)

/-- The compatible assignment assembled from a species assignment. Each of the five
  relations of `LocalFieldAlgebra.Assignment` is quantified over the whole generator
  space; each is obtained from its species-wise form by the extension lemmas of section
  A. -/
def toAssignment : LocalFieldAlgebra.Assignment
    (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA B where
  fermion := SpeciesComponentSpace.assemble Vf d.fermion
  boson := SpeciesComponentSpace.assemble Vb d.boson
  connection := d.connection
  fermion_mul_self :=
    (assemble_mul_self_iff d.fermion).2 ⟨d.fermion_mul_self, d.fermion_mul_swap⟩
  boson_commute := DirectSum.commute_of_lof fun i j x y => by
    simpa using d.boson_commute i j x y
  connection_commute := d.connection_commute
  boson_commute_connection := fun v w =>
    DirectSum.commute_of_lof_left (fun j y => by
      simpa using d.boson_commute_connection j y w) v
  boson_commute_fermion := DirectSum.commute_of_lof fun j i y x => by
    simpa using d.boson_commute_fermion j i y x
  connection_commute_fermion := fun v w =>
    (DirectSum.commute_of_lof_left (fun i x => by
      simpa using (d.connection_commute_fermion v i x).symm) w).symm

@[simp]
lemma toAssignment_fermion :
    d.toAssignment.fermion = SpeciesComponentSpace.assemble Vf d.fermion := rfl

@[simp]
lemma toAssignment_boson :
    d.toAssignment.boson = SpeciesComponentSpace.assemble Vb d.boson := rfl

@[simp]
lemma toAssignment_connection : d.toAssignment.connection = d.connection := rfl

/-!

### D.2. The induced algebra homomorphism and its computation rules

-/

/-- The algebra homomorphism induced by a species assignment. -/
noncomputable def lift : SpeciesLocalFieldAlgebra Vf Vb EA →ₐ[ℂ] B :=
  d.toAssignment.lift

@[simp]
lemma lift_ιFermionSpecies (i : ιf) (x : JetComponentSpace (Vf i)) :
    d.lift (ιFermionSpecies Vf Vb EA i x) = d.fermion i x := by
  rw [lift, ιFermionSpecies_apply, LocalFieldAlgebra.Assignment.lift_ιFermion,
    toAssignment_fermion, SpeciesComponentSpace.assemble_incl]

@[simp]
lemma lift_ιBosonSpecies (j : ιb) (y : JetComponentSpace (Vb j)) :
    d.lift (ιBosonSpecies Vf Vb EA j y) = d.boson j y := by
  rw [lift, ιBosonSpecies_apply, LocalFieldAlgebra.Assignment.lift_ιBoson,
    toAssignment_boson, SpeciesComponentSpace.assemble_incl]

@[simp]
lemma lift_ιConnection (v : EA) :
    d.lift (LocalFieldAlgebra.ιConnection
      (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA v) = d.connection v :=
  d.toAssignment.lift_ιConnection v

/-!

### D.3. Uniqueness

-/

/-- Two algebra maps agreeing on every species are equal. -/
lemma algHom_ext {Φ Ψ : SpeciesLocalFieldAlgebra Vf Vb EA →ₐ[ℂ] B}
    (hf : ∀ i x, Φ (ιFermionSpecies Vf Vb EA i x) = Ψ (ιFermionSpecies Vf Vb EA i x))
    (hb : ∀ j y, Φ (ιBosonSpecies Vf Vb EA j y) = Ψ (ιBosonSpecies Vf Vb EA j y))
    (ha : ∀ v, Φ (LocalFieldAlgebra.ιConnection
        (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA v)
      = Ψ (LocalFieldAlgebra.ιConnection
        (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA v)) : Φ = Ψ :=
  LocalFieldAlgebra.algHom_ext _ _ EA
    (fun v => LinearMap.congr_fun (SpeciesComponentSpace.hom_ext
      (F := Φ.toLinearMap.comp (LocalFieldAlgebra.ιFermion _ _ EA))
      (G := Ψ.toLinearMap.comp (LocalFieldAlgebra.ιFermion _ _ EA)) hf) v)
    (fun w => LinearMap.congr_fun (SpeciesComponentSpace.hom_ext
      (F := Φ.toLinearMap.comp (LocalFieldAlgebra.ιBoson _ _ EA))
      (G := Ψ.toLinearMap.comp (LocalFieldAlgebra.ιBoson _ _ EA)) hb) w)
    ha

/-- The mapping-out universal property in species form. A compatible species assignment in
  an arbitrary associative complex algebra `B` extends to one and only one complex algebra
  homomorphism out of the local field algebra of the family. -/
lemma existsUnique_algHom :
    ∃! Φ : SpeciesLocalFieldAlgebra Vf Vb EA →ₐ[ℂ] B,
      (∀ i x, Φ (ιFermionSpecies Vf Vb EA i x) = d.fermion i x) ∧
        (∀ j y, Φ (ιBosonSpecies Vf Vb EA j y) = d.boson j y) ∧
          (∀ v, Φ (LocalFieldAlgebra.ιConnection
            (SpeciesComponentSpace Vf) (SpeciesComponentSpace Vb) EA v) = d.connection v) :=
  ⟨d.lift, ⟨d.lift_ιFermionSpecies, d.lift_ιBosonSpecies, d.lift_ιConnection⟩, fun _ hΦ =>
    algHom_ext (fun i x => (hΦ.1 i x).trans (d.lift_ιFermionSpecies i x).symm)
      (fun j y => (hΦ.2.1 j y).trans (d.lift_ιBosonSpecies j y).symm)
      (fun v => (hΦ.2.2 v).trans (d.lift_ιConnection v).symm)⟩

end SpeciesAssignment

end SpeciesAlgebra

