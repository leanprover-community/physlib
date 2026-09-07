/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
public import Physlib.Relativity.DerivAlgebra
public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Mathematics.ConjModule
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Physlib.Relativity.SL2C.Basic
/-!

# The Standard Model EFT Lagrangian without derivatives

## i. Overview

-/

@[expose] public section

/-!

## The basic type for a lagrangian theory

-/
open Matrix MatrixGroups Module TensorProduct

structure LagrangianTheory (G : Type) [Group G] where
  -- The fermions
  FermionIrreps : Type
  [fermionIrreps_fintype : Fintype FermionIrreps]
  [fermionIrreps_decEq : DecidableEq FermionIrreps]
  FermionComponents : FermionIrreps → Type
  [fermionComponents_fintype : ∀ φ, Fintype (FermionComponents φ)]
  [fermionComponents_decEq : ∀ φ, DecidableEq (FermionComponents φ)]
  fermionModule : ∀ (_ : FermionIrreps), Type
  [fermionModule_addCommGroup : ∀ φ, AddCommGroup (fermionModule φ)]
  [fermionModule_module : ∀ φ, Module ℂ (fermionModule φ)]
  fermionBasis : ∀ φ, Basis (FermionComponents φ) ℂ (fermionModule φ)
  fermionRepLorentzGroup : ∀ φ, Representation ℂ SL(2,ℂ) (fermionModule φ)
  fermionRepGaugeGroup : ∀ φ, Representation ℂ G (fermionModule φ)
  -- The complex scalars
  ComplexScalarIrreps : Type
  [complexScalarIrreps_fintype : Fintype ComplexScalarIrreps]
  [complexScalarIrreps_decEq : DecidableEq ComplexScalarIrreps]
  ComplexScalarComponents : ComplexScalarIrreps → Type
  [complexScalarComponents_fintype : ∀ φ, Fintype (ComplexScalarComponents φ)]
  [complexScalarComponents_decEq : ∀ φ, DecidableEq (ComplexScalarComponents φ)]
  complexScalarModule : ∀ (_ : ComplexScalarIrreps), Type
  [complexScalarModule_addCommGroup : ∀ φ, AddCommGroup (complexScalarModule φ)]
  [complexScalarModule_module : ∀ φ, Module ℂ (complexScalarModule φ)]
  complexScalarBasis : ∀ φ, Basis (ComplexScalarComponents φ) ℂ (complexScalarModule φ)
  complexScalarRepLorentzGroup : ∀ φ, Representation ℂ SL(2,ℂ) (complexScalarModule φ)
  complexScalarRepGaugeGroup : ∀ φ, Representation ℂ G (complexScalarModule φ)
  -- The real bosonic fields (e.g. the gauge bosons of the theory.)
  RealBosonIrreps : Type
  [realBosonIrreps_fintype : Fintype RealBosonIrreps]
  [realBosonIrreps_decEq : DecidableEq RealBosonIrreps]
  RealBosonComponents : RealBosonIrreps → Type
  [realBosonComponents_fintype : ∀ φ, Fintype (RealBosonComponents φ)]
  [realBosonComponents_decEq : ∀ φ, DecidableEq (RealBosonComponents φ)]
  realBosonModule : ∀ (_ : RealBosonIrreps), Type
  [realBosonModule_addCommGroup : ∀ φ, AddCommGroup (realBosonModule φ)]
  [realBosonModule_module : ∀ φ, Module ℝ (realBosonModule φ)]
  realBosonBasis : ∀ φ, Basis (RealBosonComponents φ) ℝ (realBosonModule φ)
  realBosonRepLorentzGroup : ∀ φ, Representation ℝ SL(2,ℂ) (realBosonModule φ)
  realBosonRepGaugeGroup : ∀ φ, Representation ℝ G (realBosonModule φ)

namespace LagrangianTheory


attribute [instance] fermionIrreps_fintype fermionIrreps_decEq
  fermionComponents_fintype fermionComponents_decEq
  fermionModule_addCommGroup fermionModule_module
  complexScalarIrreps_fintype complexScalarIrreps_decEq
  complexScalarComponents_fintype complexScalarComponents_decEq
  complexScalarModule_addCommGroup complexScalarModule_module
  realBosonIrreps_fintype realBosonIrreps_decEq
  realBosonComponents_fintype realBosonComponents_decEq
  realBosonModule_addCommGroup realBosonModule_module

variable {G : Type} [Group G]

/-!

## A. Definitions related to fermions

-/

inductive FermionicGenerator (L : LagrangianTheory G)
  | of (φ : L.FermionIrreps) (α : L.FermionComponents φ) : L.FermionicGenerator
  | bar (φ : L.FermionIrreps) (α : L.FermionComponents φ) : L.FermionicGenerator
deriving DecidableEq, Fintype

def FermionicGenerator.conjugate {L : LagrangianTheory G} :
    L.FermionicGenerator → L.FermionicGenerator
  | .of φ α => .bar φ α
  | .bar φ α => .of φ α

@[simp]
lemma FermionicGenerator.conjugate_conjugate {L : LagrangianTheory G} (g : L.FermionicGenerator) :
    g.conjugate.conjugate = g := by
  cases g <;> rfl

def fermionicGeneratorEquiv {L : LagrangianTheory G}  : L.FermionicGenerator ≃
  (Σ φ : L.FermionIrreps, L.FermionComponents φ) ⊕ (Σ φ : L.FermionIrreps, L.FermionComponents φ) where
  toFun g := match g with
    | .of φ α => Sum.inl ⟨φ, α⟩
    | .bar φ α => Sum.inr ⟨φ, α⟩
  invFun g := match g with
    | Sum.inl ⟨φ, α⟩ => .of φ α
    | Sum.inr ⟨φ, α⟩ => .bar φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

inductive FermionicJetGenerator (L : LagrangianTheory G)
  | of (μ : Multiset (Fin 1 ⊕ Fin 3)) (φ : L.FermionIrreps) (α : L.FermionComponents φ) :
      L.FermionicJetGenerator
  | bar (μ : Multiset (Fin 1 ⊕ Fin 3)) (φ : L.FermionIrreps) (α : L.FermionComponents φ) :
      L.FermionicJetGenerator

def fermionicJetGeneratorEquiv {L : LagrangianTheory G}  : L.FermionicJetGenerator ≃
  (Multiset (Fin 1 ⊕ Fin 3) × Σ φ : L.FermionIrreps, L.FermionComponents φ) ⊕
  (Multiset (Fin 1 ⊕ Fin 3) × Σ φ : L.FermionIrreps, L.FermionComponents φ) where
  toFun g := match g with
    | .of μ φ α => Sum.inl (μ, ⟨φ, α⟩)
    | .bar μ φ α => Sum.inr (μ, ⟨φ, α⟩)
  invFun g := match g with
    | Sum.inl (μ, ⟨φ, α⟩) => .of μ φ α
    | Sum.inr (μ, ⟨φ, α⟩) => .bar μ φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

/-!

### A.1. The vector spaces of the fermionic fields.

-/

/-- The target vector space of the fermionic fields.
  If fermions are consider in terms of an associated-bundle, this vector space
  would be the fiber of that bundle.

  This vector space includes all the fields appearing in the theory. -/
abbrev FermionicTargetSpace (L : LagrangianTheory G) := Π (φ : L.FermionIrreps),  L.fermionModule φ

/-- The target vector space of the jet-bundle coordinates of fermions e.g. ∂_μ ψ.
  This is the fiber of the jet bundle associated with the fermions: since partial
  derivatives commute, the derivative slots form a symmetric algebra.

  This vector space includes all the fields in the theory + their derivative coordinates. -/
abbrev FermionicJetSpace (L : LagrangianTheory G) :=
  SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.FermionicTargetSpace

/-- The fermionic target space linearly embeds into the fermionic target space with derivatives. -/
def FermionicTargetSpace.toFermionicJetSpace {L : LagrangianTheory G} :
    L.FermionicTargetSpace →ₗ[ℂ] L.FermionicJetSpace :=
  TensorProduct.mk ℂ (SymmetricAlgebra ℂ Lorentz.CoℂModule) L.FermionicTargetSpace 1

/-- Since fermions are complex fields, we also need to consider the target space of their
  complex conjugate. The vector space `FermionicTargetSpaceWithComplex` is defined
  to contain both the target space of the fields, and their conjugates.

  This vector space includes all the fields appearing in the theory + their conjugates.  -/
abbrev FermionicTargetSpaceWithComplex (L : LagrangianTheory G) := L.FermionicTargetSpace ×
  ConjModule L.FermionicTargetSpace

/-- Similar to `FermionicTargetSpaceWithComplex` except including derivatives.

  This vector space includes all the fields present in the theory + their conjugates + all
  their jet-bundle derivative coordinates. -/
abbrev FermionicJetSpaceWithComplex (L : LagrangianTheory G) :=
  (SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.FermionicTargetSpace) ×
  (SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] ConjModule L.FermionicTargetSpace)

/-- The vector space dual to `FermionicTargetSpaceWithComplex` and spanned by the component
  functions of all the fields + their conjugates in the theory. -/
abbrev FermionicComponentSpace (L : LagrangianTheory G) :=
  Module.Dual ℂ L.FermionicTargetSpaceWithComplex

/-- The vector space spanned by the component functions of all the fields + their
  conjugates + all their jet-bundle derivative coordinates in the theory.

  This is the *graded* dual of `FermionicJetSpaceWithComplex`: the duals of the
  finite-dimensional building blocks are dualized individually and reassembled. The full
  `Module.Dual` of `FermionicJetSpaceWithComplex` is strictly larger (the latter is
  infinite dimensional) and is not spanned by the component functions. -/
abbrev FermionicJetComponentSpace (L : LagrangianTheory G) :=
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ L.FermionicTargetSpace) ×
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ (ConjModule L.FermionicTargetSpace))

/-!

## A.2. The fermionic algebras

-/

/-- The EFT algebra spanned by the fermions in the theory + their conjugate. -/
abbrev FermionicEFTExclDeriv (L : LagrangianTheory G) := ExteriorAlgebra ℂ L.FermionicComponentSpace

/-- The EFT algebra spanned by the fermions in the theory + their conjugate + all their
  jet-bundle derivative coordinates, without taking account of total derivatives or
  equations of motion relations. -/
abbrev FermionicEFTJet (L : LagrangianTheory G) :=
  ExteriorAlgebra ℂ L.FermionicJetComponentSpace

/-!

## A.3. The basis of the fermionic vector spaces

The main vector spaces are `FermionicComponentSpace` and `FermionicJetComponentSpace`.
On these spaces we want to define a basis indexed by `FermionicGenerator` and
`FermionicJetGenerator` respectively.

-/

noncomputable def FermionicComponentSpace.basis {L : LagrangianTheory G}  :
    Basis L.FermionicGenerator ℂ L.FermionicComponentSpace :=
  ((Pi.basis (fun φ => L.fermionBasis φ)).prod
  ((Pi.basis (fun φ => L.fermionBasis φ)).conj)).dualBasis.reindex fermionicGeneratorEquiv.symm

noncomputable def FermionicJetComponentSpace.basis {L : LagrangianTheory G} :
    Basis L.FermionicJetGenerator ℂ L.FermionicJetComponentSpace :=
  ((DerivAlgebraComplex.basis.tensorProduct
      (Pi.basis fun φ => L.fermionBasis φ).dualBasis).prod
    (DerivAlgebraComplex.basis.tensorProduct
      ((Pi.basis fun φ => L.fermionBasis φ).conj.dualBasis))).reindex
    fermionicJetGeneratorEquiv.symm

/-!

## A.4. The representation of the Lorentz group on fermionic vector spaces and algebras

We now define the respresentation of the Lorentz group on the vector spaces
and algebras associated with Fermions. Note that since we are dealing with complex
fields we take the Lorentz group to be `SL(2,ℂ)`, rather than dealing with projective
representations of the Lorentz group.

We are particularly interested in the representations acting on
- the vector spaces `FermionicComponentSpace` and `FermionicJetComponentSpace`, and
- the algebras `FermionicEFTExclDeriv` and `FermionicEFTJet`.

To define the representations on vector spaces involving derivatives,
we first need to define the representations on the derivative algebras.

-/


variable {L : LagrangianTheory G}

/-- The representation of the Lorentz group on the symmetric algebra of jet
  coordinates, acting through `CoℂModule.SL2CRep` on each factor. -/
noncomputable def jetAlgebraRepLorentzGroup :
    Representation ℂ SL(2,ℂ) (SymmetricAlgebra ℂ Lorentz.CoℂModule) where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ Lorentz.CoℂModule.SL2CRep Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

def FermionicTargetSpace.repLorentzGroup : Representation ℂ SL(2,ℂ) L.FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.fermionRepLorentzGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

noncomputable def FermionicTargetSpaceWithComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicTargetSpaceWithComplex :=
  FermionicTargetSpace.repLorentzGroup.prod (FermionicTargetSpace.repLorentzGroup.conj)

noncomputable def FermionicComponentSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicComponentSpace :=
  FermionicTargetSpaceWithComplex.repLorentzGroup.dual

noncomputable def FermionicJetComponentSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicJetComponentSpace :=
  (DerivAlgebraComplex.repLorentzGroup.tprod FermionicTargetSpace.repLorentzGroup.dual).prod
  (DerivAlgebraComplex.repLorentzGroup.tprod FermionicTargetSpace.repLorentzGroup.conj.dual)

noncomputable def FermionicEFTExclDeriv.repLorentzGroup : Representation ℂ SL(2,ℂ) L.FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

/-- The representation of the Lorentz group on the algebra `FermionicEFTJet`.  -/
noncomputable def FermionicEFTJet.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.FermionicEFTJet where
  toFun Λ := (ExteriorAlgebra.map (FermionicJetComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

/-!

### A.5. The representation of the Gauge group on fermionic vector spaces and algebras

-/

def FermionicTargetSpace.repGaugeGroup : Representation ℂ G L.FermionicTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.fermionRepGaugeGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

noncomputable def FermionicTargetSpaceWithComplex.repGaugeGroup :
    Representation ℂ G L.FermionicTargetSpaceWithComplex :=
  FermionicTargetSpace.repGaugeGroup.prod (FermionicTargetSpace.repGaugeGroup.conj)

/-- The representation of the gauge group on the jet space of the fermionic fields.
  The gauge group acts trivially on the derivative slots, so that the jet coordinates
  `∂ ⋯ ∂ ψ` transform in the same representation of the gauge group as `ψ` itself. -/
noncomputable def FermionicJetSpace.repGaugeGroup :
    Representation ℂ G L.FermionicJetSpace :=
  (Representation.trivial ℂ G (SymmetricAlgebra ℂ Lorentz.CoℂModule)).tprod
    FermionicTargetSpace.repGaugeGroup

noncomputable def FermionicComponentSpace.repGaugeGroup : Representation ℂ G L.FermionicComponentSpace :=
  FermionicTargetSpaceWithComplex.repGaugeGroup.dual

/-- The representation of the gauge group on the space of component functions of the
  fermionic fields, their conjugates, and their jet-bundle derivative coordinates;
  trivial on the derivative slots. -/
noncomputable def FermionicJetComponentSpace.repGaugeGroup :
    Representation ℂ G L.FermionicJetComponentSpace :=
  ((Representation.trivial ℂ G (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))).tprod
    FermionicTargetSpace.repGaugeGroup.dual).prod
  ((Representation.trivial ℂ G (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))).tprod
    FermionicTargetSpace.repGaugeGroup.conj.dual)

noncomputable def FermionicEFTExclDeriv.repGaugeGroup : Representation ℂ G L.FermionicEFTExclDeriv where
  toFun Λ := (ExteriorAlgebra.map (FermionicComponentSpace.repGaugeGroup Λ)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' Λ1 Λ2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

noncomputable def FermionicEFTJet.repGaugeGroup :
    Representation ℂ G L.FermionicEFTJet where
  toFun g := (ExteriorAlgebra.map (FermionicJetComponentSpace.repGaugeGroup g)).toLinearMap
  map_one' := by
    simp only [map_one, End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g1 g2 := by
    simp only [map_mul, End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

/-!

## B. Definitions related to the complex scalars

-/

inductive ComplexScalarGenerator (L : LagrangianTheory G)
  | of (φ : L.ComplexScalarIrreps) (α : L.ComplexScalarComponents φ) : L.ComplexScalarGenerator
  | bar (φ : L.ComplexScalarIrreps) (α : L.ComplexScalarComponents φ) : L.ComplexScalarGenerator
deriving DecidableEq, Fintype

def ComplexScalarGenerator.conjugate : L.ComplexScalarGenerator → L.ComplexScalarGenerator
  | .of φ α => .bar φ α
  | .bar φ α => .of φ α

@[simp]
lemma ComplexScalarGenerator.conjugate_conjugate (g : L.ComplexScalarGenerator) :
    g.conjugate.conjugate = g := by
  cases g <;> rfl

def complexScalarGeneratorEquiv : L.ComplexScalarGenerator ≃
    (Σ φ : L.ComplexScalarIrreps, L.ComplexScalarComponents φ) ⊕
    (Σ φ : L.ComplexScalarIrreps, L.ComplexScalarComponents φ) where
  toFun g := match g with
    | .of φ α => Sum.inl ⟨φ, α⟩
    | .bar φ α => Sum.inr ⟨φ, α⟩
  invFun g := match g with
    | Sum.inl ⟨φ, α⟩ => .of φ α
    | Sum.inr ⟨φ, α⟩ => .bar φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

inductive ComplexScalarJetGenerator (L : LagrangianTheory G)
  | of (μ : Multiset (Fin 1 ⊕ Fin 3)) (φ : L.ComplexScalarIrreps)
      (α : L.ComplexScalarComponents φ) : L.ComplexScalarJetGenerator
  | bar (μ : Multiset (Fin 1 ⊕ Fin 3)) (φ : L.ComplexScalarIrreps)
      (α : L.ComplexScalarComponents φ) : L.ComplexScalarJetGenerator

def complexScalarJetGeneratorEquiv : L.ComplexScalarJetGenerator ≃
  (Multiset (Fin 1 ⊕ Fin 3) × Σ φ : L.ComplexScalarIrreps, L.ComplexScalarComponents φ) ⊕
  (Multiset (Fin 1 ⊕ Fin 3) × Σ φ : L.ComplexScalarIrreps, L.ComplexScalarComponents φ) where
  toFun g := match g with
    | .of μ φ α => Sum.inl (μ, ⟨φ, α⟩)
    | .bar μ φ α => Sum.inr (μ, ⟨φ, α⟩)
  invFun g := match g with
    | Sum.inl (μ, ⟨φ, α⟩) => .of μ φ α
    | Sum.inr (μ, ⟨φ, α⟩) => .bar μ φ α
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

/-!

### B.1. The vector spaces of the complex scalar fields.

-/

/-- The target vector space of the complex scalar fields.

  This vector space includes all the complex scalar fields appearing in the theory. -/
abbrev ComplexScalarTargetSpace (L : LagrangianTheory G) :=
  Π (φ : L.ComplexScalarIrreps), L.complexScalarModule φ

/-- The target vector space of the jet-bundle coordinates of the complex scalar
  fields e.g. ∂_μ ϕ. This is the fiber of the jet bundle associated with the scalars:
  since partial derivatives commute, the derivative slots form a symmetric algebra.

  This vector space includes all the complex scalar fields in the theory + their
  derivative coordinates. -/
abbrev ComplexScalarJetSpace (L : LagrangianTheory G) :=
  SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.ComplexScalarTargetSpace

/-- The complex scalar target space linearly embeds into the complex scalar target
  space with derivatives. -/
def ComplexScalarTargetSpace.toComplexScalarJetSpace {L : LagrangianTheory G} :
    L.ComplexScalarTargetSpace →ₗ[ℂ] L.ComplexScalarJetSpace :=
  TensorProduct.mk ℂ (SymmetricAlgebra ℂ Lorentz.CoℂModule) L.ComplexScalarTargetSpace 1

/-- The target space of the complex scalar fields, including their conjugates. -/
abbrev ComplexScalarTargetSpaceWithComplex (L : LagrangianTheory G) :=
  L.ComplexScalarTargetSpace × ConjModule L.ComplexScalarTargetSpace

/-- Similar to `ComplexScalarTargetSpaceWithComplex` except including derivatives.

  This vector space includes all the complex scalar fields present in the theory +
  their conjugates + all their jet-bundle derivative coordinates. -/
abbrev ComplexScalarJetSpaceWithComplex (L : LagrangianTheory G) :=
  (SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] L.ComplexScalarTargetSpace) ×
  (SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] ConjModule L.ComplexScalarTargetSpace)

/-- The vector space dual to `ComplexScalarTargetSpaceWithComplex` and spanned by the
  component functions of all the complex scalar fields + their conjugates in the
  theory. -/
abbrev ComplexScalarComponentSpace (L : LagrangianTheory G) :=
  Module.Dual ℂ L.ComplexScalarTargetSpaceWithComplex

/-- The vector space spanned by the component functions of all the complex scalar
  fields + their conjugates + all their jet-bundle derivative coordinates in the
  theory.

  This is the *graded* dual of `ComplexScalarJetSpaceWithComplex`: the duals of the
  finite-dimensional building blocks are dualized individually and reassembled. The
  full `Module.Dual` of `ComplexScalarJetSpaceWithComplex` is strictly larger (the
  latter is infinite dimensional) and is not spanned by the component functions. -/
abbrev ComplexScalarJetComponentSpace (L : LagrangianTheory G) :=
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ L.ComplexScalarTargetSpace) ×
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ (ConjModule L.ComplexScalarTargetSpace))

/-!

### B.2. The complex scalar algebras

-/

/-- The EFT algebra spanned by the complex scalars in the theory + their conjugate. -/
abbrev ComplexScalarEFTExclDeriv (L : LagrangianTheory G) :=
  SymmetricAlgebra ℂ L.ComplexScalarComponentSpace

/-- The EFT algebra spanned by the complex scalars in the theory + their conjugate +
  all their jet-bundle derivative coordinates, without taking account of total
  derivatives or equations of motion relations. -/
abbrev ComplexScalarEFTJet (L : LagrangianTheory G) :=
  SymmetricAlgebra ℂ L.ComplexScalarJetComponentSpace

/-!

### B.3. The basis of the complex scalar vector spaces

The main vector spaces are `ComplexScalarComponentSpace` and
`ComplexScalarJetComponentSpace`. On these spaces we want to define a basis
indexed by `ComplexScalarGenerator` and `ComplexScalarJetGenerator` respectively.

-/

noncomputable def ComplexScalarComponentSpace.basis :
    Basis L.ComplexScalarGenerator ℂ L.ComplexScalarComponentSpace :=
  ((Pi.basis (fun φ => L.complexScalarBasis φ)).prod
  ((Pi.basis (fun φ => L.complexScalarBasis φ)).conj)).dualBasis.reindex
    complexScalarGeneratorEquiv.symm

noncomputable def ComplexScalarJetComponentSpace.basis :
    Basis L.ComplexScalarJetGenerator ℂ L.ComplexScalarJetComponentSpace :=
  ((DerivAlgebraComplex.basis.tensorProduct
      (Pi.basis fun φ => L.complexScalarBasis φ).dualBasis).prod
    (DerivAlgebraComplex.basis.tensorProduct
      ((Pi.basis fun φ => L.complexScalarBasis φ).conj.dualBasis))).reindex
    complexScalarJetGeneratorEquiv.symm

/-!

### B.4. The representation of the Lorentz group on complex scalar vector spaces and algebras

-/

def ComplexScalarTargetSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.complexScalarRepLorentzGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

noncomputable def ComplexScalarTargetSpaceWithComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarTargetSpaceWithComplex :=
  ComplexScalarTargetSpace.repLorentzGroup.prod (ComplexScalarTargetSpace.repLorentzGroup.conj)

noncomputable def ComplexScalarComponentSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarComponentSpace :=
  ComplexScalarTargetSpaceWithComplex.repLorentzGroup.dual

noncomputable def ComplexScalarJetComponentSpace.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarJetComponentSpace :=
  (DerivAlgebraComplex.repLorentzGroup.tprod ComplexScalarTargetSpace.repLorentzGroup.dual).prod
  (DerivAlgebraComplex.repLorentzGroup.tprod ComplexScalarTargetSpace.repLorentzGroup.conj.dual)

noncomputable def ComplexScalarEFTExclDeriv.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarEFTExclDeriv where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repLorentzGroup Λ2)) by
      rw [h]; rfl
    ext v
    simp

/-- The representation of the Lorentz group on the algebra `ComplexScalarEFTJet`. -/
noncomputable def ComplexScalarEFTJet.repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.ComplexScalarEFTJet where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repLorentzGroup Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

/-!

### B.5. The representation of the Gauge group on complex scalar vector spaces and algebras

-/

def ComplexScalarTargetSpace.repGaugeGroup :
    Representation ℂ G L.ComplexScalarTargetSpace where
  toFun g := LinearMap.piMap fun φ => L.complexScalarRepGaugeGroup φ g
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' g1 g2 := by
    ext x i y
    simp

noncomputable def ComplexScalarTargetSpaceWithComplex.repGaugeGroup :
    Representation ℂ G L.ComplexScalarTargetSpaceWithComplex :=
  ComplexScalarTargetSpace.repGaugeGroup.prod (ComplexScalarTargetSpace.repGaugeGroup.conj)

/-- The representation of the gauge group on the jet space of the complex scalar
  fields. The gauge group acts trivially on the derivative slots, so that the jet
  coordinates `∂ ⋯ ∂ ϕ` transform in the same representation of the gauge group as
  `ϕ` itself. -/
noncomputable def ComplexScalarJetSpace.repGaugeGroup :
    Representation ℂ G L.ComplexScalarJetSpace :=
  (Representation.trivial ℂ G (SymmetricAlgebra ℂ Lorentz.CoℂModule)).tprod
    ComplexScalarTargetSpace.repGaugeGroup

noncomputable def ComplexScalarComponentSpace.repGaugeGroup :
    Representation ℂ G L.ComplexScalarComponentSpace :=
  ComplexScalarTargetSpaceWithComplex.repGaugeGroup.dual

/-- The representation of the gauge group on the space of component functions of the
  complex scalar fields, their conjugates, and their jet-bundle derivative
  coordinates; trivial on the derivative slots. -/
noncomputable def ComplexScalarJetComponentSpace.repGaugeGroup :
    Representation ℂ G L.ComplexScalarJetComponentSpace :=
  ((Representation.trivial ℂ G (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))).tprod
    ComplexScalarTargetSpace.repGaugeGroup.dual).prod
  ((Representation.trivial ℂ G (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))).tprod
    ComplexScalarTargetSpace.repGaugeGroup.conj.dual)

noncomputable def ComplexScalarEFTExclDeriv.repGaugeGroup :
    Representation ℂ G L.ComplexScalarEFTExclDeriv where
  toFun g := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup g)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' g1 g2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup (g1 * g2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup g1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpace.repGaugeGroup g2)) by
      rw [h]; rfl
    ext v
    simp

noncomputable def ComplexScalarEFTJet.repGaugeGroup :
    Representation ℂ G L.ComplexScalarEFTJet where
  toFun g := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repGaugeGroup g)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' g1 g2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repGaugeGroup (g1 * g2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repGaugeGroup g1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarJetComponentSpace.repGaugeGroup g2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

/-!

## C. Definitions related to real bosons

The real bosonic fields (for example the field strengths of the gauge bosons) are
genuinely real, so unlike the fermions and complex scalars there is no conjugate
field, and every vector space and algebra below is taken over `ℝ`.

-/

inductive RealBosonGenerator (L : LagrangianTheory G)
  | of (φ : L.RealBosonIrreps) (α : L.RealBosonComponents φ) : L.RealBosonGenerator
deriving DecidableEq, Fintype

def realBosonGeneratorEquiv :
    L.RealBosonGenerator ≃ Σ φ : L.RealBosonIrreps, L.RealBosonComponents φ where
  toFun g := match g with
    | .of φ α => ⟨φ, α⟩
  invFun g := match g with
    | ⟨φ, α⟩ => .of φ α
  left_inv g := by cases g; rfl
  right_inv g := by cases g; rfl

inductive RealBosonJetGenerator (L : LagrangianTheory G)
  | of (μ : Multiset (Fin 1 ⊕ Fin 3)) (φ : L.RealBosonIrreps) (α : L.RealBosonComponents φ) :
      L.RealBosonJetGenerator

def realBosonJetGeneratorEquiv : L.RealBosonJetGenerator ≃
    Multiset (Fin 1 ⊕ Fin 3) × Σ φ : L.RealBosonIrreps, L.RealBosonComponents φ where
  toFun g := match g with
    | .of μ φ α => (μ, ⟨φ, α⟩)
  invFun g := match g with
    | (μ, ⟨φ, α⟩) => .of μ φ α
  left_inv g := by cases g; rfl
  right_inv g := by cases g; rfl

/-!

### C.1. The vector spaces of the real bosonic fields.

-/

/-- The target vector space of the real bosonic fields.

  This vector space includes all the real bosonic fields appearing in the theory. -/
abbrev RealBosonTargetSpace (L : LagrangianTheory G) :=
  Π (φ : L.RealBosonIrreps), L.realBosonModule φ

/-- The target vector space of the jet-bundle coordinates of the real bosonic fields
  e.g. ∂_μ B. Since partial derivatives commute, the derivative slots form a
  symmetric algebra.

  This vector space includes all the real bosonic fields in the theory + their
  derivative coordinates. -/
abbrev RealBosonJetSpace (L : LagrangianTheory G) :=
  SymmetricAlgebra ℝ Lorentz.CoVector ⊗[ℝ] L.RealBosonTargetSpace

/-- The real bosonic target space linearly embeds into the real bosonic target space
  with derivatives. -/
def RealBosonTargetSpace.toRealBosonJetSpace {L : LagrangianTheory G} :
    L.RealBosonTargetSpace →ₗ[ℝ] L.RealBosonJetSpace :=
  TensorProduct.mk ℝ (SymmetricAlgebra ℝ Lorentz.CoVector) L.RealBosonTargetSpace 1

/-- The vector space dual to `RealBosonTargetSpace` and spanned by the component
  functions of all the real bosonic fields in the theory. There is no conjugate
  factor, since the fields are real. -/
abbrev RealBosonComponentSpace (L : LagrangianTheory G) :=
  Module.Dual ℝ L.RealBosonTargetSpace

/-- The vector space spanned by the component functions of all the real bosonic
  fields + all their jet-bundle derivative coordinates in the theory.

  This is the *graded* dual of `RealBosonJetSpace`: the duals of the
  finite-dimensional building blocks are dualized individually and reassembled. -/
abbrev RealBosonJetComponentSpace (L : LagrangianTheory G) :=
  SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) ⊗[ℝ] Module.Dual ℝ L.RealBosonTargetSpace

/-!

### C.2. The real bosonic algebras

-/

/-- The EFT algebra spanned by the real bosonic fields in the theory. -/
abbrev RealBosonEFTExclDeriv (L : LagrangianTheory G) :=
  SymmetricAlgebra ℝ L.RealBosonComponentSpace

/-- The EFT algebra spanned by the real bosonic fields in the theory + all their
  jet-bundle derivative coordinates, without taking account of total derivatives or
  equations of motion relations. -/
abbrev RealBosonEFTJet (L : LagrangianTheory G) :=
  SymmetricAlgebra ℝ L.RealBosonJetComponentSpace


/-- The real bosonic EFT algebra with complex coefficients: the real bosonic EFT
  algebra with scalars extended from `ℝ` to `ℂ`, so that it can be combined with the
  complex scalar and fermionic algebras in the full EFT Lagrangian. -/
abbrev RealBosonEFTExclDerivComplex (L : LagrangianTheory G) :=  ℂ ⊗[ℝ] L.RealBosonEFTExclDeriv

/-- The real bosonic EFT algebra including jet-bundle derivative coordinates, with complex
  coefficients: `RealBosonEFTJet` with scalars extended from `ℝ` to `ℂ`, so
  that it can be combined with the complex scalar and fermionic algebras in the full
  EFT Lagrangian. -/
abbrev RealBosonEFTJetComplex (L : LagrangianTheory G) := ℂ ⊗[ℝ] L.RealBosonEFTJet


/-!

### C.3. The basis of the real bosonic vector spaces

-/

noncomputable def RealBosonComponentSpace.basis :
    Basis L.RealBosonGenerator ℝ L.RealBosonComponentSpace :=
  (Pi.basis (fun φ => L.realBosonBasis φ)).dualBasis.reindex realBosonGeneratorEquiv.symm

/-- The basis of the symmetric algebra of dual real jet slots, indexed by multisets of
  spacetime indices. -/
noncomputable def dualRealJetAlgebraBasis :
    Basis (Multiset (Fin 1 ⊕ Fin 3)) ℝ (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)) :=
  Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.reindex Multiset.toFinsupp.toEquiv.symm

/-- The multiset basis of the dual derivative symbols, as a basis vector of the
  symmetric algebra at the corresponding multi-index. -/
lemma dualRealJetAlgebraBasis_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    dualRealJetAlgebraBasis s =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s) := by
  rw [dualRealJetAlgebraBasis, Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The multiset basis vectors of the real dual derivative slots multiply by adding the
  multisets. -/
lemma dualRealJetAlgebraBasis_mul (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    dualRealJetAlgebraBasis s * dualRealJetAlgebraBasis t =
      dualRealJetAlgebraBasis (s + t) := by
  rw [dualRealJetAlgebraBasis_apply, dualRealJetAlgebraBasis_apply,
    dualRealJetAlgebraBasis_apply, map_add]
  simp only [Basis.symmetricAlgebra, Basis.map_apply,
    show ∀ p, (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv p =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm p
      from fun _ => rfl,
    ← map_mul, MvPolynomial.coe_basisMonomials]
  simp only [MvPolynomial.monomial_mul, mul_one]

/-- The multiset basis of the real dual derivative slots at the empty multiset is the
  unit. -/
lemma dualRealJetAlgebraBasis_nil :
    dualRealJetAlgebraBasis (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 := by
  rw [dualRealJetAlgebraBasis_apply,
    show Multiset.toFinsupp (0 : Multiset (Fin 1 ⊕ Fin 3)) = 0 by simp,
    Basis.symmetricAlgebra, Basis.map_apply,
    show (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv
        ((MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) 0) =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm
        ((MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) 0) from rfl,
    show (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ)
        = 1 from by
      rw [MvPolynomial.coe_basisMonomials]
      show MvPolynomial.monomial 0 1 = 1
      rw [MvPolynomial.monomial_zero', MvPolynomial.C_1],
    map_one]

/-- The multiset basis of the real dual derivative slots at a singleton index. -/
lemma dualRealJetAlgebraBasis_singleton (μ : Fin 1 ⊕ Fin 3) :
    dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
        (Lorentz.CoVector.basis.dualBasis μ) := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (Finsupp.single μ 1) =
      MvPolynomial.X μ := rfl
  rw [dualRealJetAlgebraBasis, Basis.reindex_apply, Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Finsupp.single μ 1 by simp,
    Basis.symmetricAlgebra, Basis.map_apply, h]
  simp

noncomputable def RealBosonJetComponentSpace.basis :
    Basis L.RealBosonJetGenerator ℝ L.RealBosonJetComponentSpace :=
  (dualRealJetAlgebraBasis.tensorProduct
    (Pi.basis fun φ => L.realBosonBasis φ).dualBasis).reindex
    realBosonJetGeneratorEquiv.symm

/-!

### C.4. The representation of the Lorentz group on real bosonic vector spaces and algebras

-/

/-- The representation of the Lorentz group on the real Lorentz-covector derivative
  slots, obtained from the real Lorentz-vector representation through the covering
  map `SL(2,ℂ) →* LorentzGroup 3`. -/
noncomputable def realBosonSlotRepLorentzGroup : Representation ℝ SL(2,ℂ) Lorentz.CoVector :=
  MonoidHom.comp Lorentz.CoVector.rep Lorentz.SL2C.toLorentzGroup

/-- The representation of the Lorentz group on the symmetric algebra of real jet
  coordinate slots. -/
noncomputable def realJetAlgebraRepLorentzGroup :
    Representation ℝ SL(2,ℂ) (SymmetricAlgebra ℝ Lorentz.CoVector) where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

/-- The representation of the Lorentz group on the symmetric algebra of dual real
  jet coordinate slots. -/
noncomputable def dualRealJetAlgebraRepLorentzGroup :
    Representation ℝ SL(2,ℂ) (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)) where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup.dual Λ)).toLinearMap
  map_one' := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup.dual 1) =
        AlgHom.id ℝ (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
    rfl
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup.dual (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup.dual Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ realBosonSlotRepLorentzGroup.dual Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

def RealBosonTargetSpace.repLorentzGroup :
    Representation ℝ SL(2,ℂ) L.RealBosonTargetSpace where
  toFun Λ := LinearMap.piMap fun φ => L.realBosonRepLorentzGroup φ Λ
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' Λ1 Λ2 := by
    ext x i y
    simp

/-- The representation of the Lorentz group on the jet space of the real bosonic
  fields: the tensor product of the action on the derivative slots and the action on
  the real bosonic target space. -/
noncomputable def RealBosonJetSpace.repLorentzGroup :
    Representation ℝ SL(2,ℂ) L.RealBosonJetSpace :=
  realJetAlgebraRepLorentzGroup.tprod RealBosonTargetSpace.repLorentzGroup

noncomputable def RealBosonComponentSpace.repLorentzGroup :
    Representation ℝ SL(2,ℂ) L.RealBosonComponentSpace :=
  RealBosonTargetSpace.repLorentzGroup.dual

noncomputable def RealBosonJetComponentSpace.repLorentzGroup :
    Representation ℝ SL(2,ℂ) L.RealBosonJetComponentSpace :=
  dualRealJetAlgebraRepLorentzGroup.tprod RealBosonTargetSpace.repLorentzGroup.dual

noncomputable def RealBosonEFTExclDeriv.repLorentzGroup :
    Representation ℝ SL(2,ℂ) L.RealBosonEFTExclDeriv where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repLorentzGroup Λ2)) by
      rw [h]; rfl
    ext v
    simp

/-- The representation of the Lorentz group on the algebra `RealBosonEFTJet`. -/
noncomputable def RealBosonEFTJet.repLorentzGroup :
    Representation ℝ SL(2,ℂ) L.RealBosonEFTJet where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repLorentzGroup Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]


/-- The representation of the Lorentz group on the complexified real bosonic EFT
  algebra, obtained from the real representation by extension of scalars and
  transported to the wrapper type. -/
noncomputable def RealBosonEFTExclDerivComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) (RealBosonEFTExclDerivComplex L) where
  toFun Λ :=
    LinearMap.baseChange ℂ (RealBosonEFTExclDeriv.repLorentzGroup Λ)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- The representation of the Lorentz group on the complexified real bosonic EFT
  algebra with derivatives, obtained from the real representation by extension of
  scalars. -/
noncomputable def RealBosonEFTJetComplex.repLorentzGroup :
    Representation ℂ SL(2,ℂ) (RealBosonEFTJetComplex L) where
  toFun Λ :=
    LinearMap.baseChange ℂ (RealBosonEFTJet.repLorentzGroup Λ)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]


/-!

### C.5. The representation of the Gauge group on real bosonic vector spaces and algebras

-/

def RealBosonTargetSpace.repGaugeGroup :
    Representation ℝ G L.RealBosonTargetSpace where
  toFun g := LinearMap.piMap fun φ => L.realBosonRepGaugeGroup φ g
  map_one' := by
    ext x i y
    simp only [map_one, LinearMap.coe_comp, LinearMap.coe_piMap, LinearMap.coe_single,
      Function.comp_apply, Pi.map_apply, End.one_apply]
  map_mul' g1 g2 := by
    ext x i y
    simp

/-- The representation of the gauge group on the jet space of the real bosonic
  fields. The gauge group acts trivially on the derivative slots, so that the jet
  coordinates `∂ ⋯ ∂ B` transform in the same representation of the gauge group as
  `B` itself. -/
noncomputable def RealBosonJetSpace.repGaugeGroup :
    Representation ℝ G L.RealBosonJetSpace :=
  (Representation.trivial ℝ G (SymmetricAlgebra ℝ Lorentz.CoVector)).tprod
    RealBosonTargetSpace.repGaugeGroup

noncomputable def RealBosonComponentSpace.repGaugeGroup :
    Representation ℝ G L.RealBosonComponentSpace :=
  RealBosonTargetSpace.repGaugeGroup.dual

/-- The representation of the gauge group on the space of component functions of the
  real bosonic fields and their jet-bundle derivative coordinates; trivial on the
  derivative slots. -/
noncomputable def RealBosonJetComponentSpace.repGaugeGroup :
    Representation ℝ G L.RealBosonJetComponentSpace :=
  (Representation.trivial ℝ G (SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector))).tprod
    RealBosonTargetSpace.repGaugeGroup.dual

noncomputable def RealBosonEFTExclDeriv.repGaugeGroup :
    Representation ℝ G L.RealBosonEFTExclDeriv where
  toFun g := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repGaugeGroup g)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' g1 g2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repGaugeGroup (g1 * g2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repGaugeGroup g1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpace.repGaugeGroup g2)) by
      rw [h]; rfl
    ext v
    simp

noncomputable def RealBosonEFTJet.repGaugeGroup :
    Representation ℝ G L.RealBosonEFTJet where
  toFun g := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repGaugeGroup g)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' g1 g2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repGaugeGroup (g1 * g2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repGaugeGroup g1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonJetComponentSpace.repGaugeGroup g2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

noncomputable def RealBosonEFTExclDerivComplex.repGaugeGroup :
    Representation ℂ G (RealBosonEFTExclDerivComplex L) where
  toFun g :=
    LinearMap.baseChange ℂ (RealBosonEFTExclDeriv.repGaugeGroup g)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' g1 g2 := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- The representation of the gauge group on the complexified real bosonic EFT
  algebra with derivatives, obtained from the real representation by extension of
  scalars. -/
noncomputable def RealBosonEFTJetComplex.repGaugeGroup :
    Representation ℂ G (RealBosonEFTJetComplex L) where
  toFun g :=
    LinearMap.baseChange ℂ (RealBosonEFTJet.repGaugeGroup g)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' g1 g2 := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-!

## D. General field generators

-/


inductive FieldGenerators (L : LagrangianTheory G)
  | cScalar (_ : L.ComplexScalarGenerator) : FieldGenerators L
  | fermion (_ : L.FermionicGenerator) : FieldGenerators L
  | realBoson (_ : L.RealBosonGenerator) : FieldGenerators L
deriving DecidableEq, Fintype

def FieldGenerators.IsFermion : L.FieldGenerators → Bool
  | .cScalar _ => False
  | .fermion _ => True
  | .realBoson _ => False

def FieldGenerators.IsBoson : L.FieldGenerators → Bool
  | .cScalar _ => True
  | .fermion _ => False
  | .realBoson _ => True

def FieldGenerators.conjugate : L.FieldGenerators → L.FieldGenerators
  | .cScalar g => .cScalar g.conjugate
  | .fermion g => .fermion g.conjugate
  | .realBoson g => .realBoson g

@[simp]
lemma FieldGenerators.conjugate_conjugate (ϕ : L.FieldGenerators) :
    ϕ.conjugate.conjugate = ϕ := by
  cases ϕ <;> simp [conjugate]

@[simp]
lemma FieldGenerators.cScalar_isFermion (ϕ : L.ComplexScalarGenerator) :
     (cScalar ϕ).IsFermion = False := by simp [IsFermion]

@[simp]
lemma FieldGenerators.fermion_isFermion (ϕ : L.FermionicGenerator) :
     (fermion ϕ).IsFermion = True := by simp [IsFermion]

@[simp]
lemma FieldGenerators.cScalar_isBoson (ϕ : L.ComplexScalarGenerator) :
     (cScalar ϕ).IsBoson = True := by simp [IsBoson]

@[simp]
lemma FieldGenerators.fermion_isBoson (ϕ : L.FermionicGenerator) :
     (fermion ϕ).IsBoson = False := by simp [IsBoson]


end LagrangianTheory
