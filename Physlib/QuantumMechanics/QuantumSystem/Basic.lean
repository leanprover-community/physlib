/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Mathlib.Analysis.Normed.Group.SemiNormedGrp
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
/-!

# Quantum system

## i. Overview

In non-relativistic quantum mechanics a quantum system is characterized by a Hilbert space
(complete inner product space) and self-adjoint Hamiltonian operator; these data are collected in
the `QuantumSystem` structure.

Two quantum systems are said to be "unitary equivalent" if there is a unitary bijection between
their respective Hilbert spaces which sends one Hamiltonian to the other under conjugation.
Unitary equivalent quantum systems are physically indestinguishable, as all operators, states,
matrix elements, probabilities, eigenvalues, etc. are in 1-1 correspondence.

## ii. Key results

Definitions
- `QuantumSystem` : Structure bundling together a choice of Hilbert space
    and self-adjoint Hamiltonian operator.
- `QuantumSystem.Hom` : Morphisms of quantum systems (Hamiltonian-intertwining contractions).
- `UnitaryRelation` : The unitary equivalence relation.

## iii. Table of contents

- A. Definition
- B. Creation from an essentially self-adjoint operator
- C. Zero
- D. Unitary equivalence

## iv. References

* None.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics

open LinearPMap

/-!
## A. Definition
-/

/-- A quantum system is identified by its Hilbert space and self-adjoint Hamiltonian operator. -/
structure QuantumSystem where
  /-- The complex Hilbert space. -/
  HS : Type*
  /-- The Hilbert space is a normed, commutative group. -/
  [instNormed : NormedAddCommGroup HS]
  /-- The Hilbert space is a complex inner product space. -/
  [instInner : InnerProductSpace ℂ HS]
  /-- The Hilbert space is complete. -/
  [instComplete : CompleteSpace HS]
  /-- The self-adjoint Hamiltonian operator. -/
  ℋ : HS →ₗ.[ℂ] HS
  ℋ_self_adjoint : IsSelfAdjoint ℋ

namespace QuantumSystem

attribute [instance] instNormed instInner instComplete

instance : CoeSort QuantumSystem (Type*) :=
  ⟨(·.HS)⟩

/-- The type of morphisms of the category of quantum systems;
contractions which preserve the Hamiltonian. -/
@[ext]
structure Hom (Q₁ Q₂ : QuantumSystem) where
  /-- The underlying continuous linear map. -/
  toCLM : Q₁ →L[ℂ] Q₂
  norm_le : ∀ x : Q₁, ‖toCLM x‖ ≤ ‖x‖
  domain_le : Q₁.ℋ.domain.map toCLM.toLinearMap ≤ Q₂.ℋ.domain
  toCLM_ℋ : ∀ ψ : Q₁.ℋ.domain,
    toCLM (Q₁.ℋ ψ) = Q₂.ℋ ⟨toCLM ψ, domain_le ⟨ψ, ψ.2, rfl⟩⟩

instance : CategoryTheory.Category QuantumSystem where
  Hom := Hom
  id M := ⟨.id ℂ M, fun _ ↦ le_rfl, by simp, by simp⟩
  comp f g := ⟨g.toCLM.comp f.toCLM, fun x ↦ (g.norm_le _).trans (f.norm_le x), by
    have : (g.toCLM.comp f.toCLM).toLinearMap =
      g.toCLM.toLinearMap.comp f.toCLM.toLinearMap := rfl
    grw [this, Submodule.map_comp, f.domain_le, g.domain_le],
    fun ψ ↦ by simp [Hom.toCLM_ℋ]⟩

instance (Q₁ Q₂ : QuantumSystem) : FunLike (Hom Q₁ Q₂) Q₁ Q₂ where
  coe f := f.toCLM
  coe_injective _ _ h := by
    ext x
    exact congrFun h x

instance : CategoryTheory.ConcreteCategory QuantumSystem Hom where
  hom f := f
  ofHom f := f

instance : CategoryTheory.HasForget₂ QuantumSystem SemiNormedGrp₁ where
  forget₂ :=
    { obj := fun Q ↦ SemiNormedGrp₁.of Q
      map := fun f ↦ SemiNormedGrp₁.mkHom
        { toFun := f.toCLM
          map_add' := map_add f.toCLM
          bound' := ⟨1, fun x ↦ by simpa using f.norm_le x⟩ }
        f.norm_le }

/-- Extract the underlying linear isometry equivalence from an isomorphism of quantum systems. -/
def linearIsometryEquivOfIso {Q₁ Q₂ : QuantumSystem} (i : Q₁ ≅ Q₂) : Q₁ ≃ₗᵢ[ℂ] Q₂ where
  toLinearEquiv :=
    { i.hom.toCLM.toLinearMap with
      invFun := i.inv.toCLM
      left_inv := fun x ↦ congrArg (fun f : Q₁ ⟶ Q₁ ↦ f.toCLM x) i.hom_inv_id
      right_inv := fun y ↦ congrArg (fun f : Q₂ ⟶ Q₂ ↦ f.toCLM y) i.inv_hom_id }
  norm_map' x := by
    change ‖i.hom.toCLM x‖ = ‖x‖
    refine le_antisymm (i.hom.norm_le x) ?_
    have hli : i.inv.toCLM (i.hom.toCLM x) = x :=
      congrArg (fun f : Q₁ ⟶ Q₁ ↦ f.toCLM x) i.hom_inv_id
    simpa [hli] using i.inv.norm_le (i.hom.toCLM x)

@[simp]
lemma linearIsometryEquivOfIso_apply {Q₁ Q₂ : QuantumSystem} (i : Q₁ ≅ Q₂) (x : Q₁) :
    linearIsometryEquivOfIso i x = i.hom x := rfl

lemma linearIsometryEquivOfIso_map_domain {Q₁ Q₂ : QuantumSystem} (i : Q₁ ≅ Q₂) :
    Q₁.ℋ.domain.map (linearIsometryEquivOfIso i).toLinearMap = Q₂.ℋ.domain :=
  le_antisymm i.hom.domain_le fun y hy ↦
    ⟨i.inv.toCLM y, i.inv.domain_le ⟨y, hy, rfl⟩,
      congrArg (fun f : Q₂ ⟶ Q₂ ↦ f.toCLM y) i.inv_hom_id⟩

/-- Construct an isomorphism of quantum systems from a linear isometry equivalence
  intertwining their Hamiltonians and mapping one domain onto the other. -/
def isoOfLinearIsometryEquiv {Q₁ Q₂ : QuantumSystem} (e : Q₁ ≃ₗᵢ[ℂ] Q₂)
    (h : Q₁.ℋ.domain.map e.toLinearMap = Q₂.ℋ.domain)
    (hℋ : ∀ ψ : Q₁.ℋ.domain, e (Q₁.ℋ ψ) = Q₂.ℋ ⟨e ψ, by simp [← h]⟩) : Q₁ ≅ Q₂ where
  hom := ⟨e.toLinearIsometry.toContinuousLinearMap, fun x ↦ (e.norm_map x).le, h.le, hℋ⟩
  inv :=
    { toCLM := e.symm.toLinearIsometry.toContinuousLinearMap
      norm_le := fun x ↦ (e.symm.norm_map x).le
      domain_le := by
        rintro _ ⟨y, hy, rfl⟩
        rcases h ▸ hy with ⟨x, hx, rfl⟩
        simpa using hx
      toCLM_ℋ := fun ⟨y, hy⟩ ↦ by
        have hψ₂ : e.symm y ∈ Q₁.ℋ.domain := by
          rcases h ▸ hy with ⟨x, hx, rfl⟩
          simpa using hx
        apply e.symm_apply_eq.mpr
        simpa using (hℋ ⟨e.symm y, hψ₂⟩).symm }
  hom_inv_id := by
    apply Hom.ext
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply Hom.ext
    ext x
    exact e.apply_symm_apply x

/-!
## B. Creation from an essentially self-adjoint operator

An essentially self-adjoint operator has a unique self-adjoint extension
(c.f. `IsEssentiallySelfAdjoint.unique_self_adjoint_extension`).
For this reason, a quantum system can be uniquely associated to an e.s.a. Hamiltonian operator.
-/

/-- Create a quantum system from a Hamiltonian operator which is merely
  essentially self-adjoint by taking its closure. -/
abbrev mkESA {HS : Type*} [NormedAddCommGroup HS] [InnerProductSpace ℂ HS] [CompleteSpace HS]
    {ℋ : HS →ₗ.[ℂ] HS} (hℋ : IsEssentiallySelfAdjoint ℋ) : QuantumSystem := ⟨HS, ℋ.closure, hℋ⟩

/-!
## C. Zero
-/

instance instZero : Zero QuantumSystem := ⟨PUnit, 0, adjoint_zero⟩

instance : Subsingleton (0 : QuantumSystem) := inferInstanceAs (Subsingleton PUnit)

instance (Q : QuantumSystem) : Unique ((0 : QuantumSystem) ⟶ Q) where
  default := ⟨0, fun _ ↦ by simp, by simp, fun _ ↦ by
    change 0 = Q.ℋ 0
    simp⟩
  uniq m := by
    apply Hom.ext
    ext x
    rw [Subsingleton.elim x 0]
    simp

instance (Q : QuantumSystem) : Unique (Q ⟶ (0 : QuantumSystem)) where
  default := ⟨0, fun _ ↦ by simp, by simp, fun _ ↦ Subsingleton.elim _ _⟩
  uniq m := by
    apply Hom.ext
    ext x
    exact Subsingleton.elim _ _

/-- The zero quantum system is a zero object in `QuantumSystem`. -/
lemma isZero_zero : CategoryTheory.Limits.IsZero (0 : QuantumSystem) :=
  ⟨fun _ ↦ ⟨inferInstance⟩, fun _ ↦ ⟨inferInstance⟩⟩

instance : CategoryTheory.Limits.HasZeroObject QuantumSystem :=
  ⟨0, isZero_zero⟩

/-!
## D. Unitary equivalence
-/

/-- The relation on quantum systems where `Q₁` is related to `Q₂` if there exists a linear isometry
  equivalence `e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS` between the respective Hilbert spaces satisfying
  `e ∘ Q₁.ℋ ∘ e.symm = Q₂.ℋ`. -/
abbrev UnitaryRelation (Q₁ Q₂ : QuantumSystem) : Prop :=
  CategoryTheory.IsIsomorphic Q₁ Q₂

/-- Two quantum systems are unitarily equivalent iff there is a linear isometry equivalence
  `e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS` intertwining their Hamiltonians and mapping one domain onto the other. -/
lemma unitaryRelation_iff (Q₁ Q₂ : QuantumSystem) :
    UnitaryRelation Q₁ Q₂ ↔
      ∃ (e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS) (h : Q₁.ℋ.domain.map e.toLinearMap = Q₂.ℋ.domain),
        ∀ ψ : Q₁.ℋ.domain, e (Q₁.ℋ ψ) = Q₂.ℋ ⟨e ψ, by simp [← h]⟩ :=
  ⟨fun ⟨i⟩ ↦ ⟨linearIsometryEquivOfIso i, linearIsometryEquivOfIso_map_domain i,
    fun ψ ↦ i.hom.toCLM_ℋ ψ⟩,
   fun ⟨e, h, hℋ⟩ ↦ ⟨isoOfLinearIsometryEquiv e h hℋ⟩⟩

/-- The setoid of quantum systems with `UnitaryRelation` for equivalence relation. -/
instance QuantumSystemSetoid : Setoid QuantumSystem :=
  CategoryTheory.isIsomorphicSetoid _

end QuantumSystem
end QuantumMechanics
end
