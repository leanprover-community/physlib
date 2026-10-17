/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.Complex.Basic

/-!

# The GNS representation of a state on a unital `*`-algebra

A state on a unital complex `*`-algebra defines a Hilbert space, the completion of the algebra for
the inner product `⟨a, b⟩ = ω(a* b)`, on which a group of state preserving `*`-automorphisms acts
unitarily.

## i. Overview

A *state* on a unital complex `*`-algebra `A` is a linear functional `ω` with `ω(1) = 1`,
`ω(a*) = conj ω(a)`, and `ω(a* a) ≥ 0` for every `a`. The form `⟨a, b⟩ = ω(a* b)` is a positive
semidefinite inner product on `A`, and the quotient by its null vectors, completed, is the
*GNS Hilbert space*. No norm on `A` is needed, so the construction applies to algebras that are
not complete, such as the quasi-local algebra of an infinite lattice before completion.

A `*`-automorphism `σ` of `A` that preserves `ω` preserves the inner product, so it defines an
isometry on the pre-Hilbert space, and a unitary operator on the GNS space. A group of such
automorphisms is represented unitarily, and each unitary fixes the class of the unit, the
cyclic vector.

## ii. Key results

- `AlgState` : a state on a unital `*`-algebra.
- `AlgState.GNS` : the Hilbert space of a state.
- `AlgState.gnsAut` : the unitary implementing a state preserving automorphism.
- `AlgState.gnsRep` : the unitary representation of a group of state preserving automorphisms.

## iii. Table of contents

- A. States and the pre-Hilbert space
- B. Implementing automorphisms
- C. Representations of groups
- D. Composition and commutation of implementing operators

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 2.3.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace

/-! ## A. States and the pre-Hilbert space -/

/-- A state on a unital complex `*`-algebra: a normalized, Hermitian, positive linear
functional. -/
structure AlgState (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] where
  /-- The linear functional. -/
  toLinearMap : A →ₗ[ℂ] ℂ
  /-- The state is normalized. -/
  map_one' : toLinearMap 1 = 1
  /-- The state is Hermitian. -/
  map_star' : ∀ a, toLinearMap (star a) = star (toLinearMap a)
  /-- The state is positive. -/
  nonneg' : ∀ a, 0 ≤ toLinearMap (star a * a)

namespace AlgState

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

instance : FunLike (AlgState A) A ℂ where
  coe ω := ω.toLinearMap
  coe_injective ω ω' h := by
    cases ω; cases ω'
    simp only at h
    congr
    exact LinearMap.ext (congrFun h)

variable (ω : AlgState A)

lemma map_one : ω 1 = 1 := ω.map_one'

lemma map_star (a : A) : ω (star a) = star (ω a) := ω.map_star' a

lemma nonneg (a : A) : 0 ≤ ω (star a * a) := ω.nonneg' a

lemma map_add (a b : A) : ω (a + b) = ω a + ω b := ω.toLinearMap.map_add a b

lemma map_smul (c : ℂ) (a : A) : ω (c • a) = c * ω a := ω.toLinearMap.map_smul c a

/-- The algebra with the inner product induced by a state, before completion. -/
@[nolint unusedArguments]
def PreGNS (_ω : AlgState A) := A

instance : AddCommGroup ω.PreGNS := inferInstanceAs (AddCommGroup A)
instance : Module ℂ ω.PreGNS := inferInstanceAs (Module ℂ A)

/-- The identification of the algebra with its pre-Hilbert space. -/
def toPre : A ≃ₗ[ℂ] ω.PreGNS := LinearEquiv.refl ℂ _

/-- The identification of the pre-Hilbert space with the algebra. -/
def ofPre : ω.PreGNS ≃ₗ[ℂ] A := ω.toPre.symm

/-- The inner product `⟨a, b⟩ = ω (a* b)`. -/
noncomputable abbrev core : PreInnerProductSpace.Core ℂ ω.PreGNS where
  inner a b := ω (star (ω.ofPre a) * ω.ofPre b)
  conj_inner_symm x y := by
    change star (ω (star (ω.ofPre y) * ω.ofPre x)) = ω (star (ω.ofPre x) * ω.ofPre y)
    rw [← ω.map_star, star_mul, star_star]
  re_inner_nonneg x := (Complex.nonneg_iff.mp (ω.nonneg (ω.ofPre x))).1
  add_left x y z := by
    change ω (star (ω.ofPre (x + y)) * ω.ofPre z) =
      ω (star (ω.ofPre x) * ω.ofPre z) + ω (star (ω.ofPre y) * ω.ofPre z)
    rw [_root_.map_add, star_add, add_mul, ω.map_add]
  smul_left x y r := by
    change ω (star (ω.ofPre (r • x)) * ω.ofPre y) = star r * ω (star (ω.ofPre x) * ω.ofPre y)
    rw [_root_.map_smul, star_smul, smul_mul_assoc, ω.map_smul]

noncomputable instance : SeminormedAddCommGroup ω.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := ω.core)

noncomputable instance : InnerProductSpace ℂ ω.PreGNS := InnerProductSpace.ofCore ω.core

lemma inner_pre (a b : ω.PreGNS) : ⟪a, b⟫_ℂ = ω (star (ω.ofPre a) * ω.ofPre b) := rfl

/-- The **GNS Hilbert space** of a state: the completion of the algebra for the inner product
`⟨a, b⟩ = ω (a* b)`.   -/
abbrev GNS : Type _ := UniformSpace.Completion ω.PreGNS

/-! ## B. Implementing automorphisms -/

variable {ω} (σ : A ≃⋆ₐ[ℂ] A)

variable (ω) in
/-- The map `[a] ↦ [σ a]` on the pre-Hilbert space. -/
def preAut : ω.PreGNS →ₗ[ℂ] ω.PreGNS :=
  ω.toPre.toLinearMap ∘ₗ σ.toAlgEquiv.toLinearMap ∘ₗ ω.ofPre.toLinearMap

lemma ofPre_preAut (x : ω.PreGNS) : ω.ofPre (preAut ω σ x) = σ (ω.ofPre x) := rfl

lemma inner_preAut (hσ : ∀ a, ω (σ a) = ω a) (x y : ω.PreGNS) :
    ⟪preAut ω σ x, preAut ω σ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_pre, inner_pre, ofPre_preAut, ofPre_preAut, ← StarHomClass.map_star σ,
    ← _root_.map_mul σ]
  exact hσ _

lemma norm_preAut (hσ : ∀ a, ω (σ a) = ω a) (x : ω.PreGNS) : ‖preAut ω σ x‖ = ‖x‖ := by
  have h := inner_preAut σ hσ x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖preAut ω σ x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (preAut ω σ x), norm_nonneg x]

/-- The automorphism as a bounded operator on the pre-Hilbert space. -/
def preAutCLM (hσ : ∀ a, ω (σ a) = ω a) : ω.PreGNS →L[ℂ] ω.PreGNS :=
  (preAut ω σ).mkContinuous 1 fun x => by rw [one_mul, norm_preAut σ hσ]

/-- **The operator on the GNS space implementing a state preserving automorphism.** -/
def gnsAut (hσ : ∀ a, ω (σ a) = ω a) : ω.GNS →L[ℂ] ω.GNS := (preAutCLM σ hσ).completion

lemma gnsAut_coe (hσ : ∀ a, ω (σ a) = ω a) (x : ω.PreGNS) :
    gnsAut σ hσ (x : ω.GNS) = ((preAut ω σ x : ω.PreGNS) : ω.GNS) := by
  simp [gnsAut, preAutCLM]

lemma inner_gnsAut (hσ : ∀ a, ω (σ a) = ω a) (x y : ω.GNS) :
    ⟪gnsAut σ hσ x, gnsAut σ hσ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq ((continuous_inner.comp ((gnsAut σ hσ).continuous.prodMap
      (gnsAut σ hσ).continuous)).comp continuous_id) continuous_inner
  | ih x y =>
    rw [gnsAut_coe, gnsAut_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, inner_preAut σ hσ]

/-! ## C. Representations of groups -/

section Group

variable {Γ : Type*} [Group Γ] {α : Γ →* (A ≃⋆ₐ[ℂ] A)} (hα : ∀ g a, ω (α g a) = ω a)

include hα

lemma gnsAut_mul (g h : Γ) :
    gnsAut (α (g * h)) (hα (g * h)) = gnsAut (α g) (hα g) * gnsAut (α h) (hα h) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (gnsAut (α (g * h)) (hα (g * h))).continuous
      (gnsAut (α g) (hα g) * gnsAut (α h) (hα h)).continuous
  | ih x =>
    rw [mul_apply_eq_comp, gnsAut_coe, gnsAut_coe, gnsAut_coe]
    congr 1
    change ω.toPre (α (g * h) (ω.ofPre x)) = ω.toPre (α g (α h (ω.ofPre x)))
    rw [map_mul]
    rfl

lemma gnsAut_one : gnsAut (α 1) (hα 1) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (gnsAut (α 1) (hα 1)).continuous continuous_id
  | ih x =>
    rw [gnsAut_coe]
    simp only [one_apply_eq_self]
    congr 1
    change ω.toPre (α 1 (ω.ofPre x)) = x
    rw [_root_.map_one]
    rfl

lemma star_gnsAut_mul_gnsAut (g : Γ) :
    star (gnsAut (α g) (hα g)) * gnsAut (α g) (hα g) = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  exact (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp
    (fun x y => inner_gnsAut (α g) (hα g) x y)

lemma star_gnsAut (g : Γ) : star (gnsAut (α g) (hα g)) = gnsAut (α g⁻¹) (hα g⁻¹) := by
  have h1 : gnsAut (α g) (hα g) * gnsAut (α g⁻¹) (hα g⁻¹) = 1 := by
    rw [← gnsAut_mul hα, mul_inv_cancel, gnsAut_one hα]
  calc star (gnsAut (α g) (hα g))
      = star (gnsAut (α g) (hα g)) * (gnsAut (α g) (hα g) * gnsAut (α g⁻¹) (hα g⁻¹)) := by
        rw [h1, mul_one]
    _ = gnsAut (α g⁻¹) (hα g⁻¹) := by rw [← mul_assoc, star_gnsAut_mul_gnsAut hα, one_mul]

/-- **The unitary operator on the GNS space implementing a symmetry** of the state. -/
def gnsUnitary (g : Γ) : unitary (ω.GNS →L[ℂ] ω.GNS) :=
  ⟨gnsAut (α g) (hα g), by
    rw [Unitary.mem_iff]
    refine ⟨star_gnsAut_mul_gnsAut hα g, ?_⟩
    rw [star_gnsAut hα g, ← gnsAut_mul hα, mul_inv_cancel, gnsAut_one hα]⟩

/-- **The unitary representation of a group of symmetries on the GNS space of an invariant
state.**   -/
def gnsRep : Γ →* unitary (ω.GNS →L[ℂ] ω.GNS) where
  toFun := gnsUnitary hα
  map_one' := Subtype.ext (gnsAut_one hα)
  map_mul' g h := Subtype.ext (gnsAut_mul hα g h)

/-- The cyclic vector: the class of the unit. -/
def cyclicVector : ω.GNS := ((ω.toPre 1 : ω.PreGNS) : ω.GNS)

end Group

/-! ## D. Composition and commutation of implementing operators -/

section Comp

variable {σ τ : A ≃⋆ₐ[ℂ] A} (hσ : ∀ a, ω (σ a) = ω a) (hτ : ∀ a, ω (τ a) = ω a)

include hσ hτ

/-- The operator implementing a composite of automorphisms is the composite of the operators. -/
lemma gnsAut_comp :
    gnsAut (σ * τ) (fun a => by rw [StarAlgEquiv.mul_apply, hσ, hτ]) =
      gnsAut σ hσ * gnsAut τ hτ := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (gnsAut (σ * τ) _).continuous (gnsAut σ hσ * gnsAut τ hτ).continuous
  | ih x =>
    rw [mul_apply_eq_comp, gnsAut_coe, gnsAut_coe, gnsAut_coe]
    rfl

end Comp

/-- Equal automorphisms are implemented by equal operators. -/
lemma gnsAut_congr {σ τ : A ≃⋆ₐ[ℂ] A} (h : σ = τ) (hσ : ∀ a, ω (σ a) = ω a)
    (hτ : ∀ a, ω (τ a) = ω a) : gnsAut σ hσ = gnsAut τ hτ := by
  subst h; rfl

/-- Commuting automorphisms are implemented by commuting operators. -/
lemma gnsAut_commute {σ τ : A ≃⋆ₐ[ℂ] A} (hσ : ∀ a, ω (σ a) = ω a) (hτ : ∀ a, ω (τ a) = ω a)
    (h : σ * τ = τ * σ) : Commute (gnsAut σ hσ) (gnsAut τ hτ) := by
  have h1 := gnsAut_comp hσ hτ
  have h2 := gnsAut_comp hτ hσ
  have h3 := gnsAut_congr h (fun a => by rw [StarAlgEquiv.mul_apply, hσ, hτ])
    (fun a => by rw [StarAlgEquiv.mul_apply, hτ, hσ])
  exact h1.symm.trans (h3.trans h2)


end AlgState

end ProbabilisticTheory

end
