/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization.Symmetrized
public import Physlib.Mathematics.Fin
public import Mathlib.RingTheory.Flat.Basic
/-!
# The field strength in the local gauge field algebra

## i. Overview

The field strength and its covariant derivatives are built for an arbitrary realization of
the gauge bosons in `Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization`, as
families of derivative symbols over a family of gauge-field symbols. Here they are
specialized to the real algebra `LocalGaugeFieldAlgebra 𝔤` itself, whose symbols are its
own generators `∂_s A_μ^φ` (`derivA`).

Two facts make the specialization work. The symbols that the families carry are honest
iterated derivatives of their base values
(`iteratedCovDerivAdjoint_fieldStrength_derivA`), which turns the symbol-level recursion
of `iteratedCovDerivAdjoint` into the recursion `covDerivFieldStrength_cons` on elements
of the algebra. And the gauge law is not reproved: the complexified tower is the image of
the real one under `x ↦ 1 ⊗ₜ x`, which is injective and intertwines the two gauge actions,
so the law of the identity realization descends. The Lorentz law is proved directly from
the recursion.

Everything here is over `ℝ`. The complexification `ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤`
appears only as that bridge; it is never identified with the real algebra.

## ii. Key results

- `LocalGaugeFieldAlgebra.fieldStrength`, `LocalGaugeFieldAlgebra.covDerivFieldStrength` :
  the field strength `F_μν^φ` and its ordered covariant derivatives `∇_l F_μν^φ`.
- `LocalGaugeFieldAlgebra.repJet_covDerivFieldStrength_eval` : the gauge law, through the
  value of the jet alone.
- `LocalGaugeFieldAlgebra.repLorentzGroup_covDerivFieldStrength` : the Lorentz law.

## iii. Table of contents

- A. The derivative symbols of the real algebra
- B. The field strength and its covariant derivatives
- C. The derivative symbols of the covariant tower are iterated derivatives
- D. The gauge law, by descent from the complexification
- E. The Lorentz law

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

open TensorProduct Matrix MatrixGroups Lorentz
open GaugeAlgebraRealization (bracketFam commutatorFam bracketFamConv covDerivAdjoint
  iteratedCovDerivAdjoint)

namespace LocalGaugeFieldAlgebra

/-!

## A. The derivative symbols of the real algebra

-/

variable (𝔤) in
/-- The derivative symbols `∂_s A_μ^φ` of the local gauge field algebra, as a family over
  the derivative multiset `s` and the spacetime index `μ`: the iterated total derivative of
  the gauge-field generator. The field strength and its covariant derivatives are built
  out of this family. -/
noncomputable def derivA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] LocalGaugeFieldAlgebra 𝔤 :=
  (iteratedJetDeriv 𝔤 s).comp (ofA 𝔤 μ)

lemma derivA_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) : derivA 𝔤 s μ φ = iteratedJetDeriv 𝔤 s (ofA 𝔤 μ φ) := rfl

@[simp]
lemma derivA_zero (μ : Fin 1 ⊕ Fin 3) : derivA 𝔤 0 μ = ofA 𝔤 μ := rfl

/-- The derivative symbols are the iterated derivatives of the undifferentiated symbol. -/
lemma derivA_eq_iteratedJetDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) : derivA 𝔤 s μ φ = iteratedJetDeriv 𝔤 s (derivA 𝔤 0 μ φ) := rfl

/-- The complexified symbols `gaugeField` are the images of the real symbols. -/
lemma gaugeField_eq_one_tmul_derivA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) : gaugeField 𝔤 s μ φ = (1 : ℂ) ⊗ₜ[ℝ] derivA 𝔤 s μ φ := by
  rw [gaugeField_apply, iteratedD_complexJetDeriv_one_tmul]
  rfl

/-- Two algebra maps out of the local gauge field algebra agreeing on the derivative
  symbols `∂_s A_μ^φ` are equal. -/
lemma algHom_ext {B : Type} [Semiring B] [Algebra ℝ B] {f g : LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] B}
    (h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤),
      f (derivA 𝔤 s μ φ) = g (derivA 𝔤 s μ φ)) : f = g := by
  refine AlgHom.ext_of_adjoin_eq_top adjoin_iteratedJetDeriv_eq_top fun x hx => ?_
  obtain ⟨_, ⟨s, rfl⟩, _, ⟨μ, rfl⟩, φ, rfl⟩ := hx
  exact h s μ φ

/-!

## B. The field strength and its covariant derivatives

-/

variable (𝔤) in
/-- The field strength `F_μν = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆` of the local gauge field
  algebra: the underived field strength of the family of derivative symbols, in the
  conventions of `GaugeAlgebraRealization.fieldStrength`, where the bracket of the gauge
  algebra carries the physicists' factor of `i`. -/
noncomputable def fieldStrength (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] LocalGaugeFieldAlgebra 𝔤 :=
  GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν 0

/-- The field strength written in the generators of the algebra. -/
lemma fieldStrength_apply (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    fieldStrength 𝔤 μ ν φ = jetDeriv 𝔤 μ (ofA 𝔤 ν φ) - jetDeriv 𝔤 ν (ofA 𝔤 μ φ)
      + bracketFam (ofA 𝔤 μ) (ofA 𝔤 ν) φ := by
  rw [fieldStrength, GaugeAlgebraRealization.fieldStrength_zero,
    GaugeAlgebraRealization.commutator_eq_bracketFam]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, derivA_apply, iteratedJetDeriv_singleton,
    derivA_zero]

/-- The field strength is antisymmetric in its two covector indices. -/
lemma fieldStrength_swap (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength 𝔤 ν μ = - fieldStrength 𝔤 μ ν :=
  GaugeAlgebraRealization.fieldStrength_swap (derivA 𝔤) (fun _ _ _ _ _ _ => Commute.all _ _) μ ν 0

variable (𝔤) in
/-- The iterated covariant derivative `∇_{l₁} ⋯ ∇_{lₙ} F_μν` of the field strength along an
  ordered list of directions, with `∇_ρ F = ∂_ρ F + ⁅A_ρ, F⁆` the covariant derivative in
  the adjoint. Covariant derivatives do not commute, so the iteration is indexed by a list
  and not by a multiset; the empty list gives the field strength itself. -/
noncomputable def covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] LocalGaugeFieldAlgebra 𝔤 :=
  iteratedCovDerivAdjoint (derivA 𝔤) l (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν) 0

/-- Zero covariant derivatives: the field strength itself. -/
@[simp]
lemma covDerivFieldStrength_nil (μ ν : Fin 1 ⊕ Fin 3) :
    covDerivFieldStrength 𝔤 [] μ ν = fieldStrength 𝔤 μ ν := rfl

/-!

## C. The derivative symbols of the covariant tower are iterated derivatives

The families of `GaugeAlgebraRealization` carry the derivative symbols `∂_s F` of a
covariant expression as data. Here the Leibniz convolutions defining the derived brackets
really are the Leibniz rule of the total derivative, so those symbols are the iterated
total derivatives `∂_s` of the value at `0`.

-/

/-- The Leibniz rule of the iterated total derivative on a bracket of families: the
  antidiagonal convolution of the iterated derivatives of the two factors. -/
lemma iteratedJetDeriv_bracketFam (s : Multiset (Fin 1 ⊕ Fin 3))
    (f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] LocalGaugeFieldAlgebra 𝔤) (φ : Module.Dual ℝ 𝔤) :
    iteratedJetDeriv 𝔤 s (bracketFam f g φ) = (s.antidiagonal.map fun p =>
      bracketFam (iteratedJetDeriv 𝔤 p.1 ∘ₗ f) (iteratedJetDeriv 𝔤 p.2 ∘ₗ g) φ).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [iteratedJetDeriv_zero, LinearMap.id_apply, Multiset.antidiagonal_zero,
      Multiset.map_singleton, Multiset.sum_singleton, LinearMap.id_comp]
  | cons κ s ih =>
    have hterm : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
        jetDeriv 𝔤 κ (bracketFam (iteratedJetDeriv 𝔤 p.1 ∘ₗ f) (iteratedJetDeriv 𝔤 p.2 ∘ₗ g) φ)
          = bracketFam (iteratedJetDeriv 𝔤 (κ ::ₘ p.1) ∘ₗ f) (iteratedJetDeriv 𝔤 p.2 ∘ₗ g) φ
            + bracketFam (iteratedJetDeriv 𝔤 p.1 ∘ₗ f)
              (iteratedJetDeriv 𝔤 (κ ::ₘ p.2) ∘ₗ g) φ := by
      intro p
      rw [← LinearMap.comp_apply (jetDeriv 𝔤 κ),
        GaugeAlgebraRealization.bracketFam_derivation _ (jetDeriv_mul κ), LinearMap.add_apply,
        iteratedJetDeriv_cons, iteratedJetDeriv_cons, LinearMap.comp_assoc,
        LinearMap.comp_assoc]
    rw [iteratedJetDeriv_cons, LinearMap.comp_apply, ih, map_multiset_sum, Multiset.map_map]
    simp only [Function.comp_def]
    rw [Multiset.map_congr rfl fun p _ => hterm p, Multiset.sum_map_add,
      Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map]
    simp only [Function.comp_def, Prod.map, id_eq]
    abel

/-- If a family consists of the iterated derivatives of its base value, so does its derived
  bracket against the gauge field: the Leibniz convolution is the iterated derivative of the
  bracket of the base values. -/
lemma bracketFamConv_derivA (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ]
      LocalGaugeFieldAlgebra 𝔤)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤),
      F s φ = iteratedJetDeriv 𝔤 s (F 0 φ))
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    bracketFamConv (derivA 𝔤) ρ F s φ
      = iteratedJetDeriv 𝔤 s (bracketFam (ofA 𝔤 ρ) (F 0) φ) := by
  have hF' : ∀ t, F t = iteratedJetDeriv 𝔤 t ∘ₗ F 0 := fun t => LinearMap.ext (hF t)
  rw [iteratedJetDeriv_bracketFam, bracketFamConv, Multiset.sum_linearMap_apply,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, hF' p.2]
  rfl

/-- The covariant derivative of a family of iterated derivatives is again a family of
  iterated derivatives. -/
lemma covDerivAdjoint_derivA (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ]
      LocalGaugeFieldAlgebra 𝔤)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤),
      F s φ = iteratedJetDeriv 𝔤 s (F 0 φ))
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    covDerivAdjoint (derivA 𝔤) F ρ s φ
      = iteratedJetDeriv 𝔤 s (covDerivAdjoint (derivA 𝔤) F ρ 0 φ) := by
  have h1 : F (ρ ::ₘ s) φ = iteratedJetDeriv 𝔤 s (F (ρ ::ₘ 0) φ) := by
    rw [hF (ρ ::ₘ s), hF (ρ ::ₘ 0), iteratedJetDeriv_cons', iteratedJetDeriv_cons',
      iteratedJetDeriv_zero, LinearMap.id_comp, LinearMap.comp_apply]
  rw [GaugeAlgebraRealization.covDerivAdjoint_apply,
    GaugeAlgebraRealization.covDerivAdjoint_apply, map_add, h1, bracketFamConv_derivA F hF,
    bracketFamConv_derivA F hF ρ 0, iteratedJetDeriv_zero, LinearMap.id_apply]

/-- The derivative symbols of the field strength are the iterated derivatives of the field
  strength. -/
lemma fieldStrength_derivA (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ 𝔤) :
    GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν s φ
      = iteratedJetDeriv 𝔤 s (fieldStrength 𝔤 μ ν φ) := by
  have hd : ∀ σ τ : Fin 1 ⊕ Fin 3,
      derivA 𝔤 (σ ::ₘ s) τ φ = iteratedJetDeriv 𝔤 s (derivA 𝔤 (σ ::ₘ 0) τ φ) := by
    intro σ τ
    rw [derivA_apply, derivA_apply, iteratedJetDeriv_cons', iteratedJetDeriv_cons',
      iteratedJetDeriv_zero, LinearMap.id_comp, LinearMap.comp_apply]
  have hcomm : ∀ t, commutatorFam (derivA 𝔤) μ ν t
      = bracketFamConv (derivA 𝔤) μ (fun r => derivA 𝔤 r ν) t := fun t => rfl
  rw [fieldStrength, GaugeAlgebraRealization.fieldStrength_apply,
    GaugeAlgebraRealization.fieldStrength_apply, map_add, map_sub, hd μ ν, hd ν μ, hcomm,
    hcomm, bracketFamConv_derivA _ (fun _ _ => rfl), bracketFamConv_derivA _ (fun _ _ => rfl),
    iteratedJetDeriv_zero, LinearMap.id_apply]

/-- The derivative symbols of the covariant derivatives of the field strength are the
  iterated derivatives of their base values. -/
lemma iteratedCovDerivAdjoint_fieldStrength_derivA (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    iteratedCovDerivAdjoint (derivA 𝔤) l (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν)
        s φ
      = iteratedJetDeriv 𝔤 s (covDerivFieldStrength 𝔤 l μ ν φ) := by
  induction l generalizing s φ with
  | nil => exact fieldStrength_derivA μ ν s φ
  | cons ρ l ih => exact covDerivAdjoint_derivA _ ih ρ s φ

/-- The covariant derivative `∇_ρ F = ∂_ρ F + ⁅A_ρ, F⁆` peeled off the front of the list:
  the recursion on elements of the algebra. -/
lemma covDerivFieldStrength_cons (ρ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    covDerivFieldStrength 𝔤 (ρ :: l) μ ν φ
      = jetDeriv 𝔤 ρ (covDerivFieldStrength 𝔤 l μ ν φ)
        + bracketFam (ofA 𝔤 ρ) (covDerivFieldStrength 𝔤 l μ ν) φ := by
  show covDerivAdjoint (derivA 𝔤) (iteratedCovDerivAdjoint (derivA 𝔤) l
    (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν)) ρ 0 φ = _
  rw [GaugeAlgebraRealization.covDerivAdjoint_apply, iteratedCovDerivAdjoint_fieldStrength_derivA,
    bracketFamConv_derivA _ (iteratedCovDerivAdjoint_fieldStrength_derivA l μ ν),
    iteratedJetDeriv_zero, LinearMap.id_apply, iteratedJetDeriv_cons', iteratedJetDeriv_zero,
    LinearMap.id_comp]
  rfl

/-!

## D. The gauge law, by descent from the complexification

The gauge law is proved in
`Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization` for a realization in a
complex algebra, and `GaugeAlgebraRealization.id` realizes the real algebra in its
complexification. Injectivity of `x ↦ 1 ⊗ₜ x` reads the real law off the complex one; no
reality argument beyond that is involved.

-/

/-- The complexified covariant tower of the identity realization is the image of the real
  one. -/
lemma one_tmul_iteratedCovDerivAdjoint_fieldStrength (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    (1 : ℂ) ⊗ₜ[ℝ] iteratedCovDerivAdjoint (derivA 𝔤) l
        (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν) s φ
      = iteratedCovDerivAdjoint (gaugeField 𝔤) l
        (GaugeAlgebraRealization.fieldStrength (gaugeField 𝔤) μ ν) s φ := by
  set ι : LocalGaugeFieldAlgebra 𝔤 →ₗ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤 :=
    (Algebra.TensorProduct.includeRight :
      LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤).toLinearMap with hι
  have hmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y =>
    map_mul (Algebra.TensorProduct.includeRight :
      LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) x y
  have hA : (fun p ρ => ι ∘ₗ derivA 𝔤 p ρ) = gaugeField 𝔤 := by
    funext p ρ
    exact LinearMap.ext fun φ => (gaugeField_eq_one_tmul_derivA p ρ φ).symm
  have key := congrFun (GaugeAlgebraRealization.iteratedCovDerivAdjoint_map ι hmul (derivA 𝔤) l
    (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν)) s
  rw [show (fun p => ι ∘ₗ GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν p)
      = GaugeAlgebraRealization.fieldStrength (fun p ρ => ι ∘ₗ derivA 𝔤 p ρ) μ ν from
      funext fun p => (GaugeAlgebraRealization.fieldStrength_map ι hmul _ μ ν p).symm, hA] at key
  exact (LinearMap.congr_fun key φ).symm

/-- The gauge law of the covariant derivatives of the field strength at every derivative
  order: a jet acts by the Leibniz convolution of the dual adjoint Taylor coefficients of
  `U⁻¹` against lower derivative symbols, with no Maurer–Cartan shift. -/
theorem repJet_iteratedCovDerivAdjoint_fieldStrength (U : GJ) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    repJet jets U (iteratedCovDerivAdjoint (derivA 𝔤) l
        (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν) s φ)
      = (s.antidiagonal.map fun p => iteratedCovDerivAdjoint (derivA 𝔤) l
          (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν) p.2
          (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum := by
  -- `x ↦ 1 ⊗ₜ x` is injective: `ℝ → ℂ` is injective and every real module is flat.
  apply Module.Flat.tensorProduct_mk_injective ℝ _ ℂ
  simp only [TensorProduct.mk_apply]
  rw [← complexRepJet_tmul, one_tmul_iteratedCovDerivAdjoint_fieldStrength, Multiset.tmul_sum,
    Multiset.map_map]
  refine (GaugeAlgebraRealization.transformsInAdjoint_iteratedCovDerivAdjoint
    (GaugeAlgebraRealization.id jets) l μ ν U φ s).trans ?_
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  exact (one_tmul_iteratedCovDerivAdjoint_fieldStrength l μ ν p.2 _).symm

/-- The gauge law of the covariant derivatives of the field strength: a jet acts through
  the zeroth dual adjoint Taylor coefficient of `U⁻¹` on the adjoint index alone. -/
theorem repJet_covDerivFieldStrength (U : GJ) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repJet jets U (covDerivFieldStrength 𝔤 l μ ν φ)
      = covDerivFieldStrength 𝔤 l μ ν (jets.adjointDualCoeff U⁻¹ 0 φ) := by
  rw [covDerivFieldStrength]
  simpa only [Multiset.antidiagonal_zero, Multiset.map_singleton, Multiset.sum_singleton]
    using repJet_iteratedCovDerivAdjoint_fieldStrength (jets := jets) U l μ ν 0 φ

/-- On the covariant derivatives of the field strength the local gauge action factors
  through evaluation: a jet `U` acts through the dual base-point adjoint action of the
  value `jets.eval U⁻¹` of its inverse, and the derivatives of the jet are not seen. The
  covariant expressions are gauge covariant, not gauge invariant. -/
theorem repJet_covDerivFieldStrength_eval (U : GJ) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repJet jets U (covDerivFieldStrength 𝔤 l μ ν φ)
      = covDerivFieldStrength 𝔤 l μ ν ((jets.adjointValue (jets.eval U⁻¹)).dualMap φ) := by
  rw [repJet_covDerivFieldStrength, jets.adjointDualCoeff_zero]

/-- The field strength transforms in the adjoint. -/
lemma repJet_fieldStrength (U : GJ) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repJet jets U (fieldStrength 𝔤 μ ν φ)
      = fieldStrength 𝔤 μ ν ((jets.adjointValue (jets.eval U⁻¹)).dualMap φ) :=
  repJet_covDerivFieldStrength_eval U [] μ ν φ

/-!

## E. The Lorentz law

-/

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => ((SL2C.toLorentzGroup Λ).1 b a : ℝ)

/-- The Lorentz action on the gauge-field generator, as a linear map. -/
lemma repLorentzGroup_comp_ofA (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    (repLorentzGroup 𝔤 Λ) ∘ₗ ofA 𝔤 μ = ∑ a, L[Λ] a μ • ofA 𝔤 a :=
  LinearMap.ext fun φ => by
    simp only [LinearMap.comp_apply, repLorentzGroup_ofA, LinearMap.sum_apply,
      LinearMap.smul_apply]

/-- The Lorentz law of the derivative symbols, read off the complexified law
  `repLorentz_gaugeField` along the injective `x ↦ 1 ⊗ₜ x`. -/
lemma repLorentzGroup_derivA (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repLorentzGroup 𝔤 Λ (derivA 𝔤 (List.ofFn l) μ φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i)) •
          ∑ a, L[Λ] a μ • derivA 𝔤 (List.ofFn p) a φ := by
  -- `x ↦ 1 ⊗ₜ x` is injective: `ℝ → ℂ` is injective and every real module is flat.
  apply Module.Flat.tensorProduct_mk_injective ℝ _ ℂ
  simp only [TensorProduct.mk_apply]
  rw [← complexRepLorentzGroup_tmul, ← gaugeField_eq_one_tmul_derivA, repLorentz_gaugeField,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_sum, ← Complex.ofReal_prod,
    show (((∏ i, L[Λ] (p i) (l i) : ℝ)) : ℂ) = algebraMap ℝ ℂ (∏ i, L[Λ] (p i) (l i)) from rfl,
    algebraMap_smul]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [TensorProduct.tmul_smul, gaugeField_eq_one_tmul_derivA,
    show ((L[Λ] a μ : ℝ) : ℂ) = algebraMap ℝ ℂ (L[Λ] a μ) from rfl, algebraMap_smul]

/-- The Lorentz action passes through the bracket of a gauge-field generator against a
  family, mixing the covector index of the generator. -/
lemma repLorentzGroup_bracketFam_ofA (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (F : Module.Dual ℝ 𝔤 →ₗ[ℝ] LocalGaugeFieldAlgebra 𝔤) (φ : Module.Dual ℝ 𝔤) :
    repLorentzGroup 𝔤 Λ (bracketFam (ofA 𝔤 ρ) F φ)
      = ∑ a, L[Λ] a ρ • bracketFam (ofA 𝔤 a) ((repLorentzGroup 𝔤 Λ) ∘ₗ F) φ := by
  rw [← LinearMap.comp_apply,
    ← GaugeAlgebraRealization.bracketFam_map _ (repLorentzGroup_apply_mul Λ),
    repLorentzGroup_comp_ofA, GaugeAlgebraRealization.bracketFam_finset_sum_left,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GaugeAlgebraRealization.bracketFam_smul_left, LinearMap.smul_apply]

/-- The Lorentz law of the field strength: both covector indices mix by the columns of the
  Lorentz matrix, the adjoint index is untouched. -/
lemma repLorentzGroup_fieldStrength (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repLorentzGroup 𝔤 Λ (fieldStrength 𝔤 μ ν φ)
      = ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • fieldStrength 𝔤 a b φ := by
  have hder : ∀ σ τ : Fin 1 ⊕ Fin 3, repLorentzGroup 𝔤 Λ (jetDeriv 𝔤 σ (ofA 𝔤 τ φ))
      = ∑ a, L[Λ] a σ • ∑ b, L[Λ] b τ • jetDeriv 𝔤 a (ofA 𝔤 b φ) := by
    intro σ τ
    rw [repLorentzGroup_jetDeriv]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [repLorentzGroup_ofA, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul]
  have hswap : ∑ a, L[Λ] a ν • ∑ b, L[Λ] b μ • jetDeriv 𝔤 a (ofA 𝔤 b φ)
      = ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • jetDeriv 𝔤 b (ofA 𝔤 a φ) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  have hbr : repLorentzGroup 𝔤 Λ (bracketFam (ofA 𝔤 μ) (ofA 𝔤 ν) φ)
      = ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • bracketFam (ofA 𝔤 a) (ofA 𝔤 b) φ := by
    rw [repLorentzGroup_bracketFam_ofA, Finset.sum_congr rfl fun a _ => by
      rw [repLorentzGroup_comp_ofA, GaugeAlgebraRealization.bracketFam_finset_sum_right,
        LinearMap.sum_apply, Finset.sum_congr rfl fun b _ => by
          rw [GaugeAlgebraRealization.bracketFam_smul_right, LinearMap.smul_apply]]]
  rw [fieldStrength_apply, map_add, map_sub, hder, hder, hswap, hbr]
  simp only [fieldStrength_apply, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

/-- The Lorentz law of the covariant derivatives of the field strength: every covariant
  slot and both covector indices of the field strength mix by the columns of the Lorentz
  matrix, the adjoint index is untouched. -/
theorem repLorentzGroup_covDerivFieldStrength (Λ : SL(2,ℂ)) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repLorentzGroup 𝔤 Λ (covDerivFieldStrength 𝔤 (List.ofFn l) μ ν φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i)) •
          ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • covDerivFieldStrength 𝔤 (List.ofFn p) a b φ := by
  induction n generalizing φ with
  | zero =>
    rw [List.ofFn_zero, covDerivFieldStrength_nil, repLorentzGroup_fieldStrength,
      Fintype.sum_unique (ι := Fin 0 → (Fin 1 ⊕ Fin 3))]
    simp
  | succ n ih =>
    have hT : (repLorentzGroup 𝔤 Λ) ∘ₗ covDerivFieldStrength 𝔤 (List.ofFn fun i => l i.succ) μ ν
        = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i.succ)) •
          ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • covDerivFieldStrength 𝔤 (List.ofFn p) a b :=
      LinearMap.ext fun φ => by
        simp only [LinearMap.comp_apply, ih (fun i => l i.succ), LinearMap.sum_apply,
          LinearMap.smul_apply]
    have hcov : ∀ (c : Fin 1 ⊕ Fin 3) (p : Fin n → (Fin 1 ⊕ Fin 3)),
        ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
            covDerivFieldStrength 𝔤 (List.ofFn (Fin.cons c p)) a b φ
          = jetDeriv 𝔤 c (∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
              covDerivFieldStrength 𝔤 (List.ofFn p) a b φ)
            + bracketFam (ofA 𝔤 c) (∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
              covDerivFieldStrength 𝔤 (List.ofFn p) a b) φ := by
      intro c p
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, covDerivFieldStrength_cons,
        map_sum, map_smul, GaugeAlgebraRealization.bracketFam_finset_sum_right,
        GaugeAlgebraRealization.bracketFam_smul_right, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_add, Finset.sum_add_distrib]
    rw [List.ofFn_succ, covDerivFieldStrength_cons, map_add, repLorentzGroup_jetDeriv,
      repLorentzGroup_bracketFam_ofA, hT, ← Finset.sum_add_distrib,
      Physlib.Fin.sum_pi_succ_prod_smul (fun i b => L[Λ] b (l i))]
    simp only [mul_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih (fun i => l i.succ), map_sum (jetDeriv 𝔤 c),
      GaugeAlgebraRealization.bracketFam_finset_sum_right, LinearMap.sum_apply,
      Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hcov c p]
    simp only [smul_add, map_smul, GaugeAlgebraRealization.bracketFam_smul_right,
      LinearMap.smul_apply]

end LocalGaugeFieldAlgebra
