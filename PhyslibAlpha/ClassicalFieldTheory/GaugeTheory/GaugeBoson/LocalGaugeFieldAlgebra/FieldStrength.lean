/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeField
public import Mathlib.RingTheory.Flat.Basic
/-!
# The field strength in the local gauge field algebra

The field strength `F_μν` of the gauge bosons and its covariant derivatives, with their gauge
and Lorentz laws.

## i. Overview

The field strength and its covariant derivatives are built for an arbitrary family of
gauge-field symbols in an arbitrary algebra in the directory
`PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/GaugeBoson/AdjointFamily`, as
families of derivative symbols. Here they are
specialized to the real algebra `LocalGaugeFieldAlgebra G` itself, whose symbols are its
own generators `∂_s A_μ^φ` (`derivA`).

Two facts make the specialization work. The symbols that the families carry are honest
iterated derivatives of their base values
(`iteratedCovDerivAdjoint_fieldStrength_derivA`), which turns the symbol-level recursion
of `iteratedCovDerivAdjoint` into the recursion `covDerivFieldStrength_cons` on elements
of the algebra. And the gauge law is not reproved: the complexified tower is the image of
the real one under `x ↦ 1 ⊗ₜ x`, which is injective and intertwines the two gauge actions,
so the law of the complexified symbols descends. The Lorentz law is proved directly from
the recursion.

Everything here is over `ℝ`. The complexification `ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G`
appears only as that bridge, and it is never identified with the real algebra.

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

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

open TensorProduct Matrix MatrixGroups Lorentz
open GaugeBoson (bracketFam commutatorFam bracketFamConv covDerivAdjoint
  iteratedCovDerivAdjoint)

namespace LocalGaugeFieldAlgebra

/-!

## A. The derivative symbols of the real algebra

-/

variable (G) in
/-- The derivative symbols `∂_s A_μ^φ` of the local gauge field algebra, as a family over
  the derivative multiset `s` and the spacetime index `μ`, the iterated total derivative of
  the gauge-field generator. The field strength and its covariant derivatives are built
  out of this family. -/
noncomputable def derivA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] LocalGaugeFieldAlgebra G :=
  (iteratedJetDeriv G s).comp (ofA G μ)

lemma derivA_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) : derivA G s μ φ = iteratedJetDeriv G s (ofA G μ φ) := rfl

@[simp]
lemma derivA_zero (μ : Fin 1 ⊕ Fin 3) : derivA G 0 μ = ofA G μ := rfl

/-- The complexified symbols `gaugeField` are the images of the real symbols. -/
lemma gaugeField_eq_one_tmul_derivA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) : gaugeField G s μ φ = (1 : ℂ) ⊗ₜ[ℝ] derivA G s μ φ := by
  rw [gaugeField_apply, iteratedD_complexJetDeriv_one_tmul]
  rfl

/-- Two algebra maps out of the local gauge field algebra agreeing on the derivative
  symbols `∂_s A_μ^φ` are equal. -/
lemma algHom_ext {B : Type} [Semiring B] [Algebra ℝ B] {f g : LocalGaugeFieldAlgebra G →ₐ[ℝ] B}
    (h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra),
      f (derivA G s μ φ) = g (derivA G s μ φ)) : f = g := by
  refine AlgHom.ext_of_adjoin_eq_top adjoin_iteratedJetDeriv_eq_top fun x hx => ?_
  obtain ⟨_, ⟨s, rfl⟩, _, ⟨μ, rfl⟩, φ, rfl⟩ := hx
  exact h s μ φ

/-!

## B. The field strength and its covariant derivatives

-/

variable (G) in
/-- The field strength `F_μν = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆` of the local gauge field
  algebra, the underived field strength of the family of derivative symbols, in the
  conventions of `GaugeBoson.fieldStrength`, where the bracket of the gauge
  algebra carries the physicists' factor of `i`. -/
noncomputable def fieldStrength (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] LocalGaugeFieldAlgebra G :=
  GaugeBoson.fieldStrength (derivA G) μ ν 0

/-- The field strength written in the generators of the algebra. -/
lemma fieldStrength_apply (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    fieldStrength G μ ν φ = jetDeriv G μ (ofA G ν φ) - jetDeriv G ν (ofA G μ φ)
      + bracketFam (ofA G μ) (ofA G ν) φ := by
  rw [fieldStrength, GaugeBoson.fieldStrength_zero,
    GaugeBoson.commutator_eq_bracketFam]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, derivA_apply, iteratedJetDeriv_singleton,
    derivA_zero]

/-- The field strength is antisymmetric in its two covector indices. -/
lemma fieldStrength_swap (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength G ν μ = - fieldStrength G μ ν :=
  GaugeBoson.fieldStrength_swap (derivA G) (fun _ _ _ _ _ _ => Commute.all _ _) μ ν 0

variable (G) in
/-- The iterated covariant derivative `∇_{l₁} ⋯ ∇_{lₙ} F_μν` of the field strength along an
  ordered list of directions, with `∇_ρ F = ∂_ρ F + ⁅A_ρ, F⁆` the covariant derivative in
  the adjoint. Covariant derivatives do not commute, so the iteration is indexed by a list
  and not by a multiset; the empty list gives the field strength itself. -/
noncomputable def covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] LocalGaugeFieldAlgebra G :=
  iteratedCovDerivAdjoint (derivA G) l (GaugeBoson.fieldStrength (derivA G) μ ν) 0

/-- With zero covariant derivatives this is the field strength itself. -/
@[simp]
lemma covDerivFieldStrength_nil (μ ν : Fin 1 ⊕ Fin 3) :
    covDerivFieldStrength G [] μ ν = fieldStrength G μ ν := rfl

/-!

## C. The derivative symbols of the covariant tower are iterated derivatives

The adjoint families carry the derivative symbols `∂_s F` of a
covariant expression as data. Here the Leibniz convolutions defining the derived brackets
really are the Leibniz rule of the total derivative, so those symbols are the iterated
total derivatives `∂_s` of the value at `0`.

-/

/-- The Leibniz rule of the iterated total derivative on a bracket of families, as the
  antidiagonal convolution of the iterated derivatives of the two factors. -/
lemma iteratedJetDeriv_bracketFam (s : Multiset (Fin 1 ⊕ Fin 3))
    (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] LocalGaugeFieldAlgebra G)
      (φ : Module.Dual ℝ G.lieSubalgebra) :
    iteratedJetDeriv G s (bracketFam f g φ) = (s.antidiagonal.map fun p =>
      bracketFam (iteratedJetDeriv G p.1 ∘ₗ f) (iteratedJetDeriv G p.2 ∘ₗ g) φ).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [iteratedJetDeriv_zero, LinearMap.id_apply, Multiset.antidiagonal_zero,
      Multiset.map_singleton, Multiset.sum_singleton, LinearMap.id_comp]
  | cons κ s ih =>
    have hterm : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
        jetDeriv G κ (bracketFam (iteratedJetDeriv G p.1 ∘ₗ f) (iteratedJetDeriv G p.2 ∘ₗ g) φ)
          = bracketFam (iteratedJetDeriv G (κ ::ₘ p.1) ∘ₗ f) (iteratedJetDeriv G p.2 ∘ₗ g) φ
            + bracketFam (iteratedJetDeriv G p.1 ∘ₗ f)
              (iteratedJetDeriv G (κ ::ₘ p.2) ∘ₗ g) φ := by
      intro p
      rw [← LinearMap.comp_apply (jetDeriv G κ),
        GaugeBoson.bracketFam_derivation _ (jetDeriv_mul κ), LinearMap.add_apply,
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
  bracket against the gauge field. The Leibniz convolution is the iterated derivative of the
  bracket of the base values. -/
lemma bracketFamConv_derivA (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ]
    LocalGaugeFieldAlgebra G)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra),
      F s φ = iteratedJetDeriv G s (F 0 φ))
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    bracketFamConv (derivA G) ρ F s φ
      = iteratedJetDeriv G s (bracketFam (ofA G ρ) (F 0) φ) := by
  have hF' : ∀ t, F t = iteratedJetDeriv G t ∘ₗ F 0 := fun t => LinearMap.ext (hF t)
  rw [iteratedJetDeriv_bracketFam, bracketFamConv, Multiset.sum_linearMap_apply,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, hF' p.2]
  rfl

/-- The covariant derivative of a family of iterated derivatives is again a family of
  iterated derivatives. -/
lemma covDerivAdjoint_derivA (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ]
    LocalGaugeFieldAlgebra G)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra),
      F s φ = iteratedJetDeriv G s (F 0 φ))
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    covDerivAdjoint (derivA G) F ρ s φ
      = iteratedJetDeriv G s (covDerivAdjoint (derivA G) F ρ 0 φ) := by
  have h1 : F (ρ ::ₘ s) φ = iteratedJetDeriv G s (F (ρ ::ₘ 0) φ) := by
    rw [hF (ρ ::ₘ s), hF (ρ ::ₘ 0), iteratedJetDeriv_cons', iteratedJetDeriv_cons',
      iteratedJetDeriv_zero, LinearMap.id_comp, LinearMap.comp_apply]
  rw [GaugeBoson.covDerivAdjoint_apply,
    GaugeBoson.covDerivAdjoint_apply, map_add, h1, bracketFamConv_derivA F hF,
    bracketFamConv_derivA F hF ρ 0, iteratedJetDeriv_zero, LinearMap.id_apply]

/-- The derivative symbols of the field strength are the iterated derivatives of the field
  strength. -/
lemma fieldStrength_derivA (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    GaugeBoson.fieldStrength (derivA G) μ ν s φ
      = iteratedJetDeriv G s (fieldStrength G μ ν φ) := by
  have hd : ∀ σ τ : Fin 1 ⊕ Fin 3,
      derivA G (σ ::ₘ s) τ φ = iteratedJetDeriv G s (derivA G (σ ::ₘ 0) τ φ) := by
    intro σ τ
    rw [derivA_apply, derivA_apply, iteratedJetDeriv_cons', iteratedJetDeriv_cons',
      iteratedJetDeriv_zero, LinearMap.id_comp, LinearMap.comp_apply]
  have hcomm : ∀ t, commutatorFam (derivA G) μ ν t
      = bracketFamConv (derivA G) μ (fun r => derivA G r ν) t := fun t => rfl
  rw [fieldStrength, GaugeBoson.fieldStrength_apply,
    GaugeBoson.fieldStrength_apply, map_add, map_sub, hd μ ν, hd ν μ, hcomm,
    hcomm, bracketFamConv_derivA _ (fun _ _ => rfl), bracketFamConv_derivA _ (fun _ _ => rfl),
    iteratedJetDeriv_zero, LinearMap.id_apply]

/-- The derivative symbols of the covariant derivatives of the field strength are the
  iterated derivatives of their base values. -/
lemma iteratedCovDerivAdjoint_fieldStrength_derivA (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    iteratedCovDerivAdjoint (derivA G) l (GaugeBoson.fieldStrength (derivA G) μ ν)
        s φ
      = iteratedJetDeriv G s (covDerivFieldStrength G l μ ν φ) := by
  induction l generalizing s φ with
  | nil => exact fieldStrength_derivA μ ν s φ
  | cons ρ l ih => exact covDerivAdjoint_derivA _ ih ρ s φ

/-- The covariant derivative `∇_ρ F = ∂_ρ F + ⁅A_ρ, F⁆` peeled off the front of the list,
  giving the recursion on elements of the algebra. -/
lemma covDerivFieldStrength_cons (ρ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    covDerivFieldStrength G (ρ :: l) μ ν φ
      = jetDeriv G ρ (covDerivFieldStrength G l μ ν φ)
        + bracketFam (ofA G ρ) (covDerivFieldStrength G l μ ν) φ := by
  show covDerivAdjoint (derivA G) (iteratedCovDerivAdjoint (derivA G) l
    (GaugeBoson.fieldStrength (derivA G) μ ν)) ρ 0 φ = _
  rw [GaugeBoson.covDerivAdjoint_apply, iteratedCovDerivAdjoint_fieldStrength_derivA,
    bracketFamConv_derivA _ (iteratedCovDerivAdjoint_fieldStrength_derivA l μ ν),
    iteratedJetDeriv_zero, LinearMap.id_apply, iteratedJetDeriv_cons', iteratedJetDeriv_zero,
    LinearMap.id_comp]
  rfl

/-!

## D. The gauge law, by descent from the complexification

The gauge law is proved in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.GaugeLaw` for any
family transforming as a gauge field in a complex algebra, such as the symbols of the
complexification (`transformsAsGaugeField_gaugeField`). Injectivity of `x ↦ 1 ⊗ₜ x` reads the
real law off the complex one, and no reality argument beyond that is involved.

-/

/-- The complexified covariant tower is the image of the real
  one. -/
lemma one_tmul_iteratedCovDerivAdjoint_fieldStrength (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (1 : ℂ) ⊗ₜ[ℝ] iteratedCovDerivAdjoint (derivA G) l
        (GaugeBoson.fieldStrength (derivA G) μ ν) s φ
      = iteratedCovDerivAdjoint (gaugeField G) l
        (GaugeBoson.fieldStrength (gaugeField G) μ ν) s φ := by
  set ι : LocalGaugeFieldAlgebra G →ₗ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G :=
    (Algebra.TensorProduct.includeRight :
      LocalGaugeFieldAlgebra G →ₐ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G).toLinearMap with hι
  have hmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y =>
    map_mul (Algebra.TensorProduct.includeRight :
      LocalGaugeFieldAlgebra G →ₐ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) x y
  have hA : (fun p ρ => ι ∘ₗ derivA G p ρ) = gaugeField G := by
    funext p ρ
    exact LinearMap.ext fun φ => (gaugeField_eq_one_tmul_derivA p ρ φ).symm
  have key := congrFun (GaugeBoson.iteratedCovDerivAdjoint_map ι hmul (derivA G) l
    (GaugeBoson.fieldStrength (derivA G) μ ν)) s
  rw [show (fun p => ι ∘ₗ GaugeBoson.fieldStrength (derivA G) μ ν p)
      = GaugeBoson.fieldStrength (fun p ρ => ι ∘ₗ derivA G p ρ) μ ν from
      funext fun p => (GaugeBoson.fieldStrength_map ι hmul _ μ ν p).symm, hA] at key
  exact (LinearMap.congr_fun key φ).symm

/-- The gauge law of the covariant derivatives of the field strength at every derivative
  order. A jet acts by the Leibniz convolution of the dual adjoint Taylor coefficients of
  `U⁻¹` against lower derivative symbols, with no Maurer–Cartan shift. -/
lemma repJet_iteratedCovDerivAdjoint_fieldStrength (U : G.gaugeJetGroup) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repJet G U (iteratedCovDerivAdjoint (derivA G) l
        (GaugeBoson.fieldStrength (derivA G) μ ν) s φ)
      = (s.antidiagonal.map fun p => iteratedCovDerivAdjoint (derivA G) l
          (GaugeBoson.fieldStrength (derivA G) μ ν) p.2
          (G.adjointDualCoeff U⁻¹ p.1 φ)).sum := by
  -- `x ↦ 1 ⊗ₜ x` is injective: `ℝ → ℂ` is injective and every real module is flat.
  apply Module.Flat.tensorProduct_mk_injective ℝ _ ℂ
  simp only [TensorProduct.mk_apply]
  rw [← complexRepJet_tmul,
    one_tmul_iteratedCovDerivAdjoint_fieldStrength (G := G) l μ ν s φ,
    Multiset.tmul_sum, Multiset.map_map]
  refine ((transformsAsGaugeField_gaugeField G).transformsInAdjoint_iteratedCovDerivAdjoint
    complexRepJet_apply_mul l μ ν U φ s).trans ?_
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  exact (one_tmul_iteratedCovDerivAdjoint_fieldStrength l μ ν p.2 _).symm

/-- The gauge law of the covariant derivatives of the field strength. A jet acts through
  the zeroth dual adjoint Taylor coefficient of `U⁻¹` on the adjoint index alone. -/
lemma repJet_covDerivFieldStrength (U : G.gaugeJetGroup) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repJet G U (covDerivFieldStrength G l μ ν φ)
      = covDerivFieldStrength G l μ ν (G.adjointDualCoeff U⁻¹ 0 φ) := by
  rw [covDerivFieldStrength]
  simpa only [Multiset.antidiagonal_zero, Multiset.map_singleton, Multiset.sum_singleton]
    using repJet_iteratedCovDerivAdjoint_fieldStrength (G := G) U l μ ν 0 φ

/-- On the covariant derivatives of the field strength the local gauge action factors
  through evaluation. A jet `U` acts through the dual base-point adjoint action of the
  value `G.evalGaugeJet U⁻¹` of its inverse, and the derivatives of the jet are not seen. The
  covariant expressions are gauge covariant, not gauge invariant. -/
lemma repJet_covDerivFieldStrength_eval (U : G.gaugeJetGroup) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repJet G U (covDerivFieldStrength G l μ ν φ)
      = covDerivFieldStrength G l μ ν ((G.adjointRep
        (G.evalGaugeJet U⁻¹)).dualMap φ) := by
  rw [repJet_covDerivFieldStrength, G.adjointDualCoeff_zero_evalGaugeJet]

/-!

## E. The Lorentz law

-/

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => ((SL2C.toLorentzGroup Λ).1 b a : ℝ)

/-- The Lorentz action on the gauge-field generator, as a linear map. -/
lemma repLorentzGroup_comp_ofA (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    (repLorentzGroup G Λ) ∘ₗ ofA G μ = ∑ a, L[Λ] a μ • ofA G a :=
  LinearMap.ext fun φ => by
    simp only [LinearMap.comp_apply, repLorentzGroup_ofA, LinearMap.sum_apply,
      LinearMap.smul_apply]

/-- The Lorentz action passes through the bracket of a gauge-field generator against a
  family, mixing the covector index of the generator. -/
lemma repLorentzGroup_bracketFam_ofA (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (F : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] LocalGaugeFieldAlgebra G)
      (φ : Module.Dual ℝ G.lieSubalgebra) :
    repLorentzGroup G Λ (bracketFam (ofA G ρ) F φ)
      = ∑ a, L[Λ] a ρ • bracketFam (ofA G a) ((repLorentzGroup G Λ) ∘ₗ F) φ := by
  rw [← LinearMap.comp_apply,
    ← GaugeBoson.bracketFam_map _ (repLorentzGroup_apply_mul Λ),
    repLorentzGroup_comp_ofA, GaugeBoson.bracketFam_finset_sum_left,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GaugeBoson.bracketFam_smul_left, LinearMap.smul_apply]

/-- The Lorentz law of the field strength. Both covector indices mix by the columns of the
  Lorentz matrix, and the adjoint index is untouched. -/
lemma repLorentzGroup_fieldStrength (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repLorentzGroup G Λ (fieldStrength G μ ν φ)
      = ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • fieldStrength G a b φ := by
  have hder : ∀ σ τ : Fin 1 ⊕ Fin 3, repLorentzGroup G Λ (jetDeriv G σ (ofA G τ φ))
      = ∑ a, L[Λ] a σ • ∑ b, L[Λ] b τ • jetDeriv G a (ofA G b φ) := by
    intro σ τ
    rw [repLorentzGroup_jetDeriv]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [repLorentzGroup_ofA, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul]
  have hswap : ∑ a, L[Λ] a ν • ∑ b, L[Λ] b μ • jetDeriv G a (ofA G b φ)
      = ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • jetDeriv G b (ofA G a φ) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  have hbr : repLorentzGroup G Λ (bracketFam (ofA G μ) (ofA G ν) φ)
      = ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • bracketFam (ofA G a) (ofA G b) φ := by
    rw [repLorentzGroup_bracketFam_ofA, Finset.sum_congr rfl fun a _ => by
      rw [repLorentzGroup_comp_ofA, GaugeBoson.bracketFam_finset_sum_right,
        LinearMap.sum_apply, Finset.sum_congr rfl fun b _ => by
          rw [GaugeBoson.bracketFam_smul_right, LinearMap.smul_apply]]]
  rw [fieldStrength_apply, map_add, map_sub, hder, hder, hswap, hbr]
  simp only [fieldStrength_apply, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

/-- The Lorentz law of the covariant derivatives of the field strength. Every covariant
  slot and both covector indices of the field strength mix by the columns of the Lorentz
  matrix, and the adjoint index is untouched. -/
lemma repLorentzGroup_covDerivFieldStrength (Λ : SL(2,ℂ)) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repLorentzGroup G Λ (covDerivFieldStrength G (List.ofFn l) μ ν φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i)) •
          ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • covDerivFieldStrength G (List.ofFn p) a b φ := by
  induction n generalizing φ with
  | zero =>
    rw [List.ofFn_zero, covDerivFieldStrength_nil, repLorentzGroup_fieldStrength,
      Fintype.sum_unique (ι := Fin 0 → (Fin 1 ⊕ Fin 3))]
    simp
  | succ n ih =>
    have hT : (repLorentzGroup G Λ) ∘ₗ covDerivFieldStrength G (List.ofFn fun i => l i.succ) μ ν
        = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i.succ)) •
          ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • covDerivFieldStrength G (List.ofFn p) a b :=
      LinearMap.ext fun φ => by
        simp only [LinearMap.comp_apply, ih (fun i => l i.succ), LinearMap.sum_apply,
          LinearMap.smul_apply]
    have hcov : ∀ (c : Fin 1 ⊕ Fin 3) (p : Fin n → (Fin 1 ⊕ Fin 3)),
        ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
            covDerivFieldStrength G (List.ofFn (Fin.cons c p)) a b φ
          = jetDeriv G c (∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
              covDerivFieldStrength G (List.ofFn p) a b φ)
            + bracketFam (ofA G c) (∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
              covDerivFieldStrength G (List.ofFn p) a b) φ := by
      intro c p
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, covDerivFieldStrength_cons,
        map_sum, map_smul, GaugeBoson.bracketFam_finset_sum_right,
        GaugeBoson.bracketFam_smul_right, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_add, Finset.sum_add_distrib]
    rw [List.ofFn_succ, covDerivFieldStrength_cons, map_add, repLorentzGroup_jetDeriv,
      repLorentzGroup_bracketFam_ofA, hT, ← Finset.sum_add_distrib,
      Physlib.Fin.sum_pi_succ_prod_smul (fun i b => L[Λ] b (l i))]
    simp only [mul_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih (fun i => l i.succ), map_sum (jetDeriv G c),
      GaugeBoson.bracketFam_finset_sum_right, LinearMap.sum_apply,
      Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hcov c p]
    simp only [smul_add, map_smul, GaugeBoson.bracketFam_smul_right,
      LinearMap.smul_apply]

end LocalGaugeFieldAlgebra
