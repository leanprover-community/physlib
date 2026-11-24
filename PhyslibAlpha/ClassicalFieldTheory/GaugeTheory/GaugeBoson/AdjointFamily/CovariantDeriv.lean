/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.Bracket
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Truncation
/-!
# The field strength and the covariant derivative of an adjoint family

The field strength of a family of gauge-field symbols, the covariant derivative in the
adjoint, and the gauge law of an adjoint gauge tensor.

## i. Overview

Let `A` be a family of gauge-field symbols `∂_s A_μ^φ` in an algebra `B`, indexed by a
derivative multiset `s`, a direction `μ` and a dual vector `φ` of the gauge algebra. Its field
strength is
```
  F_{μν} = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆
```
with `⁅·,·⁆` the gauge-algebra bracket, which carries the physicists' factor of `i` (on the
matrix factors `⁅a, b⁆ = i(ab − ba)`). In terms of the plain matrix commutator this is
`F_{μν} = ∂_μ A_ν − ∂_ν A_μ + i [A_μ, A_ν]`, the sign forced by the convention
`ω_μ(g) = i (∂_μ g) g⁻¹` for the Maurer–Cartan form. With the derivative symbols as primitives
the field strength is itself a family of derivative symbols `s ↦ [∂_s F_μν]`. The derivative
terms shift the multiset index, and the commutator term is the Leibniz convolution
`commutatorFam`.

The covariant derivative of an adjoint family `F` is `∇_ρ F = [∂_ρ F] + ⁅A_ρ, F⁆`, and
`iteratedCovDerivAdjoint` iterates it along a list of directions. All of these are formulas in
an arbitrary algebra `B`, natural under multiplicative linear maps (`fieldStrength_map`,
`iteratedCovDerivAdjoint_map`).

A family transforms in the adjoint, `TransformsInAdjoint`, when every derivative symbol
transforms by the Leibniz convolution of the dual adjoint coefficients of the jet, with no
inhomogeneous term. That the field strength and its covariant derivatives transform in the
adjoint is proved in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.GaugeLaw`.

## ii. Key results

- `GaugeBoson.fieldStrength` : the field strength of a family of gauge-field symbols.
- `GaugeBoson.covDerivAdjoint`, `GaugeBoson.iteratedCovDerivAdjoint` : the covariant derivative
  of an adjoint family and its iterates.
- `GaugeBoson.sum_bracketFam_conv_eq` : the derived bracket against the dual adjoint
  coefficients, regrouped by the exchange of the four-fold splitting.
- `GaugeBoson.iteratedCovDerivAdjoint_fieldStrength_map` : the covariant field-strength tower
  is natural in the algebra.
- `GaugeBoson.TransformsInAdjoint` : a family transforms in the adjoint.
- `GaugeBoson.iteratedCovDerivAdjoint_mem_massWeightEigenspace` : the mass weight of an adjoint
  covariant tower.

## iii. Table of contents

- A. The field strength
- B. The covariant derivative in the adjoint
- C. Iterated covariant derivatives
- D. Families transforming in the adjoint
- E. Mass weights

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct
variable {B : Type} [Ring B]
variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

namespace GaugeBoson

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

/-!

## A. The field strength

The field strength is antisymmetric in its two covector indices as soon as the symbols of the
gauge field commute with one another in `B`.

-/

/-- The field strength `F_μν = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆` of a family of
  gauge-field symbols, as a family of derivative symbols. The `s`-th derivative has
  the derivative terms through the shifted symbols `A (μ ::ₘ s) ν`, and the commutator
  term through the Leibniz convolution `commutatorFam`. This is the physicists'
  `F_μν^a = ∂_μ A_ν^a − ∂_ν A_μ^a + f^a_{bc} A_μ^b A_ν^c`. The gauge-algebra bracket
  already carries the physicists' factor of `i`, so no explicit factor appears. This is
  the normalization of the structural equation of the Maurer–Cartan form, which makes the
  field strength transform without inhomogeneous terms
  (`TransformsAsGaugeField.repGauge_fieldStrength`). -/
noncomputable def fieldStrength
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  A (μ ::ₘ s) ν - A (ν ::ₘ s) μ + commutatorFam A μ ν s

@[simp]
lemma fieldStrength_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    fieldStrength A μ ν s φ = A (μ ::ₘ s) ν φ - A (ν ::ₘ s) μ φ + commutatorFam A μ ν s φ :=
  rfl

/-- The underived field strength, derivative symbols on singletons, plus the plain
  commutator. -/
lemma fieldStrength_zero
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength A μ ν 0 = A {μ} ν - A {ν} μ + commutator A μ ν := by
  rw [fieldStrength, commutatorFam_zero]
  rfl

/-- The antisymmetrized pair of derivative symbols is the field strength minus its
  commutator term. -/
lemma pair_eq_fieldStrength_sub_commutatorFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ν μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    A (ν ::ₘ s) μ - A (μ ::ₘ s) ν = fieldStrength A ν μ s - commutatorFam A ν μ s := by
  rw [fieldStrength, add_sub_cancel_right]

/-- The field strength is antisymmetric in its two covector indices when the symbols of
  the gauge field commute. The two derivative terms swap outright, and the commutator term
  swaps by `commutatorFam_swap`. -/
lemma fieldStrength_swap
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (hA : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
      (ψ ψ' : Module.Dual ℝ G.lieSubalgebra), Commute (A s μ ψ) (A s' μ' ψ'))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    fieldStrength A ν μ s = - fieldStrength A μ ν s := by
  rw [fieldStrength, fieldStrength, commutatorFam_swap A hA μ ν s]
  abel

/-- The field strength is natural in the algebra. A multiplicative linear map carries the
  field strength of a family to the field strength of its image. -/
lemma fieldStrength_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    fieldStrength (fun p ρ => Φ ∘ₗ A p ρ) μ ν s = Φ ∘ₗ fieldStrength A μ ν s := by
  rw [fieldStrength, fieldStrength, commutatorFam_map Φ hΦ, LinearMap.comp_add,
    LinearMap.comp_sub]

/-!

## B. The covariant derivative in the adjoint

-/

/-- The derived bracket family `⁅A_ρ, F⁆`, the `s`-derivative of the bracket of the
  gauge field against a family, given by the Leibniz convolution of the derivative
  symbols over the multiset antidiagonal. -/
noncomputable def bracketFamConv
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  (s.antidiagonal.map fun p => bracketFam (A p.1 ρ) (F p.2)).sum

/-- The covariant derivative `∇_ρ F = [∂_ρ F] + ⁅A_ρ, F⁆` of an adjoint-valued family
  of derivative symbols, the extra derivative on the symbol plus the derived bracket
  against the gauge field. The gauge-algebra bracket carries the physicists' `i`, so
  in matrix terms this is `∂_ρ F + i [A_ρ, F]`, the adjoint-representation covariant
  derivative in the same `D = ∂ + i A` convention as the field strength. It preserves
  `TransformsInAdjoint` (`TransformsInAdjoint.covDerivAdjoint`). -/
noncomputable def covDerivAdjoint
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  F (ρ ::ₘ s) + bracketFamConv A ρ F s

@[simp]
lemma covDerivAdjoint_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    covDerivAdjoint A F ρ s φ = F (ρ ::ₘ s) φ + bracketFamConv A ρ F s φ := rfl

/-- At a dual vector vanishing on every bracket the derived bracket term drops out and the
  covariant derivative is the ordinary one, `(∇_ρ F)^φ = ∂_ρ F^φ`. -/
lemma covDerivAdjoint_apply_of_map_lie {φ : Module.Dual ℝ G.lieSubalgebra}
    (hφ : ∀ x y : G.lieSubalgebra, φ ⁅x, y⁆ = 0)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    covDerivAdjoint A F ρ s φ = F (ρ ::ₘ s) φ := by
  simp [bracketFamConv, Multiset.sum_linearMap_apply, bracketFam_apply_eq_zero_of_map_lie hφ]

/-- The derived bracket family is natural in the algebra. -/
lemma bracketFamConv_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    bracketFamConv (fun p σ => Φ ∘ₗ A p σ) ρ (fun p => Φ ∘ₗ F p) s =
      Φ ∘ₗ bracketFamConv A ρ F s := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, bracketFamConv, bracketFamConv, Multiset.sum_linearMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Multiset.map_map, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [bracketFam_map Φ hΦ]
  rfl

/-- The covariant derivative is natural in the algebra. -/
lemma covDerivAdjoint_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    covDerivAdjoint (fun p σ => Φ ∘ₗ A p σ) (fun p => Φ ∘ₗ F p) ρ s =
      Φ ∘ₗ covDerivAdjoint A F ρ s := by
  rw [covDerivAdjoint, covDerivAdjoint, bracketFamConv_map Φ hΦ, LinearMap.comp_add]

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
/-- A sum of families transported by the dual adjoint coefficients of a jet, evaluated at a
  dual vector. -/
lemma sum_comp_adjointDualCoeff_apply (U : G.gaugeJetGroup)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ G.lieSubalgebra) :
    ((t.antidiagonal.map fun r => F r.2 ∘ₗ G.adjointDualCoeff U r.1).sum) ψ =
      (t.antidiagonal.map fun r => F r.2 (G.adjointDualCoeff U r.1 ψ)).sum := by
  rw [Multiset.sum_linearMap_apply, Multiset.map_map]
  rfl

/-- The derived bracket against the dual adjoint coefficients, regrouped. Bracketing the
  families `A` and `F` transported by the dual adjoint coefficients of a jet, summed over all
  splittings, gives the antidiagonal convolution of the derived bracket `⁅A_ρ, F⁆` against the
  coefficients. This is the exchange of the four-fold splitting. -/
lemma sum_bracketFam_conv_eq (U : G.gaugeJetGroup)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (s.antidiagonal.map fun p =>
      bracketFam ((p.1.antidiagonal.map fun q => A q.2 ρ ∘ₗ G.adjointDualCoeff U q.1).sum)
        ((p.2.antidiagonal.map fun r => F r.2 ∘ₗ G.adjointDualCoeff U r.1).sum) φ).sum =
      (s.antidiagonal.map fun p => bracketFamConv A ρ F p.2 (G.adjointDualCoeff U p.1 φ)).sum := by
  have hMa : (s.antidiagonal.map fun p =>
      bracketFam ((p.1.antidiagonal.map fun q => A q.2 ρ ∘ₗ G.adjointDualCoeff U q.1).sum)
        ((p.2.antidiagonal.map fun r => F r.2 ∘ₗ G.adjointDualCoeff U r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (A q.2 ρ ∘ₗ G.adjointDualCoeff U q.1)
              (F r.2 ∘ₗ G.adjointDualCoeff U r.1) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [bracketFam_sum_left, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [bracketFam_sum_right, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
  have hMc : (s.antidiagonal.map fun p =>
      bracketFamConv A ρ F p.2 (G.adjointDualCoeff U p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (A r.1 ρ ∘ₗ G.adjointDualCoeff U q.1)
              (F r.2 ∘ₗ G.adjointDualCoeff U q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_congr rfl (fun r hr => by
        rw [Function.comp_apply, bracketFam_adjointDualCoeff U p.1 (A r.1 ρ) (F r.2) φ]),
      Multiset.sum_map_sum_map]
  exact hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
    bracketFam (A b ρ ∘ₗ G.adjointDualCoeff U a) (F d ∘ₗ G.adjointDualCoeff U c) φ).trans hMc.symm)

/-!

## C. Iterated covariant derivatives

-/

/-- The iterated covariant derivative `𝒟_l F` of an adjoint family of derivative
  symbols along a list of directions. Covariant derivatives do not commute (their
  commutator is an `ad F` term), so the iteration is order-dependent and indexed by a
  list. The result is again a family of derivative symbols, and the underived covariant
  tower is its value at the empty multiset. -/
noncomputable def iteratedCovDerivAdjoint
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    List (Fin 1 ⊕ Fin 3) →
      (Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) →
      Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B
  | [], F => F
  | ρ :: l, F => covDerivAdjoint A (iteratedCovDerivAdjoint A l F) ρ

/-- The iterated covariant derivative is natural in the algebra. -/
lemma iteratedCovDerivAdjoint_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (l : List (Fin 1 ⊕ Fin 3)) (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra
      →ₗ[ℝ] B) :
    iteratedCovDerivAdjoint (fun p σ => Φ ∘ₗ A p σ) l (fun p => Φ ∘ₗ F p) =
      fun p => Φ ∘ₗ iteratedCovDerivAdjoint A l F p := by
  induction l with
  | nil => rfl
  | cons ρ l ih =>
    funext s
    show covDerivAdjoint (fun p σ => Φ ∘ₗ A p σ)
        (iteratedCovDerivAdjoint (fun p σ => Φ ∘ₗ A p σ) l (fun p => Φ ∘ₗ F p)) ρ s =
      Φ ∘ₗ covDerivAdjoint A (iteratedCovDerivAdjoint A l F) ρ s
    rw [ih, covDerivAdjoint_map Φ hΦ]

/-- The iterated covariant derivative is odd in the family it differentiates. -/
lemma iteratedCovDerivAdjoint_neg_fam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    ∀ l : List (Fin 1 ⊕ Fin 3),
      iteratedCovDerivAdjoint A l (fun t => - F t) = fun t => - iteratedCovDerivAdjoint A l F t
  | [] => rfl
  | ρ :: l => by
    funext s
    refine LinearMap.ext fun φ => ?_
    have ih := iteratedCovDerivAdjoint_neg_fam A F l
    simp only [iteratedCovDerivAdjoint, ih, covDerivAdjoint_apply, bracketFamConv,
      bracketFam_neg_right, Multiset.sum_map_neg'', LinearMap.neg_apply, neg_add]

/-- The covariant tower of the field strength is natural in the algebra. The tower of the
  image family is the image of the tower. -/
lemma iteratedCovDerivAdjoint_fieldStrength_map {B' : Type} [Ring B'] [Module ℝ B']
    [SMulCommClass ℝ B' B'] [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B')
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    iteratedCovDerivAdjoint (fun p σ => Φ ∘ₗ A p σ) l
        (fieldStrength (fun p σ => Φ ∘ₗ A p σ) μ ν) 0 φ
      = Φ (iteratedCovDerivAdjoint A l (fieldStrength A μ ν) 0 φ) := by
  have key := congrFun (iteratedCovDerivAdjoint_map Φ hΦ A l (fieldStrength A μ ν)) 0
  rw [show (fun p => Φ ∘ₗ fieldStrength A μ ν p) = fieldStrength (fun p σ => Φ ∘ₗ A p σ) μ ν
      from funext fun p => (fieldStrength_map Φ hΦ A μ ν p).symm] at key
  exact LinearMap.congr_fun key φ

/-- At a dual vector vanishing on every bracket, such as the coordinate of an abelian factor,
  the iterated covariant derivative is the ordinary derivative along the multiset of its
  directions. No bracket correction survives at any order. -/
lemma iteratedCovDerivAdjoint_apply_of_map_lie {φ : Module.Dual ℝ G.lieSubalgebra}
    (hφ : ∀ x y : G.lieSubalgebra, φ ⁅x, y⁆ = 0)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (l : List (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedCovDerivAdjoint A l F s φ = F (↑l + s) φ := by
  induction l generalizing s with
  | nil => simp [iteratedCovDerivAdjoint]
  | cons ρ l ih =>
    rw [iteratedCovDerivAdjoint, covDerivAdjoint_apply_of_map_lie hφ, ih, Multiset.add_cons,
      ← Multiset.cons_coe, Multiset.cons_add]

/-- Hence at such a dual vector the covariant derivatives commute. The iterated covariant
  derivative depends only on the multiset of its directions. -/
lemma iteratedCovDerivAdjoint_apply_perm_of_map_lie {φ : Module.Dual ℝ G.lieSubalgebra}
    (hφ : ∀ x y : G.lieSubalgebra, φ ⁅x, y⁆ = 0)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    {l l' : List (Fin 1 ⊕ Fin 3)} (hl : l.Perm l') (s : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedCovDerivAdjoint A l F s φ = iteratedCovDerivAdjoint A l' F s φ := by
  rw [iteratedCovDerivAdjoint_apply_of_map_lie hφ, iteratedCovDerivAdjoint_apply_of_map_lie hφ,
    Multiset.coe_eq_coe.2 hl]

end RealScalars

/-!

## D. Families transforming in the adjoint

-/

section ComplexScalars

variable [Algebra ℂ B] {repGauge : Representation ℂ G.gaugeJetGroup B}

variable (G) in
/-- A family of derivative symbols `F` transforms in the adjoint (is an adjoint gauge
  tensor) for the gauge representation `repGauge` when each symbol `[∂_s F^φ]`
  transforms by the Leibniz convolution of the dual adjoint coefficients against lower
  symbols. This is the shape of `TransformsAsGaugeField` with no Maurer–Cartan shift. At
  `s = 0` it is the homogeneous law `U • F^φ = F^{Ad₀^* φ}`. -/
def TransformsInAdjoint (repGauge : Representation ℂ G.gaugeJetGroup B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) : Prop :=
  ∀ (U : G.gaugeJetGroup) (φ : Module.Dual ℝ G.lieSubalgebra) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (F s φ) =
      (s.antidiagonal.map fun p => F p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum

/-- An adjoint gauge tensor transforms at the base point through the dual adjoint
  coefficient of the value of the gauge jet alone. The antidiagonal of the empty multiset
  has a single term. -/
lemma TransformsInAdjoint.repGauge_zero
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hF : TransformsInAdjoint G repGauge F) (U : G.gaugeJetGroup)
      (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (F 0 φ) = F 0 (G.adjointDualCoeff U⁻¹ 0 φ) := by
  simpa only [Multiset.antidiagonal_zero, Multiset.map_singleton, Multiset.sum_singleton]
    using hF U φ 0

/-- If `F` transforms in the adjoint, so do its `κ ::ₘ s`-derived symbols, with the
  extra derivative traced through `GlobalGaugeGroup.adjointDualCoeff_cons`. The result is
  the Leibniz splittings where `κ` stays a derivative, minus the convolution where `κ` hits
  the adjoint, an `ad` of the derived Maurer–Cartan form. -/
lemma TransformsInAdjoint.repGauge_cons
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hF : TransformsInAdjoint G repGauge F)
    (U : G.gaugeJetGroup) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (F (κ ::ₘ s) φ) =
      (s.antidiagonal.map fun p =>
        F (κ ::ₘ p.2) (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (G.adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ q.1
                  (-G.maurerCartan U⁻¹ κ)))))).sum).sum := by
  rw [hF U φ (κ ::ₘ s)]
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        F p.2 (G.adjointDualCoeff U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (G.adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ q.1
                  (-G.maurerCartan U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [G.adjointDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

/-- Anything that transforms in the adjoint is invariant under the pure jets. At `s = 0`
  the transformation law is the dual adjoint action of the base-point value `U₀⁻¹ = 1`. -/
lemma TransformsInAdjoint.repGauge_eq_of_mem_truncationKer_zero
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hF : TransformsInAdjoint G repGauge F) (U : G.truncationKer 0)
    (φ : Module.Dual ℝ G.lieSubalgebra) : repGauge U.1 (F 0 φ) = F 0 φ := by
  rw [hF.repGauge_zero, G.adjointDualCoeff_zero_of_evalGaugeJet_eq_one
    (by rw [map_inv, G.mem_truncationKer_zero_iff_evalGaugeJet.mp U.2, inv_one]),
    LinearMap.id_apply]

end ComplexScalars

/-!

## E. Mass weights

-/

section ComplexScalars

variable [Algebra ℂ B]

/-- The mass weight of the field strength is `4 + 2 * |s|` when each symbol `∂_p A_μ` has
  weight `2 * (1 + |p|)`. Each term is two gauge-field symbols, or one with an extra
  derivative. -/
lemma fieldStrength_mem_massWeightEigenspace
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (P : B →ₐ[ℂ] Polynomial B)
    (hA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ G.lieSubalgebra),
      A p μ ψ ∈ massWeightEigenspace P (2 * (1 + Multiset.card p)))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    fieldStrength A μ ν s φ ∈ massWeightEigenspace P (4 + 2 * Multiset.card s) := by
  rw [fieldStrength_apply]
  refine add_mem (sub_mem ?_ ?_) ?_
  · have hstep := hA (μ ::ₘ s) ν φ
    rwa [Multiset.card_cons,
      show 2 * (1 + (Multiset.card s + 1)) = 4 + 2 * Multiset.card s by ring] at hstep
  · have hstep := hA (ν ::ₘ s) μ φ
    rwa [Multiset.card_cons,
      show 2 * (1 + (Multiset.card s + 1)) = 4 + 2 * Multiset.card s by ring] at hstep
  · rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map]
    refine multiset_sum_mem _ fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    have hle : Multiset.card p.1 + Multiset.card p.2 = Multiset.card s := by
      rw [← Multiset.card_add, Multiset.mem_antidiagonal.mp hp]
    simp only [Function.comp_apply]
    refine bracketFam_apply_mem_submodule (fun ψ χ => ?_) _
    have hmul := mul_mem_massWeightEigenspace (hA p.1 μ ψ) (hA p.2 ν χ)
    rwa [show 2 * (1 + Multiset.card p.1) + 2 * (1 + Multiset.card p.2)
      = 4 + 2 * Multiset.card s by omega] at hmul

/-- The mass weight of an adjoint covariant tower. If the gauge-field symbols `∂_p A_μ` have
  weight `2 * (1 + |p|)` and the family `G` has weight `c + 2 * |t|` at the derivative
  multiset `t`, then `𝒟_l G` has weight `c + 2 * |l| + 2 * |s|` at `s`. Each covariant
  derivative costs two units, whether it lands on the derivative index or brings down a
  gauge-field factor. -/
lemma iteratedCovDerivAdjoint_mem_massWeightEigenspace
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (P : B →ₐ[ℂ] Polynomial B)
    (hA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ G.lieSubalgebra),
      A p μ ψ ∈ massWeightEigenspace P (2 * (1 + Multiset.card p)))
    (c : ℕ) (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (hF : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℝ G.lieSubalgebra),
      F t χ ∈ massWeightEigenspace P (c + 2 * Multiset.card t))
    (l : List (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    iteratedCovDerivAdjoint A l F s φ ∈
      massWeightEigenspace P (c + 2 * l.length + 2 * Multiset.card s) := by
  induction l generalizing s φ with
  | nil =>
      rw [show iteratedCovDerivAdjoint A ([] : List (Fin 1 ⊕ Fin 3)) F = F from rfl]
      simpa using hF s φ
  | cons ρ l ih =>
      rw [show iteratedCovDerivAdjoint A (ρ :: l) F
          = covDerivAdjoint A (iteratedCovDerivAdjoint A l F) ρ from rfl,
        covDerivAdjoint_apply, List.length_cons]
      refine add_mem ?_ ?_
      · have hstep := ih (ρ ::ₘ s) φ
        rwa [Multiset.card_cons, show c + 2 * l.length + 2 * (Multiset.card s + 1)
            = c + 2 * (l.length + 1) + 2 * Multiset.card s by ring] at hstep
      · rw [bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
        refine multiset_sum_mem _ fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
        have hle : Multiset.card p.1 + Multiset.card p.2 = Multiset.card s := by
          rw [← Multiset.card_add, Multiset.mem_antidiagonal.mp hp]
        simp only [Function.comp_apply]
        refine bracketFam_apply_mem_submodule (fun ψ χ => ?_) _
        have hmul := mul_mem_massWeightEigenspace (hA p.1 ρ ψ) (ih p.2 χ)
        rwa [show 2 * (1 + Multiset.card p.1) + (c + 2 * l.length + 2 * Multiset.card p.2)
          = c + 2 * (l.length + 1) + 2 * Multiset.card s by omega] at hmul

end ComplexScalars

end GaugeBoson
