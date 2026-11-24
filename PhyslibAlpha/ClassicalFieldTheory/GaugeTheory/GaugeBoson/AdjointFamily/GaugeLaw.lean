/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.Generation
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
/-!
# The gauge law of a gauge field and of its covariant expressions

A family of gauge-field symbols transforming as a gauge field makes its field strength and the
covariant derivatives of it transform in the adjoint.

## i. Overview

A family `A` of symbols `∂_s A_μ^φ` in an algebra `B` transforms as a gauge field,
`TransformsAsGaugeField`, when a jet `U` acts on `∂_s A_μ^φ` by the Leibniz convolution of the
dual adjoint Taylor coefficients of `U⁻¹` against lower symbols, plus the base-point value of
the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. This is the law that the symbols of
the gauge-boson jet algebra satisfy (`LocalGaugeFieldAlgebra.transformsAsGaugeField_gaugeField`),
and that their images under any algebra map intertwining the gauge actions inherit
(`LocalGaugeFieldAlgebra.transformsAsGaugeField_mapGaugeField`). The Lorentz law of such a
family is `LorentzTransformsAsGaugeField`.

From the gauge law and the multiplicativity of the action on `B` alone, this file works out
the action on the expressions built from the symbols. The derived commutators pick up `ad`
cross terms and a constant bracket (`TransformsAsGaugeField.repGauge_commutatorFam`). In the
field strength these cancel against the inhomogeneous terms of the derivative symbols, through
the structural equation of the Maurer–Cartan form, so the field strength transforms in the
adjoint at every derivative order. The covariant derivative preserves the adjoint law
(`TransformsInAdjoint.covDerivAdjoint`), so every covariant derivative of the field strength
transforms in the adjoint. A jet acts on the symmetrized derivatives by the symmetrized
adjoint convolution plus a translation by its symmetrized Maurer–Cartan data.

## ii. Key results

- `GaugeBoson.TransformsAsGaugeField` : the gauge law of a family of gauge-field symbols.
- `GaugeBoson.LorentzTransformsAsGaugeField` : the Lorentz law of a family of gauge-field
  symbols.
- `GaugeBoson.TransformsAsGaugeField.repGauge_commutatorFam` : the gauge law of the derived
  commutators.
- `GaugeBoson.TransformsAsGaugeField.transformsInAdjoint_fieldStrength` : the field strength
  transforms in the adjoint.
- `GaugeBoson.TransformsInAdjoint.covDerivAdjoint` : the covariant derivative preserves the
  adjoint law.
- `GaugeBoson.TransformsAsGaugeField.transformsInAdjoint_iteratedCovDerivAdjoint` : every
  covariant derivative of the field strength transforms in the adjoint.
- `GaugeBoson.TransformsAsGaugeField.repGauge_symmetrizedDeriv_translation` : deep pure jets
  act on the symmetrized derivatives by translations.

## iii. Table of contents

- A. The gauge and Lorentz laws of a gauge field
- B. The gauge law of the derived commutators
- C. The field strength and its covariant derivatives transform in the adjoint
- D. The gauge action on the symmetrized derivatives

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct Lorentz

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

namespace GaugeBoson

/-!

## A. The gauge and Lorentz laws of a gauge field

-/

variable (G) in
/-- A family `A` of gauge-field symbols `∂_s A_μ^φ` transforms as a gauge field under the
  representation `repGauge` of the jet gauge group. A jet `U` acts on `∂_s A_μ^φ` by the
  Leibniz convolution of the dual adjoint Taylor coefficients of `U⁻¹` against lower symbols,
  the multiset antidiagonal carrying the multinomial coefficients, plus the base-point value of
  the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
def TransformsAsGaugeField (repGauge : Representation ℂ G.gaugeJetGroup B)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    Prop :=
  ∀ (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra),
    repGauge U (A s μ φ) =
      (s.antidiagonal.map fun p => A p.2 μ (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + algebraMap ℂ B (φ (G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U⁻¹ μ))))

/-- A family `A` of gauge-field symbols transforms as a gauge field under the Lorentz
  representation `repLorentz`. The symbol carries one covector index, and each derivative slot
  transforms as a covector. -/
def LorentzTransformsAsGaugeField (repLorentz : Representation ℂ SL(2,ℂ) B)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    Prop :=
  ∀ (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra),
    repLorentz Λ (A (List.ofFn l) μ φ) =
      ∑ (p : Fin n → (Fin 1 ⊕ Fin 3)),
        (∏ (i : Fin n), (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
      ∑ a, (((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • A (List.ofFn p) a φ

variable {repGauge : Representation ℂ G.gaugeJetGroup B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
  (hA : TransformsAsGaugeField G repGauge A)
  (hmul : ∀ (U : G.gaugeJetGroup) (b₁ b₂ : B), repGauge U (b₁ * b₂) = repGauge U b₁ * repGauge U b₂)

/-!

## B. The gauge law of the derived commutators

-/

/-- The structural equation of the Maurer–Cartan form of `U⁻¹`, at every derivative order, read
  through a dual vector into the scalars of `B`. -/
lemma algebraMap_maurerCartan_structure (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    algebraMap ℂ B (φ (G.evalLie (G.iteratedDerivJ (μ ::ₘ s) (-G.maurerCartan U⁻¹ ν)))) =
      algebraMap ℂ B (φ (G.evalLie (G.iteratedDerivJ (ν ::ₘ s) (-G.maurerCartan U⁻¹ μ))))
      - (s.antidiagonal.map fun p => algebraMap ℂ B (φ ⁅G.evalLie (G.iteratedDerivJ p.1
          (-G.maurerCartan U⁻¹ μ)), G.evalLie (G.iteratedDerivJ p.2
          (-G.maurerCartan U⁻¹ ν))⁆)).sum := by
  set Θ : G.lieSubalgebra →+ B := ((algebraMap ℂ B).toAddMonoidHom.comp
    ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp φ.toAddMonoidHom)) with hΘdef
  have hΘ : ∀ z : G.lieSubalgebra, algebraMap ℂ B ((φ z : ℝ) : ℂ) = Θ z := fun z => rfl
  simp only [hΘ]
  rw [G.evalLie_iteratedDerivJ_maurerCartan_structure U⁻¹ s μ ν, map_sub, map_multiset_sum,
    Multiset.map_map]
  congr 1

include hA in
/-- The `κ ::ₘ s` case of the gauge law, with the extra derivative traced through. The result
  is the Leibniz splittings where `κ` stays a derivative, minus (by
  `GlobalGaugeGroup.adjointDualCoeff_cons`) the splittings where `κ` hits the adjoint, an
  `ad` of the derived Maurer–Cartan form, plus the derived Maurer–Cartan shift. -/
lemma TransformsAsGaugeField.repGauge_cons
    (U : G.gaugeJetGroup) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (τ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (A (κ ::ₘ s) τ φ) =
      (s.antidiagonal.map fun p =>
        A (κ ::ₘ p.2) τ (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            A p.2 τ (G.adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ q.1
                  (-G.maurerCartan U⁻¹ κ)))))).sum).sum
      + algebraMap ℂ B (φ (G.evalLie (G.iteratedDerivJ (κ ::ₘ s)
          (-G.maurerCartan U⁻¹ τ)))) := by
  rw [hA U (κ ::ₘ s) τ φ]
  congr 1
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        A p.2 τ (G.adjointDualCoeff U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            A p.2 τ (G.adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ q.1
                  (-G.maurerCartan U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [G.adjointDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

include hA hmul in
/-- The all-orders gauge transformation of the derived commutator term. It is the Leibniz
  convolution of the transformed commutator, the two `ad` cross-term convolutions,
  and the convolution of Maurer–Cartan bracket shifts, at every derivative order
  simultaneously. The four-fold splitting is regrouped by `sum_bracketFam_conv_eq`. -/
lemma TransformsAsGaugeField.repGauge_commutatorFam
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (commutatorFam A μ ν s φ) =
      (s.antidiagonal.map fun p =>
        commutatorFam A μ ν p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            A r.2 ν (G.adjointDualCoeff U⁻¹ r.1
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ p.1
                  (-G.maurerCartan U⁻¹ μ)))))).sum).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            A q.2 μ (G.adjointDualCoeff U⁻¹ q.1
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ p.2
                  (-G.maurerCartan U⁻¹ ν)))))).sum).sum
      + (s.antidiagonal.map fun p =>
          algebraMap ℂ B (φ ⁅G.evalLie (G.iteratedDerivJ p.1
              (-G.maurerCartan U⁻¹ μ)),
            G.evalLie (G.iteratedDerivJ p.2
              (-G.maurerCartan U⁻¹ ν))⁆)).sum := by
  -- the affine transformation law of the derived symbols, with the Leibniz sum as a map
  have hAlaw : ∀ (τ : Fin 1 ⊕ Fin 3) (u : Multiset (Fin 1 ⊕ Fin 3))
      (ψ : Module.Dual ℝ G.lieSubalgebra),
      repGauge U (A u τ ψ) =
        ((u.antidiagonal.map fun q => A q.2 τ ∘ₗ G.adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (G.evalLie
            (G.iteratedDerivJ u (-G.maurerCartan U⁻¹ τ)))) := by
    intro τ u ψ
    rw [hA U u τ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  -- expand the left side and split the four convolutions
  rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        repGauge_bracketFam U (hmul U) (hAlaw μ p.1) (hAlaw ν p.2) φ,
        sum_comp_adjointDualCoeff_apply U⁻¹ (fun t => A t ν) p.2,
        sum_comp_adjointDualCoeff_apply U⁻¹ (fun t => A t μ) p.1]),
    Multiset.sum_map_add, Multiset.sum_map_sub, Multiset.sum_map_add,
    sum_bracketFam_conv_eq U⁻¹ A μ (fun t => A t ν) s φ]
  rfl

/-!

## C. The field strength and its covariant derivatives transform in the adjoint

-/

include hA hmul in
/-- The field strength transforms in the adjoint, at every derivative order. Under a gauge
  jet `U` every derivative symbol of `F_μν` transforms by the pure Leibniz convolution of the
  dual adjoint action over the multiset antidiagonal. This is the gauge law of the symbols
  with no Maurer–Cartan shift, since the field strength transforms homogeneously. The
  `κ`-into-the-adjoint splittings of the derivative terms (`TransformsAsGaugeField.repGauge_cons`)
  cancel the `ad` cross-term convolutions of the commutator
  (`TransformsAsGaugeField.repGauge_commutatorFam`) through the coassociativity and swap of
  the antidiagonal, and the derived Maurer–Cartan shifts cancel the bracket-shift
  convolution through the all-orders structural equation. -/
lemma TransformsAsGaugeField.repGauge_fieldStrength
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (fieldStrength A μ ν s φ) =
      (s.antidiagonal.map fun p =>
        fieldStrength A μ ν p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum := by
  have hR : (s.antidiagonal.map fun p =>
      fieldStrength A μ ν p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        A (μ ::ₘ p.2) ν (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
        A (ν ::ₘ p.2) μ (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
        commutatorFam A μ ν p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum := by
    rw [← Multiset.sum_map_sub, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [fieldStrength_apply]
  have hcancel₁ : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        A p.2 ν (G.adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
            (G.iteratedDerivJ q.1 (-G.maurerCartan U⁻¹ μ)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        A r.2 ν (G.adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
            (G.iteratedDerivJ p.1 (-G.maurerCartan U⁻¹ μ)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      A c ν (G.adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
          (G.iteratedDerivJ a (-G.maurerCartan U⁻¹ μ))))))
  have hcancel₂ : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        A p.2 μ (G.adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
            (G.iteratedDerivJ q.1 (-G.maurerCartan U⁻¹ ν)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        A q.2 μ (G.adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
            (G.iteratedDerivJ p.2 (-G.maurerCartan U⁻¹ ν)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc_cycle s (fun a b c =>
      A c μ (G.adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
          (G.iteratedDerivJ a (-G.maurerCartan U⁻¹ ν))))))
  rw [fieldStrength_apply, map_add, map_sub, hA.repGauge_cons U μ s ν φ,
    hA.repGauge_cons U ν s μ φ, hA.repGauge_commutatorFam hmul U s μ ν φ, hR,
    algebraMap_maurerCartan_structure U s μ ν φ, hcancel₁, hcancel₂]
  abel

include hA hmul in
/-- The field strength is an adjoint gauge tensor. This packages
  `TransformsAsGaugeField.repGauge_fieldStrength` as `TransformsInAdjoint`, the base case of
  the covariant-derivative recursion `TransformsInAdjoint.covDerivAdjoint`. -/
lemma TransformsAsGaugeField.transformsInAdjoint_fieldStrength
    (μ ν : Fin 1 ⊕ Fin 3) : TransformsInAdjoint G repGauge (fieldStrength A μ ν) :=
  fun U φ s => hA.repGauge_fieldStrength hmul U s μ ν φ

include hA hmul in
/-- The all-orders gauge transformation of the derived bracket `⁅A_ρ, F⁆` against an
  adjoint gauge tensor `F`. Since `F` transforms homogeneously, only one `ad` cross-term
  convolution survives. This is the analogue of `TransformsAsGaugeField.repGauge_commutatorFam`
  with a gauge tensor in the second slot. -/
lemma TransformsInAdjoint.repGauge_bracketFamConv
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hF : TransformsInAdjoint G repGauge F)
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (bracketFamConv A ρ F s φ) =
      (s.antidiagonal.map fun p =>
        bracketFamConv A ρ F p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            F r.2 (G.adjointDualCoeff U⁻¹ r.1
              (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
                (G.iteratedDerivJ p.1
                  (-G.maurerCartan U⁻¹ ρ)))))).sum).sum := by
  have hAlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ G.lieSubalgebra),
      repGauge U (A u ρ ψ) =
        ((u.antidiagonal.map fun q => A q.2 ρ ∘ₗ G.adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (G.evalLie
            (G.iteratedDerivJ u (-G.maurerCartan U⁻¹ ρ)))) := by
    intro u ψ
    rw [hA U u ρ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hFlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ G.lieSubalgebra),
      repGauge U (F u ψ) =
        ((u.antidiagonal.map fun r => F r.2 ∘ₗ G.adjointDualCoeff U⁻¹ r.1).sum) ψ
        + algebraMap ℂ B (ψ (0 : G.lieSubalgebra)) := by
    intro u ψ
    rw [hF U ψ u, Multiset.sum_linearMap_apply, Multiset.map_map]
    simp only [map_zero, Complex.ofReal_zero, add_zero]
    congr 1
  rw [bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        repGauge_bracketFam U (hmul U) (hAlaw p.1) (hFlaw p.2) φ,
        sum_comp_adjointDualCoeff_apply U⁻¹ F p.2, map_zero,
        LinearMap.comp_zero, map_zero, sub_zero, lie_zero, map_zero,
        Complex.ofReal_zero, map_zero, add_zero]),
    Multiset.sum_map_add, sum_bracketFam_conv_eq U⁻¹ A ρ F s φ]

include hA hmul in
/-- Adjoint gauge tensors are closed under the covariant derivative. If `F` transforms in the
  adjoint, so does `∇_ρ F = [∂_ρ F] + ⁅A_ρ, F⁆`. The single inhomogeneous convolution of
  `[∂_{ρ ::ₘ s} F]` (`TransformsInAdjoint.repGauge_cons`) cancels the single `ad` cross-term
  convolution of `⁅A_ρ, F⁆` (`TransformsInAdjoint.repGauge_bracketFamConv`) through the
  coassociativity of the antidiagonal, and no structural equation is needed. Together with
  `TransformsAsGaugeField.transformsInAdjoint_fieldStrength` this makes every iterated
  covariant derivative of the field strength an adjoint gauge tensor, by recursion. -/
lemma TransformsInAdjoint.covDerivAdjoint
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hF : TransformsInAdjoint G repGauge F) (ρ : Fin 1 ⊕ Fin 3) :
    TransformsInAdjoint G repGauge (GaugeBoson.covDerivAdjoint A F ρ) := by
  intro U φ s
  have hL : repGauge U (GaugeBoson.covDerivAdjoint A F ρ s φ) =
      repGauge U (F (ρ ::ₘ s) φ) + repGauge U (bracketFamConv A ρ F s φ) := by
    rw [covDerivAdjoint_apply, map_add]
  have hR : (s.antidiagonal.map fun p =>
      GaugeBoson.covDerivAdjoint A F ρ p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        F (ρ ::ₘ p.2) (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
        bracketFamConv A ρ F p.2 (G.adjointDualCoeff U⁻¹ p.1 φ)).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [covDerivAdjoint_apply]
  have hcancel : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        F p.2 (G.adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
            (G.iteratedDerivJ q.1
              (-G.maurerCartan U⁻¹ ρ)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        F r.2 (G.adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
            (G.iteratedDerivJ p.1
              (-G.maurerCartan U⁻¹ ρ)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      F c (G.adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
          (G.iteratedDerivJ a (-G.maurerCartan U⁻¹ ρ))))))
  rw [hL, hF.repGauge_cons U ρ s φ, hF.repGauge_bracketFamConv hA hmul U s ρ φ,
    hR, hcancel]
  abel

include hA hmul in
/-- Every iterated covariant derivative of the field strength is an adjoint gauge tensor, by
  the recursion of `TransformsInAdjoint.covDerivAdjoint` over the list of directions, from
  the base case `TransformsAsGaugeField.transformsInAdjoint_fieldStrength`. -/
lemma TransformsAsGaugeField.transformsInAdjoint_iteratedCovDerivAdjoint (l : List (Fin 1 ⊕ Fin 3))
    (ν lam : Fin 1 ⊕ Fin 3) :
    TransformsInAdjoint G repGauge
      (iteratedCovDerivAdjoint A l (fieldStrength A ν lam)) := by
  induction l with
  | nil => exact hA.transformsInAdjoint_fieldStrength hmul ν lam
  | cons ρ l ih => exact TransformsInAdjoint.covDerivAdjoint hA hmul ih ρ

include hA hmul in
/-- The covariant derivatives of the field strength are invariant under the pure jets. -/
lemma TransformsAsGaugeField.repGauge_fieldStrengthTower_of_mem_truncationKer_zero
    (U : G.truncationKer 0)
    (l : List (Fin 1 ⊕ Fin 3)) (ν lam : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U.1 (iteratedCovDerivAdjoint A l (fieldStrength A ν lam) 0 φ) =
      iteratedCovDerivAdjoint A l (fieldStrength A ν lam) 0 φ :=
  TransformsInAdjoint.repGauge_eq_of_mem_truncationKer_zero
    (hA.transformsInAdjoint_iteratedCovDerivAdjoint hmul l ν lam) U φ

/-!

## D. The gauge action on the symmetrized derivatives

-/

include hA in
/-- The gauge transformation of the symmetrized derivatives. Averaging the gauge law of the
  individual derivative symbols over the multiset `s`, the homogeneous part is the
  symmetrized adjoint convolution, and the inhomogeneous Maurer–Cartan shifts average to
  exactly the base-point value of the symmetrized Maurer–Cartan form of `U⁻¹`,

  `U • sym(∂_s A)^φ = (1/|s|) ∑_{μ ∈ s} ∑_{x+y=s−μ} ∂_y A_μ^{∂_x Ad*(U⁻¹) φ}`
  `                   + φ( sym(ω(U⁻¹))_s |₀ )`. -/
lemma TransformsAsGaugeField.repGauge_symmetrizedDeriv
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (symmetrizedDeriv s A φ) =
      (1/(s.card : ℝ)) • (s.map fun μ =>
        ((s - {μ}).antidiagonal.map fun p =>
          A p.2 μ (G.adjointDualCoeff U⁻¹ p.1 φ)).sum).sum
      + algebraMap ℂ B (φ (G.evalLie (G.symmetrizedMaurerCartanForm U⁻¹ s))) := by
  set L : G.jetLieSubalgebra →ₗ[ℝ] B :=
    (Algebra.linearMap ℂ B).restrictScalars ℝ ∘ₗ Algebra.linearMap ℝ ℂ ∘ₗ
      φ ∘ₗ G.evalLie.toLinearMap with hL
  rw [symmetrizedDeriv, LinearMap.map_smul_of_tower, map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def]
  rw [Multiset.map_congr rfl (fun μ _ => hA U (s - {μ}) μ φ),
    Multiset.sum_map_add, smul_add]
  congr 1
  calc (1/(s.card : ℝ)) • (s.map fun μ => algebraMap ℂ B (φ (G.evalLie
        (G.iteratedDerivJ (s - {μ}) (-G.maurerCartan U⁻¹ μ))))).sum
      = (1/(s.card : ℝ)) • (s.map fun μ =>
          L (G.iteratedDerivJ (s - {μ})
            (-G.maurerCartan U⁻¹ μ))).sum := rfl
    _ = L ((1/(s.card : ℝ)) • (s.map fun μ =>
          G.iteratedDerivJ (s - {μ}) (-G.maurerCartan U⁻¹ μ)).sum) := by
        rw [map_smul, map_multiset_sum, Multiset.map_map]
        simp only [Function.comp_def]
    _ = algebraMap ℂ B (φ (G.evalLie (G.symmetrizedMaurerCartanForm U⁻¹ s))) := by
        rw [GlobalGaugeGroup.symmetrizedMaurerCartanForm]
        rfl

include hA in
/-- A pure jet acts on the symmetrized derivatives through the symmetrized Maurer–Cartan
  data. For a gauge jet `U` with identity value, the inhomogeneous shift of `sym(∂_s A)^φ`
  is the pairing of `φ` with the symmetrized Maurer–Cartan coefficient of `U⁻¹` at `s`, the
  very data that classifies pure jets. -/
lemma TransformsAsGaugeField.repGauge_symmetrizedDeriv_truncationKer
    (U : G.truncationKer 0) (s : Multiset (Fin 1 ⊕ Fin 3)) (hs : s ≠ 0)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U.1 (symmetrizedDeriv s A φ) =
      (1/(s.card : ℝ)) • (s.map fun μ =>
        ((s - {μ}).antidiagonal.map fun p =>
          A p.2 μ (G.adjointDualCoeff (U.1)⁻¹ p.1 φ)).sum).sum
      + algebraMap ℂ B (φ (G.symmetrizedMaurerCartanCoeff U⁻¹ ⟨s, hs⟩)) := by
  rw [hA.repGauge_symmetrizedDeriv U.1 s φ]
  rfl

include hA in
/-- Pure translation. When all positive dual adjoint coefficients of `U⁻¹` below the order
  of `s` vanish, the adjoint convolution in the transformation of the symmetrized symbol
  collapses to the symbol itself, and the action is a translation by the symmetrized
  Maurer–Cartan coefficient. -/
lemma TransformsAsGaugeField.repGauge_symmetrizedDeriv_translation
    (U : G.truncationKer 0) (s : Multiset (Fin 1 ⊕ Fin 3)) (hs : s ≠ 0)
    (hU : ∀ x : Multiset (Fin 1 ⊕ Fin 3), x ≠ 0 → x.card < s.card →
      G.adjointDualCoeff (U.1)⁻¹ x = 0)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U.1 (symmetrizedDeriv s A φ) =
      symmetrizedDeriv s A φ +
        algebraMap ℂ B (φ (G.symmetrizedMaurerCartanCoeff U⁻¹ ⟨s, hs⟩)) := by
  rw [hA.repGauge_symmetrizedDeriv_truncationKer U s hs φ]
  congr 1
  have hid : G.adjointDualCoeff (U.1)⁻¹ 0 = LinearMap.id :=
    G.adjointDualCoeff_zero_of_evalGaugeJet_eq_one
      (by rw [map_inv, G.mem_truncationKer_zero_iff_evalGaugeJet.mp U.2, inv_one])
  rw [symmetrizedDeriv]
  congr 1
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => ?_)
  rw [Multiset.sum_antidiagonal_eq_of_fst_ne_zero _ _ fun p hp hp1 => ?_, hid]
  · rfl
  · have h1 := Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)
    have h2 : (s - {μ}).card = s.card - 1 := by
      rw [Multiset.sub_singleton, Multiset.card_erase_of_mem hμ, Nat.pred_eq_sub_one]
    have h3 : s.card ≠ 0 := fun h => hs (Multiset.card_eq_zero.mp h)
    rw [hU p.1 hp1 (by omega)]
    simp

end GaugeBoson
