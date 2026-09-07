/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.Basic
/-!

# Adjoint gauge tensors and the covariant derivative

A family of derivative symbols is an *adjoint gauge tensor* when all its symbols
transform by the pure Leibniz convolution of the dual adjoint action, with no
inhomogeneous term. The convolution is forced: the gauge group acts on the
derivative symbols by substitution and the chain rule, so `U • [∂_s F^φ]` produces
every splitting `s = x + y` — `x` derivatives hitting the adjoint, `y` remaining on
`F`; the naive law `U • [∂_s F^φ] = F^{(∂_s Ad)^* φ}` holds only at `s = 0`.

The two theorems of this section: the field strength is an adjoint gauge tensor
(`transformsInAdjoint_fieldStrength`), and adjoint gauge tensors are closed under
the covariant derivative `∇_ρ F = [∂_ρ F] + ⁅A_ρ, F⁆`
(`TransformsInAdjoint.covDerivAdjoint`) — so by recursion every iterated covariant
derivative of the field strength is an adjoint gauge tensor.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct
variable {B : Type} [Ring B] [Algebra ℂ B]
variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable [GaugeJet G 𝔤 G₀ 𝔤J]

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ G B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}

/-- A family of derivative symbols `F` *transforms in the adjoint* (is an adjoint gauge
  tensor) for the gauge representation `repGauge` when each symbol `[∂_s F^φ]`
  transforms by the Leibniz convolution of the dual adjoint coefficients against lower
  symbols — the shape of `gauge_apply_deriv` with no Maurer–Cartan shift. At `s = 0`
  this is the homogeneous law `U • F^φ = F^{Ad₀^* φ}`. -/
def TransformsInAdjoint (repGauge : Representation ℂ G B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B) : Prop :=
  ∀ (U : G) (φ : Module.Dual ℝ 𝔤) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (F s φ) =
      (s.antidiagonal.map fun p => F p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum

/-- **The derived bracket family** `⁅A_ρ, F⁆`: the `s`-derivative of the bracket of the
  gauge field against a family, given by the Leibniz convolution of the derivative
  symbols over the multiset antidiagonal. -/
noncomputable def bracketFamConv
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  (s.antidiagonal.map fun p => bracketFam (A p.1 ρ) (F p.2)).sum

/-- The covariant derivative `∇_ρ F = [∂_ρ F] + ⁅A_ρ, F⁆` of an adjoint-valued family
  of derivative symbols: the extra derivative on the symbol plus the derived bracket
  against the gauge field. The gauge-algebra bracket carries the physicists' `i`, so
  in matrix terms this is `∂_ρ F + i [A_ρ, F]` — the adjoint-representation covariant
  derivative in the same `D = ∂ + i A` convention as the field strength. It preserves
  `TransformsInAdjoint` (`TransformsInAdjoint.covDerivAdjoint`). -/
noncomputable def covDerivAdjoint
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  F (ρ ::ₘ s) + bracketFamConv A ρ F s

@[simp]
lemma covDerivAdjoint_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    covDerivAdjoint A F ρ s φ = F (ρ ::ₘ s) φ + bracketFamConv A ρ F s φ := rfl

/-!

## The iterated covariance of the covariant derivative

-/

/-- If `F` transforms in the adjoint, so do its `κ ::ₘ s`-derived symbols with the
  extra derivative traced through `adjointDualCoeff_cons`: the Leibniz splittings
  where `κ` stays a derivative, minus the convolution where `κ` hits the adjoint —
  an `ad` of the derived Maurer–Cartan form. -/
lemma TransformsInAdjoint.repGauge_cons
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
    (hF : TransformsInAdjoint repGauge F)
    (U : G) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ 𝔤) :
    repGauge U (F (κ ::ₘ s) φ) =
      (s.antidiagonal.map fun p =>
        F (κ ::ₘ p.2) (adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
                (GaugeJet.iteratedDeriv G 𝔤 q.1
                  (GaugeJet.mc 𝔤 (G := G) U⁻¹ κ)))))).sum).sum := by
  rw [hF U φ (κ ::ₘ s)]
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        F p.2 (adjointDualCoeff U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (adjointDualCoeff U⁻¹ q.2
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
                (GaugeJet.iteratedDeriv G 𝔤 q.1
                  (GaugeJet.mc 𝔤 (G := G) U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [adjointDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

set_option maxHeartbeats 2000000 in
/-- The all-orders gauge transformation of the derived bracket `⁅A_ρ, F⁆` against an
  adjoint gauge tensor `F`: since `F` transforms homogeneously, only one `ad`
  cross-term convolution survives — the analogue of `repGauge_commutatorFam`
  with a gauge tensor in the second slot. -/
lemma TransformsInAdjoint.repGauge_bracketFamConv
    (hA : IsGaugeField repLorentz repGauge A)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
    (hF : TransformsInAdjoint repGauge F)
    (U : G) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repGauge U (bracketFamConv A ρ F s φ) =
      (s.antidiagonal.map fun p =>
        bracketFamConv A ρ F p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            F r.2 (adjointDualCoeff U⁻¹ r.1
              (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
                (GaugeJet.iteratedDeriv G 𝔤 p.1
                  (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ)))))).sum).sum := by
  have hAlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ 𝔤),
      repGauge U (A u ρ ψ) =
        ((u.antidiagonal.map fun q => A q.2 ρ ∘ₗ adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 u (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ)))) := by
    intro u ψ
    rw [hA.gauge_apply_deriv U u ρ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hFlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ 𝔤),
      repGauge U (F u ψ) =
        ((u.antidiagonal.map fun r => F r.2 ∘ₗ adjointDualCoeff U⁻¹ r.1).sum) ψ
        + algebraMap ℂ B (ψ (0 : 𝔤)) := by
    intro u ψ
    rw [hF U ψ u, Multiset.sum_linearMap_apply, Multiset.map_map]
    simp only [map_zero, Complex.ofReal_zero, add_zero]
    congr 1
  have hMa : (s.antidiagonal.map fun p =>
      bracketFam ((p.1.antidiagonal.map fun q => A q.2 ρ ∘ₗ adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r => F r.2 ∘ₗ adjointDualCoeff U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (A q.2 ρ ∘ₗ adjointDualCoeff U⁻¹ q.1)
              (F r.2 ∘ₗ adjointDualCoeff U⁻¹ r.1) φ).sum).sum).sum := by
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
      bracketFamConv A ρ F p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            bracketFam (A r.1 ρ ∘ₗ adjointDualCoeff U⁻¹ q.1)
              (F r.2 ∘ₗ adjointDualCoeff U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_congr rfl (fun r hr => by
        rw [Function.comp_apply,
          bracketFam_adjointDualCoeff U⁻¹ p.1 (A r.1 ρ) (F r.2) φ]),
      Multiset.sum_map_sum_map]
  have hM := hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      bracketFam (A b ρ ∘ₗ adjointDualCoeff U⁻¹ a)
        (F d ∘ₗ adjointDualCoeff U⁻¹ c) φ).trans hMc.symm)
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r => F r.2 ∘ₗ adjointDualCoeff U⁻¹ r.1).sum)
        (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
          (GaugeJet.iteratedDeriv G 𝔤 p.1 (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ)))) =
      (p.2.antidiagonal.map fun r =>
        F r.2 (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 p.1 (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  rw [bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        hA.repGauge_bracketFam U (hAlaw p.1) (hFlaw p.2) φ, hCg p, map_zero,
        LinearMap.comp_zero, map_zero, sub_zero, lie_zero, map_zero,
        Complex.ofReal_zero, map_zero, add_zero]),
    Multiset.sum_map_add, hM]

set_option maxHeartbeats 2000000 in
/-- **Adjoint gauge tensors are closed under the covariant derivative**: if `F`
  transforms in the adjoint, so does `∇_ρ F = [∂_ρ F] + ⁅A_ρ, F⁆`. The single
  inhomogeneous convolution of `[∂_{ρ ::ₘ s} F]`
  (`TransformsInAdjoint.repGauge_cons`) cancels the single `ad` cross-term
  convolution of `⁅A_ρ, F⁆` (`TransformsInAdjoint.repGauge_bracketFamConv`)
  through the coassociativity of the antidiagonal; no structural equation is needed.
  Together with `transformsInAdjoint_fieldStrength` this makes every iterated
  covariant derivative of the field strength an adjoint gauge tensor, by recursion. -/
theorem TransformsInAdjoint.covDerivAdjoint
    (hA : IsGaugeField repLorentz repGauge A)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
    (hF : TransformsInAdjoint repGauge F) (ρ : Fin 1 ⊕ Fin 3) :
    TransformsInAdjoint repGauge (IsGaugeField.covDerivAdjoint A F ρ) := by
  intro U φ s
  have hL : repGauge U (IsGaugeField.covDerivAdjoint A F ρ s φ) =
      repGauge U (F (ρ ::ₘ s) φ) + repGauge U (bracketFamConv A ρ F s φ) := by
    rw [covDerivAdjoint_apply, map_add]
  have hR : (s.antidiagonal.map fun p =>
      IsGaugeField.covDerivAdjoint A F ρ p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        F (ρ ::ₘ p.2) (adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
        bracketFamConv A ρ F p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [covDerivAdjoint_apply]
  have hcancel : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        F p.2 (adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 q.1
              (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        F r.2 (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 p.1
              (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      F c (adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
          (GaugeJet.iteratedDeriv G 𝔤 a (GaugeJet.mc 𝔤 (G := G) U⁻¹ ρ))))))
  rw [hL, hF.repGauge_cons U ρ s φ, hF.repGauge_bracketFamConv hA U s ρ φ,
    hR, hcancel]
  abel

end IsGaugeField

