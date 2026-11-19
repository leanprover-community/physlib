/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.GaugeJetAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.CovariantDeriv
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.GaugeLaw
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Truncation
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.JetRep
/-!
# The infinitesimal action underlying a matter representation

The compatibility of a Lie-algebra action with a jet representation, and the covariance of the
covariant derivative it implies.

## i. Overview

The covariant derivative `∇_ρ F = [∂_ρ F] + A_ρ · F` of a matter family is built from
an action `act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V` of the gauge algebra on the value space. For the
covariant derivative to transform covariantly, `act` must be the *infinitesimal action*
underlying the representation `rep` of the jet gauge group in which the family
transforms — the physicists' statement that the matrices `i dρ(T^a)` generate `rep`.
This file packages that compatibility as the structure `IsInfinitesimalActionOf`, and
proves the theorem it exists for. Call a family `F` of symbols a gauge tensor of `rep` when
each derivative symbol `[∂_s F^φ]` transforms by the Leibniz convolution of the base-point
Taylor coefficients of `rep` against the lower symbols, with no inhomogeneous term. Then the
covariant derivative of a gauge tensor is again one,
`IsInfinitesimalActionOf.repGauge_covDerivAction`, and by induction so is every iterated
covariant derivative. The gauge field may be any family transforming as a gauge field,
`GaugeBoson.TransformsAsGaugeField`, under an action of the jet gauge group by multiplicative
maps.

Everything is stated over a global gauge group `G : GlobalGaugeGroup κ`; nothing depends on the
Standard Model choice of it. The last sections show that for a matter field `M` the Lie
algebra action `M.repAlgebra` is the infinitesimal action underlying its jet action `M.repJet`,
that pure jets act trivially at the base point, and record the condition that the gauge and
Lorentz actions on the target space commute. This is `MatterField.GaugeLorentzCommute` for the
group and `MatterField.GaugeLorentzCompatible` for the Lie algebra, and the first implies the
second.

## ii. Key results

- `GlobalGaugeGroup.IsInfinitesimalActionOf` : `act` is the infinitesimal action underlying
  `rep`.
- `GlobalGaugeGroup.IsInfinitesimalActionOf.repGauge_covDerivAction` : the covariant derivative
  preserves the Leibniz transformation law of a family of symbols.
- `GlobalGaugeGroup.IsInfinitesimalActionOf.repGauge_covDerivIter` : so does every iterated
  covariant derivative, and `repGauge_covDerivIter_zero` is its underived symbol.
- `GlobalGaugeGroup.IsInfinitesimalActionOf.conj` : the conjugate action underlies the
  conjugate representation.
- `GlobalGaugeGroup.IsInfinitesimalActionOf.eq_of_repCoeff_zero` : a fibrewise representation
  is determined by its infinitesimal action and its base-point values.
- `GlobalGaugeGroup.MatterField.isInfinitesimalActionOf` : `dρ` is the infinitesimal
  action underlying the jet action of a matter field.
- `GlobalGaugeGroup.repDualCoeff_inv_zero_eq_ofConstant_eval` : if pure jets act trivially at
  the base point, the base-point action of a jet factors through its value.
- `GlobalGaugeGroup.MatterField.repCoeff_zero_of_eval_eq_one` : pure jets act trivially
  at the base point.
- `GlobalGaugeGroup.MatterField.GaugeLorentzCommute`,
  `GlobalGaugeGroup.MatterField.GaugeLorentzCompatible` : the gauge and Lorentz actions
  commute, at the level of the group and of the Lie algebra.
- `GlobalGaugeGroup.MatterField.GaugeLorentzCommute.gaugeLorentzCompatible` : the first
  condition implies the second.

## iii. Table of contents

- A. The infinitesimal action underlying a representation
- B. The covariant derivative preserves the transformation law
- C. The conjugate action and the conjugate representation
- D. Uniqueness
- E. Factorization through evaluation
- F. The infinitesimal action of a matter field
- G. Pure jets act trivially
- H. Compatibility of the gauge and Lorentz actions

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct MvPowerSeries

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

namespace GlobalGaugeGroup

open GaugeBoson (dualPairEquiv symm_comp_right)

variable {repGauge : Representation ℂ G.gaugeJetGroup B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
  (hA : GaugeBoson.TransformsAsGaugeField G repGauge A)
  (hmul : ∀ (U : G.gaugeJetGroup) (b₁ b₂ : B), repGauge U (b₁ * b₂) = repGauge U b₁ * repGauge U b₂)

/-!

## A. The infinitesimal action underlying a representation

-/

/-- `act` is the *infinitesimal action* of the gauge algebra underlying the
  representation `rep` of the jet gauge group, when the base-point Taylor
  coefficients of `rep` satisfy the two laws forced by `rep` being generated by
  `act`.

  * `repCoeff_cons` is the Leibniz rule in the Maurer–Cartan form. Differentiating
    the representation once produces minus the action of the Maurer–Cartan form,
    with the remaining derivatives distributed over the antidiagonal (for the
    adjoint representation this is `GlobalGaugeGroup.adjointCoeff_cons`);
  * `repCoeff_act` says that the transports of `rep` intertwine `act` with the adjoint
    transports, as an antidiagonal convolution (for the adjoint representation this
    is `GlobalGaugeGroup.adjointCoeff_lie`); at `x = 0` it is the classical equivariance
    `rep(U)|₀ ∘ act c = act (Ad(U) c)|₀ ∘ rep(U)|₀`.

  These are exactly the identities consumed by the proof that the covariant
  derivative `covDerivAction` preserves the Leibniz transformation law of a family. -/
structure IsInfinitesimalActionOf (G : GlobalGaugeGroup κ)
    (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V)) : Prop where
  repCoeff_cons : ∀ (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3)),
    repCoeff rep U (μ ::ₘ x) =
      -((x.antidiagonal.map fun p =>
        act (G.evalLie (G.iteratedDerivJ p.1
          (-G.maurerCartan U μ))) ∘ₗ
          repCoeff rep U p.2).sum)
  repCoeff_act : ∀ (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) (c : G.lieSubalgebra),
    repCoeff rep U x ∘ₗ act c =
      ((x.antidiagonal.map fun p =>
        act (G.adjointCoeff U p.1 c) ∘ₗ repCoeff rep U p.2).sum)

/-- The dual form of the Leibniz law. The once-more-derived dual coefficient is
  minus the antidiagonal convolution of dual coefficients against `act` of the
  derived Maurer–Cartan form — the analogue of `GlobalGaugeGroup.adjointDualCoeff_cons`. -/
lemma IsInfinitesimalActionOf.repDualCoeff_cons
    {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V}
    {rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V)}
    (h : IsInfinitesimalActionOf G act rep) (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repDualCoeff rep U (μ ::ₘ x) φ =
      -((x.antidiagonal.map fun p =>
        repDualCoeff rep U p.2 (φ ∘ₗ act (G.evalLie
          (G.iteratedDerivJ p.1 (-G.maurerCartan U μ))))).sum) := by
  refine LinearMap.ext fun v => ?_
  have h1 := LinearMap.congr_fun (h.repCoeff_cons U μ x) v
  simp only [LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
    Function.comp_apply, LinearMap.coe_comp] at h1
  simp only [repDualCoeff, LinearMap.dualMap_apply, LinearMap.neg_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_apply,
    LinearMap.coe_comp]
  rw [h1, map_neg, map_multiset_sum, Multiset.map_map]
  exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))

/-!

## B. The covariant derivative preserves the transformation law

-/

section MatterCovariance

variable {rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V)}
variable {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V}
variable [FiniteDimensional ℂ V]

/-- The action of families against the dual representation coefficients, the
  antidiagonal convolution mixing the adjoint transport on the field slot with the
  representation transport on the matter slot — the family-level form of
  `IsInfinitesimalActionOf.repCoeff_act`, and the analogue of
  `GaugeBoson.bracketFam_adjointDualCoeff`. -/
lemma IsInfinitesimalActionOf.actionFam_repDualCoeff
    (h : IsInfinitesimalActionOf G act rep) (U : G.gaugeJetGroup)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (g : Module.Dual ℂ V →ₗ[ℂ] B) (φ : Module.Dual ℂ V) :
    actionFam act f g (repDualCoeff rep U x φ) =
      (x.antidiagonal.map fun p =>
        actionFam act (f ∘ₗ G.adjointDualCoeff U p.1)
          (g ∘ₗ repDualCoeff rep U p.2) φ).sum := by
  have hT : ∀ (c : G.lieSubalgebra) (v : V), repCoeff rep U x (act c v) =
      (x.antidiagonal.map fun p =>
        act (G.adjointCoeff U p.1 c) (repCoeff rep U p.2 v)).sum := by
    intro c v
    have h1 := LinearMap.congr_fun (h.repCoeff_act U x c) v
    simpa [Multiset.sum_linearMap_apply, Multiset.map_map, LinearMap.coe_comp,
      Function.comp_apply] using h1
  rw [show repDualCoeff rep U x = (repCoeff rep U x).dualMap from rfl,
    show actionFam act f g ((repCoeff rep U x).dualMap φ) =
      dualPairEquivC ((TensorProduct.map LinearMap.id (repCoeff rep U x))
        (tensorAction act (dualPairEquiv.symm f) (dualPairEquivC.symm g))) φ from
      (dualPairEquivC_map_right (repCoeff rep U x) _ φ).symm,
    ← tensorAction_map_right_antidiagonal act (G.adjointCoeff U) (repCoeff rep U) x hT,
    map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [← symm_comp_right, ← symm_comp_right_C]
  rfl

omit [FiniteDimensional ℂ V] in
/-- If `F` transforms by the Leibniz law of `rep`, the transformation of its `κ ::ₘ s`-derived
  symbols has the extra derivative traced through `IsInfinitesimalActionOf.repDualCoeff_cons`,
  giving the Leibniz splittings where `κ` stays a derivative, minus the convolution where `κ`
  hits the representation, `act` of the derived Maurer–Cartan form. -/
lemma IsInfinitesimalActionOf.repGauge_cons (hact : IsInfinitesimalActionOf G act rep)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : ∀ (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
      repGauge U (F s φ) = (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum)
    (U : G.gaugeJetGroup) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    repGauge U (F (κ ::ₘ s) φ) =
      (s.antidiagonal.map fun p =>
        F (κ ::ₘ p.2) (repDualCoeff rep U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (repDualCoeff rep U⁻¹ q.2
              (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ q.1
                (-G.maurerCartan U⁻¹ κ)))))).sum).sum := by
  rw [hF U φ (κ ::ₘ s)]
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        F p.2 (repDualCoeff rep U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (repDualCoeff rep U⁻¹ q.2
              (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ q.1
                (-G.maurerCartan U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hact.repDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

/-- The action of the transformed gauge-field symbols on the transformed matter symbols,
  summed over the antidiagonal, is the antidiagonal convolution of the derived action `A_ρ · F`
  against the dual representation coefficients. It is the homogeneous part of the
  transformation of `A_ρ · F`, rearranged by the coassociativity of the antidiagonal. -/
lemma IsInfinitesimalActionOf.sum_actionFam_conv_eq (hact : IsInfinitesimalActionOf G act rep)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ V) :
    (s.antidiagonal.map fun p =>
      actionFam act ((p.1.antidiagonal.map fun q =>
          A q.2 ρ ∘ₗ G.adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r =>
          F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        actionFamConv A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum := by
  have hMa : (s.antidiagonal.map fun p =>
      actionFam act ((p.1.antidiagonal.map fun q =>
          A q.2 ρ ∘ₗ G.adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r =>
          F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            actionFam act (A q.2 ρ ∘ₗ G.adjointDualCoeff U⁻¹ q.1)
              (F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [actionFam_sum_left, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [actionFam_sum_right, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
  have hMc : (s.antidiagonal.map fun p =>
      actionFamConv A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            actionFam act (A r.1 ρ ∘ₗ G.adjointDualCoeff U⁻¹ q.1)
              (F r.2 ∘ₗ repDualCoeff rep U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_congr rfl (fun r hr => by
        rw [Function.comp_apply,
          hact.actionFam_repDualCoeff U⁻¹ p.1 (A r.1 ρ) (F r.2) φ]),
      Multiset.sum_map_sum_map]
  exact hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      actionFam act (A b ρ ∘ₗ G.adjointDualCoeff U⁻¹ a)
        (F d ∘ₗ repDualCoeff rep U⁻¹ c) φ).trans hMc.symm)

include hA hmul in
/-- The all-orders gauge transformation of the derived action `A_ρ · F` for `F`
  transforming by the Leibniz law of `rep`. Since `F` transforms homogeneously, only one
  cross-term convolution through `act` survives — the analogue of
  `GaugeBoson.TransformsInAdjoint.repGauge_bracketFamConv` with a matter field in the second
  slot. -/
lemma IsInfinitesimalActionOf.repGauge_actionFamConv (hact : IsInfinitesimalActionOf G act rep)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : ∀ (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
      repGauge U (F s φ) = (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum)
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ V) :
    repGauge U (actionFamConv A act ρ F s φ) =
      (s.antidiagonal.map fun p =>
        actionFamConv A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            F r.2 (repDualCoeff rep U⁻¹ r.1
              (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ p.1
                (-G.maurerCartan U⁻¹ ρ)))))).sum).sum := by
  have hAlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ G.lieSubalgebra),
      repGauge U (A u ρ ψ) =
        ((u.antidiagonal.map fun q => A q.2 ρ ∘ₗ G.adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (G.evalLie
            (G.iteratedDerivJ u (-G.maurerCartan U⁻¹ ρ)))) := by
    intro u ψ
    rw [hA U u ρ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hFlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℂ V),
      repGauge U (F u ψ) =
        ((u.antidiagonal.map fun r => F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum) ψ := by
    intro u ψ
    rw [hF U ψ u, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hM := hact.sum_actionFam_conv_eq (A := A) (F := F) U s ρ φ
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r => F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum)
        (φ ∘ₗ act (G.evalLie
          (G.iteratedDerivJ p.1 (-G.maurerCartan U⁻¹ ρ)))) =
      (p.2.antidiagonal.map fun r =>
        F r.2 (repDualCoeff rep U⁻¹ r.1
          (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ p.1
            (-G.maurerCartan U⁻¹ ρ)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        repGauge_actionFam U (hmul U) (hAlaw p.1) (hFlaw p.2) φ, hCg p]),
    Multiset.sum_map_add, hM]

include hA hmul in
/-- The covariant derivative preserves the transformation law. If each derivative symbol of `F`
  transforms by the Leibniz convolution of the coefficients of `rep`, and `act` is the
  infinitesimal action underlying `rep`, then so does each derivative symbol of
  `∇_ρ F = [∂_ρ F] + A_ρ · F`. The single inhomogeneous
  convolution of `[∂_{ρ ::ₘ s} F]` cancels the single `act` cross-term convolution of
  `A_ρ · F` through the coassociativity of the antidiagonal — the matter-field
  analogue of `GaugeBoson.TransformsInAdjoint.covDerivAdjoint`. -/
lemma IsInfinitesimalActionOf.repGauge_covDerivAction (hact : IsInfinitesimalActionOf G act rep)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : ∀ (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
      repGauge U (F s φ) = (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum)
    (ρ : Fin 1 ⊕ Fin 3) (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repGauge U (GlobalGaugeGroup.covDerivAction A act F ρ s φ) =
      (s.antidiagonal.map fun p => GlobalGaugeGroup.covDerivAction A act F ρ p.2
        (repDualCoeff rep U⁻¹ p.1 φ)).sum := by
  have hL : repGauge U (GlobalGaugeGroup.covDerivAction A act F ρ s φ) =
      repGauge U (F (ρ ::ₘ s) φ) + repGauge U (actionFamConv A act ρ F s φ) := by
    rw [GlobalGaugeGroup.covDerivAction_apply, map_add]
  have hR : (s.antidiagonal.map fun p =>
      GlobalGaugeGroup.covDerivAction A act F ρ p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        F (ρ ::ₘ p.2) (repDualCoeff rep U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
        actionFamConv A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [GlobalGaugeGroup.covDerivAction_apply]
  have hcancel : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        F p.2 (repDualCoeff rep U⁻¹ q.2
          (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ q.1
            (-G.maurerCartan U⁻¹ ρ)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        F r.2 (repDualCoeff rep U⁻¹ r.1
          (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ p.1
            (-G.maurerCartan U⁻¹ ρ)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      F c (repDualCoeff rep U⁻¹ b
        (φ ∘ₗ act (G.evalLie (G.iteratedDerivJ a
          (-G.maurerCartan U⁻¹ ρ))))))
  rw [hL, hact.repGauge_cons hF U ρ s φ, hact.repGauge_actionFamConv hA hmul hF U s ρ φ,
    hR, hcancel]
  abel

include hA hmul in
/-- Every iterated covariant derivative preserves the transformation law. If each derivative
  symbol of `F` transforms by the Leibniz convolution of the coefficients of `rep`, and `act` is
  the infinitesimal action underlying `rep`, then so does each derivative symbol of
  `∇_{l 0} ⋯ ∇_{l (n-1)} F`. This is induction on the number `n` of covariant derivatives,
  each step being `IsInfinitesimalActionOf.repGauge_covDerivAction`. -/
lemma IsInfinitesimalActionOf.repGauge_covDerivIter (hact : IsInfinitesimalActionOf G act rep)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : ∀ (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
      repGauge U (F s φ) = (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repGauge U (GlobalGaugeGroup.covDerivIter A act F n l s φ) =
      (s.antidiagonal.map fun p => GlobalGaugeGroup.covDerivIter A act F n l p.2
        (repDualCoeff rep U⁻¹ p.1 φ)).sum := by
  induction n generalizing U φ s with
  | zero => exact hF U φ s
  | succ n ih => exact hact.repGauge_covDerivAction hA hmul (ih fun i => l i.succ) (l 0) U φ s

include hA hmul in
/-- The underived symbol of an iterated covariant derivative transforms through the
  base-point coefficient alone, since the antidiagonal of the empty multiset has a single term. -/
lemma IsInfinitesimalActionOf.repGauge_covDerivIter_zero
    (hact : IsInfinitesimalActionOf G act rep)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : ∀ (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
      repGauge U (F s φ) = (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) :
    repGauge U (GlobalGaugeGroup.covDerivIter A act F n l 0 φ) =
      GlobalGaugeGroup.covDerivIter A act F n l 0 (repDualCoeff rep U⁻¹ 0 φ) := by
  simpa only [Multiset.antidiagonal_zero, Multiset.map_singleton, Multiset.sum_singleton] using
    hact.repGauge_covDerivIter hA hmul hF n l U φ 0

end MatterCovariance

/-!

## C. The conjugate action and the conjugate representation

-/

section ConjugateAction

/-- The conjugate of an infinitesimal action. It is the same maps, read on the conjugate
  module, the generators of the conjugate representation. -/
noncomputable def actionConj (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) :
    G.lieSubalgebra →ₗ[ℝ] ConjModule V →ₗ[ℂ] ConjModule V where
  toFun c := ConjModule.endConj (act c)
  map_add' c₁ c₂ := by rw [map_add, ConjModule.endConj_add]
  map_smul' r c := by rw [map_smul, ConjModule.endConj_real_smul, RingHom.id_apply]

@[simp]
lemma actionConj_apply (act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V) (c : G.lieSubalgebra) :
    actionConj act c = ConjModule.endConj (act c) := rfl

/-- The identification of the jets of a conjugate field with the conjugates of the
  jets. Conjugation is monoidal, and the star of the jet-ring factor absorbs the
  twist — `conj (g ⊗ u) ↦ star g ⊗ conj u`. This is the equivalence along which
  `FieldDerivSpace.repConj` carries the conjugated representation. -/
noncomputable def conjJetEquiv :
    ConjModule (SpaceTimeAlgebra ⊗[ℂ] V) ≃ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] ConjModule V :=
  (ConjModule.tensorEquiv (k := ℂ) (M := SpaceTimeAlgebra) (N := V)).symm.trans
    (TensorProduct.congr SpaceTimeAlgebra.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V)))

lemma conjJetEquiv_conjEquiv_tmul (g : SpaceTimeAlgebra) (u : V) :
    conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) (g ⊗ₜ[ℂ] u))
      = star g ⊗ₜ[ℂ] conjEquiv (k := ℂ) (M := V) u := by
  rw [conjJetEquiv, LinearEquiv.trans_apply, ConjModule.tensorEquiv_symm_conjEquiv_tmul,
    TensorProduct.congr_tmul, SpaceTimeAlgebra.starConjEquiv_apply, LinearEquiv.refl_apply,
    LinearEquiv.symm_apply_apply]

section ConjRep

variable {rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V)}
variable {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V}

/-- The conjugate representation acts through `conjJetEquiv` by the original maps. -/
lemma repConj_conjJetEquiv (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : G.gaugeJetGroup) (w : SpaceTimeAlgebra ⊗[ℂ] V) :
    FieldDerivSpace.repConj rep U
        (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
      = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) (rep U w)) := by
  show conjJetEquiv ((rep.conj U) (conjJetEquiv.symm
      (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w)))) = _
  rw [LinearEquiv.symm_apply_apply, Representation.conj_apply,
    LinearEquiv.symm_apply_apply]

/-- The base-point Taylor coefficients of the conjugate representation are the
  conjugated coefficients. The derivative directions are real, so conjugation passes
  through `∂_x` and the base-point evaluation untouched. -/
lemma repCoeff_repConj (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff (FieldDerivSpace.repConj rep) U x
      = ConjModule.endConj (repCoeff rep U x) := by
  have hE_tmul := conjJetEquiv_conjEquiv_tmul (V := V)
  -- conjugation intertwines the formal derivative
  have hderiv1 : ∀ (μ : Fin 1 ⊕ Fin 3) (w : SpaceTimeAlgebra ⊗[ℂ] V),
      jetDeriv μ (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
        = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) (jetDeriv μ w)) := by
    intro μ w
    induction w using TensorProduct.inductionOn with
    | tmul g u =>
        rw [hE_tmul, jetDeriv_tmul, jetDeriv_tmul, hE_tmul, SpaceTimeAlgebra.pderiv_star]
    | add a b ha hb =>
        rw [map_add, map_add, map_add, ha, hb, map_add, map_add, map_add]
  have hderiv : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (w : SpaceTimeAlgebra ⊗[ℂ] V),
      jetIteratedDeriv s (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
        = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V)
            (jetIteratedDeriv s w)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro w; rw [jetIteratedDeriv_zero]; rfl
    | cons μ t ih =>
        intro w
        rw [jetIteratedDeriv_cons, LinearMap.comp_apply, ih, hderiv1,
          jetIteratedDeriv_cons, LinearMap.comp_apply]
  -- conjugation intertwines the base-point evaluation
  have heval : ∀ w : SpaceTimeAlgebra ⊗[ℂ] V,
      jetEval (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
        = conjEquiv (k := ℂ) (M := V) (jetEval w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul g u =>
        rw [hE_tmul, jetEval_tmul, jetEval_tmul, SpaceTimeAlgebra.constantCoeff_star,
          map_smulₛₗ, starRingEnd_apply]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, map_add]
  refine LinearMap.ext fun v => ?_
  have hv : jetOfConstant v = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V)
      (jetOfConstant ((conjEquiv (k := ℂ) (M := V)).symm v))) := by
    rw [jetOfConstant_apply, jetOfConstant_apply, hE_tmul, star_one,
      LinearEquiv.apply_symm_apply]
  show jetEval (jetIteratedDeriv x
    (FieldDerivSpace.repConj rep U (jetOfConstant v))) = _
  rw [hv, repConj_conjJetEquiv, hderiv, heval]
  rfl

/-- The base-point triviality of the zeroth Taylor coefficient passes to the
  conjugate representation. -/
lemma repCoeff_repConj_zero_eq_id {W : G.gaugeJetGroup}
    (hrep : repCoeff rep W 0 = LinearMap.id) :
    repCoeff (FieldDerivSpace.repConj rep) W 0 = LinearMap.id := by
  rw [repCoeff_repConj, hrep, ConjModule.endConj_id]

/-- The conjugate of an infinitesimal action underlies the conjugate
  representation. Conjugating the Taylor coefficients preserves both the
  Maurer–Cartan Leibniz law and the adjoint intertwining, since the gauge-algebra
  inputs are real. -/
lemma IsInfinitesimalActionOf.conj (h : IsInfinitesimalActionOf G act rep) :
    IsInfinitesimalActionOf G (actionConj act) (FieldDerivSpace.repConj rep) := by
  constructor
  · intro U μ x
    rw [repCoeff_repConj, h.repCoeff_cons U μ x, ConjModule.endConj_neg,
      ConjModule.endConj_multiset_sum, Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum
      (Multiset.map_congr rfl fun p hp => ?_))
    rw [Function.comp_apply, ConjModule.endConj_comp, repCoeff_repConj]
    rfl
  · intro U x c
    rw [repCoeff_repConj, show actionConj act c = ConjModule.endConj (act c) from rfl,
      ← ConjModule.endConj_comp, h.repCoeff_act U x c,
      ConjModule.endConj_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, ConjModule.endConj_comp, repCoeff_repConj]
    rfl

end ConjRep

end ConjugateAction

/-!

## D. Uniqueness

A representation generated by an infinitesimal action is determined, Taylor coefficient by
Taylor coefficient, by its values at the base point: `repCoeff_cons` expresses each
coefficient through coefficients of lower order.

-/

section Uniqueness

variable {rep rep' : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V)}
variable {act : G.lieSubalgebra →ₗ[ℝ] V →ₗ[ℂ] V}

/-- Two representations with the same infinitesimal action and the same base-point values
  of a gauge jet have the same Taylor coefficients at that jet. -/
lemma IsInfinitesimalActionOf.repCoeff_eq_of_repCoeff_zero
    (h : IsInfinitesimalActionOf G act rep) (h' : IsInfinitesimalActionOf G act rep')
    {U : G.gaugeJetGroup} (h0 : repCoeff rep U 0 = repCoeff rep' U 0)
      (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff rep U x = repCoeff rep' U x := by
  induction x using Multiset.strongInductionOn with
  | ih s ih =>
    rcases Multiset.empty_or_exists_mem s with rfl | ⟨μ, hμ⟩
    · exact h0
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hμ
    rw [h.repCoeff_cons, h'.repCoeff_cons]
    refine congrArg (fun m => -Multiset.sum m) (Multiset.map_congr rfl fun p hp => ?_)
    rw [ih p.2 (lt_of_le_of_lt (Multiset.snd_le_of_mem_antidiagonal hp)
      (Multiset.lt_cons_self t μ))]

/-- A fibrewise representation is determined by its infinitesimal action and its
  base-point values. Two fibrewise representations generated by the same action, with the
  same value `repCoeff · U 0` at every gauge jet, are equal. -/
lemma IsInfinitesimalActionOf.eq_of_repCoeff_zero [FiniteDimensional ℂ V]
    (h : IsInfinitesimalActionOf G act rep) (h' : IsInfinitesimalActionOf G act rep')
    (hs : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) z, rep U (χ • z) = χ • rep U z)
    (hs' : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) z, rep' U (χ • z) = χ • rep' U z)
    (h0 : ∀ U, repCoeff rep U 0 = repCoeff rep' U 0) : rep = rep' := by
  refine MonoidHom.ext fun U => TensorProduct.ext' fun f v => ?_
  have hc : rep U (jetOfConstant v) = rep' U (jetOfConstant v) :=
    jet_ext_of_jetDerivValue fun s =>
      LinearMap.congr_fun (h.repCoeff_eq_of_repCoeff_zero h' (h0 U) s) v
  have hf : f ⊗ₜ[ℂ] v = f • jetOfConstant v := by
    rw [jetOfConstant_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hf, hs, hs', hc]

end Uniqueness

/-!

## E. Factorization through evaluation

If pure jets act trivially at the base point, the base-point action of a jet is that of the
constant jet of its value.

-/

variable (G) in
/-- If pure jets act trivially at the base point, the zeroth Taylor coefficient of a jet
  is that of the constant jet of its value. Every jet is a pure jet times the constant jet
  of its value, and the zeroth coefficients are multiplicative for a fibrewise
  representation. -/
lemma repCoeff_zero_eq_ofConstant_eval
    (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (hrep : ∀ {W : G.gaugeJetGroup}, G.evalGaugeJet W = 1 → repCoeff rep W 0 = LinearMap.id)
    (U : G.gaugeJetGroup) :
    repCoeff rep U 0 = repCoeff rep (G.gaugeJetOfConstant (G.evalGaugeJet U)) 0 := by
  have hW : G.evalGaugeJet (U * (G.gaugeJetOfConstant (G.evalGaugeJet U))⁻¹) = 1 := by
    rw [map_mul, map_inv, G.evalGaugeJet_gaugeJetOfConstant, mul_inv_cancel]
  calc repCoeff rep U 0
      = repCoeff rep (U * (G.gaugeJetOfConstant (G.evalGaugeJet U))⁻¹ *
        G.gaugeJetOfConstant (G.evalGaugeJet U)) 0 := by
        rw [inv_mul_cancel_right]
    _ = repCoeff rep (G.gaugeJetOfConstant (G.evalGaugeJet U)) 0 := by
        rw [repCoeff_zero_mul rep hlin, hrep hW, LinearMap.id_comp]

/-- If pure jets act trivially at the base point, the dual base-point coefficient of the
  inverse of a jet is that of the inverse of the constant jet of its value. -/
lemma repDualCoeff_inv_zero_eq_ofConstant_eval
    (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (hrep : ∀ {W : G.gaugeJetGroup}, G.evalGaugeJet W = 1 → repCoeff rep W 0 = LinearMap.id)
    (U : G.gaugeJetGroup) :
    repDualCoeff rep U⁻¹ 0 = repDualCoeff rep (G.gaugeJetOfConstant (G.evalGaugeJet U))⁻¹ 0 := by
  rw [repDualCoeff, repDualCoeff, repCoeff_zero_eq_ofConstant_eval G rep hlin hrep U⁻¹,
    map_inv G.evalGaugeJet, ← map_inv G.gaugeJetOfConstant]

end GlobalGaugeGroup

namespace GlobalGaugeGroup.MatterField

variable (M : G.MatterField)

/-!

## F. The infinitesimal action of a matter field

For a matter field `M` the action `M.repAlgebra = dρ` of the Lie algebra and the jet
action `M.repJet` form such a pair, by the Leibniz and intertwining laws of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.GaugeJetAction`.

-/

/-- The base-point Taylor coefficients of the jet action are those of the jet action as a
  representation. -/
lemma repCoeff_repJet (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GlobalGaugeGroup.repCoeff M.repJet U x = M.repCoeff U x := rfl

/-- The action `dρ` of the Lie algebra is the infinitesimal action underlying the jet action
  of the gauge jets. -/
lemma isInfinitesimalActionOf : G.IsInfinitesimalActionOf M.repAlgebra M.repJet :=
  ⟨M.repCoeff_cons, M.repCoeff_act⟩

/-!

## G. Pure jets act trivially

-/

/-- Pure jets act trivially at the base point. A jet of value one has identity zeroth Taylor
  coefficient on the target space, for every matter field. -/
lemma repCoeff_zero_of_eval_eq_one {W : G.gaugeJetGroup} (hW : G.evalGaugeJet W = 1) :
    GlobalGaugeGroup.repCoeff M.repJet W 0 = LinearMap.id := by
  rw [repCoeff_repJet, repCoeff_zero, show G.evalGaugeJet W = 1 from hW, map_one,
    Units.val_one]
  rfl

/-!

## H. Compatibility of the gauge and Lorentz actions

-/

/-- The gauge and Lorentz representations of a matter field commute. -/
def GaugeLorentzCommute : Prop :=
  ∀ (g : G.group) (Λ : SL(2,ℂ)) (v : M.V),
    (M.rep g : M.V →L[ℂ] M.V) (M.repLorentz Λ v) = M.repLorentz Λ ((M.rep g : M.V →L[ℂ] M.V) v)

/-- The internal gauge symmetry of the matter field commutes with its Lorentz symmetry, that
  is, the action of the Lie algebra commutes with the Lorentz representation on the target
  space. The covariant derivative adds the term `A_ρ · F`, built from the Lie algebra action, to
  the ordinary derivative, so its Lorentz law holds only when this commutation does. The later
  algebras of covariant expressions are stable under the Lorentz group for the same reason.
  It follows from `GaugeLorentzCommute`, but not conversely. It determines the gauge action
  on the identity component alone, so it says nothing about the other components of a
  disconnected gauge group. -/
def GaugeLorentzCompatible : Prop :=
  ∀ (c : G.lieSubalgebra) (Λ : SL(2,ℂ)) (v : M.V),
    M.repAlgebra c (M.repLorentz Λ v) = M.repLorentz Λ (M.repAlgebra c v)

variable {M} in
/-- If the gauge and Lorentz representations commute, so do the Lie algebra action and the
  Lorentz representation, the Lie algebra action being the derivative of the gauge
  representation. -/
lemma GaugeLorentzCommute.gaugeLorentzCompatible (h : M.GaugeLorentzCommute) :
    M.GaugeLorentzCompatible := fun c Λ v =>
  DFunLike.congr_fun ((M.commute_lieAlgebraRep
    (L := LinearMap.toContinuousLinearMap (M.repLorentz Λ))
    fun g => ContinuousLinearMap.ext fun w => h g Λ w) c).eq v

end GlobalGaugeGroup.MatterField
