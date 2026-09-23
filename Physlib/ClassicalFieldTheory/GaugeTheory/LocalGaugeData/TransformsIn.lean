/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.CovariantDeriv
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Truncation
/-!
# Gauge tensors in a representation

## i. Overview

A matter field valued in a representation space `V` has symbols `[∂_s ψ^i]` contracted
against duals of `V`. It is a *gauge tensor* — it *transforms in* the representation
`rep` of the jet gauge group — when each derivative symbol transforms by the Leibniz
convolution of the base-point Taylor coefficients `repDualCoeff` of `rep` against the
lower symbols, with no inhomogeneous term. This is the generalization of
`TransformsInAdjoint` from the adjoint representation to an arbitrary one, and the
property preserved by the covariant derivative in
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction`.

Nothing here depends on the local gauge data beyond the group `GJ` acting; the definition
lives in the `LocalGaugeData` namespace with the transformation laws that consume it.

## ii. Key results

- `LocalGaugeData.TransformsIn` : the gauge tensors of a representation.
- `LocalGaugeData.TransformsIn.repGauge_zero` : the underived symbol transforms through
  the base-point value of the gauge jet alone.
- `LocalGaugeData.TransformsIn.repGauge_eq_of_eval_eq_one`,
  `LocalGaugeData.TransformsIn.repGauge_eq_of_mem_truncationKer_zero` : a pure jet fixes the
  underived symbol, when the representation is trivial on such jets.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct MvPowerSeries

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {GJ : Type} [Group GJ]

namespace LocalGaugeData

open GaugeAlgebraRealization

/-- A component family `F`, valued in `B` and indexed by the complex dual of the
  representation space `V`, *transforms in* the representation `rep` of the jet gauge
  group — with the ambient action `repGauge` on `B` — when each derivative symbol
  `[∂_s F^φ]` transforms by the Leibniz convolution of the dual representation
  coefficients against lower symbols, with no inhomogeneous term — the generalization
  of `TransformsInAdjoint` from the adjoint representation to an arbitrary one, and
  the form consumed by `AlgebraRealization`. -/
def TransformsIn (repGauge : Representation ℂ GJ B)
    (rep : Representation ℂ GJ (JetRing ⊗[ℂ] V))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B) : Prop :=
  ∀ (U : GJ) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)),
    repGauge U (F s φ) =
      (s.antidiagonal.map fun p => F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum

variable {repGauge : Representation ℂ GJ B}
  {rep : Representation ℂ GJ (JetRing ⊗[ℂ] V)}
  {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}

/-- A matter gauge tensor transforms at the base point through the dual coefficient of the
  base-point value of the gauge jet alone: the antidiagonal of the empty multiset has a
  single term. -/
lemma TransformsIn.repGauge_zero (hF : TransformsIn repGauge rep F) (U : GJ)
    (φ : Module.Dual ℂ V) :
    repGauge U (F 0 φ) = F 0 (repDualCoeff rep U⁻¹ 0 φ) := by
  simpa only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] using hF U φ 0

/-- Matter gauge tensors whose zeroth representation coefficient is trivial on pure
  jets are fixed by pure jets: for a family transforming in `rep`, a gauge jet with
  trivial base-point value acts trivially on the underived symbol, provided the
  representation's zeroth Taylor coefficient is the identity on such jets. -/
lemma TransformsIn.repGauge_eq_of_eval_eq_one {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (hF : TransformsIn repGauge rep F)
    (hrep : ∀ {W : GJ}, jets.eval W = 1 → repCoeff rep W 0 = LinearMap.id)
    {U : GJ} (hU : jets.eval U = 1) (φ : Module.Dual ℂ V) :
    repGauge U (F 0 φ) = F 0 φ := by
  have hinv : jets.eval U⁻¹ = 1 := by rw [map_inv, hU, inv_one]
  rw [hF.repGauge_zero U φ,
    show repDualCoeff rep U⁻¹ 0 = (repCoeff rep U⁻¹ 0).dualMap from rfl, hrep hinv]
  rfl

/-- If pure jets act trivially at the base point, the zeroth Taylor coefficient of a jet
  is that of the constant jet of its value: every jet is a pure jet times the constant jet
  of its value, and the zeroth coefficients are multiplicative for a fibrewise
  representation. -/
lemma repCoeff_zero_eq_ofConstant_eval {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) (rep : Representation ℂ GJ (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : GJ) (χ : JetRing) (z : JetRing ⊗[ℂ] V), rep U (χ • z) = χ • rep U z)
    (hrep : ∀ {W : GJ}, jets.eval W = 1 → repCoeff rep W 0 = LinearMap.id) (U : GJ) :
    repCoeff rep U 0 = repCoeff rep (jets.ofConstant (jets.eval U)) 0 := by
  have hW : jets.eval (U * (jets.ofConstant (jets.eval U))⁻¹) = 1 := by
    rw [map_mul, map_inv, jets.eval_ofConstant, mul_inv_cancel]
  calc repCoeff rep U 0
      = repCoeff rep (U * (jets.ofConstant (jets.eval U))⁻¹ * jets.ofConstant (jets.eval U)) 0 := by
        rw [inv_mul_cancel_right]
    _ = repCoeff rep (jets.ofConstant (jets.eval U)) 0 := by
        rw [repCoeff_zero_mul rep hlin, hrep hW, LinearMap.id_comp]

/-- If pure jets act trivially at the base point, a matter gauge tensor transforms at the
  base point as under the constant jet of the value of the gauge jet: the jet action on
  underived symbols factors through evaluation. -/
lemma TransformsIn.repGauge_zero_eq_ofConstant_eval {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (hF : TransformsIn repGauge rep F)
    (hlin : ∀ (U : GJ) (χ : JetRing) (z : JetRing ⊗[ℂ] V), rep U (χ • z) = χ • rep U z)
    (hrep : ∀ {W : GJ}, jets.eval W = 1 → repCoeff rep W 0 = LinearMap.id) (U : GJ)
    (φ : Module.Dual ℂ V) :
    repGauge U (F 0 φ) = repGauge (jets.ofConstant (jets.eval U)) (F 0 φ) := by
  rw [hF.repGauge_zero, hF.repGauge_zero, repDualCoeff, repDualCoeff,
    repCoeff_zero_eq_ofConstant_eval jets rep hlin hrep U⁻¹, map_inv jets.eval,
    ← map_inv jets.ofConstant]

/-- Matter gauge tensors are fixed by pure jets: the members of the zeroth truncation kernel
  are the jets with trivial base-point value, so `repGauge_eq_of_eval_eq_one` applies. -/
lemma TransformsIn.repGauge_eq_of_mem_truncationKer_zero {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (hF : TransformsIn repGauge rep F)
    (hrep : ∀ {W : GJ}, jets.eval W = 1 → repCoeff rep W 0 = LinearMap.id)
    (U : jets.truncationKer 0) (φ : Module.Dual ℂ V) :
    repGauge U.1 (F 0 φ) = F 0 φ :=
  hF.repGauge_eq_of_eval_eq_one hrep (jets.mem_truncationKer_zero_iff.mp U.2) φ

end LocalGaugeData
