/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.LorentzAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeAction
public import Physlib.Relativity.SL2C.Basic
/-!
# The gauge-field symbols of the jet algebra and their laws

## i. Overview

The derivative symbols `∂_s A_μ^φ` of the complexified gauge-boson jet algebra, packaged as
a family over the derivative multiset, the spacetime index and the dual of the gauge
algebra, `LocalGaugeFieldAlgebra.gaugeField`, and the two transformation laws they satisfy: the
Lorentz law, in which the symbol carries one covector index and each derivative slot
transforms as a covector, and the gauge law, in which a jet acts by the Leibniz convolution
of its adjoint Taylor coefficients plus the Maurer–Cartan shift. These are the laws that a
realization of the jet algebra in another algebra inherits.

## ii. Key results

- `LocalGaugeFieldAlgebra.gaugeField` : the gauge-field symbols of the jet algebra.
- `LocalGaugeFieldAlgebra.repLorentz_gaugeField` : the Lorentz law.
- `LocalGaugeFieldAlgebra.repJet_gaugeField` : the gauge law.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

open TensorProduct Matrix MatrixGroups Lorentz

namespace LocalGaugeFieldAlgebra

variable (𝔤) in
/-- The gauge-field derivative symbols of the complexified gauge-boson jet algebra, as a
  family over the derivative multiset, the spacetime index and the dual of the gauge
  algebra — the form consumed by the abstract covariance machinery. -/
noncomputable def gaugeField (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra 𝔤) :=
  (Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s).restrictScalars ℝ ∘ₗ
    (TensorProduct.mk ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) 1).comp ((ofA 𝔤) μ)

@[simp]
lemma gaugeField_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    (gaugeField 𝔤) s μ φ = Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s
      ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ) := rfl

/-- The Lorentz law of the jet algebra: the symbol `∂_s A_μ^φ` carries one covector index,
  and each derivative slot transforms as a covector, by `IsLorentzDeriv`. -/
lemma repLorentz_gaugeField (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (complexRepLorentzGroup 𝔤) Λ (gaugeField 𝔤 (List.ofFn l) μ φ) =
      ∑ (p : Fin n → (Fin 1 ⊕ Fin 3)),
        (∏ (i : Fin n), (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        gaugeField 𝔤 (List.ofFn p) a φ := by
  calc (complexRepLorentzGroup 𝔤) Λ ((gaugeField 𝔤) (List.ofFn l) μ φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
          (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm (List.ofFn p)
            ((complexRepLorentzGroup 𝔤) Λ ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ)) :=
        Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn complexJetDeriv_comm Λ l
          ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ)
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [complexRepLorentzGroup_one_tmul_ofA, map_sum]
        refine congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun a _ => ?_)
        rw [map_smul]
        rfl

variable (jets) in
/-- The gauge law of the jet algebra: a jet `U` acts on `∂_s A_μ^φ` by the Leibniz
  convolution of the dual adjoint Taylor coefficients of `U⁻¹` against lower symbols, plus
  the base-point value of the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
lemma repJet_gaugeField (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    complexRepJet jets U (gaugeField 𝔤 s μ φ) =
      (s.antidiagonal.map fun p => gaugeField 𝔤 p.2 μ (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + algebraMap ℂ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤)
          (φ (jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U⁻¹ μ)))) :=
  complexRepJet_iteratedD_one_tmul_ofA U s μ φ

end LocalGaugeFieldAlgebra
