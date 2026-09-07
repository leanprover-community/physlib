/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LorentzAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.Basic
/-!
# The gauge-boson jet algebra is a gauge field

The symbols `∂_s A_μ^φ` of the algebra of gauge-boson jets, complexified, satisfy the
transformation laws `IsGaugeField` of a gauge field: the Lorentz law from `IsLorentzDeriv`, and
the gauge law from the action of the jet gauge group constructed in `GaugeAction`. This holds
for any `GaugeJet` with the Taylor–Leibniz rule `GaugeJetLeibniz`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable [GaugeJet G 𝔤 G₀ 𝔤J]
variable [GaugeJetLeibniz G 𝔤 G₀ 𝔤J]

set_option maxHeartbeats 1000000


namespace GaugeJetAlgebra

open TensorProduct Matrix MatrixGroups

/-!

## A. The gauge-field structure

-/

/-!

### A.1. The gauge-field derivative symbols

-/

variable (𝔤) in
/-- The gauge-field derivative symbols of the complexified gauge-boson jet algebra, as a
  family over the derivative multiset, the spacetime index and the dual of the gauge
  algebra — the form consumed by the abstract covariance machinery. -/
noncomputable def gaugeField (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] ℂ ⊗[ℝ] (GaugeJetAlgebra 𝔤) :=
  (Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s).restrictScalars ℝ ∘ₗ
    (TensorProduct.mk ℝ ℂ (GaugeJetAlgebra 𝔤) 1).comp ((ofA 𝔤) μ)

@[simp]
lemma gaugeField_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    (gaugeField 𝔤) s μ φ = Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s
      ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ) := rfl

/-!

### A.2. The `IsGaugeField` instance

-/

/-- **The complexified gauge-boson jet algebra is a gauge field**: its derivative symbols
  are those of a Lorentz covector, transform under the jet gauge group by the all-orders
  Leibniz convolution of the adjoint Taylor coefficients plus the Maurer–Cartan shift, and
  the gauge action is multiplicative. -/
theorem isGaugeField :
    IsGaugeField (complexRepLorentzGroup 𝔤) (complexRepJet G 𝔤) (gaugeField 𝔤) where
  lorentz_apply Λ n l μ φ := by
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
  gauge_apply_deriv U s μ φ := complexRepJet_iteratedD_one_tmul_ofA U s μ φ
  gauge_mul U b₁ b₂ := complexRepJet_apply_mul U b₁ b₂


end GaugeJetAlgebra
