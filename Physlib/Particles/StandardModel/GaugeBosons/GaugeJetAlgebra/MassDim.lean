/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.JetDeriv
/-!
# Mass dimension on the gauge-boson jet algebra

## i. Overview

The mass dimension of the gauge bosons is tracked multiplicatively through the
*mass-weight scaling*: the algebra endomorphism multiplying each generator `∂_s A_μ^φ` by
`c ^ (2 + 2 |s|)` — the gauge field has mass dimension one, i.e. mass weight two, and each
derivative adds mass weight two. A monomial of total mass weight `n` is scaled by `c ^ n`,
so the scaling records the mass-weight grading of the jet algebra. This mirrors
`Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim`, on the real, single-half
component space of the gauge bosons.

## ii. Key results

- `GaugeBoson.JetComponentSpace.massWeightScale` : the scaling on the component space.
- `GaugeJetAlgebra.massWeightScale` : the mass-weight scaling.
- `GaugeJetAlgebra.massWeightScale_ofA` : the gauge field carries mass weight two.
- `GaugeJetAlgebra.massWeightScale_jetDeriv` : a derivative adds mass weight two.
- `GaugeJetAlgebra.massWeightScale_iteratedJetDeriv` : `∂_s` adds mass weight `2 |s|`.

## iii. Table of contents

- A. The mass-weight scaling on the component space
- B. The mass-weight scaling on the jet algebra
- C. The mass weight of the gauge field and its derivatives

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The mass-weight scaling on the component space

-/

namespace GaugeBoson

/-- The mass-weight scaling on the jet component space of the gauge bosons: the generator
  `∂_s A_μ^φ` is scaled by `c ^ (2 + 2 |s|)`, through the derivative-degree scaling
  `DerivAlgebraReal.gradeScale` on the derivative label. -/
noncomputable def JetComponentSpace.massWeightScale (c : ℝ) :
    JetComponentSpace →ₗ[ℝ] JetComponentSpace :=
  c ^ 2 • TensorProduct.map (DerivAlgebraReal.gradeScale (c ^ 2)).toLinearMap LinearMap.id

lemma JetComponentSpace.massWeightScale_tmul (c : ℝ) (a : DerivAlgebraReal)
    (φ : Module.Dual ℝ GaugeBoson) :
    JetComponentSpace.massWeightScale c (a ⊗ₜ[ℝ] φ)
      = c ^ 2 • (DerivAlgebraReal.gradeScale (c ^ 2) a ⊗ₜ[ℝ] φ) := rfl

/-- **The derivative shift carries mass weight two** on the component space. -/
lemma JetComponentSpace.massWeightScale_jetDeriv (c : ℝ) (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace) :
    JetComponentSpace.massWeightScale c (JetComponentSpace.jetDeriv μ v)
      = c ^ 2 • JetComponentSpace.jetDeriv μ (JetComponentSpace.massWeightScale c v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul a φ =>
    rw [JetComponentSpace.jetDeriv_tmul, JetComponentSpace.massWeightScale_tmul, map_mul,
      LagrangianTheory.dualRealJetAlgebraBasis_singleton,
      DerivAlgebraReal.gradeScale_ι, ← LagrangianTheory.dualRealJetAlgebraBasis_singleton,
      JetComponentSpace.massWeightScale_tmul, map_smul, JetComponentSpace.jetDeriv_tmul,
      mul_smul_comm, TensorProduct.smul_tmul', smul_smul, smul_smul, mul_comm (c ^ 2)]
    rfl

end GaugeBoson

namespace GaugeJetAlgebra

/-!

## B. The mass-weight scaling on the jet algebra

-/

/-- **The mass-weight scaling on the gauge-boson jet algebra**: the algebra endomorphism
  scaling the generator `∂_s A_μ^φ` by `c ^ (2 + 2 |s|)`, the functorial lift of the
  scaling on the jet component space. -/
noncomputable def massWeightScale (c : ℝ) : GaugeJetAlgebra →ₐ[ℝ] GaugeJetAlgebra :=
  SymmetricAlgebra.map (GaugeBoson.JetComponentSpace.massWeightScale c)

@[simp]
lemma massWeightScale_ι (c : ℝ) (x : GaugeBoson.JetComponentSpace) :
    massWeightScale c (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.ι ℝ _ (GaugeBoson.JetComponentSpace.massWeightScale c x) :=
  SymmetricAlgebra.map_apply_ι _ x

/-!

## C. The mass weight of the gauge field and its derivatives

-/

/-- **The gauge field carries mass weight two** — mass dimension one. -/
@[simp]
lemma massWeightScale_ofA (c : ℝ) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    massWeightScale c (ofA μ φ) = c ^ 2 • ofA μ φ := by
  rw [ofA_apply, ofComponent_apply, massWeightScale_ι,
    GaugeBoson.JetComponentSpace.massWeightScale_tmul, map_one, map_smul]

/-- **A total derivative adds mass weight two.** -/
lemma massWeightScale_jetDeriv (c : ℝ) (μ : Fin 1 ⊕ Fin 3) (x : GaugeJetAlgebra) :
    massWeightScale c (jetDeriv μ x) = c ^ 2 • jetDeriv μ (massWeightScale c x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => rw [jetDeriv_algebraMap, map_zero, AlgHom.commutes, jetDeriv_algebraMap,
      smul_zero]
  | ι v =>
    rw [jetDeriv_ι, massWeightScale_ι, massWeightScale_ι, jetDeriv_ι, ← map_smul]
    exact congrArg (SymmetricAlgebra.ι ℝ _)
      (GaugeBoson.JetComponentSpace.massWeightScale_jetDeriv c μ v)
  | mul a b ha hb =>
    simp only [jetDeriv_mul, map_add, map_mul, ha, hb, smul_add, smul_mul_assoc,
      mul_smul_comm]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]

/-- **The iterated derivative `∂_s` adds mass weight `2 |s|`.** -/
lemma massWeightScale_iteratedJetDeriv (c : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (x : GaugeJetAlgebra) :
    massWeightScale c (iteratedJetDeriv s x)
      = c ^ (2 * Multiset.card s) • iteratedJetDeriv s (massWeightScale c x) := by
  induction s using Multiset.induction_on generalizing x with
  | empty => simp
  | cons μ s ih =>
    rw [iteratedJetDeriv_cons, LinearMap.comp_apply, massWeightScale_jetDeriv,
      show massWeightScale c (iteratedJetDeriv s x)
        = c ^ (2 * Multiset.card s) • iteratedJetDeriv s (massWeightScale c x) from ih x,
      map_smul, LinearMap.comp_apply, smul_smul, ← pow_add]
    congr 2
    rw [Multiset.card_cons]
    ring

end GaugeJetAlgebra

end StandardModel
