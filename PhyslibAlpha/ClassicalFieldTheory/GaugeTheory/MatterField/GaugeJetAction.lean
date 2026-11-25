/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.JetRep
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.AdjointCoeff
/-!
# The jet action of a matter field

The action of gauge jets and of the Lie algebra on the jets of a matter field.

## i. Overview

A matter field `M` of a global gauge group `G` has a continuous representation
`ρ : G → GL(V)` on its target space `V`. The jets of the field are `SpaceTimeAlgebra ⊗[ℂ] V`,
on which the jets of linear maps `SpaceTimeAlgebra ⊗[ℂ] (V →L[ℂ] V)` act fibrewise, `f ⊗ a`
sending `g ⊗ v` to `f g ⊗ a v`. A gauge jet `U` acts through its jet representation `ρ(U)`, of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.JetRep`, and the
Lie algebra through `dρ`.

The physicists' `∂_x ρ(U)|₀` is the base-point Taylor coefficient `M.repCoeff U x` of the jet
action, the base-point derivative of `ρ(U)`. It obeys two laws, which make `dρ` the
infinitesimal action underlying the jet action. The Leibniz law `repCoeff_cons` is the
derivative identity `∂_μ ρ(U) = dρ(ω_μ) ρ(U)` at the base point. The intertwining law
`repCoeff_act` is the equivariance `ρ(U) dρ(c) = dρ(U c U⁻¹) ρ(U)` at the base
point, in terms of the adjoint Taylor coefficients `G.adjointCoeff`.

## ii. Key results

- `GlobalGaugeGroup.MatterField.jetAction` : the action of jets of linear maps on the
  jets of the field.
- `GlobalGaugeGroup.MatterField.repJet` : the action of the gauge jets.
- `GlobalGaugeGroup.MatterField.repAlgebra` : the action of the Lie algebra, `dρ`.
- `GlobalGaugeGroup.MatterField.repCoeff` : the base-point Taylor coefficients
  `∂_x ρ(U)|₀`, with the laws `repCoeff_cons` and `repCoeff_act`.

## iii. Table of contents

- A. The action of jets of linear maps on jets of the field
- B. The jet action of the gauge jets
  - B.1. The base-point Taylor coefficients of the jet action
  - B.2. The infinitesimal action

## iv. References

* None.

-/

@[expose] public section

open MvPowerSeries SpaceTimeAlgebra TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

/- The jets `SpaceTimeAlgebra ⊗[ℂ] (V →L[ℂ] V)` are formed with the module structure of the
algebra `V →L[ℂ] V`, as in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.JetRep`. -/
attribute [local instance 2000] Algebra.toModule

namespace GlobalGaugeGroup.MatterField

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}
  (M : G.MatterField)

/-!

## A. The action of jets of linear maps on jets of the field

-/

/-- The continuous linear maps on the target space, as linear maps. -/
noncomputable def toLinearMapAlgHom : (M.V →L[ℂ] M.V) →ₐ[ℂ] Module.End ℂ M.V :=
  { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ => rfl }

/-- The action of jets of linear maps on the jets of the field, where `f ⊗ a` sends `g ⊗ v` to
  `f g ⊗ a v`. -/
noncomputable def jetAction : M.EndJet →ₐ[ℂ] Module.End ℂ (SpaceTimeAlgebra ⊗[ℂ] M.V) :=
  (Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
    (Algebra.TensorProduct.map (Algebra.lmul ℂ SpaceTimeAlgebra) (toLinearMapAlgHom M))

@[simp]
lemma jetAction_tmul_tmul (f g : SpaceTimeAlgebra) (a : M.V →L[ℂ] M.V) (v : M.V) :
    jetAction M (f ⊗ₜ[ℂ] a) (g ⊗ₜ[ℂ] v) = (f * g) ⊗ₜ[ℂ] a v := rfl

/-- The action is fibrewise, so it commutes with multiplication by scalar jets. -/
lemma jetAction_smul (T : M.EndJet) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] M.V) :
    jetAction M T (χ • z) = χ • jetAction M T z := by
  induction T using TensorProduct.inductionOn with
  | add T₁ T₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂, smul_add]
  | tmul f a =>
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
    | tmul g v =>
      rw [TensorProduct.smul_tmul', jetAction_tmul_tmul, jetAction_tmul_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- The base-point Taylor coefficient along `x` of the action of a jet `T` on a constant is the
  base-point derivative of `T` along `x`. -/
lemma jetEval_jetIteratedDeriv_jetAction (T : M.EndJet) (x : Multiset (Fin 1 ⊕ Fin 3))
    (v : M.V) :
    jetEval (jetIteratedDeriv x (jetAction M T (jetOfConstant v))) = jetDerivValue x T v := by
  induction T using TensorProduct.inductionOn with
  | add T₁ T₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, map_add, map_add, h₁, h₂, map_add,
      _root_.add_apply]
  | tmul f a =>
    rw [jetOfConstant_apply, jetAction_tmul_tmul, mul_one, jetIteratedDeriv_tmul, jetEval_tmul,
      jetDerivValue_tmul, _root_.smul_apply]

/-!

## B. The jet action of the gauge jets

-/

/-- The action of the gauge algebra, `dρ` as linear maps on the target space. -/
noncomputable def repAlgebra : G.lieSubalgebra →ₗ[ℝ] M.V →ₗ[ℂ] M.V :=
  ((ContinuousLinearMap.coeLM ℂ).restrictScalars ℝ) ∘ₗ (lieAlgebraRep M).toLinearMap

@[simp]
lemma repAlgebra_apply (a : G.lieSubalgebra) :
    repAlgebra M a = ((lieAlgebraRep M a : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) := rfl

/-- The jet action of the jet gauge group, where a gauge jet `U` acts through its jet
  representation `ρ(U)`. -/
noncomputable def repJet : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] M.V) :=
  (jetAction M).toMonoidHom.comp (jetRep M)

@[simp]
lemma repJet_apply (U : G.gaugeJetGroup) : repJet M U = jetAction M (jetRep M U) := rfl

/-- The jet action is fibrewise, so it commutes with multiplication by scalar jets. -/
lemma repJet_smul (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra)
    (z : SpaceTimeAlgebra ⊗[ℂ] M.V) : repJet M U (χ • z) = χ • repJet M U z :=
  jetAction_smul M _ χ z

/-!

### B.1. The base-point Taylor coefficients of the jet action

-/

/-- The physicists' `∂_x ρ(U)|₀`, the base-point Taylor coefficient of the jet action of a
  gauge jet `U` along the multiset of directions `x`, on constant fields. -/
noncomputable def repCoeff (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    M.V →ₗ[ℂ] M.V :=
  jetEval ∘ₗ jetIteratedDeriv x ∘ₗ repJet M U ∘ₗ jetOfConstant

/-- The base-point Taylor coefficients of the jet action are the base-point derivatives of the
  jet representation. -/
lemma repCoeff_eq (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff M U x = ((jetDerivValue x (jetRep M U) : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) :=
  LinearMap.ext fun v => jetEval_jetIteratedDeriv_jetAction M _ x v

/-- The base-point value of the jet action of a gauge jet is `ρ` of its value. -/
lemma repCoeff_zero (U : G.gaugeJetGroup) :
    repCoeff M U 0 =
      ((M.rep (G.evalGaugeJet U) : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V) := by
  rw [repCoeff_eq, jetDerivValue_zero, jetRep_apply, jetEval_jetRepFun]

/-- `dρ` of the base-point derivatives of a Lie algebra jet are the base-point derivatives of
  its jet `dρ(A)`. -/
lemma lieAlgebraRep_evalLie_iteratedDeriv (p : Multiset (Fin 1 ⊕ Fin 3))
    (A : G.jetLieSubalgebra) :
    lieAlgebraRep M (G.evalLie (G.iteratedDerivJ p A)) =
      jetDerivValue p (jetLieAlgebraRep M A) := by
  rw [jetDerivValue_jetLieAlgebraRep]
  exact lieAlgebraRepFun_congr M (evalLie_iteratedDerivJ_val G p A)

/-!

### B.2. The infinitesimal action

-/

/-- The Leibniz law of the base-point Taylor coefficients, the derivative identity
  `∂_μ ρ(U) = dρ(ω_μ) ρ(U)` at the base point. -/
lemma repCoeff_cons (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff M U (μ ::ₘ x) =
      -((x.antidiagonal.map fun p =>
        repAlgebra M (G.evalLie (G.iteratedDerivJ p.1
          (-G.maurerCartan U μ))) ∘ₗ
            repCoeff M U p.2).sum) := by
  rw [repCoeff_eq, jetDerivValue_cons, jetDeriv_jetRep, jetDerivValue_mul]
  refine (map_multiset_sum (ContinuousLinearMap.coeLM ℂ) _).trans ?_
  rw [Multiset.map_map, ← Multiset.sum_map_neg]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply, repAlgebra_apply, repCoeff_eq,
    map_neg, lieAlgebraRep_evalLie_iteratedDeriv, ContinuousLinearMap.coeLM_apply,
    ContinuousLinearMap.toLinearMap_mul, LinearMap.neg_comp,
    neg_neg, Module.End.mul_eq_comp]

/-- The intertwining law of the base-point Taylor coefficients, the equivariance
  `ρ(U) dρ(c) = dρ(U c U⁻¹) ρ(U)` at the base point. -/
lemma repCoeff_act (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3))
    (c : G.lieSubalgebra) :
    repCoeff M U x ∘ₗ repAlgebra M c =
      (x.antidiagonal.map fun p =>
        repAlgebra M (G.adjointCoeff U p.1 c) ∘ₗ
          repCoeff M U p.2).sum := by
  have h := jetLieAlgebraRep_adjoint_mul_jetRep M U (G.ofConstantLie c)
  rw [jetLieAlgebraRep_ofConstantLie] at h
  rw [repCoeff_eq, repAlgebra_apply, ← Module.End.mul_eq_comp,
    ← ContinuousLinearMap.toLinearMap_mul, ← jetDerivValue_mul_jetOfConstant, ← h,
    jetDerivValue_mul]
  refine (map_multiset_sum (ContinuousLinearMap.coeLM ℂ) _).trans ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply, repAlgebra_apply, repCoeff_eq,
    adjointCoeff_eq_evalLie, lieAlgebraRep_evalLie_iteratedDeriv,
    ContinuousLinearMap.coeLM_apply, ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp]

end GlobalGaugeGroup.MatterField
