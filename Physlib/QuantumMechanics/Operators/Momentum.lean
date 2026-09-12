/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumCLM` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩` for `momentumOperator`

## iii. Table of contents

- A. Momentum vector operator
- B. Unbounded momentum vector operator

## iv. References

* None.
-/

TODO "Extend the domain of the momentum operator to the Sobolev space `H¹`."

TODO "Prove that the momentum operator is self-adjoint (relies on 15310236534648318597)."

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Constants Complex
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-!

## A. Momentum vector operator

-/

/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumCLM]
notation "𝐩" => momentumCLM

@[inherit_doc momentumCLM]
notation "𝐩[" d' "]" => momentumCLM (d := d')

lemma momentumCLM_apply_fun (ψ : 𝓢(Space d, ℂ)) : 𝐩 i ψ = (-I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumCLM_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) : 𝐩 i ψ x = -I * ℏ * ∂[i] ψ x :=
  rfl

/-!

## B. Unbounded momentum vector operator

-/

open LinearPMap
open MeasureTheory
open SpaceDHilbertSpace
open SchwartzSubmodule

/-- The momentum operator as a LinearPMap with domain the Schwartz submodule. -/
def momentumOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (𝐩 i).1 ∘ₗ (schwartzEquiv volume).symm.1

@[inherit_doc momentumOperator]
notation "𝓟" => momentumOperator

lemma momentumOperator_apply (ψ : SchwartzSubmodule d) :
    𝓟 i ψ = schwartzEquiv volume (𝐩 i ((schwartzEquiv volume).symm ψ)) := rfl

lemma momentumOperator_apply_ae (ψ : SchwartzSubmodule d) :
    𝓟 i ψ =ᵐ[volume] 𝐩 i ((schwartzEquiv volume).symm ψ) :=
  schwartzEquiv_coe_ae _

lemma momentumOperator_range (ψ : SchwartzSubmodule d) : 𝓟 i ψ ∈ SchwartzSubmodule d := by
  simp [momentumOperator_apply]

lemma momentumOperator_hasDenseDomain : (𝓟 i).HasDenseDomain := SchwartzSubmodule.dense d _

lemma momentumOperator_isSymmetric : (𝓟 i).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [momentumOperator_apply, ← Submodule.coe_inner, schwartzEquiv_inner,
    (schwartzEquiv volume).symm_apply_apply, momentumCLM_apply]
  have heq : ∀ x, fderiv ℝ (star ∘ f) x = (starL' ℝ).toContinuousLinearMap ∘L (fderiv ℝ f x) :=
    fun _ ↦ fderiv_star
  have hI₁ : Integrable fun x ↦ star (f x) := (starL' ℝ).integrable_comp_iff.mpr f.integrable
  have hI₂ : Integrable fun x ↦ fderiv ℝ g x (basis i) * star (f x) := by
    refine hI₁.mul_of_top_right ?_
    exact ((g.fderivCLM ℂ _ _).evalCLM ℂ _ _ _).memLp_top
  have hI₃ : Integrable fun x ↦ g x * fderiv ℝ (star ∘ f) x (basis i) := by
    simp_rw [heq]
    refine Integrable.mul_of_top_right ?_ g.memLp_top
    apply (starL' ℝ).integrable_comp_iff.mpr
    exact ((f.fderivCLM ℂ _ _).evalCLM ℂ _ _ _).integrable
  have hI₄ : Integrable fun x ↦ g x * star (f x) := hI₁.mul_of_top_right g.memLp_top
  trans I * ℏ * ∫ x, g x * fderiv ℝ (star ∘ f) x (basis i)
  · simp_rw [← integral_const_mul_of_integrable hI₃, heq]
    simp [mul_comm, mul_left_comm, Space.deriv_eq]
  symm
  trans I * ℏ * -∫ x, fderiv ℝ ⇑g x (basis i) * star (f x)
  · rw [mul_neg, ← neg_mul, ← integral_const_mul_of_integrable hI₂]
    simp [mul_left_comm, mul_comm, Space.deriv_eq]
  symm
  congr 2
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI₂ hI₃ hI₄ (by fun_prop) (by fun_prop)

open scoped InnerProductSpace in
/-- The momentum operator is symmetric on Schwartz maps, in terms of `momentumCLM`. -/
lemma momentumCLM_inner (f g : 𝓢(Space d, ℂ)) :
    ⟪(schwartzEquiv volume (𝐩 i f) : SpaceDHilbertSpace d), schwartzEquiv volume g⟫_ℂ
      = ⟪(schwartzEquiv volume f : SpaceDHilbertSpace d), schwartzEquiv volume (𝐩 i g)⟫_ℂ := by
  have h := momentumOperator_isSymmetric (d := d) i (schwartzEquiv volume f)
    (schwartzEquiv volume g)
  simpa [momentumOperator_apply] using h

lemma momentumOperator_isUnbounded : (𝓟 i).IsUnbounded := by
  refine (LinearPMap.IsSymmetric.isUnbounded_iff_hasDenseDomain ?_).mpr ?_
  · exact momentumOperator_isSymmetric i
  · exact momentumOperator_hasDenseDomain i

/-- The square of the momentum operator. -/
def momentumSqOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  sum fun i ↦ (𝓟 i).comp (𝓟 i) (momentumOperator_range i)

lemma momentumSqOperator_eq :
    momentumSqOperator (d := d) = sum fun i ↦ (𝓟 i).comp (𝓟 i) (momentumOperator_range i) := rfl

lemma momentumSqOperator_domain_eq : momentumSqOperator.domain = SchwartzSubmodule d := by
  rw [momentumSqOperator_eq, sum_domain]
  rcases eq_zero_or_pos d with rfl | hd
  · simp [SchwartzSubmodule.zero_eq_top]
  · let := Fin.pos_iff_nonempty.mp hd
    rw [← iInf_const (a := SchwartzSubmodule d) (ι := Fin d)]
    congr

end
end QuantumMechanics
