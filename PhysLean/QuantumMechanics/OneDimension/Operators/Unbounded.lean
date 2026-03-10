/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PlaneWaves
public import PhysLean.QuantumMechanics.PlanckConstant
public import Mathlib.Analysis.Calculus.FDeriv.Star
/-!

# Unbounded operators

## Note

It is likely one day the material in this file will be moved to or appear
in another form within Mathlib.

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace

/-- An unbounded operator on the one-dimensional Hilbert space,
  corresponds to a subobject `ι : S →L[ℂ] HilbertSpace` of the Hilbert
  space along with the operator `op : S →L[ℂ] HilbertSpace` -/
@[nolint unusedArguments]
def UnboundedOperator {S : Type} [AddCommGroup S] [Module ℂ S]
    [TopologicalSpace S] (ι : S →L[ℂ] HilbertSpace)
    (_ : Function.Injective ι) := S →L[ℂ] HilbertSpace

namespace UnboundedOperator

variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι)

instance : CoeFun (UnboundedOperator ι hι) (fun _ => S → HilbertSpace) where
  coe := fun U => U.toFun

/-- An unbounded operator created from a continuous linear map ` S →L[ℂ] S`. -/
def ofSelfCLM (Op : S →L[ℂ] S) : UnboundedOperator ι hι := ι ∘L Op

@[simp]
lemma ofSelfCLM_apply (Op : S →L[ℂ] S) (ψ : S) :
    ofSelfCLM (hι := hι) Op ψ = ι (Op ψ) := rfl

/-- A map `F : S →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U`
  on `S` if there is an eigenvalue `c` such that for all `ψ`, `F (U ψ) = c ⬝ F ψ` -/
def IsGeneralizedEigenvector (F : S →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : S, ∃ ψ' : S, ι ψ' = U ψ ∧ F ψ' = c • F ψ

lemma isGeneralizedEigenvector_ofSelfCLM_iff {Op : S →L[ℂ] S}
    (F : S →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSelfCLM (hι := hι) Op) F c ↔
    ∀ ψ : S, F (Op ψ) = c • F ψ := by
  constructor
  · intro h ψ
    obtain ⟨ψ', hψ', hF⟩ := h ψ
    simp at hψ'
    rw [hι.eq_iff] at hψ'
    subst hψ'
    exact hF
  · intro h ψ
    use Op ψ
    constructor
    · simp
    · rw [h ψ]

open InnerProductSpace

/-- The condition on an unbounded operator to be self-adjoint. -/
def IsSelfAdjoint : Prop :=
  ∀ ψ1 ψ2 : S, ⟪U ψ1, ι ψ2⟫_ℂ = ⟪ι ψ1, U ψ2⟫_ℂ

end UnboundedOperator

end
end OneDimension
end QuantumMechanics
