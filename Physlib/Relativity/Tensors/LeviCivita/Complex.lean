/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.OfGaussianInt
public import Physlib.Relativity.Tensors.LeviCivita.Basic
public import Physlib.Relativity.Tensors.RealTensor.ToComplex
/-!

# The Levi-Civita tensor as a complex Lorentz tensor

This file complexifies the real Lorentz Levi-Civita tensor and records its components in the
Gaussian integer tensor basis.

-/

@[expose] public section

noncomputable section

namespace complexLorentzTensor

open Physlib
open KroneckerDelta
open TensorSpecies
open Tensor

/-!

## A. Definition and components

-/

/-- The index colors of the complexified real Levi-Civita tensor agree with four complex
contravariant Lorentz indices. -/
lemma leviCivita_isReindexing : IsReindexing
    (realLorentzTensor.colorToComplex ∘
      ![realLorentzTensor.Color.up, realLorentzTensor.Color.up,
        realLorentzTensor.Color.up, realLorentzTensor.Color.up])
    ![Color.up, Color.up, Color.up, Color.up] id := by
  exact IsReindexing.auto

/-- The Levi-Civita tensor `εᵘᵛᵖᵟ` as a complex Lorentz tensor, with `ε⁰¹²³ = 1`. -/
noncomputable def leviCivita : ℂT[.up, .up, .up, .up] :=
  permT id leviCivita_isReindexing
    (realLorentzTensor.toComplex realLorentzTensor.leviCivita)

/-- The complex Lorentz Levi-Civita tensor. -/
scoped[complexLorentzTensor] notation "ε4ℂ" => leviCivita

/-- The complex Levi-Civita tensor has the Levi-Civita symbol as its real component and zero
imaginary component in the standard basis. -/
lemma leviCivita_eq_ofGaussianInt : ε4ℂ = ofGaussianInt (fun
    b : ComponentIdx (S := complexLorentzTensor) ![Color.up, Color.up, Color.up, Color.up] =>
    (generalizedKroneckerDelta
      (fun i => finSumFinEquiv (basisIdxCongr (c1 := Color.up) (by fin_cases i <;> rfl) (b i)))
      (id : Fin 4 → Fin 4) : GaussianInt)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [leviCivita, permT_basis_repr_symm_apply]
  have hinv (i : Fin 4) : IsReindexing.inv id leviCivita_isReindexing i = i := by
    have h := IsReindexing.inv_apply_apply id leviCivita_isReindexing i
    simpa using h
  rw [ofGaussianInt_basis_repr_apply]
  let j : ComponentIdx (S := complexLorentzTensor)
      (realLorentzTensor.colorToComplex ∘
        ![realLorentzTensor.Color.up, realLorentzTensor.Color.up,
          realLorentzTensor.Color.up, realLorentzTensor.Color.up]) :=
    fun i => basisIdxCongr (by simp [IsReindexing.inv_perserve_color])
      (b (IsReindexing.inv id leviCivita_isReindexing i))
  change (Tensor.basis _).repr
    (realLorentzTensor.toComplex realLorentzTensor.leviCivita) j = _
  have hrepr := realLorentzTensor.toComplex_repr realLorentzTensor.leviCivita
    (ComponentIdx.complexify.symm j)
  rw [Equiv.apply_symm_apply] at hrepr
  rw [hrepr, realLorentzTensor.leviCivita_basis_repr_apply]
  simp only [map_intCast, Complex.ofReal_intCast, Int.cast_inj]
  apply congrArg (fun f : Fin 4 → Fin 4 => generalizedKroneckerDelta f id)
  funext i
  apply congrArg finSumFinEquiv
  have key : ∀ x y : Fin 4, x = y →
      ∀ (h1 : ![Color.up, Color.up, Color.up, Color.up] x =
          (realLorentzTensor.colorToComplex ∘ ![realLorentzTensor.Color.up,
            realLorentzTensor.Color.up, realLorentzTensor.Color.up, realLorentzTensor.Color.up]) y)
        (h2 : ![Color.up, Color.up, Color.up, Color.up] y = Color.up),
      realLorentzTensor.basisIdxColorToComplex
          (![realLorentzTensor.Color.up, realLorentzTensor.Color.up, realLorentzTensor.Color.up,
            realLorentzTensor.Color.up] y) (basisIdxCongr h1 (b x)) =
        basisIdxCongr h2 (b y) := by
    rintro x y rfl h1 h2
    fin_cases x <;> rfl
  exact key _ _ (hinv i) _ _

/-- The components of the complex Levi-Civita tensor as the product over pairs `i < j` of the
sign of `b j - b i`, from `leviCivitaSymbol_eq_prod_prod_Ioi`. Unlike the determinant appearing
in `leviCivita_eq_ofGaussianInt`, these components are cheap to evaluate, e.g. by `decide`. -/
lemma leviCivita_eq_ofGaussianInt_prod : ε4ℂ = ofGaussianInt (fun
    b : ComponentIdx (S := complexLorentzTensor) ![Color.up, Color.up, Color.up, Color.up] =>
    (((∏ i : Fin 4, ∏ j ∈ Finset.Ioi i,
      (if finSumFinEquiv (basisIdxCongr (c1 := Color.up) (by fin_cases i <;> rfl) (b i)) <
          finSumFinEquiv (basisIdxCongr (c1 := Color.up) (by fin_cases j <;> rfl) (b j)) then 1
        else if finSumFinEquiv (basisIdxCongr (c1 := Color.up) (by fin_cases i <;> rfl) (b i)) =
          finSumFinEquiv (basisIdxCongr (c1 := Color.up) (by fin_cases j <;> rfl) (b j))
        then 0 else -1) : ℤ) :
      GaussianInt))) := by
  rw [leviCivita_eq_ofGaussianInt]
  refine congrArg ofGaussianInt (funext fun b => ?_)
  have h := leviCivitaSymbol_eq_prod_prod_Ioi
    (fun i : Fin 4 =>
      finSumFinEquiv (basisIdxCongr (c1 := Color.up) (by fin_cases i <;> rfl) (b i)))
  rw [← h]
  rfl

end complexLorentzTensor
