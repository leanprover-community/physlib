/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.OfRat
public import Physlib.Relativity.Tensors.LeviCivita.Basic
public import Physlib.Relativity.Tensors.RealTensor.ToComplex
/-!

# The Levi-Civita tensor as a complex Lorentz tensor

This file complexifies the real Lorentz Levi-Civita tensor and records its components in the
rational complex tensor basis.

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

/-- A color cast in the complex Lorentz basis preserves the underlying finite index value. -/
private lemma basisIdxCongr_val {c c1 : Color} (h : c = c1)
    (i : Fin (complexLorentzTensor.repDim c)) :
    (TensorSpecies.basisIdxCongr
      (basisIdx := fun c => Fin (complexLorentzTensor.repDim c)) h i).val = i.val := by
  rw [basisIdxCongr_eq_cast]
  rfl

/-- The Levi-Civita tensor `εᵘᵛᵖᵟ` as a complex Lorentz tensor, with `ε⁰¹²³ = 1`. -/
noncomputable def leviCivita : ℂT[.up, .up, .up, .up] :=
  permT id leviCivita_isReindexing
    (realLorentzTensor.toComplex realLorentzTensor.leviCivita)

/-- The complex Lorentz Levi-Civita tensor. -/
scoped[complexLorentzTensor] notation "ε4ℂ" => leviCivita

/-- The complex Levi-Civita tensor has the Levi-Civita symbol as its real component and zero
imaginary component in the standard basis. -/
lemma leviCivita_eq_ofRat : ε4ℂ = ofRat (fun
    b : ComponentIdx (S := complexLorentzTensor) ![Color.up, Color.up, Color.up, Color.up] =>
    ⟨generalizedKroneckerDelta
      (fun i => Fin.cast (by fin_cases i <;> rfl) (b i)) (id : Fin 4 → Fin 4), 0⟩) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [leviCivita, permT_basis_repr_symm_apply]
  have hinv (i : Fin 4) : IsReindexing.inv id leviCivita_isReindexing i = i := by
    have h := IsReindexing.inv_apply_apply id leviCivita_isReindexing i
    simpa using h
  rw [ofRat_basis_repr_apply]
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
  simp [Physlib.RatComplexNum.toComplexNum]
  apply congrArg (fun f : Fin 4 → Fin 4 => generalizedKroneckerDelta f id)
  funext i
  have hcomplexify :
      (finSumFinEquiv (ComponentIdx.complexify.symm j i)).val = (j i).val := by
    have h := congrArg Fin.val
      (congrFun (ComponentIdx.complexify.apply_symm_apply j) i)
    simpa only [realLorentzTensor.ComponentIdx.complexify_apply, Fin.val_cast] using h
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [hcomplexify]
  simp only [j]
  exact (basisIdxCongr_val
    (by simp [IsReindexing.inv_perserve_color])
    (b (IsReindexing.inv id leviCivita_isReindexing i))).trans
    (congrArg (fun x => (b x).val) (hinv i))

/-- The components of the complex Levi-Civita tensor as the product over pairs `i < j` of the
sign of `b j - b i`, from `leviCivitaSymbol_eq_prod_prod_Ioi`. Unlike the determinant appearing
in `leviCivita_eq_ofRat`, these components are cheap to evaluate, e.g. by `decide`. -/
lemma leviCivita_eq_ofRat_prod : ε4ℂ = ofRat (fun
    b : ComponentIdx (S := complexLorentzTensor) ![Color.up, Color.up, Color.up, Color.up] =>
    ⟨((∏ i : Fin 4, ∏ j ∈ Finset.Ioi i,
      (if (Fin.cast (by fin_cases i <;> rfl) (b i) : Fin 4) <
          (Fin.cast (by fin_cases j <;> rfl) (b j) : Fin 4) then 1
        else if (Fin.cast (by fin_cases i <;> rfl) (b i) : Fin 4) =
          (Fin.cast (by fin_cases j <;> rfl) (b j) : Fin 4) then 0 else -1) : ℤ) : ℚ), 0⟩) := by
  rw [leviCivita_eq_ofRat]
  refine congrArg ofRat (funext fun b => ?_)
  have h := leviCivitaSymbol_eq_prod_prod_Ioi
    (fun i : Fin 4 => (Fin.cast (by fin_cases i <;> rfl) (b i) : Fin 4))
  rw [← h]
  rfl

end complexLorentzTensor
