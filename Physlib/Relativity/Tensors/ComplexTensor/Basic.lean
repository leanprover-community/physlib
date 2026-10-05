/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nikolai Kashcheev
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import Physlib.Relativity.Fermions.Weyl.Metric
/-!

## Complex Lorentz tensors

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace complexLorentzTensor

set_option backward.isDefEq.respectTransparency false in
/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics. -/
inductive Color
  /-- The color associated with Left handed fermions. -/
  | upL : Color
  /-- The color associated with dual-Left handed fermions. -/
  | downL : Color
  /-- The color associated with Right handed fermions. -/
  | upR : Color
  /-- The color associated with dual-Right handed fermions. -/
  | downR : Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color
deriving Fintype

/-- Color for complex Lorentz tensors is decidable. -/
instance : DecidableEq Color := fun x y =>
  match x, y with
  | Color.upL, Color.upL => isTrue rfl
  | Color.downL, Color.downL => isTrue rfl
  | Color.upR, Color.upR => isTrue rfl
  | Color.downR, Color.downR => isTrue rfl
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.upL, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.up => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.down => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.up => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.down => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.up => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.down => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.up => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.down => isFalse fun h => Color.noConfusion h
  | Color.up, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.up, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.up, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.up, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.down, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.down, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.down, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h

/-- The dimensions of each of the different types of complex Lorentz vector space. -/
abbrev repDim (c : Color) : ℕ :=
  match c with
  | Color.upL => 2
  | Color.downL => 2
  | Color.upR => 2
  | Color.downR => 2
  | Color.up => 4
  | Color.down => 4

/-- The modules associated with each of the different types of complex Lorentz vector space. -/
abbrev modules : Color → Type
  | Color.upL => Fermion.LeftHandedWeyl
  | Color.downL => Fermion.DualLeftHandedWeyl
  | Color.upR => Fermion.RightHandedWeyl
  | Color.downR => Fermion.DualRightHandedWeyl
  | Color.up => Lorentz.ContrℂModule
  | Color.down => Lorentz.CoℂModule

instance modulesAddCommGroup : ∀ c, AddCommGroup (modules c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance

noncomputable instance modulesModule : ∀ c, Module ℂ (modules c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance

end complexLorentzTensor

noncomputable section
open complexLorentzTensor in
set_option maxHeartbeats 0 in
/-- The tensor structure for complex Lorentz tensors. -/
def complexLorentzTensor : TensorSpecies ℂ complexLorentzTensor.Color SL(2, ℂ)
    (fun c => match c with
      | Color.upL => Fermion.LeftHandedWeyl
      | Color.downL => Fermion.DualLeftHandedWeyl
      | Color.upR => Fermion.RightHandedWeyl
      | Color.downR => Fermion.DualRightHandedWeyl
      | Color.up => Lorentz.ContrℂModule
      | Color.down => Lorentz.CoℂModule)
    (fun c => Fin (repDim c))
    (fun c => match c with
      | Color.upL => Fermion.LeftHandedWeyl.rep
      | Color.downL => Fermion.DualLeftHandedWeyl.rep
      | Color.upR => Fermion.RightHandedWeyl.rep
      | Color.downR => Fermion.DualRightHandedWeyl.rep
      | Color.up => Lorentz.ContrℂModule.SL2CRep
      | Color.down => Lorentz.CoℂModule.SL2CRep)
    (fun c => match c with
    | Color.upL => Fermion.LeftHandedWeyl.basis
    | Color.downL => Fermion.DualLeftHandedWeyl.basis
    | Color.upR => Fermion.RightHandedWeyl.basis
    | Color.downR => Fermion.DualRightHandedWeyl.basis
    | Color.up => Lorentz.complexContrBasisFin4
    | Color.down => Lorentz.complexCoBasisFin4) where

  τ := fun c =>
    match c with
    | Color.upL => Color.downL
    | Color.downL => Color.upL
    | Color.upR => Color.downR
    | Color.downR => Color.upR
    | Color.up => Color.down
    | Color.down => Color.up
  τ_involution c := by
    match c with
    | Color.upL => rfl
    | Color.downL => rfl
    | Color.upR => rfl
    | Color.downR => rfl
    | Color.up => rfl
    | Color.down => rfl
  contr := fun c =>
    match c with
    | Color.upL => Fermion.leftDualContraction
    | Color.downL => Fermion.dualLeftContraction
    | Color.upR => Fermion.rightDualContraction
    | Color.downR => Fermion.dualRightContraction
    | Color.up => Lorentz.contrCoContraction
    | Color.down => Lorentz.coContrContraction
  metric := fun c =>
    match c with
    | Color.upL => Fermion.leftMetric
    | Color.downL => Fermion.dualLeftMetric
    | Color.upR => Fermion.rightMetric
    | Color.downR => Fermion.dualRightMetric
    | Color.up => Lorentz.contrMetric
    | Color.down => Lorentz.coMetric
  unit := fun c =>
    match c with
    | Color.upL => Fermion.dualLeftLeftUnit
    | Color.downL => Fermion.leftDualLeftUnit
    | Color.upR => Fermion.dualRightRightUnit
    | Color.downR => Fermion.rightDualRightUnit
    | Color.up => Lorentz.coContrUnit
    | Color.down => Lorentz.contrCoUnit
  contr_tmul_symm := fun c =>
    match c with
    | Color.upL => Fermion.leftDualContraction_tmul_symm
    | Color.downL => Fermion.dualLeftContraction_tmul_symm
    | Color.upR => Fermion.rightDualContraction_tmul_symm
    | Color.downR => Fermion.dualRightContraction_tmul_symm
    | Color.up => Lorentz.contrCoContraction_tmul_symm
    | Color.down => Lorentz.coContrContraction_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.upL => Fermion.contr_dualLeftLeftUnit
    | Color.downL => Fermion.contr_leftDualLeftUnit
    | Color.upR => Fermion.contr_dualRightRightUnit
    | Color.downR => Fermion.contr_rightDualRightUnit
    | Color.up => Lorentz.contr_coContrUnit
    | Color.down => Lorentz.contr_contrCoUnit
  unit_symm := fun c =>
    match c with
    | Color.upL => Fermion.dualLeftLeftUnit_symm
    | Color.downL => Fermion.leftDualLeftUnit_symm
    | Color.upR => Fermion.dualRightRightUnit_symm
    | Color.downR => Fermion.rightDualRightUnit_symm
    | Color.up => Lorentz.coContrUnit_symm
    | Color.down => Lorentz.contrCoUnit_symm
  contr_metric := fun c =>
    match c with
    | Color.upL => by
      simpa using Fermion.leftDualContraction_apply_metric
    | Color.downL => by
      simpa using Fermion.dualLeftContraction_apply_metric
    | Color.upR => by
      simpa using Fermion.rightDualContraction_apply_metric
    | Color.downR => by
      simpa using Fermion.dualRightContraction_apply_metric
    | Color.up => by
      simpa using Lorentz.contrCoContraction_apply_metric
    | Color.down => by
      simpa using Lorentz.coContrContraction_apply_metric

namespace complexLorentzTensor

/-- Complex Lorentz tensor. -/
syntax (name := complexLorentzTensorSyntax) "ℂT[" term,* "]" : term

/-- The basis associated with each of the different types of complex Lorentz vector space. -/
abbrev basis (c : Color) : Module.Basis (Fin (repDim c)) ℂ (modules c) :=
  match c with
  | Color.upL => Fermion.LeftHandedWeyl.basis
  | Color.downL => Fermion.DualLeftHandedWeyl.basis
  | Color.upR => Fermion.RightHandedWeyl.basis
  | Color.downR => Fermion.DualRightHandedWeyl.basis
  | Color.up => Lorentz.complexContrBasisFin4
  | Color.down => Lorentz.complexCoBasisFin4

/-- The reps associated with each of the different types of complex Lorentz vector space. -/
abbrev rep (c : Color) : Representation ℂ SL(2, ℂ) (modules c) :=
  match c with
  | Color.upL => Fermion.LeftHandedWeyl.rep
  | Color.downL => Fermion.DualLeftHandedWeyl.rep
  | Color.upR => Fermion.RightHandedWeyl.rep
  | Color.downR => Fermion.DualRightHandedWeyl.rep
  | Color.up => Lorentz.ContrℂModule.SL2CRep
  | Color.down => Lorentz.CoℂModule.SL2CRep

macro_rules
  | `(ℂT[$term:term, $terms:term,*]) =>
    `(complexLorentzTensor.Tensor (vecCons $term ![$terms,*]))
  | `(ℂT[$term:term]) => `(complexLorentzTensor.Tensor (vecCons $term ![]))
  | `(ℂT[]) =>`(complexLorentzTensor.Tensor (vecEmpty))

/-- Complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "ℂT(" c ")" => complexLorentzTensor.Tensor c

open TensorSpecies Tensor

lemma basisIdxCongr_eq_cast {c1 c2 : complexLorentzTensor.Color}
    (h : c1 = c2) (i : Fin (repDim c1)) :
    TensorSpecies.basisIdxCongr (basisIdx := fun c => Fin (repDim c)) h i =
      Fin.cast (by simp [h]) i := by
  subst h
  rfl

lemma repDim_tau {c : complexLorentzTensor.Color} :
    repDim (complexLorentzTensor.τ c) = repDim c := by
  cases c <;> rfl

/-- At every complex Lorentz color, the bases at the color and its dual are dual bases, with
labels matched by `finCongr repDim_tau`. -/
lemma isContrDualMatching_finCongr (c : complexLorentzTensor.Color) :
    IsContrDualMatching complexLorentzTensor c (finCongr repDim_tau) := by
  intro x₁ x₂
  cases c <;> refine Eq.trans ?_ (if_congr Fin.ext_iff.symm rfl rfl)
  exacts [Fermion.leftDualContraction_basis x₁ x₂, Fermion.dualLeftContraction_basis x₁ x₂,
    Fermion.rightDualContraction_basis x₁ x₂, Fermion.dualRightContraction_basis x₁ x₂,
    Lorentz.contrCoContraction_basis x₁ x₂, Lorentz.coContrContraction_basis x₁ x₂]

/-- Complex Lorentz tensors have dual bases under contraction, with the matching
`finCongr repDim_tau`. -/
instance : HasContrDualBases complexLorentzTensor where
  exists_matching c := ⟨_, isContrDualMatching_finCongr c⟩

/-- The dual-label matching of complex Lorentz tensors is `finCongr repDim_tau`. -/
@[simp]
lemma contrDualIdxEquiv_eq_finCongr (c : complexLorentzTensor.Color) :
    HasContrDualBases.contrDualIdxEquiv complexLorentzTensor c = finCongr repDim_tau :=
  HasContrDualBases.contrDualIdxEquiv_eq_of_isContrDualMatching (isContrDualMatching_finCongr c)

lemma contrPCoeff_basis {n : ℕ} {c : Fin n → complexLorentzTensor.Color} (i j : Fin n)
    (hij : i ≠ j ∧ (complexLorentzTensor.τ (c i) = c j))
    (b : ComponentIdx (S := complexLorentzTensor) c) :
    Pure.contrPCoeff i j hij (Pure.basisVector c b) = if b i =
      Fin.cast (by simp [← hij.2, repDim_tau]) (b j)
    then 1 else 0 := by
  rw [Pure.contrPCoeff_basisVector, contrDualIdxEquiv_eq_finCongr]
  refine if_congr (Eq.congr_right ?_) rfl rfl
  simp [basisIdxCongr_eq_cast]

end complexLorentzTensor
end
