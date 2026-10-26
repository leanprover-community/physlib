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
    | Color.upL => Fermion.LeftHandedWeyl.contr
    | Color.downL => Fermion.DualLeftHandedWeyl.contr
    | Color.upR => Fermion.RightHandedWeyl.contr
    | Color.downR => Fermion.DualRightHandedWeyl.contr
    | Color.up => Lorentz.ContrℂModule.contr
    | Color.down => Lorentz.CoℂModule.contr
  unit := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.unit
    | Color.downL => Fermion.DualLeftHandedWeyl.unit
    | Color.upR => Fermion.RightHandedWeyl.unit
    | Color.downR => Fermion.DualRightHandedWeyl.unit
    | Color.up => Lorentz.ContrℂModule.unit
    | Color.down => Lorentz.CoℂModule.unit
  contr_tmul_symm := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr_tmul_symm
    | Color.downL => Fermion.DualLeftHandedWeyl.contr_tmul_symm
    | Color.upR => Fermion.RightHandedWeyl.contr_tmul_symm
    | Color.downR => Fermion.DualRightHandedWeyl.contr_tmul_symm
    | Color.up => Lorentz.ContrℂModule.contr_tmul_symm
    | Color.down => Lorentz.CoℂModule.contr_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr_unit
    | Color.downL => Fermion.DualLeftHandedWeyl.contr_unit
    | Color.upR => Fermion.RightHandedWeyl.contr_unit
    | Color.downR => Fermion.DualRightHandedWeyl.contr_unit
    | Color.up => Lorentz.ContrℂModule.contr_unit
    | Color.down => Lorentz.CoℂModule.contr_unit
  unit_symm := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.unit_symm
    | Color.downL => Fermion.DualLeftHandedWeyl.unit_symm
    | Color.upR => Fermion.RightHandedWeyl.unit_symm
    | Color.downR => Fermion.DualRightHandedWeyl.unit_symm
    | Color.up => Lorentz.ContrℂModule.unit_symm
    | Color.down => Lorentz.CoℂModule.unit_symm

namespace complexLorentzTensor

/-- The metrics of the complex Lorentz tensors: `ε` on the four Weyl colors and `η` on the two
  vector colors. -/
instance instWithMetric : complexLorentzTensor.WithMetric where
  metric := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.metric
    | Color.downL => Fermion.DualLeftHandedWeyl.metric
    | Color.upR => Fermion.RightHandedWeyl.metric
    | Color.downR => Fermion.DualRightHandedWeyl.metric
    | Color.up => Lorentz.ContrℂModule.metric
    | Color.down => Lorentz.CoℂModule.metric
  contr_metric := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr_metric
    | Color.downL => Fermion.DualLeftHandedWeyl.contr_metric
    | Color.upR => Fermion.RightHandedWeyl.contr_metric
    | Color.downR => Fermion.DualRightHandedWeyl.contr_metric
    | Color.up => Lorentz.ContrℂModule.contr_metric
    | Color.down => Lorentz.CoℂModule.contr_metric

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
  exacts [Fermion.LeftHandedWeyl.contr_basis x₁ x₂, Fermion.DualLeftHandedWeyl.contr_basis x₁ x₂,
    Fermion.RightHandedWeyl.contr_basis x₁ x₂, Fermion.DualRightHandedWeyl.contr_basis x₁ x₂,
    Lorentz.ContrℂModule.contr_basis x₁ x₂, Lorentz.CoℂModule.contr_basis x₁ x₂]

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

/-- Complex conjugation of colours: it swaps handedness and fixes the vector colours. -/
def Color.bar : Color → Color
  | Color.upL => Color.upR
  | Color.downL => Color.downR
  | Color.upR => Color.upL
  | Color.downR => Color.downL
  | Color.up => Color.up
  | Color.down => Color.down

end complexLorentzTensor

open complexLorentzTensor in
/-- The complex Lorentz tensors as a conjugation species: conjugation swaps left- and
  right-handed Weyl colours and fixes the vector colours. -/
def complexLorentzConjTensor : ConjTensorSpecies ℂ Color SL(2, ℂ) modules
    (fun c => Fin (repDim c)) rep basis where
  toTensorSpecies := complexLorentzTensor
  bar := Color.bar
  bar_involution c := by cases c <;> rfl
  bar_tau c := by cases c <;> rfl
  barIdx_eq c := by cases c <;> rfl
  conj_basis_equivariant c g i j := by
    cases c
    · change Fermion.LeftHandedWeyl.basis.repr (Fermion.LeftHandedWeyl.rep g
          (Fermion.LeftHandedWeyl.basis i)) j = star (Fermion.RightHandedWeyl.basis.repr
          (Fermion.RightHandedWeyl.rep g (Fermion.RightHandedWeyl.basis i)) j)
      rw [Fermion.LeftHandedWeyl.rep_apply_basis_repr,
        Fermion.RightHandedWeyl.rep_apply_basis_repr, star_star]
    · change Fermion.DualLeftHandedWeyl.basis.repr (Fermion.DualLeftHandedWeyl.rep g
          (Fermion.DualLeftHandedWeyl.basis i)) j = star (Fermion.DualRightHandedWeyl.basis.repr
          (Fermion.DualRightHandedWeyl.rep g (Fermion.DualRightHandedWeyl.basis i)) j)
      rw [Fermion.DualLeftHandedWeyl.rep_apply_basis_repr,
        Fermion.DualRightHandedWeyl.rep_apply_basis_repr, star_star]
    · change Fermion.RightHandedWeyl.basis.repr (Fermion.RightHandedWeyl.rep g
          (Fermion.RightHandedWeyl.basis i)) j = star (Fermion.LeftHandedWeyl.basis.repr
          (Fermion.LeftHandedWeyl.rep g (Fermion.LeftHandedWeyl.basis i)) j)
      rw [Fermion.LeftHandedWeyl.rep_apply_basis_repr,
        Fermion.RightHandedWeyl.rep_apply_basis_repr]
    · change Fermion.DualRightHandedWeyl.basis.repr (Fermion.DualRightHandedWeyl.rep g
          (Fermion.DualRightHandedWeyl.basis i)) j = star (Fermion.DualLeftHandedWeyl.basis.repr
          (Fermion.DualLeftHandedWeyl.rep g (Fermion.DualLeftHandedWeyl.basis i)) j)
      rw [Fermion.DualLeftHandedWeyl.rep_apply_basis_repr,
        Fermion.DualRightHandedWeyl.rep_apply_basis_repr]
    · change Lorentz.complexContrBasisFin4.repr (Lorentz.ContrℂModule.SL2CRep g
          (Lorentz.complexContrBasisFin4 i)) j = star (Lorentz.complexContrBasisFin4.repr
          (Lorentz.ContrℂModule.SL2CRep g (Lorentz.complexContrBasisFin4 i)) j)
      rw [Lorentz.complexContrBasisFin4_eq_reindex, Module.Basis.repr_reindex_apply,
        Module.Basis.reindex_apply, ← LinearMap.toMatrix_apply, Lorentz.complexContrBasis_ρ_apply,
        LorentzGroup.star_toComplex_apply]
    · change Lorentz.complexCoBasisFin4.repr (Lorentz.CoℂModule.SL2CRep g
          (Lorentz.complexCoBasisFin4 i)) j = star (Lorentz.complexCoBasisFin4.repr
          (Lorentz.CoℂModule.SL2CRep g (Lorentz.complexCoBasisFin4 i)) j)
      rw [Lorentz.complexCoBasisFin4_eq_reindex, Module.Basis.repr_reindex_apply,
        Module.Basis.reindex_apply, ← LinearMap.toMatrix_apply, Lorentz.complexCoBasis_ρ_apply,
        LorentzGroup.toComplex_inv, Matrix.transpose_apply, LorentzGroup.star_toComplex_apply]
  conj_contrComm d x₁ x₂ := by
    cases d <;>
    · simp only [TensorSpecies.HasContrDualBases.contr_basis_eq_ite, contrDualIdxEquiv_eq_finCongr]
      rw [apply_ite star]
      exact if_congr Iff.rfl (by simp) (by simp)

end
