/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Metric
/-!

## Complex Lorentz tensors

-/

@[expose] public section
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace complexLorentzTensor

/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics. -/
inductive Color
  /-- The color associated with Left handed fermions. -/
  | upL : Color
  /-- The color associated with alt-Left handed fermions. -/
  | downL : Color
  /-- The color associated with Right handed fermions. -/
  | upR : Color
  /-- The color associated with alt-Right handed fermions. -/
  | downR : Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color

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

end complexLorentzTensor

noncomputable section
open complexLorentzTensor in
/-- The tensor structure for complex Lorentz tensors. -/
def complexLorentzTensor : TensorSpecies ℂ complexLorentzTensor.Color SL(2, ℂ) where
  FD := Discrete.functor fun c =>
    match c with
    | Color.upL => Fermion.leftHanded
    | Color.downL => Fermion.altLeftHanded
    | Color.upR => Fermion.rightHanded
    | Color.downR => Fermion.altRightHanded
    | Color.up => Lorentz.complexContr
    | Color.down => Lorentz.complexCo
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
  contr := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.upL => Fermion.leftAltContraction
    | Discrete.mk Color.downL => Fermion.altLeftContraction
    | Discrete.mk Color.upR => Fermion.rightAltContraction
    | Discrete.mk Color.downR => Fermion.altRightContraction
    | Discrete.mk Color.up => Lorentz.contrCoContraction
    | Discrete.mk Color.down => Lorentz.coContrContraction
  metric := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.upL => Fermion.leftMetric
    | Discrete.mk Color.downL => Fermion.altLeftMetric
    | Discrete.mk Color.upR => Fermion.rightMetric
    | Discrete.mk Color.downR => Fermion.altRightMetric
    | Discrete.mk Color.up => Lorentz.contrMetric
    | Discrete.mk Color.down => Lorentz.coMetric
  unit := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.upL => Fermion.altLeftLeftUnit
    | Discrete.mk Color.downL => Fermion.leftAltLeftUnit
    | Discrete.mk Color.upR => Fermion.altRightRightUnit
    | Discrete.mk Color.downR => Fermion.rightAltRightUnit
    | Discrete.mk Color.up => Lorentz.coContrUnit
    | Discrete.mk Color.down => Lorentz.contrCoUnit
  repDim := fun c =>
    match c with
    | Color.upL => 2
    | Color.downL => 2
    | Color.upR => 2
    | Color.downR => 2
    | Color.up => 4
    | Color.down => 4
  repDim_neZero := fun c =>
    match c with
    | Color.upL => inferInstance
    | Color.downL => inferInstance
    | Color.upR => inferInstance
    | Color.downR => inferInstance
    | Color.up => inferInstance
    | Color.down => inferInstance
  basis := fun c =>
    match c with
    | Color.upL => Fermion.leftBasis
    | Color.downL => Fermion.altLeftBasis
    | Color.upR => Fermion.rightBasis
    | Color.downR => Fermion.altRightBasis
    | Color.up => Lorentz.complexContrBasisFin4
    | Color.down => Lorentz.complexCoBasisFin4
  contr_tmul_symm := fun c =>
    match c with
    | Color.upL => Fermion.leftAltContraction_tmul_symm
    | Color.downL => Fermion.altLeftContraction_tmul_symm
    | Color.upR => Fermion.rightAltContraction_tmul_symm
    | Color.downR => Fermion.altRightContraction_tmul_symm
    | Color.up => Lorentz.contrCoContraction_tmul_symm
    | Color.down => Lorentz.coContrContraction_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.upL => Fermion.contr_altLeftLeftUnit
    | Color.downL => Fermion.contr_leftAltLeftUnit
    | Color.upR => Fermion.contr_altRightRightUnit
    | Color.downR => Fermion.contr_rightAltRightUnit
    | Color.up => Lorentz.contr_coContrUnit
    | Color.down => Lorentz.contr_contrCoUnit
  unit_symm := fun c =>
    match c with
    | Color.upL => Fermion.altLeftLeftUnit_symm
    | Color.downL => Fermion.leftAltLeftUnit_symm
    | Color.upR => Fermion.altRightRightUnit_symm
    | Color.downR => Fermion.rightAltRightUnit_symm
    | Color.up => Lorentz.coContrUnit_symm
    | Color.down => Lorentz.contrCoUnit_symm
  contr_metric := fun c =>
    match c with
    | Color.upL => by
      simpa using Fermion.leftAltContraction_apply_metric
    | Color.downL => by
      simpa using Fermion.altLeftContraction_apply_metric
    | Color.upR => by
      simpa using Fermion.rightAltContraction_apply_metric
    | Color.downR => by
      simpa using Fermion.altRightContraction_apply_metric
    | Color.up => by
      simpa using Lorentz.contrCoContraction_apply_metric
    | Color.down => by
      simpa using Lorentz.coContrContraction_apply_metric

namespace complexLorentzTensor

/-- Complex Lorentz tensor. -/
syntax (name := complexLorentzTensorSyntax) "ℂT[" term,* "]" : term

macro_rules
  | `(ℂT[$term:term, $terms:term,*]) =>
    `(complexLorentzTensor.Tensor (vecCons $term ![$terms,*]))
  | `(ℂT[$term:term]) => `(complexLorentzTensor.Tensor (vecCons $term ![]))
  | `(ℂT[]) =>`(complexLorentzTensor.Tensor (vecEmpty))

/-- Complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "ℂT(" c ")" => complexLorentzTensor.Tensor c

/-- Contracting two basis elements gives `1` if the index for the basis elements is the same,
  and `0` otherwise. Holds for any color of index. -/
lemma basis_contr (c : complexLorentzTensor.Color) (i : Fin (complexLorentzTensor.repDim c))
    (j : Fin (complexLorentzTensor.repDim (complexLorentzTensor.τ c))) :
    complexLorentzTensor.castToField
    ((complexLorentzTensor.contr.app {as := c}).hom
    (complexLorentzTensor.basis c i ⊗ₜ complexLorentzTensor.basis (complexLorentzTensor.τ c) j)) =
    if i.val = j.val then 1 else 0 :=
  match c with
  | Color.upL => Fermion.leftAltContraction_basis _ _
  | Color.downL => Fermion.altLeftContraction_basis _ _
  | Color.upR => Fermion.rightAltContraction_basis _ _
  | Color.downR => Fermion.altRightContraction_basis _ _
  | Color.up => Lorentz.contrCoContraction_basis _ _
  | Color.down => Lorentz.coContrContraction_basis _ _

/-- For any object in the over color category, with source `Fin n`, has a decidable source. -/
instance {n : ℕ} {c : Fin n → complexLorentzTensor.Color} :
    DecidableEq (OverColor.mk c).left := instDecidableEqFin n

/-- For any object in the over color category, with source `Fin n`, has a finite source. -/
instance {n : ℕ} {c : Fin n → complexLorentzTensor.Color} :
    Fintype (OverColor.mk c).left := Fin.fintype n

/-- The equality of two maps in `OverColor C` from objects based on `Fin _` is decidable. -/
instance {n m : ℕ} {c : Fin n → complexLorentzTensor.Color}
    {c1 : Fin m → complexLorentzTensor.Color} (σ σ' : OverColor.mk c ⟶ OverColor.mk c1) :
    Decidable (σ = σ') :=
  decidable_of_iff _ (OverColor.Hom.ext_iff σ σ')

/-!

## Relating basis

-/

lemma basis_up_eq {i : Fin 4} :
    complexLorentzTensor.basis Color.up i = Lorentz.complexContrBasisFin4 i := rfl

lemma basis_down_eq {i : Fin 4} :
    complexLorentzTensor.basis Color.down i = Lorentz.complexCoBasisFin4 i := rfl

lemma basis_upL_eq {i : Fin 2} :
    complexLorentzTensor.basis Color.upL i = Fermion.leftBasis i := rfl

lemma basis_downL_eq {i : Fin 2} :
    complexLorentzTensor.basis Color.downL i = Fermion.altLeftBasis i := rfl

lemma basis_upR_eq {i : Fin 2} :
    complexLorentzTensor.basis Color.upR i = Fermion.rightBasis i := rfl

lemma basis_downR_eq {i : Fin 2} :
    complexLorentzTensor.basis Color.downR i = Fermion.altRightBasis i := rfl

end complexLorentzTensor
end
