/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Basic
public import PhyslibAlpha.Relativity.SL2C.AxisRotations
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import PhyslibAlpha.Relativity.Tensors.Equivariant
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization.Lorentz
/-!
# Reynolds elements for complex Lorentz tensors

The action of `SL(2, ℂ)` on complex Lorentz tensors is continuous, so the tensors have a Reynolds
element.

## i. Overview

A family of vectors in a representation `repLorentz` of `SL(2,ℂ)` on `B`, carrying Lorentz
indices of colours `c`, is packaged as a linear map `f : ℂT(c) →ₗ[ℂ] B`, equivariant in the sense
`complexLorentzTensor.IsEquivariant c repLorentz f`. The invariants in the range of such a map
come from invariant tensors whenever the tensors have a Reynolds element,
`TensorSpecies.HasReynolds`.

In its basis the matrix of `g` on a colour is `g`, `(g⁻¹)ᵀ`, the entrywise conjugate of `g`,
`(g⁻¹)ᴴ`, the Lorentz matrix of `g`, or the transpose of the inverse of that (A). So its entries
depend continuously on `g` (B). The tensors with any list of colours are finite-dimensional, and
the continuous action of `SL(2,ℂ)` on them has a Reynolds element by
`Representation.exists_isReynolds_of_specialLinearGroup`, `complexLorentzTensor.hasReynolds` (C).

## ii. Key results

- `Lorentz.continuous_toMatrix_rep` : the matrix entries of every colour depend continuously on
  the element of `SL(2,ℂ)`.
- `complexLorentzTensor.hasReynolds` : the tensors with any list of colours have a Reynolds
  element.

## iii. Table of contents

- A. The matrices of the colours
- B. Continuity of the matrices
- C. Reynolds elements

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C TensorSpecies Tensor complexLorentzTensor

/-!

## A. The matrices of the colours

-/

/-- The matrix of `g` on the left-handed Weyl colour is `g`. -/
lemma toMatrix_rep_upL (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .upL) (complexLorentzTensor.basis .upL)
      (complexLorentzTensor.rep .upL g) = g.1 :=
  Fermion.LeftHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the dual left-handed Weyl colour is `(g⁻¹)ᵀ`. -/
lemma toMatrix_rep_downL (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .downL) (complexLorentzTensor.basis .downL)
      (complexLorentzTensor.rep .downL g) = (g.1⁻¹)ᵀ :=
  Fermion.DualLeftHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the right-handed Weyl colour is the entrywise conjugate of `g`. -/
lemma toMatrix_rep_upR (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .upR) (complexLorentzTensor.basis .upR)
      (complexLorentzTensor.rep .upR g) = g.1.map star :=
  Fermion.RightHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the dual right-handed Weyl colour is `(g⁻¹)ᴴ`. -/
lemma toMatrix_rep_downR (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .downR) (complexLorentzTensor.basis .downR)
      (complexLorentzTensor.rep .downR g) = (g.1⁻¹)ᴴ :=
  Fermion.DualRightHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the contravariant vector colour is the Lorentz matrix of `g`. -/
lemma toMatrix_rep_up_apply (g : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix (complexLorentzTensor.basis .up) (complexLorentzTensor.basis .up)
      (complexLorentzTensor.rep .up g) μ ν
      = (((SL2C.toLorentzGroup g).1 μ ν : ℝ) : ℂ) := by
  change LinearMap.toMatrix ComplexVector.basis ComplexVector.basis
    (ComplexVector.SL2CRep g) μ ν = _
  rw [ComplexVector.basis_ρ_apply]
  rfl

/-- The matrix of `g` on the covariant vector colour is the transpose of the inverse of the
  Lorentz matrix of `g`. -/
lemma toMatrix_rep_down_apply (g : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix (complexLorentzTensor.basis .down) (complexLorentzTensor.basis .down)
      (complexLorentzTensor.rep .down g) μ ν
      = (((SL2C.toLorentzGroup g)⁻¹.1 ν μ : ℝ) : ℂ) := by
  change LinearMap.toMatrix ComplexCoVector.basis ComplexCoVector.basis
    (ComplexCoVector.SL2CRep g) μ ν = _
  rw [ComplexCoVector.basis_ρ_apply, Matrix.transpose_apply, LorentzGroup.toComplex_inv]
  rfl

/-!

## B. Continuity of the matrices

-/

/-- The entries of the Lorentz matrix of `g` depend continuously on `g`, through the trace
  formula `L(g)_{i j} = ½ tr (σ'_i g σ'_j g†)`. -/
lemma continuous_toLorentzGroup_apply (i j : Fin 1 ⊕ Fin 3) :
    Continuous fun g : SL(2,ℂ) => (((SL2C.toLorentzGroup g).1 i j : ℝ) : ℂ) := by
  simp only [SL2C.toLorentzGroup_eq_trace]
  have hg : Continuous fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact ((continuous_const.matrix_mul ((hg.matrix_mul continuous_const).matrix_mul
    hg.matrix_conjTranspose)).matrix_trace).div_const 2

/-- The entries of the matrix of `g` on every colour depend continuously on `g`. -/
lemma continuous_toMatrix_rep (k : complexLorentzTensor.Color) (x y : basisIdx k) :
    Continuous fun g : SL(2,ℂ) => LinearMap.toMatrix (complexLorentzTensor.basis k)
      (complexLorentzTensor.basis k) (complexLorentzTensor.rep k g) x y := by
  have hg : Continuous fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have hi : Continuous fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
    simp_rw [SL2C.inverse_coe]
    exact hg.comp continuous_inv
  cases k
  · exact (hg.matrix_elem x y).congr fun g => (congrFun (congrFun (toMatrix_rep_upL g) x) y).symm
  · exact (hi.matrix_elem y x).congr fun g =>
      (congrFun (congrFun (toMatrix_rep_downL g) x) y).symm
  · exact (continuous_star.comp (hg.matrix_elem x y)).congr fun g =>
      (congrFun (congrFun (toMatrix_rep_upR g) x) y).symm
  · exact (continuous_star.comp (hi.matrix_elem y x)).congr fun g =>
      (congrFun (congrFun (toMatrix_rep_downR g) x) y).symm
  · exact (continuous_toLorentzGroup_apply x y).congr fun g => (toMatrix_rep_up_apply g x y).symm
  · exact ((continuous_toLorentzGroup_apply y x).comp continuous_inv).congr fun g =>
      ((toMatrix_rep_down_apply g x y).trans (congrArg
        (fun Λ : LorentzGroup 3 => ((Λ.1 y x : ℝ) : ℂ)) (map_inv SL2C.toLorentzGroup g).symm)).symm

end Lorentz

/-!

## C. Reynolds elements

-/

/-- The complex Lorentz tensors with any list of colours have a Reynolds element. They are
  finite-dimensional, and `SL(2,ℂ)` acts on them continuously. -/
lemma complexLorentzTensor.hasReynolds {n : ℕ} (c : Fin n → complexLorentzTensor.Color) :
    complexLorentzTensor.HasReynolds c := by
  have := Module.Finite.of_basis (TensorSpecies.Tensor.basis (S := complexLorentzTensor) c)
  exact TensorSpecies.HasReynolds.of_comp (φ := MonoidHom.id _) Function.surjective_id
    (Representation.exists_isReynolds_of_specialLinearGroup ⊤
      (TensorSpecies.continuousMatrixCoeff_top_comp _ Lorentz.continuous_toMatrix_rep))
