/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Physlib.Particles.StandardModel.Fermions.UpSinglet
public import PhyslibAlpha.Mathematics.RepresentationDual
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
/-!
# Up-type singlets

The basis of the up-type singlet `(3, 1)_{4}`, its Lorentz and gauge actions on components,
and the gauge weights of the components.

## i. Overview

The Standard Model up-type singlet is a right-handed Weyl spinor in the `(3, 1)_{4}`
representation. Here charges are normalized as `6Y`, so `4` is the usual hypercharge
`Y = 2/3`. Its value space `UpSinglet`, the Lorentz action `UpSinglet.repLorentzGroup` and the
gauge action `UpSinglet.repGaugeGroupI` are in `Physlib.Particles.StandardModel.Fermions.UpSinglet`.
The Weyl factor carries the Lorentz index and the three-dimensional factor the colour index.

This file writes both actions on the basis of spinor–colour tensors, together with their dual,
conjugate and conjugate-dual forms, which are what a component of an up-singlet symbol needs.
The centre `-1` of `SL(2,ℂ)` acts by `-1`, as on any single Weyl-spinor index. The gauge torus
acts diagonally on the basis, with the colour weights and hypercharge `4`.

## ii. Key results

- `StandardModel.UpSinglet.basis` : the basis of spinor–colour tensors.
- `StandardModel.UpSinglet.repLorentzGroup_apply_basis`,
  `StandardModel.UpSinglet.repGaugeGroupI_apply_basis` : the Lorentz and gauge actions on the
  basis, with their dual and conjugate forms.
- `StandardModel.UpSinglet.repLorentzGroup_neg_one` : the centre of `SL(2,ℂ)` acts by `-1`.
- `StandardModel.UpSinglet.valueGaugeWeight` : the gauge weights of the basis, with
  `StandardModel.UpSinglet.repGaugeGroupI_gaugeTorusGen_basis`.

## iii. Table of contents

- A. The basis
- B. The Lorentz action on components
- C. The gauge action on components
- D. The gauge weights of the components

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace UpSinglet

open Matrix MatrixGroups

/-!

## A. The basis

The basis of `UpSinglet` is the tensor product of the right-handed Weyl basis and the standard
colour basis.

-/

/-- A basis on the up singlets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3) ℂ UpSinglet :=
  (Fermion.RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).map valLinEquiv.symm

/-- The up-singlet space is finite-dimensional. -/
instance : Module.Finite ℂ UpSinglet := Module.Finite.of_basis basis

/-- The up-singlet space is free. -/
instance : Module.Free ℂ UpSinglet := Module.Free.of_basis basis

/-- The up-singlet basis vector as an explicit spinor–colour tensor. -/
lemma basis_eq_mk (k : Fin 2) (c : Fin 3) : basis (k, c) =
    ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    OrthonormalBasis.coe_toBasis]
  rfl

/-!

## B. The Lorentz action on components

The Lorentz group moves only the spinor index. Dualising inverts and transposes the coefficient
matrix, and conjugating stars it.

-/

/-- The Lorentz action on the up-singlet basis. The colour index is inert and the
  spinor index transforms by the entrywise conjugate matrix. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup Λ (basis j) = ∑ β, star (Λ.1 β j.1) • basis (β, j.2) := by
  obtain ⟨k, c⟩ := j
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    repLorentzGroup, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.map_tmul, Fermion.RightHandedWeyl.rep_apply_basis,
    Representation.trivial_apply, TensorProduct.sum_tmul, map_sum,
    Matrix.map_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]

/-- The up-singlet coordinate functionals transform contragrediently, by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.dual Λ (basis.dualBasis j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • basis.dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup basis Λ j
    (Matrix.of fun p q => if p.2 = q.2 then star ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The Lorentz action on the conjugate up-singlet basis. The coefficients are the
  conjugates of those of the up-singlet action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj Λ ((Basis.conj basis) j)
      = ∑ β, Λ.1 β j.1 • (Basis.conj basis) (β, j.2) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Basis.conj_apply]

/-- The conjugate up-singlet coordinate functionals transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • (Basis.conj basis).dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj (Basis.conj basis) Λ j
    (Matrix.of fun p q => if p.2 = q.2 then ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The centre of `SL(2,ℂ)` acts on the up-singlet space by `-1`. The value space carries a
  single Weyl-spinor index, and `-1` is not the identity on a half-integer spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro j
  obtain ⟨a, c⟩ := j
  rw [repLorentzGroup_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-- The centre acts on the conjugate up-singlet space by `-1` as well, conjugation not
  moving a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro j
  obtain ⟨a, c⟩ := j
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-!

## C. The gauge action on components

The gauge group moves only the colour index, up to the hypercharge scalar.

-/

/-- The gauge action on the up-singlet basis. The spinor index is inert and the colour
  index transforms by the `SU(3)` matrix, scaled by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI g (basis j) =
      ∑ c, (g.toU1.1 ^ 4 * g.toSU3.1 c j.2) • basis (j.1, c) := by
  obtain ⟨k, c⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k c

/-- The up-singlet coordinate functionals carry the contragredient gauge action, by the
  hypercharge and `SU(3)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ c, ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) • basis.dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then (g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 p.2 q.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate up-singlet basis has the coefficients of the
  up-singlet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj g ((Basis.conj basis) j) =
      ∑ c, star (g.toU1.1 ^ 4 * g.toSU3.1 c j.2) • (Basis.conj basis) (j.1, c) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate up-singlet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj.dual g ((Basis.conj basis).dualBasis j) =
      ∑ c, star ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) •
        (Basis.conj basis).dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj (Basis.conj basis) g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 p.2 q.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-!

## D. The gauge weights of the components

The gauge torus acts diagonally on the basis of `UpSinglet`. The weights are recorded by
`UpSinglet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the up-singlet basis, colour weights and hypercharge
  `4`. -/
def valueGaugeWeight (j : Fin 2 × Fin 3) : GaugeWeight :=
  ((colourWeight j.2).1, (colourWeight j.2).2, 0, 4)

/-- The gauge torus acts diagonally on the basis of `UpSinglet`, with the weights
  `UpSinglet.valueGaugeWeight`. -/
lemma repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI (gaugeTorusGen i) (UpSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) •
        UpSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  rw [basis_eq_mk, UpSinglet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo,
      Fin.sum_univ_three,
      Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star]

/-- The dual action of the gauge torus on the coordinate functionals of
  `UpSinglet` negates the weights. -/
lemma repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (UpSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i))) •
        UpSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => UpSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `UpSinglet`. The two negations cancel and the weights are those of
  the value space. -/
lemma repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) (((Basis.conj UpSinglet.basis)).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) •
        ((Basis.conj UpSinglet.basis)).coord j := by
  have hd := dual_gaugeTorusGen_coord UpSinglet.repGaugeGroupI.conj ((Basis.conj UpSinglet.basis))
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (UpSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => UpSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

end UpSinglet

end StandardModel
