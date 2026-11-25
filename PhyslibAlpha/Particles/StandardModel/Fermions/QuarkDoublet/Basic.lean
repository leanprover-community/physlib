/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import PhyslibAlpha.Mathematics.RepresentationDual
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
/-!
# Quark doublets

The basis of the quark doublet `(3, 2)_{1}`, its Lorentz and gauge actions on components, and
the gauge weights of the components.

## i. Overview

The Standard Model quark doublet is a left-handed Weyl spinor in the `(3, 2)_{1}`
representation. Here charges are normalized as `6Y`, so `1` is the usual hypercharge
`Y = 1/6`. Its value space `QuarkDoublet`, the Lorentz action `QuarkDoublet.repLorentzGroup`
and the gauge action `QuarkDoublet.repGaugeGroupI` are in
`Physlib.Particles.StandardModel.Fermions.QuarkDoublet`. The Weyl factor carries the Lorentz
index, and the colour and weak-isospin factors the internal indices.

The colour and weak indices are combined into the single index `Fin 3 × Fin 2` by
`QuarkDoublet.colourWeakEquiv`, on which a gauge transformation acts through the Kronecker
product of its `SU(3)` and `SU(2)` matrices. This file then writes both actions on the basis of
spinor–colour–weak tensors, together with their dual, conjugate and conjugate-dual forms, which
are what a component of a quark-doublet symbol needs. The centre `-1` of `SL(2,ℂ)` acts by
`-1`, as on any single Weyl-spinor index. The gauge torus acts diagonally on the basis, with the
colour and isospin weights and hypercharge `1`.

## ii. Key results

- `StandardModel.QuarkDoublet.colourWeakEquiv` : the colour and weak factors combined into a
  single factor over `Fin 3 × Fin 2`.
- `StandardModel.QuarkDoublet.basis` : the basis of spinor–colour–weak tensors.
- `StandardModel.QuarkDoublet.repLorentzGroup_apply_basis`,
  `StandardModel.QuarkDoublet.repGaugeGroupI_apply_basis` : the Lorentz and gauge actions on
  the basis, with their dual and conjugate forms.
- `StandardModel.QuarkDoublet.repLorentzGroup_neg_one` : the centre of `SL(2,ℂ)` acts by `-1`.
- `StandardModel.QuarkDoublet.valueGaugeWeight` : the gauge weights of the basis, with
  `StandardModel.QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis`.

## iii. Table of contents

- A. The combined colour and weak index
- B. The basis
- C. The Lorentz action on components
- D. The gauge action on components
- E. The gauge weights of the components

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace QuarkDoublet

open Matrix MatrixGroups

/-!

## A. The combined colour and weak index

The colour and weak indices are combined into the single index `Fin 3 × Fin 2`, on which
the `SU(3)` and `SU(2)` matrices of a gauge transformation act together through their
Kronecker product, scaled by the hypercharge phase.

-/

/-- The colour and weak factors of the quark doublet combined into a single Euclidean
  factor over `Fin 3 × Fin 2`. -/
noncomputable def colourWeakEquiv :
    EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) ≃ₗ[ℂ] (Fin 3 × Fin 2 → ℂ) :=
  (TensorProduct.congr (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))
      (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ))).trans <|
    (TensorProduct.piScalarRight ℂ ℂ (Fin 3 → ℂ) (Fin 2)).trans <|
      (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 3)).symm.trans <|
        LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (Equiv.prodComm (Fin 2) (Fin 3))

/-- The combined index of a pure colour–weak tensor is the product of its components. -/
@[simp]
lemma colourWeakEquiv_tmul (c : EuclideanSpace ℂ (Fin 3)) (w : EuclideanSpace ℂ (Fin 2))
    (p : Fin 3 × Fin 2) :
    colourWeakEquiv (c ⊗ₜ[ℂ] w) p = c.ofLp p.1 * w.ofLp p.2 := by
  simp [colourWeakEquiv, Function.uncurry, mul_comm]

/-!

## B. The basis

The basis of `QuarkDoublet` is the tensor product of the left-handed Weyl basis and the
standard colour and weak bases.

-/

/-- A basis on the quark doublets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3 × Fin 2) ℂ QuarkDoublet :=
  ((((Fermion.LeftHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).map valLinEquiv.symm).reindex
    (Equiv.prodAssoc (Fin 2) (Fin 3) (Fin 2)))

/-- The quark-doublet space is finite-dimensional. -/
instance : Module.Finite ℂ QuarkDoublet := Module.Finite.of_basis basis

/-- The quark-doublet space is free. -/
instance : Module.Free ℂ QuarkDoublet := Module.Free.of_basis basis

/-- The quark-doublet basis vector as an explicit spinor–colour–weak tensor. -/
lemma basis_eq_mk (k : Fin 2) (c : Fin 3) (w : Fin 2) : basis (k, c, w) =
    ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c
      ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ w⟩ := by
  simp only [basis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis,
    Equiv.prodAssoc_symm_apply]
  rfl

/-!

## C. The Lorentz action on components

The Lorentz group moves only the spinor index. Dualising inverts and transposes the coefficient
matrix, and conjugating stars it.

-/

/-- The Lorentz action on the quark-doublet basis. The colour and weak indices are inert
  and the spinor index transforms by the matrix itself. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup Λ (basis j) = ∑ β, Λ.1 β j.1 • basis (β, j.2.1, j.2.2) := by
  obtain ⟨k, c, w⟩ := j
  simp only [basis_eq_mk, repLorentzGroup, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    valLinEquiv_apply, TensorProduct.map_tmul, Fermion.LeftHandedWeyl.rep_apply_basis,
    Representation.trivial_apply, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
  exact map_smul valLinEquiv.symm _ _

/-- The quark-doublet coordinate functionals transform contragrediently, by the inverse
  matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup.dual Λ (basis.dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • basis.dualBasis (β, j.2.1, j.2.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup basis Λ j
    (Matrix.of fun p q => if p.2 = q.2 then (Λ⁻¹).1 p.1 q.1 else 0)
    (fun q => by
      rw [repLorentzGroup_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The Lorentz action on the conjugate quark-doublet basis. The coefficients are the
  conjugates of those of the quark-doublet action. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup.conj Λ ((Basis.conj basis) j) =
      ∑ β, star (Λ.1 β j.1) • (Basis.conj basis) (β, j.2.1, j.2.2) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate quark-doublet coordinate functionals transform by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • (Basis.conj basis).dualBasis (β, j.2.1, j.2.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj (Basis.conj basis) Λ j
    (Matrix.of fun p q => if p.2 = q.2 then star ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The centre of `SL(2,ℂ)` acts on the quark-doublet space by `-1`. The value space carries a
  single Weyl-spinor index, and `-1` is not the identity on a half-integer spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro j
  obtain ⟨a, c, w⟩ := j
  rw [repLorentzGroup_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-- The centre acts on the conjugate quark-doublet space by `-1` as well, conjugation not
  moving a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro j
  obtain ⟨a, c, w⟩ := j
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-!

## D. The gauge action on components

The gauge group moves only the colour and weak indices, up to the hypercharge scalar.

-/

/-- The gauge action on the quark-doublet basis. The spinor index is inert, the colour
  index transforms by the `SU(3)` matrix and the weak index by the `SU(2)` matrix, scaled
  by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI g (basis j) =
      ∑ c, ∑ w, (g.toU1.1 * g.toSU3.1 c j.2.1 * g.toSU2.1 w j.2.2) • basis (j.1, c, w) := by
  obtain ⟨k, c, w⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k c w

/-- The quark-doublet coordinate functionals carry the contragredient gauge action, by the
  hypercharge, `SU(3)` and `SU(2)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ c, ∑ w, ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        basis.dualBasis (j.1, c, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q => if p.1 = q.1 then
      (g⁻¹).toU1.1 * (g⁻¹).toSU3.1 p.2.1 q.2.1 * (g⁻¹).toSU2.1 p.2.2 q.2.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate quark-doublet basis has the coefficients of the
  quark-doublet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI.conj g ((Basis.conj basis) j) =
      ∑ c, ∑ w, star (g.toU1.1 * g.toSU3.1 c j.2.1 * g.toSU2.1 w j.2.2) •
        (Basis.conj basis) (j.1, c, w) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate quark-doublet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI.conj.dual g ((Basis.conj basis).dualBasis j) =
      ∑ c, ∑ w, star ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        (Basis.conj basis).dualBasis (j.1, c, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj (Basis.conj basis) g j
    (Matrix.of fun p q => if p.1 = q.1 then
      star ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 p.2.1 q.2.1 * (g⁻¹).toSU2.1 p.2.2 q.2.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-!

## E. The gauge weights of the components

The gauge torus acts diagonally on the basis of `QuarkDoublet`. The weights are recorded by
`QuarkDoublet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the quark-doublet basis, colour and isospin weights and
  hypercharge `1`. -/
def valueGaugeWeight (j : Fin 2 × Fin 3 × Fin 2) : GaugeWeight :=
  ((colourWeight j.2.1).1, (colourWeight j.2.1).2, isoWeight j.2.2, 1)

/-- The gauge torus acts diagonally on the basis of `QuarkDoublet`, with the weights
  `QuarkDoublet.valueGaugeWeight`. -/
lemma repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI (gaugeTorusGen i) (QuarkDoublet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) •
        QuarkDoublet.basis j := by
  obtain ⟨k, c, s⟩ := j
  rw [basis_eq_mk, QuarkDoublet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo,
      Fin.sum_univ_three, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      QuarkDoublet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star]

/-- The dual action of the gauge torus on the coordinate functionals of
  `QuarkDoublet` negates the weights. -/
lemma repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4)
    (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI.dual (gaugeTorusGen i) (QuarkDoublet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i))) •
        QuarkDoublet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `QuarkDoublet`. The two negations cancel and the weights are those of
  the value space. -/
lemma repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4)
    (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI.conj.dual (gaugeTorusGen i)
      (((Basis.conj QuarkDoublet.basis)).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) •
        ((Basis.conj QuarkDoublet.basis)).coord j := by
  have hd := dual_gaugeTorusGen_coord QuarkDoublet.repGaugeGroupI.conj
    ((Basis.conj QuarkDoublet.basis))
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

end QuarkDoublet

end StandardModel
