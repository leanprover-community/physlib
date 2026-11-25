/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet
public import PhyslibAlpha.Mathematics.RepresentationDual
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Charged-lepton singlets

The basis of the charged-lepton singlet `(1, 1)_{-6}`, its Lorentz and gauge actions on
components, and the gauge weights of the components.

## i. Overview

The Standard Model charged-lepton singlet is a right-handed Weyl spinor in the `(1, 1)_{-6}`
representation. Here charges are normalized as `6Y`, so `-6` is the usual hypercharge
`Y = -1`. Its value space `LeptonSinglet`, the Lorentz action `LeptonSinglet.repLorentzGroup`
and the gauge action `LeptonSinglet.repGaugeGroupI` are in
`Physlib.Particles.StandardModel.Fermions.LeptonSinglet`. The Weyl spinor carries the Lorentz
index and is the whole of the multiplet, a charged-lepton singlet having no colour and no
weak-isospin index.

This file writes both actions on the Weyl basis, together with their dual, conjugate and
conjugate-dual forms, which are what a component of a lepton-singlet symbol needs. The centre
`-1` of `SL(2,ℂ)` acts by `-1`, as on any single Weyl-spinor index. The gauge group acts by the
hypercharge scalar alone, so the gauge torus acts diagonally with weight hypercharge `-6`.

## ii. Key results

- `StandardModel.LeptonSinglet.basis` : the Weyl basis.
- `StandardModel.LeptonSinglet.repLorentzGroup_apply_basis`,
  `StandardModel.LeptonSinglet.repGaugeGroupI_apply_basis` : the Lorentz and gauge actions on
  the basis, with their dual and conjugate forms.
- `StandardModel.LeptonSinglet.repLorentzGroup_neg_one` : the centre of `SL(2,ℂ)` acts by `-1`.
- `StandardModel.LeptonSinglet.valueGaugeWeight` : the gauge weights of the basis, with
  `StandardModel.LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis`.

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

namespace LeptonSinglet

open Matrix MatrixGroups

/-!

## A. The basis

-/

/-- A basis on the charged-lepton singlets. -/
noncomputable def basis : Module.Basis (Fin 2) ℂ LeptonSinglet :=
  Fermion.RightHandedWeyl.basis.map valLinEquiv.symm

/-- The charged-lepton-singlet space is finite-dimensional. -/
instance : Module.Finite ℂ LeptonSinglet := Module.Finite.of_basis basis

/-- The charged-lepton-singlet space is free. -/
instance : Module.Free ℂ LeptonSinglet := Module.Free.of_basis basis

/-- The charged-lepton-singlet basis vector as an explicit Weyl spinor. -/
lemma basis_eq_mk (α : Fin 2) : basis α = ⟨Fermion.RightHandedWeyl.basis α⟩ := by
  simp only [basis, Module.Basis.map_apply]
  rfl

/-!

## B. The Lorentz action on components

The Lorentz group acts through the right-handed Weyl representation. Dualising inverts and
transposes the coefficient matrix, and conjugating stars it.

-/

/-- The Lorentz action on the lepton-singlet basis is the right-handed Weyl action, by the
  entrywise conjugate matrix. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (basis α) = ∑ β, star (Λ.1 β α) • basis β := by
  simp only [basis, Module.Basis.map_apply, repLorentzGroup, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, Fermion.RightHandedWeyl.rep_apply_basis,
    Matrix.map_apply, map_sum, map_smul]

/-- The lepton-singlet coordinate functionals transform contragrediently, by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.dual Λ (basis.dualBasis α) =
      ∑ β, star ((Λ⁻¹).1 α β) • basis.dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => star ((Λ⁻¹).1 l j))
    (fun j => repLorentzGroup_apply_basis Λ⁻¹ j)

/-- The Lorentz action on the conjugate lepton-singlet basis. The coefficients are the
  conjugates of those of the lepton action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj Λ ((Basis.conj basis) α) = ∑ β, Λ.1 β α • (Basis.conj basis) β := by
  rw [Representation.conj_apply, Basis.conj_apply,
    LinearEquiv.symm_apply_apply, repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Basis.conj_apply]

/-- The conjugate lepton-singlet coordinate functionals transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis α) =
      ∑ β, (Λ⁻¹).1 α β • (Basis.conj basis).dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Λ⁻¹).1 l j)
    (fun j => repLorentzGroup_conj_apply_basis Λ⁻¹ j)

/-- The centre of `SL(2,ℂ)` acts on the charged-lepton-singlet space by `-1`. The value
  space carries a single Weyl-spinor index, and `-1` is not the identity on a half-integer
  spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro α
  rw [repLorentzGroup_apply_basis]
  fin_cases α <;> simp [Matrix.one_apply]

/-- The centre acts on the conjugate charged-lepton-singlet space by `-1` as well,
  conjugation not moving a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro α
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases α <;> simp [Matrix.one_apply]

/-!

## C. The gauge action on components

The gauge group acts by the hypercharge scalar alone, the colour and weak factors acting
trivially.

-/

/-- The gauge action on the lepton-singlet basis is multiplication by the hypercharge
  scalar, the colour and weak factors acting trivially. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI g (basis α) = (star g.toU1.1 ^ 6 : ℂ) • basis α := by
  rw [basis_eq_mk, repGaugeGroupI_basis]

/-- The lepton-singlet coordinate functionals carry the contragredient gauge action, the
  hypercharge scalar of the inverse group element. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI.dual g (basis.dualBasis α) =
      (star (g⁻¹).toU1.1 ^ 6 : ℂ) • basis.dualBasis α := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g α
    (Matrix.of fun p q => if p = q then (star (g⁻¹).toU1.1 ^ 6 : ℂ) else 0)
    (fun q => by rw [repGaugeGroupI_apply_basis]; simp [ite_smul, eq_comm])
  rw [key]
  simp [ite_smul]

/-- The gauge action on the conjugate lepton-singlet basis is the hypercharge scalar,
  conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI.conj g ((Basis.conj basis) α) =
      star (star g.toU1.1 ^ 6 : ℂ) • (Basis.conj basis) α := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, LinearEquiv.map_smulₛₗ, starRingEnd_apply]

/-- The conjugate lepton-singlet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI.conj.dual g ((Basis.conj basis).dualBasis α) =
      star (star (g⁻¹).toU1.1 ^ 6 : ℂ) • (Basis.conj basis).dualBasis α := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj (Basis.conj basis) g α
    (Matrix.of fun p q => if p = q then star (star (g⁻¹).toU1.1 ^ 6 : ℂ) else 0)
    (fun q => by rw [repGaugeGroupI_conj_apply_basis]; simp [ite_smul, eq_comm])
  rw [key]
  simp [ite_smul]

/-!

## D. The gauge weights of the components

The gauge torus acts diagonally on the basis of `LeptonSinglet`. The weights are recorded by
`LeptonSinglet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the lepton-singlet basis, hypercharge `-6`. -/
def valueGaugeWeight (_ : Fin 2) : GaugeWeight :=
  (0, 0, 0, -6)

/-- The gauge torus acts diagonally on the basis of `LeptonSinglet`, with the weights
  `LeptonSinglet.valueGaugeWeight`. -/
lemma repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI (gaugeTorusGen i) (LeptonSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) •
        LeptonSinglet.basis j := by
  rw [basis_eq_mk, LeptonSinglet.repGaugeGroupI_basis]
  fin_cases i <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1,
      LeptonSinglet.valueGaugeWeight, GaugeWeight.coord,
      starRingEnd_expI_pow]

/-- The dual action of the gauge torus on the coordinate functionals of
  `LeptonSinglet` negates the weights. -/
lemma repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (LeptonSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i))) •
        LeptonSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `LeptonSinglet`. The two negations cancel and the weights are those of
  the value space. -/
lemma repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i)
      (((Basis.conj LeptonSinglet.basis)).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) •
        ((Basis.conj LeptonSinglet.basis)).coord j := by
  have hd := dual_gaugeTorusGen_coord LeptonSinglet.repGaugeGroupI.conj
    ((Basis.conj LeptonSinglet.basis))
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

end LeptonSinglet

end StandardModel
