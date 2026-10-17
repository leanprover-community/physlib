/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.BoostWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.JetGaugeGroup.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra
public import PhyslibAlpha.Mathematics.Modules.ConjModule
/-!
# Charged-lepton singlets

## i. Overview

The Standard Model charged-lepton singlet is a right-handed Weyl spinor in the `(1, 1)_{-6}`
representation. Here charges are normalized as `6Y`, so `-6` is the usual hypercharge
`Y = -1`.

`LeptonSinglet` is the target vector space of one charged-lepton singlet. Its only index is
the Lorentz index carried by the Weyl spinor.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed
on an arbitrary spinor, used to identify its kernel, and descended to each supported global
form of the Standard Model gauge group.

## ii. Key results

- `LeptonSinglet` : the target space of the `(1, 1)_{-6}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_apply` : the gauge action on a spinor.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The charged-lepton-singlet space
- B. Linear structure
  - B.1. The basis of the charged-lepton-singlet space
- C. Lorentz action
- D. Global Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. The representation of the jet gauge group
- H. The gauge weight of the LeptonSinglet components
- I. The boost weight of the LeptonSinglet components

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

/-!

## A. The charged-lepton-singlet space

The Weyl spinor carries the right-handed Lorentz index, and it is the whole of the multiplet:
a charged-lepton singlet has no colour index and no weak-isospin index.
-/

namespace LeptonSinglet

/-!

## B. Linear structure

The wrapper distinguishes charged-lepton singlets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the Weyl-spinor space and expose
that model when defining representations.
-/

/-!

### B.1. The basis of the charged-lepton-singlet space

-/

/-- A basis on the charged-lepton singlets. -/
noncomputable def basis : Module.Basis (Fin 2) ℂ LeptonSinglet :=
  Fermion.RightHandedWeyl.basis.map valLinEquiv.symm

instance : Module.Finite ℂ LeptonSinglet := Module.Finite.of_basis basis

instance : Module.Free ℂ LeptonSinglet := Module.Free.of_basis basis

/-!

## C. Lorentz action

The Lorentz group acts through the right-handed Weyl representation, transported along the
identification of a charged-lepton singlet with its spinor.
-/

open Matrix MatrixGroups

/-- The Lorentz action on the lepton-singlet basis: the right-handed Weyl
  action by the entrywise conjugate matrix. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (basis α) = ∑ β, star (Λ.1 β α) • basis β := by
  simp only [basis, Module.Basis.map_apply, repLorentzGroup, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, Fermion.RightHandedWeyl.rep_apply_basis,
    Matrix.map_apply, map_sum, map_smul]

/-- The lepton jet coordinates transform contragrediently, by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.dual Λ (basis.dualBasis α) =
      ∑ β, star ((Λ⁻¹).1 α β) • basis.dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => star ((Λ⁻¹).1 l j))
    (fun j => repLorentzGroup_apply_basis Λ⁻¹ j)

/-- The Lorentz action on the conjugate lepton basis: the coefficients are the
  conjugates of those of the lepton action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj Λ ((Basis.conj basis) α) = ∑ β, Λ.1 β α • (Basis.conj basis) β := by
  rw [Representation.conj_apply, Basis.conj_apply,
    LinearEquiv.symm_apply_apply, repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Basis.conj_apply]

/-- The conjugate lepton jet coordinates transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis α) =
      ∑ β, (Λ⁻¹).1 α β • (Basis.conj basis).dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Λ⁻¹).1 l j)
    (fun j => repLorentzGroup_conj_apply_basis Λ⁻¹ j)

/-- **The centre of `SL(2,ℂ)` acts on the charged-lepton-singlet space by `-1`**: the value
  space carries a single Weyl-spinor index, and `-1` is not the identity on a half-integer
  spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro α
  rw [repLorentzGroup_apply_basis]
  fin_cases α <;> simp [Matrix.one_apply]

/-- The centre acts on the conjugate charged-lepton-singlet space by `-1` as well:
  conjugation does not move a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro α
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases α <;> simp [Matrix.one_apply]

/-!

## D. Global Gauge action

The colour and weak factors act trivially, so the gauge group acts only through hypercharge.
The `U(1)` action is `star z ^ 6`; since `z` is unitary, `star z = z⁻¹`, so this represents
charge `-6`.

The formulas below expose the scalar used to compare actions and compute the kernel.
-/

/-- The gauge action on the lepton-singlet basis: multiplication by the hypercharge
  scalar, the colour and weak factors acting trivially. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI g (basis α) = (star g.toU1.1 ^ 6 : ℂ) • basis α := by
  have hb : basis α = ⟨Fermion.RightHandedWeyl.basis α⟩ := by
    simp only [basis, Module.Basis.map_apply]
    rfl
  rw [hb, repGaugeGroupI_basis]

/-- The lepton-singlet coordinate functionals carry the contragredient gauge action: the
  hypercharge scalar of the inverse group element. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI.dual g (basis.dualBasis α) =
      (star (g⁻¹).toU1.1 ^ 6 : ℂ) • basis.dualBasis α := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g α
    (Matrix.of fun p q => if p = q then (star (g⁻¹).toU1.1 ^ 6 : ℂ) else 0)
    (fun q => by rw [repGaugeGroupI_apply_basis]; simp [ite_smul, eq_comm])
  rw [key]
  simp [ite_smul]

/-- The gauge action on the conjugate lepton-singlet basis: the hypercharge scalar,
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

## E. Kernel of the gauge action

An element acts trivially exactly when its hypercharge scalar is one. Its colour and weak
components are unrestricted, since neither appears in the action.
-/

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel.
The `U(1)` component of a central element is a sixth root of unity, so conjugating and raising
to the sixth power gives one, and charge `-6` therefore acts trivially.
-/

/-!

## G. The representation of the jet gauge group

The charged-lepton singlet carries no colour or weak index, so a jet of gauge
transformations acts on its jets purely through the hypercharge power series
`(star u) ^ 6`, multiplying the jet-ring factor and leaving the Weyl factor untouched.

-/

open TensorProduct in
/-- The `(1, 1)_{-6}` action of the jet gauge group on the jet space of the charged-lepton
singlet: multiplication of the jet-ring factor by the hypercharge power series
`(star u) ^ 6`. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (SpaceTimeAlgebra ⊗[ℂ] LeptonSinglet) where
  toFun U := LinearMap.rTensor LeptonSinglet
    (LinearMap.mulLeft ℂ ((star ((U.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6))
  map_one' := by
    rw [show (star (((1 : JetGaugeGroupI).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6
        = 1 from by simp, LinearMap.mulLeft_one, LinearMap.rTensor_id]
    rfl
  map_mul' U₁ U₂ := by
    rw [show (star (((U₁ * U₂).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6
          = (star ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6
            * (star ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6 from by
        rw [show (((U₁ * U₂).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)
            = ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) *
                ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)
            from rfl, star_mul', mul_pow, mul_comm],
      show LinearMap.mulLeft ℂ
          ((star ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6
            * (star ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6)
        = (LinearMap.mulLeft ℂ
            ((star ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6)) ∘ₗ
          (LinearMap.mulLeft ℂ
              ((star ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6)) from
        LinearMap.ext fun z => mul_assoc _ _ z,
      LinearMap.rTensor_comp]
    rfl

open TensorProduct in
/-- The jet gauge action on a pure tensor of the jet space of the charged-lepton
singlet. -/
lemma repJetGaugeGroupI_tmul (U : JetGaugeGroupI) (f : SpaceTimeAlgebra) (ψ : LeptonSinglet) :
    repJetGaugeGroupI U (f ⊗ₜ[ℂ] ψ)
      = ((star ((U.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 6 * f) ⊗ₜ[ℂ] ψ :=
  LinearMap.rTensor_tmul _ _ _ _

open TensorProduct in
/-- **The jet gauge action on the jets of the charged-lepton singlet is fibrewise**: it
commutes with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : SpaceTimeAlgebra)
    (z : SpaceTimeAlgebra ⊗[ℂ] LeptonSinglet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul f ψ =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, repJetGaugeGroupI_tmul,
      repJetGaugeGroupI_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_left_comm]

open TensorProduct in
/-- On jets of constant gauge transformations the jet action reduces to the global
gauge action on the fibre: the `(1, 1)_{-6}` action on the lepton-singlet factor, and
the trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext f x
  obtain ⟨ψ⟩ := x
  have hu : (((JetGaugeGroupI.ofConstant g).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)
      = MvPowerSeries.C ((g.toU1.1 : ℂ)) := rfl
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, repJetGaugeGroupI_tmul, hu, SpaceTimeAlgebra.star_C, ← map_pow,
    TensorProduct.map_tmul, LinearMap.id_apply, repGaugeGroupI_apply]
  rw [show (⟨(star (g.toU1.1 : ℂ) ^ 6) • ψ⟩ : LeptonSinglet)
      = (star (g.toU1.1 : ℂ) ^ 6) • (⟨ψ⟩ : LeptonSinglet) from rfl,
    TensorProduct.tmul_smul,
    show (MvPowerSeries.C (star (g.toU1.1 : ℂ) ^ 6) * f) = (star (g.toU1.1 : ℂ) ^ 6) • f from
      by rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply],
    TensorProduct.smul_tmul']

end LeptonSinglet

/-!

## H. The gauge weight of the LeptonSinglet components

The gauge torus acts diagonally on the basis of `LeptonSinglet`; the weights are recorded by
`LeptonSinglet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the lepton-singlet basis: hypercharge `-6`. -/
def LeptonSinglet.valueGaugeWeight (_ : Fin 2) : GaugeWeight :=
  (0, 0, 0, -6)

/-- The gauge torus acts diagonally on the basis of `LeptonSinglet`, with the weights
  `LeptonSinglet.valueGaugeWeight`. -/
lemma LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI (gaugeTorusGen i) (LeptonSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) •
        LeptonSinglet.basis j := by
  have hb : LeptonSinglet.basis j = ⟨Fermion.RightHandedWeyl.basis j⟩ := by
    simp only [LeptonSinglet.basis, Module.Basis.map_apply]
    rfl
  rw [hb, LeptonSinglet.repGaugeGroupI_basis]
  fin_cases i <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1,
      LeptonSinglet.valueGaugeWeight, GaugeWeight.coord,
      starRingEnd_expI_pow]
  (try congr 1)

/-- The dual action of the gauge torus on the coordinate functionals of
  `LeptonSinglet`: the weights are negated. -/
lemma LeptonSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (LeptonSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i))) •
        LeptonSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `LeptonSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma LeptonSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2) :
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

/-!

## I. The boost weight of the LeptonSinglet components

-/

open Lorentz in
/-- The charged-lepton-singlet basis diagonalises the `z`-boost. -/
lemma leptonSinglet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0) (j : Fin 2) :
    LeptonSinglet.repLorentzGroup (SL2C.boostAxis 2 t ht) (LeptonSinglet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j) • LeptonSinglet.basis j := by
  simp [LeptonSinglet.basis, LeptonSinglet.repLorentzGroup, Module.Basis.map_apply,
    rightHandedWeyl_rep_boostAxis_two_basis]

end StandardModel
