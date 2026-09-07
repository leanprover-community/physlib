/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Fermions.Weyl.BoostWeight
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.DerivAlgebra
public import Physlib.Mathematics.ConjModule
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

-/

@[expose] public section

namespace StandardModel

/-!

## A. The charged-lepton-singlet space

The Weyl spinor carries the right-handed Lorentz index, and it is the whole of the multiplet:
a charged-lepton singlet has no colour index and no weak-isospin index.
-/

/-- The target vector space of one Standard Model charged-lepton singlet.
  It carries the `(1, 1)_{-6}` representation of the gauge group. -/
@[ext]
structure LeptonSinglet where
  /-- The right-handed Weyl spinor. -/
  val : Fermion.RightHandedWeyl

namespace LeptonSinglet

/-!

## B. Linear structure

The wrapper distinguishes charged-lepton singlets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the Weyl-spinor space and expose
that model when defining representations.
-/

/-- Identifies a charged-lepton singlet with its underlying Weyl spinor. -/
def valEquiv : LeptonSinglet ≃ Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying Weyl-spinor space. -/
def valLinEquiv : LeptonSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (l : LeptonSinglet) : valLinEquiv l = l.val := rfl

lemma valLinEquiv_symm_apply (m : Fermion.RightHandedWeyl) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (l₁ l₂ : LeptonSinglet) : (l₁ + l₂).val = l₁.val + l₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (l : LeptonSinglet) : (r • l).val = r • l.val := rfl

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

/-- The right-handed Lorentz representation on charged-lepton singlets. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ Fermion.RightHandedWeyl.rep Λ ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 l
    simp [Module.End.mul_eq_comp]

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
    repLorentzGroup.conj Λ (basis.conj α) = ∑ β, Λ.1 β α • basis.conj β := by
  rw [Representation.conj_apply, Module.Basis.conj_apply,
    LinearEquiv.symm_apply_apply, repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Module.Basis.conj_apply]

/-- The conjugate lepton jet coordinates transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup.conj.dual Λ (basis.conj.dualBasis α) =
      ∑ β, (Λ⁻¹).1 α β • basis.conj.dualBasis β :=
  Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Λ⁻¹).1 l j)
    (fun j => repLorentzGroup_conj_apply_basis Λ⁻¹ j)

/-!

## D. Global Gauge action

The colour and weak factors act trivially, so the gauge group acts only through hypercharge.
The `U(1)` action is `star z ^ 6`; since `z` is unitary, `star z = z⁻¹`, so this represents
charge `-6`.

The formulas below expose the scalar used to compare actions and compute the kernel.
-/

/-- The `(1, 1)_{-6}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      LinearMap.lsmul ℂ Fermion.RightHandedWeyl (star g.toU1.1 ^ 6 : ℂ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext l
    simp [smul_smul, mul_comm, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge group acts on a charged-lepton singlet by the hypercharge scalar alone. -/
lemma repGaugeGroupI_apply (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl) :
    repGaugeGroupI g ⟨ψ⟩ = ⟨(star g.toU1.1 ^ 6) • ψ⟩ := rfl

open Fermion in
/-- The gauge action is diagonal in the standard Weyl basis. -/
lemma repGaugeGroupI_basis (g : GaugeGroupI) (k : Fin 2) :
    repGaugeGroupI g ⟨RightHandedWeyl.basis k⟩ =
      (star g.toU1.1 ^ 6) • (⟨RightHandedWeyl.basis k⟩ : LeptonSinglet) := rfl

open Fermion in
/-- Two gauge elements induce the same action exactly when their hypercharge scalars agree. -/
lemma repGaugeGroupI_eq_iff {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔
      star g₁.toU1.1 ^ 6 = star g₂.toU1.1 ^ 6 := by
  constructor
  · intro h
    have h' := congrFun (congrArg (fun f => f.1) h)
      (⟨RightHandedWeyl.basis 0⟩ : LeptonSinglet)
    simp only [LinearMap.coe_toAddHom, repGaugeGroupI_apply] at h'
    have h'' := congrArg (fun v => RightHandedWeyl.basis.repr (LeptonSinglet.val v) 0) h'
    simpa using h''
  · intro h
    have h' : (starRingEnd ℂ) g₁.toU1.1 ^ 6 = (starRingEnd ℂ) g₂.toU1.1 ^ 6 := h
    ext l
    simp [repGaugeGroupI, h']

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
    repGaugeGroupI.conj g (basis.conj α) =
      star (star g.toU1.1 ^ 6 : ℂ) • basis.conj α := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, LinearEquiv.map_smulₛₗ, starRingEnd_apply]

/-- The conjugate lepton-singlet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI.conj.dual g (basis.conj.dualBasis α) =
      star (star (g⁻¹).toU1.1 ^ 6 : ℂ) • basis.conj.dualBasis α := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj basis.conj g α
    (Matrix.of fun p q => if p = q then star (star (g⁻¹).toU1.1 ^ 6 : ℂ) else 0)
    (fun q => by rw [repGaugeGroupI_conj_apply_basis]; simp [ite_smul, eq_comm])
  rw [key]
  simp [ite_smul]

/-!

## E. Kernel of the gauge action

An element acts trivially exactly when its hypercharge scalar is one. Its colour and weak
components are unrestricted, since neither appears in the action.
-/

/-- Characterizes the full-group elements acting trivially on the charged-lepton singlet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ star g.toU1.1 ^ 6 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff]
  simp

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel.
The `U(1)` component of a central element is a sixth root of unity, so conjugating and raising
to the sixth power gives one, and charge `-6` therefore acts trivially.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(1, 1)_{-6}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  simp only [gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe]
  have hx6 : (((x : ℂˣ) : ℂ)) ^ 6 = 1 := (mem_rootsOfUnity' 6 x).mp hx
  simpa [map_pow] using congrArg (starRingEnd ℂ) hx6

/-- Every supported quotient subgroup acts trivially on the charged-lepton singlet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(1, 1)_{-6}` representation for every supported global form of the
  Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) LeptonSinglet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

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
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] LeptonSinglet) where
  toFun U := LinearMap.rTensor LeptonSinglet
    (LinearMap.mulLeft ℂ ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6))
  map_one' := by
    rw [show (star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6
        = 1 from by simp, LinearMap.mulLeft_one, LinearMap.rTensor_id]
    rfl
  map_mul' U₁ U₂ := by
    rw [show (star (((U₁ * U₂).2.2 : unitary JetRing) : JetRing)) ^ 6
          = (star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 6
            * (star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 6 from by
        rw [show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing)
            = ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
            from rfl, star_mul', mul_pow, mul_comm],
      show LinearMap.mulLeft ℂ
          ((star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 6
            * (star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 6)
        = (LinearMap.mulLeft ℂ ((star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 6)) ∘ₗ
          (LinearMap.mulLeft ℂ ((star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 6)) from
        LinearMap.ext fun z => mul_assoc _ _ z,
      LinearMap.rTensor_comp]
    rfl

open TensorProduct in
/-- The jet gauge action on a pure tensor of the jet space of the charged-lepton
singlet. -/
lemma repJetGaugeGroupI_tmul (U : JetGaugeGroupI) (f : JetRing) (ψ : LeptonSinglet) :
    repJetGaugeGroupI U (f ⊗ₜ[ℂ] ψ)
      = ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6 * f) ⊗ₜ[ℂ] ψ :=
  LinearMap.rTensor_tmul _ _ _ _

open TensorProduct in
/-- **The jet gauge action on the jets of the charged-lepton singlet is fibrewise**: it
commutes with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] LeptonSinglet) :
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
  have hu : (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
      = MvPowerSeries.C ((g.toU1.1 : ℂ)) := rfl
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, repJetGaugeGroupI_tmul, hu, JetRing.star_C, ← map_pow,
    TensorProduct.map_tmul, LinearMap.id_apply, repGaugeGroupI_apply]
  rw [show (⟨(star (g.toU1.1 : ℂ) ^ 6) • ψ⟩ : LeptonSinglet)
      = (star (g.toU1.1 : ℂ) ^ 6) • (⟨ψ⟩ : LeptonSinglet) from rfl,
    TensorProduct.tmul_smul,
    show (MvPowerSeries.C (star (g.toU1.1 : ℂ) ^ 6) * f) = (star (g.toU1.1 : ℂ) ^ 6) • f from
      by rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply],
    TensorProduct.smul_tmul']

end LeptonSinglet

/-!

## The gauge weight of the LeptonSinglet components

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
    LeptonSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((LeptonSinglet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) •
        (LeptonSinglet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord LeptonSinglet.repGaugeGroupI.conj (LeptonSinglet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## The boost weight of the LeptonSinglet components

-/

open Lorentz in
/-- The charged-lepton-singlet basis diagonalises the `z`-boost. -/
lemma leptonSinglet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0) (j : Fin 2) :
    LeptonSinglet.repLorentzGroup (SL2C.boostAxis 2 t ht) (LeptonSinglet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j) • LeptonSinglet.basis j := by
  simp [LeptonSinglet.basis, LeptonSinglet.repLorentzGroup, Module.Basis.map_apply,
    rightHandedWeyl_rep_boostAxis_two_basis]

end StandardModel
