/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
public import Physlib.Relativity.Fermions.Weyl.BoostWeight
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.JetGaugeGroup.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Table
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Lepton doublets

## i. Overview

The Standard Model lepton doublet is a left-handed Weyl spinor in the `(1, 2)_{-3}`
representation. Here charges are normalized as `6Y`, so `-3` is the usual hypercharge
`Y = -1/2`.

The lepton doublet is the datum `StandardModel.Model.leptonDoublet`,
`(.L, .singlet, .fund, -3)`, of the Standard Model table. `LeptonDoublet` is its target
space, a left-handed Weyl spinor tensored with the weak coordinates, and every action on
it — Lorentz, global gauge, jet gauge — is the one the general theory derives from the
datum. The hand-built definitions are kept in comments.

The gauge action is computed on a basis, used to identify its kernel, and descended to
each supported global form of the Standard Model gauge group.

## ii. Key results

- `LeptonDoublet` : the target space of the `(1, 2)_{-3}` multiplet.
- `repLorentzGroup` : the left-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_apply_basis` : the gauge action in the spinor–weak basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.
- `repJetGaugeGroupI` : the action of the jet gauge group on the jets of the doublet.

## iii. Table of contents

- A. The lepton-doublet space
- B. The basis
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. Jet gauge action
- H. Component transformation laws

-/

@[expose] public section

namespace StandardModel

open TensorProduct MvPowerSeries

/-!

## A. The lepton-doublet space

The Weyl factor carries the left-handed Lorentz index, while the functions on `Fin 2`
carry the weak index.

-/

/-- The target vector space of one Standard Model lepton doublet: the target space of the
  datum `StandardModel.Model.leptonDoublet`, a left-handed Weyl spinor tensored with the
  weak coordinates. It carries the `(1, 2)_{-3}` representation of the gauge group. -/
abbrev LeptonDoublet : Type := Model.leptonDoublet.V

namespace LeptonDoublet

/- The hand-built wrapper, now an abbreviation of the datum's target space:

/-- The target vector space of one Standard Model lepton doublet.
  It carries the `(1, 2)_{-3}` representation of the gauge group. -/
@[ext]
structure LeptonDoublet where
  /-- The left-handed Weyl spinor with its weak-doublet index. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

/-- Identifies a lepton doublet with its underlying tensor-product value. -/
def valEquiv : LeptonDoublet ≃ Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonDoublet := AddEquiv.module ℂ { valEquiv with map_add' _ _ := rfl }

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : LeptonDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
-/

/-- The target space is the datum's target space. -/
example : LeptonDoublet = (Fermion.LeftHandedWeyl ⊗[ℂ] (Fin 2 → ℂ)) := rfl

/-!

## B. The basis

-/

/-- A basis on the lepton doublets: the Weyl basis tensored with the coordinate basis of
  the weak index. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 2) ℂ LeptonDoublet :=
  Model.leptonDoublet.basis

/-- The lepton-doublet basis vector as an explicit spinor–weak tensor. -/
lemma basis_apply (k j : Fin 2) :
    basis (k, j) = Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] Pi.single j 1 :=
  Model.leptonDoublet.basis_apply k j

/-!

## C. Lorentz action

The Lorentz group acts on the left-handed Weyl factor and leaves the weak index fixed.

-/

open Matrix MatrixGroups

/-- The left-handed Lorentz representation on lepton doublets: the Lorentz action the
  general theory derives from the datum. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonDoublet :=
  Model.leptonDoublet.toMatterField.repLorentz

/- The hand-built definition, now derived from the datum:

open Representation in
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonDoublet where
  toFun Λ := valLinEquiv.symm ∘ₗ
      (TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 2)) Λ))
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 l
    simp [TensorProduct.map_map, Module.End.mul_eq_comp]
-/

/-- The Lorentz action on a pure spinor–weak tensor: the left-handed action on the Weyl
  factor, the weak index untouched. -/
lemma repLorentzGroup_tmul (Λ : SL(2,ℂ)) (s : Fermion.LeftHandedWeyl) (v : Fin 2 → ℂ) :
    repLorentzGroup Λ (s ⊗ₜ v) = Fermion.LeftHandedWeyl.rep Λ s ⊗ₜ v :=
  LocalGaugeData.MatrixRep.repLorentz_apply_symm_tmul (LinearEquiv.refl ℂ _) _ Λ s v

/-!

## D. Gauge action

The colour factor acts trivially, while `SU(2)` acts on the weak index. The `U(1)` action
is `star z ^ 3`; since `z` is unitary, `star z = z⁻¹`, so this represents charge `-3`.

The tensor and basis formulas below expose the coefficients used to compare actions and
compute the kernel.

-/

/-- The `JetRing`-valued weak matrix of the jet gauge action on the lepton doublet: the
  matrix of jets by which a gauge jet acts on the datum. -/
noncomputable def doubletMatrix (U : JetGaugeGroupI) : Matrix (Fin 2) (Fin 2) JetRing :=
  Model.leptonDoublet.rep.mat U

open LocalGaugeData in
/-- The weak matrix of a gauge jet is its `SU(2)` matrix carrying the `-3` hypercharge
  phase `(star u) ^ 3`. -/
lemma doubletMatrix_eq (U : JetGaugeGroupI) :
    doubletMatrix U = ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 3) •
      ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) := by
  show MatterField.chargePow (-3) U.2.2 • U.2.1.1 = _
  congr 1

/-- The constant term of the weak matrix of a constant gauge jet: the `SU(2)` matrix of
  the gauge transformation carrying its `-3` hypercharge phase. -/
lemma doubletMatrix_ofConstant_map_constantCoeff (g : GaugeGroupI) :
    (doubletMatrix (JetGaugeGroupI.ofConstant g)).map (constantCoeff : JetRing → ℂ)
      = (star g.toU1.1 ^ 3) • g.toSU2.1 := by
  have hu : (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
      = MvPowerSeries.C (g.toU1.1 : ℂ) := rfl
  have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).2.1 :
        specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) i j
      = MvPowerSeries.C (g.toSU2.1 i j) := fun _ _ => rfl
  rw [doubletMatrix_eq]
  ext i j
  simp [hu, hM]

/-- The weak matrix of a constant gauge jet is constant. -/
lemma doubletMatrix_ofConstant (g : GaugeGroupI) :
    doubletMatrix (JetGaugeGroupI.ofConstant g)
      = ((doubletMatrix (JetGaugeGroupI.ofConstant g)).map (constantCoeff : JetRing → ℂ)).map
          (MvPowerSeries.C : ℂ → JetRing) := by
  have hu : (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
      = MvPowerSeries.C (g.toU1.1 : ℂ) := rfl
  have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).2.1 :
        specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) i j
      = MvPowerSeries.C (g.toSU2.1 i j) := fun _ _ => rfl
  rw [doubletMatrix_ofConstant_map_constantCoeff, doubletMatrix_eq]
  ext i j
  simp [hu, hM]

/-- The `(1, 2)_{-3}` action of the unquotiented Standard Model gauge group: the global
  action the general theory derives from the datum, the constant term of the jet action. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonDoublet :=
  Model.leptonDoublet.rep.repGlobal (LinearEquiv.refl ℂ LeptonDoublet)

/- The hand-built definition, now derived from the datum:

noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonDoublet where
  toFun g := valLinEquiv.symm ∘ₗ
        (TensorProduct.map
        (LinearMap.id (M := Fermion.LeftHandedWeyl))
        g.toSU2.1.toEuclideanLin)
      ∘ₗ LinearMap.lsmul ℂ _ (star g.toU1.1 ^ 3 : ℂ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext l
    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
    ring_nf
-/

/-- The gauge action on a pure spinor–weak tensor: the `SU(2)` matrix, scaled by the
  hypercharge factor, acts on the weak index. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (v : Fermion.LeftHandedWeyl) (w : Fin 2 → ℂ) :
    repGaugeGroupI g (v ⊗ₜ w) = v ⊗ₜ ((star g.toU1.1 ^ 3) • g.toSU2.1).mulVec w := by
  rw [← doubletMatrix_ofConstant_map_constantCoeff]
  exact LocalGaugeData.MatrixRep.repGlobal_apply_symm_tmul (LinearEquiv.refl ℂ _) _ g v w

/-- The gauge action on the lepton-doublet basis: the spinor index is inert and the weak
  index transforms by the `SU(2)` matrix, scaled by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI g (basis j) =
      ∑ w, (star g.toU1.1 ^ 3 * g.toSU2.1 w j.2) • basis (j.1, w) := by
  obtain ⟨k, s⟩ := j
  rw [basis_apply, repGaugeGroupI_tmul, Matrix.mulVec_single_one]
  have hcol : ((star g.toU1.1 ^ 3) • g.toSU2.1).col s
      = ∑ w, (star g.toU1.1 ^ 3 * g.toSU2.1 w s) • (Pi.single w 1 : Fin 2 → ℂ) := by
    ext i
    simp [Matrix.col_apply, Pi.single_apply, Finset.sum_apply]
  rw [hcol, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [basis_apply, TensorProduct.tmul_smul]

/-- Two gauge elements induce the same action exactly when their weak-basis coefficients
  agree. -/
lemma repGaugeGroupI_eq_iff_mul_eq {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔ ∀ j j',
    star g₁.toU1.1 ^ 3 * g₁.toSU2.1 j' j =
      star g₂.toU1.1 ^ 3 * g₂.toSU2.1 j' j := by
  constructor
  · intro h j j'
    have h' : repGaugeGroupI g₁ (basis (0, j)) = repGaugeGroupI g₂ (basis (0, j)) := by rw [h]
    rw [repGaugeGroupI_apply_basis, repGaugeGroupI_apply_basis] at h'
    have h'' := congrArg (fun v => basis.repr v (0, j')) h'
    fin_cases j' <;> simpa [Finsupp.single_apply] using h''
  · intro h
    refine basis.ext fun ⟨k, j⟩ => ?_
    rw [repGaugeGroupI_apply_basis, repGaugeGroupI_apply_basis]
    exact Finset.sum_congr rfl fun j' _ => by rw [h j j']

/-!

## E. Kernel of the gauge action

An element acts trivially when its weak action is scalar and that scalar cancels its
`U(1)` phase. Its colour component is unrestricted because the lepton doublet is an
`SU(3)` singlet.
-/

/-- Characterizes the full-group elements acting trivially on the lepton doublet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a : ℂ, g.toSU2.1 = a • 1 ∧
      a * star g.toU1.1 ^ 3 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor; swap
  · rintro ⟨a, h₁, h₂⟩ j j'
    simp only [Matrix.smul_apply, smul_eq_mul, h₁, map_one, OneMemClass.coe_one,
      star_one, one_pow, one_mul]
    linear_combination h₂ * (1 : Matrix _ _ ℂ) j' j
  · intro h
    have hc : star g.toU1.1 ^ 3 ≠ 0 := by
      apply pow_ne_zero
      rw [star_ne_zero]
      intro hzero
      have hu := Unitary.star_mul_self_of_mem g.toU1.2
      simp [hzero] at hu
    use g.toSU2.1 0 0
    simp only [map_one, OneMemClass.coe_one, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, ne_eq,
      one_ne_zero, not_false_eq_true, one_apply_ne, mul_eq_zero, zero_ne_one,
      star_one, one_pow, one_mul] at h
    rcases h with ⟨⟨h₀₀, h₁₀⟩, h₀₁, h₁₁⟩
    have h₁₀' := h₁₀.resolve_left hc
    have h₀₁' := h₀₁.resolve_left hc
    have hdiag : g.toSU2.1 1 1 = g.toSU2.1 0 0 := by
      apply mul_left_cancel₀ hc
      rw [h₁₁, h₀₀]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [h₁₀', h₀₁', hdiag]
    · simpa [mul_comm] using h₀₀

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its
kernel. For the central `ℤ₆`, the weak central phase and charge `-3` phase combine to a
sixth power and therefore act trivially.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(1, 2)_{-3}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  rw [mem_repGaugeGroupI_ker_iff_eq]
  use starRingEnd ℂ (x ^ 3)
  simp only [gaugeGroupℤ₆OfRoot_toSU2, gaugeGroupℤ₆SU2OfRoot_eq_mul_id,
    RCLike.star_def, Complex.conj_rootsOfUnity hx, Units.val_inv_eq_inv_val, inv_pow,
    map_pow, gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe, true_and]
  field_simp
  exact ((mem_rootsOfUnity' 6 x).mp hx).symm

/-- Every supported quotient subgroup acts trivially on the lepton doublet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(1, 2)_{-3}` representation for every supported global form of the
  Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) LeptonDoublet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## G. Jet gauge action

The `(1, 2)_{-3}` representation extends to jets: the `SU(2)` power-series matrix of a
jet of gauge transformations, scaled by the hypercharge power series `star u ^ 3`, acts
`JetRing`-linearly on the weak factor. On jets of constant gauge transformations the
action reduces to the global gauge action. Both are the general theory's, for the datum.

-/

/-- The `(1, 2)_{-3}` action of the jet gauge group on the jet space of the lepton
doublet: the jet action the general theory derives from the datum. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] LeptonDoublet) :=
  Model.leptonDoublet.toMatterField.repJet

/- The hand-built definition, now derived from the datum:

/-- Absorbs the jet ring into the weak index. -/
noncomputable def jetValLinEquiv :
    JetRing ⊗[ℂ] LeptonDoublet ≃ₗ[ℂ]
      Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 2) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) valLinEquiv).trans <|
    (TensorProduct.leftComm ℂ JetRing Fermion.LeftHandedWeyl
        (EuclideanSpace ℂ (Fin 2))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.LeftHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
            (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ))).trans <|
          ((TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 2)).trans
            (WithLp.linearEquiv 2 JetRing (Fin 2 → JetRing)).symm).restrictScalars ℂ

noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] LeptonDoublet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 2)) Fermion.LeftHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2
            (((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 3) •
              ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
                Matrix (Fin 2) (Fin 2) JetRing))).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := …
  map_mul' U₁ U₂ := …
-/

/-- **The jet gauge action on the jets of the lepton doublet is fibrewise**: it commutes
with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] LeptonDoublet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z :=
  Model.leptonDoublet.toMatterField.repJet_smul U χ z

/-- On jets of constant gauge transformations the jet action reduces to the global
gauge action on the fibre: the `(1, 2)_{-3}` action on the lepton-doublet factor, and
the trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) :=
  Model.leptonDoublet.rep.repJet_ofConstant (LinearEquiv.refl ℂ LeptonDoublet)
    doubletMatrix_ofConstant g

/-!

## H. Component transformation laws

The basis of `LeptonDoublet` splits as a left-handed Weyl index and a weak-isospin index.
The Lorentz group moves only the first, the gauge group only the second (up to the
hypercharge scalar), so both actions are recorded as a single sum over the index they move.
Dualising inverts and transposes the coefficient matrix, and conjugating stars it; the four
combinations below are what a component of a lepton-doublet symbol needs.

-/

/-- The Lorentz action on the lepton-doublet basis: the weak index is inert and the
  spinor index transforms by the matrix itself. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup Λ (basis j) = ∑ β, Λ.1 β j.1 • basis (β, j.2) := by
  obtain ⟨k, w⟩ := j
  rw [basis_apply, repLorentzGroup_tmul, Fermion.LeftHandedWeyl.rep_apply_basis,
    TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [basis_apply, TensorProduct.smul_tmul']

/-- The lepton-doublet coordinate functionals transform contragrediently, by the
  inverse matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup.dual Λ (basis.dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • basis.dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup basis Λ j
    (Matrix.of fun p q => if p.2 = q.2 then (Λ⁻¹).1 p.1 q.1 else 0)
    (fun q => by
      rw [repLorentzGroup_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The Lorentz action on the conjugate lepton-doublet basis: the coefficients are the
  conjugates of those of the lepton-doublet action. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup.conj Λ (basis.conj j)
      = ∑ β, star (Λ.1 β j.1) • basis.conj (β, j.2) := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Module.Basis.conj_apply]

/-- The conjugate lepton-doublet coordinate functionals transform by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup.conj.dual Λ (basis.conj.dualBasis j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • basis.conj.dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj basis.conj Λ j
    (Matrix.of fun p q => if p.2 = q.2 then star ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- **The centre of `SL(2,ℂ)` acts on the lepton-doublet space by `-1`**: the value space carries a
  single Weyl-spinor index, and `-1` is not the identity on a half-integer spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro j
  obtain ⟨a, w⟩ := j
  rw [repLorentzGroup_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply]

/-- The centre acts on the conjugate lepton-doublet space by `-1` as well: conjugation does not
  move a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply basis.conj.ext
  intro j
  obtain ⟨a, w⟩ := j
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply]

/-- The lepton-doublet coordinate functionals carry the contragredient gauge action: the
  hypercharge and `SU(2)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ w, (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) • basis.dualBasis (j.1, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 p.2 q.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate lepton-doublet basis: the coefficients of the
  lepton-doublet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI.conj g (basis.conj j) =
      ∑ w, star (star g.toU1.1 ^ 3 * g.toSU2.1 w j.2) • basis.conj (j.1, w) := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Module.Basis.conj_apply]

/-- The conjugate lepton-doublet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI.conj.dual g (basis.conj.dualBasis j) =
      ∑ w, star (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) •
        basis.conj.dualBasis (j.1, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj basis.conj g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 p.2 q.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

end LeptonDoublet

/-!

## The gauge weight of the LeptonDoublet components

The gauge torus acts diagonally on the basis of `LeptonDoublet`; the weights are recorded by
`LeptonDoublet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the lepton-doublet basis: the isospin weight and hypercharge
  `-3`. -/
def LeptonDoublet.valueGaugeWeight (j : Fin 2 × Fin 2) : GaugeWeight :=
  (0, 0, isoWeight j.2, -3)

/-- The gauge torus acts diagonally on the basis of `LeptonDoublet`, with the weights
  `LeptonDoublet.valueGaugeWeight`. -/
lemma LeptonDoublet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoublet.repGaugeGroupI (gaugeTorusGen i) (LeptonDoublet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i) •
        LeptonDoublet.basis j := by
  obtain ⟨k, s⟩ := j
  rw [LeptonDoublet.repGaugeGroupI_apply_basis]
  fin_cases i <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      LeptonDoublet.valueGaugeWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, starRingEnd_expI_pow]

/-- The dual action of the gauge torus on the coordinate functionals of
  `LeptonDoublet`: the weights are negated. -/
lemma LeptonDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoublet.repGaugeGroupI.dual (gaugeTorusGen i) (LeptonDoublet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i))) •
        LeptonDoublet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => LeptonDoublet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `LeptonDoublet`: the two negations cancel and the weights are those of
  the value space. -/
lemma LeptonDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoublet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((LeptonDoublet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i) •
        (LeptonDoublet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord LeptonDoublet.repGaugeGroupI.conj (LeptonDoublet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => LeptonDoublet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## The boost weight of the LeptonDoublet components

-/

open Lorentz in
/-- The lepton-doublet basis diagonalises the `z`-boost: the isospin index is inert. -/
lemma leptonDoublet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0)
    (j : Fin 2 × Fin 2) :
    LeptonDoublet.repLorentzGroup (SL2C.boostAxis 2 t ht) (LeptonDoublet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j.1) • LeptonDoublet.basis j := by
  obtain ⟨k, a⟩ := j
  rw [LeptonDoublet.basis_apply, LeptonDoublet.repLorentzGroup_tmul,
    leftHandedWeyl_rep_boostAxis_two_basis, ← TensorProduct.smul_tmul']

end StandardModel
