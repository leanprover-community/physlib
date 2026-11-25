/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import PhyslibAlpha.Mathematics.RepresentationDual
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
/-!
# Lepton doublets

The value space of the lepton doublet `(1, 2)_{-3}`, its Lorentz and gauge actions, their
kernel and descent, and the actions and gauge weights on components.

## i. Overview

The Standard Model lepton doublet is a left-handed Weyl spinor in the `(1, 2)_{-3}`
representation. Here charges are normalized as `6Y`, so `-3` is the usual hypercharge
`Y = -1/2`.

`LeptonDoubletV` is its target space, a left-handed Weyl spinor tensored with the weak
coordinates. The Lorentz group acts on the Weyl factor, the global gauge group on the weak
factor by its `SU(2)` matrix scaled by the hypercharge phase.

The gauge action is computed on a basis, used to identify its kernel, and descended to
each supported global form of the Standard Model gauge group. Both actions are then written on
the basis together with their dual, conjugate and conjugate-dual forms, which are what a
component of a lepton-doublet symbol needs. The centre `-1` of `SL(2,ℂ)` acts by `-1`, as on
any single Weyl-spinor index, and the gauge torus acts diagonally on the basis, with the isospin
weights and hypercharge `-3`.

## ii. Key results

- `LeptonDoubletV` : the target space of the `(1, 2)_{-3}` multiplet.
- `repLorentzGroup` : the left-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_apply_basis` : the gauge action in the spinor–weak basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.
- `repLorentzGroup_neg_one` : the centre of `SL(2,ℂ)` acts by `-1`.
- `valueGaugeWeight` : the gauge weights of the basis, with
  `repGaugeGroupI_gaugeTorusGen_basis`.

## iii. Table of contents

- A. The lepton-doublet space
- B. The basis
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. Component transformation laws
- H. The gauge weights of the components

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The lepton-doublet space

The Weyl factor carries the left-handed Lorentz index, while the functions on `Fin 2`
carry the weak index.

-/

/-- The target vector space of one Standard Model lepton doublet, a left-handed Weyl spinor
  tensored with the weak coordinates. It carries the `(1, 2)_{-3}` representation of the
  gauge group. -/
abbrev LeptonDoubletV : Type := Fermion.LeftHandedWeyl ⊗[ℂ] (Fin 2 → ℂ)

namespace LeptonDoubletV

/-!

## B. The basis

-/

/-- A basis on the lepton doublets, the Weyl basis tensored with the coordinate basis of
  the weak index. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 2) ℂ LeptonDoubletV :=
  Fermion.LeftHandedWeyl.basis.tensorProduct (Pi.basisFun ℂ (Fin 2))

/-- The lepton-doublet basis vector as an explicit spinor–weak tensor. -/
lemma basis_apply (k j : Fin 2) :
    basis (k, j) = Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] Pi.single j 1 := by
  rw [basis, Module.Basis.tensorProduct_apply, Pi.basisFun_apply]

/-!

## C. Lorentz action

The Lorentz group acts on the left-handed Weyl factor and leaves the weak index fixed.

-/

open Matrix MatrixGroups

/-- The left-handed Lorentz representation on lepton doublets, the left-handed Weyl action on
  the spinor factor and trivial on the weak index. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonDoubletV :=
  Fermion.LeftHandedWeyl.rep.tprod (Representation.trivial ℂ (SL(2,ℂ)) (Fin 2 → ℂ))

/-- The Lorentz action on a pure spinor–weak tensor is the left-handed action on the Weyl
  factor, the weak index untouched. -/
lemma repLorentzGroup_tmul (Λ : SL(2,ℂ)) (s : Fermion.LeftHandedWeyl) (v : Fin 2 → ℂ) :
    repLorentzGroup Λ (s ⊗ₜ v) = Fermion.LeftHandedWeyl.rep Λ s ⊗ₜ v := by
  simp [repLorentzGroup, Representation.tprod_apply]

/-!

## D. Gauge action

The colour factor acts trivially, while `SU(2)` acts on the weak index. The `U(1)` action
is `star z ^ 3`; since `z` is unitary, `star z = z⁻¹`, so this represents charge `-3`.

The tensor and basis formulas below expose the coefficients used to compare actions and
compute the kernel.

-/

/-- The `(1, 2)_{-3}` action of the unquotiented Standard Model gauge group. The `SU(2)` matrix,
  scaled by the hypercharge factor `star u ^ 3`, acts on the weak index. Since `u` is unitary,
  `star u = u⁻¹`, so this is charge `-3`. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonDoubletV where
  toFun g := TensorProduct.map LinearMap.id
    (Matrix.toLin' ((star g.toU1.1 ^ 3 : ℂ) • g.toSU2.1))
  map_one' := by
    simp [Module.End.one_eq_id]
  map_mul' g h := by
    rw [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp, ← Matrix.toLin'_mul]
    congr 2
    simp only [map_mul, Submonoid.coe_mul, star_mul', mul_pow, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [mul_comm]

/-- On a pure spinor–weak tensor the `SU(2)` matrix, scaled by the hypercharge factor, acts on
  the weak index. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (v : Fermion.LeftHandedWeyl) (w : Fin 2 → ℂ) :
    repGaugeGroupI g (v ⊗ₜ w) = v ⊗ₜ ((star g.toU1.1 ^ 3) • g.toSU2.1).mulVec w := by
  simp only [repGaugeGroupI, MonoidHom.coe_mk, OneHom.coe_mk, TensorProduct.map_tmul,
    LinearMap.id_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, TensorProduct.tmul_smul]

/-- The gauge action on the lepton-doublet basis. The spinor index is inert and the weak
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

/-- Expands the lepton-doublet gauge action on a tensor-product basis vector. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k j : Fin 2) :
    repGaugeGroupI g (basis (k, j)) =
      ∑ j' : Fin 2, (star g.toU1.1 ^ 3 * g.toSU2.1 j' j) • basis (k, j') := by
  simpa using repGaugeGroupI_apply_basis g (k, j)

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
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, IsConcreteLE.le_iff,
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
    Representation ℂ (GaugeGroup Q) LeptonDoubletV
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## G. Component transformation laws

The basis of `LeptonDoubletV` splits as a left-handed Weyl index and a weak-isospin index.
The Lorentz group moves only the first, the gauge group only the second (up to the
hypercharge scalar), so both actions are recorded as a single sum over the index they move.
Dualising inverts and transposes the coefficient matrix, and conjugating stars it. The four
combinations below are what a component of a lepton-doublet symbol needs.

-/

/-- The Lorentz action on the lepton-doublet basis. The weak index is inert and the
  spinor index transforms by the matrix itself. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup Λ (basis j) = ∑ β, Λ.1 β j.1 • basis (β, j.2) := by
  obtain ⟨k, w⟩ := j
  rw [basis_apply, repLorentzGroup_tmul, Fermion.LeftHandedWeyl.rep_apply_basis,
    TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [basis_apply, TensorProduct.smul_tmul']

/-- A sum over the spinor and weak indices with a Kronecker delta on the weak index collapses to
  a sum over the spinor index. -/
private lemma sum_ite_snd {W : Type} [AddCommMonoid W] [Module ℂ W] (c : Fin 2 → ℂ)
    (f : Fin 2 × Fin 2 → W) (q : Fin 2 × Fin 2) :
    ∑ β, c β • f (β, q.2) = ∑ p : Fin 2 × Fin 2, (if p.2 = q.2 then c p.1 else 0) • f p := by
  simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- A sum over the spinor and weak indices with a Kronecker delta on the spinor index collapses
  to a sum over the weak index. -/
private lemma sum_ite_fst {W : Type} [AddCommMonoid W] [Module ℂ W] (c : Fin 2 → ℂ)
    (f : Fin 2 × Fin 2 → W) (q : Fin 2 × Fin 2) :
    ∑ w, c w • f (q.1, w) = ∑ p : Fin 2 × Fin 2, (if p.1 = q.1 then c p.2 else 0) • f p := by
  simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero]

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

/-- The Lorentz action on the conjugate lepton-doublet basis. The coefficients are the
  conjugates of those of the lepton-doublet action. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup.conj Λ ((Basis.conj basis) j)
      = ∑ β, star (Λ.1 β j.1) • (Basis.conj basis) (β, j.2) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate lepton-doublet coordinate functionals transform by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • (Basis.conj basis).dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj (Basis.conj basis) Λ j
    (Matrix.of fun p q => if p.2 = q.2 then star ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp only [Matrix.of_apply]
      exact sum_ite_snd _ _ _)
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The centre of `SL(2,ℂ)` acts on the lepton-doublet space by `-1`. The value space carries a
  single Weyl-spinor index, and `-1` is not the identity on a half-integer spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro j
  obtain ⟨a, w⟩ := j
  rw [repLorentzGroup_apply_basis]
  fin_cases a <;>
    simp [basis_apply, Matrix.one_apply] <;> exact neg_one_smul ℂ (_ : LeptonDoubletV)

/-- The centre acts on the conjugate lepton-doublet space by `-1` as well, conjugation not
  moving a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro j
  obtain ⟨a, w⟩ := j
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases a <;>
    simp [basis_apply, Matrix.one_apply]

/-- The lepton-doublet coordinate functionals carry the contragredient gauge action, by the
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

/-- The gauge action on the conjugate lepton-doublet basis has the coefficients of the
  lepton-doublet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI.conj g ((Basis.conj basis) j) =
      ∑ w, star (star g.toU1.1 ^ 3 * g.toSU2.1 w j.2) • (Basis.conj basis) (j.1, w) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate lepton-doublet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI.conj.dual g ((Basis.conj basis).dualBasis j) =
      ∑ w, star (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) •
        (Basis.conj basis).dualBasis (j.1, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj (Basis.conj basis) g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 p.2 q.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp only [Matrix.of_apply]
      exact sum_ite_fst _ _ _)
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-!

## H. The gauge weights of the components

The gauge torus acts diagonally on the basis of `LeptonDoubletV`. The weights are recorded by
`LeptonDoubletV.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the lepton-doublet basis, isospin weight and hypercharge
  `-3`. -/
def valueGaugeWeight (j : Fin 2 × Fin 2) : GaugeWeight :=
  (0, 0, isoWeight j.2, -3)

/-- The gauge torus acts diagonally on the basis of `LeptonDoubletV`, with the weights
  `LeptonDoubletV.valueGaugeWeight`. -/
lemma repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoubletV.repGaugeGroupI (gaugeTorusGen i) (LeptonDoubletV.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoubletV.valueGaugeWeight j) i) •
        LeptonDoubletV.basis j := by
  obtain ⟨k, s⟩ := j
  rw [LeptonDoubletV.repGaugeGroupI_apply_basis]
  fin_cases i <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      LeptonDoubletV.valueGaugeWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, starRingEnd_expI_pow]

/-- The dual action of the gauge torus on the coordinate functionals of
  `LeptonDoubletV` negates the weights. -/
lemma repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoubletV.repGaugeGroupI.dual (gaugeTorusGen i) (LeptonDoubletV.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (LeptonDoubletV.valueGaugeWeight j) i))) •
        LeptonDoubletV.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => LeptonDoubletV.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `LeptonDoubletV`. The two negations cancel and the weights are those of
  the value space. -/
lemma repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoubletV.repGaugeGroupI.conj.dual (gaugeTorusGen i)
      (((Basis.conj LeptonDoubletV.basis)).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoubletV.valueGaugeWeight j) i) •
        ((Basis.conj LeptonDoubletV.basis)).coord j := by
  have hd := dual_gaugeTorusGen_coord LeptonDoubletV.repGaugeGroupI.conj
    ((Basis.conj LeptonDoubletV.basis))
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (LeptonDoubletV.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => LeptonDoubletV.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

end LeptonDoubletV

end StandardModel
