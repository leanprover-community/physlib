/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SO
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Sp
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.U1
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.OfMatrixRep
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Algebra.Group.Matrix
/-!

# Conditions for the reduction of invariants

Compactness of the gauge group, continuity of the Lorentz representations and commutation of the
gauge and Lorentz actions.

## i. Overview

Invariants of a realization of the covariant field algebra descend to invariants of the
covariant field algebra itself when both symmetry groups can be averaged over. This needs three
conditions on a gauge theory.

The gauge group must be compact, so that it has a normalized Haar measure. This is
`CompactSpace G.group`, for the topology of `G.group` as a subspace of `GL(κ, ℂ)`. A global
gauge group made of unitary matrices is compact, being closed in the compact unitary group, and
this covers `SU(n)`, `U(1)`, `SO(n)` and `Sp(n)`. The product of two compact global gauge groups
is compact, being the continuous image of the product of the two groups. So the gauge group of
the Standard Model is compact by these instances.

The Lorentz representation of every species must be continuous, in the sense that its matrix
coefficients `Λ ↦ φ (ρ(Λ) v)` are continuous on `SL(2,ℂ)`. The gauge representation of a matter
field is continuous by definition, and its matrix coefficients are continuous too.

The gauge and Lorentz representations of every species must commute,
`GaugeFieldData.GaugeLorentzCommute`. This implies the infinitesimal condition
`GaugeFieldData.GaugeLorentzCompatible` used by the covariant derivative, but not conversely,
since the infinitesimal action does not determine the action of a disconnected gauge group. For
a matter field built as a tensor product of a gauge multiplet and a Lorentz multiplet the two
actions commute.

## ii. Key results

- `GlobalGaugeGroup.compactSpace_ofSubmonoid` : a global gauge group of unitary matrices is
  compact.
- `GlobalGaugeGroup.compactSpace_prod` : the product of compact global gauge groups is compact.
- `GlobalGaugeGroup.MatterField.LorentzContinuous` : continuity of the Lorentz representation of
  a matter field.
- `GlobalGaugeGroup.MatterField.continuous_rep_apply` : continuity of the matrix coefficients of
  the gauge representation of a matter field.
- `GlobalGaugeGroup.MatterField.ofMatrixRep_lorentzContinuous`,
  `GlobalGaugeGroup.MatterField.ofMatrixRep_gaugeLorentzCommute` : both conditions hold for the
  matter field of a matrix representation, given continuity of the Lorentz representation on the
  Lorentz factor.
- `Fermion.LeftHandedWeyl.continuous_rep_apply`, `Fermion.RightHandedWeyl.continuous_rep_apply` :
  continuity of the Weyl representations.
- `GaugeFieldData.LorentzContinuous` : the continuity condition on every species of a field
  datum.

## iii. Table of contents

- A. Compact global gauge groups
  - A.1. Global gauge groups of unitary matrices
  - A.2. The groups SU(n), U(1), SO(n) and Sp(n)
  - A.3. Products
- B. Conditions on matter fields
  - B.1. Continuity of the gauge representation
  - B.2. Continuity of the Lorentz representation
  - B.3. Matter fields of matrix representations
  - B.4. Continuity of the Weyl representations
- C. Conditions on a field datum

## iv. References

- The compact classical groups, see for example
  T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-!

## A. Compact global gauge groups

### A.1. Global gauge groups of unitary matrices

-/

/-- The unitary matrices form a compact set, being closed with entries of modulus at most one. -/
lemma isCompact_unitaryGroup : IsCompact (unitaryGroup κ ℂ : Set (Matrix κ κ ℂ)) := by
  have hK : IsCompact ((Set.univ.pi fun _ : κ => Set.univ.pi fun _ : κ =>
      Metric.closedBall (0 : ℂ) 1) : Set (Matrix κ κ ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset (isClosed_unitary (R := Matrix κ κ ℂ)) fun U hU i _ j _ => ?_
  simpa using entry_norm_bound_of_unitary hU i j

/-- The global gauge group of a closed submonoid of unitary matrices is compact. -/
lemma compactSpace_ofSubmonoid {S : Submonoid (Matrix κ κ ℂ)}
    (hS : IsClosed (S : Set (Matrix κ κ ℂ))) (hU : S ≤ unitaryGroup κ ℂ) :
    CompactSpace (ofSubmonoid S hS).group :=
  isCompact_iff_compactSpace.1 (Submonoid.units_isCompact
    (isCompact_unitaryGroup.of_isClosed_subset hS hU))

/-!

### A.2. The groups SU(n), U(1), SO(n) and Sp(n)

-/

instance (n : ℕ) : CompactSpace (SU n).group := compactSpace_ofSubmonoid _ inf_le_left

instance : CompactSpace U1.group := compactSpace_ofSubmonoid _ le_rfl

instance (n : ℕ) : CompactSpace (SO n).group :=
  compactSpace_ofSubmonoid _ fun _ hA => hA.1.1

instance (n : ℕ) : CompactSpace (Sp n).group := compactSpace_ofSubmonoid _ inf_le_left

/-!

### A.3. Products

-/

section Prod

variable {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
  (G₁ : GlobalGaugeGroup κ₁) (G₂ : GlobalGaugeGroup κ₂)

/-- The pair `(g₁, g₂)` depends continuously on its factors as the block-diagonal matrix
`diag(g₁, g₂)` of the product. -/
lemma continuous_prodGroupHom : Continuous (prodGroupHom G₁ G₂) := by
  have hv {ι : Type} [Fintype ι] [DecidableEq ι] (G : GlobalGaugeGroup ι) :
      Continuous fun g : G.group => ((g : GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi {ι : Type} [Fintype ι] [DecidableEq ι] (G : GlobalGaugeGroup ι) :
      Continuous fun g : G.group => (((g⁻¹ : G.group) : GeneralLinearGroup ι ℂ) : Matrix ι ι ℂ) :=
    (hv G).comp continuous_inv
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact ((hv G₁).comp continuous_fst).matrix_fromBlocks (continuous_const (y := 0))
      (continuous_const (y := 0))
      ((hv G₂).comp continuous_snd)
  · refine (((hi G₁).comp continuous_fst).matrix_fromBlocks (continuous_const (y := 0))
      (continuous_const (y := 0))
      ((hi G₂).comp continuous_snd)).congr fun a => ?_
    have h := prodGroupHom_val G₁ G₂ a⁻¹
    rw [map_inv] at h
    exact h.symm

/-- The product of two compact global gauge groups is compact. -/
instance compactSpace_prod [CompactSpace G₁.group] [CompactSpace G₂.group] :
    CompactSpace (G₁.prod G₂).group :=
  Function.Surjective.compactSpace (continuous_prodGroupHom G₁ G₂) (prodGroupHom_surjective G₁ G₂)

end Prod

/-!

## B. Conditions on matter fields

### B.1. Continuity of the gauge representation

-/

namespace MatterField

variable {G : GlobalGaugeGroup κ} (M : G.MatterField)

/-- The matrix coefficients `g ↦ φ (ρ(g) v)` of the gauge representation of a matter field are
continuous. -/
lemma continuous_rep_apply (v : M.V) (φ : Module.Dual ℂ M.V) :
    Continuous fun g : G.group => φ ((M.rep g : M.V →L[ℂ] M.V) v) :=
  φ.continuous_of_finiteDimensional.comp
    ((Units.continuous_val.comp M.rep.continuous).clm_apply continuous_const)

/-!

### B.2. Continuity of the Lorentz representation

-/

/-- The Lorentz representation of a matter field is continuous, meaning that its matrix coefficients
`Λ ↦ φ (ρ(Λ) v)` are continuous on `SL(2,ℂ)`. As the value space is finite-dimensional, this is
continuity of `Λ ↦ ρ(Λ)` for the unique vector space topology on its linear maps. -/
def LorentzContinuous : Prop :=
  ∀ (v : M.V) (φ : Module.Dual ℂ M.V), Continuous fun Λ : SL(2,ℂ) => φ (M.repLorentz Λ v)

/-!

### B.3. Matter fields of matrix representations

-/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Type} [AddCommGroup S] [Module ℂ S]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (e : V ≃ₗ[ℂ] S ⊗[ℂ] (ι → ℂ)) (ρ : G.group →ₜ* (Matrix ι ι ℂ)ˣ)
  (repL : Representation ℂ SL(2,ℂ) S) (w : ℕ) (σ : FieldStatistic)

/-- The gauge and Lorentz representations of the matter field of a matrix representation
commute, since they act on different tensor factors. -/
lemma ofMatrixRep_gaugeLorentzCommute : (ofMatrixRep e ρ repL w σ).GaugeLorentzCommute :=
  fun _ Λ v => MatrixRep.valEnd_comm_repLorentz e repL _ Λ v

/-- The Lorentz representation of the matter field of a matrix representation is continuous
when the representation on the Lorentz factor has continuous matrix coefficients. -/
lemma ofMatrixRep_lorentzContinuous
    (h : ∀ (s : S) (ψ : Module.Dual ℂ S), Continuous fun Λ : SL(2,ℂ) => ψ (repL Λ s)) :
    (ofMatrixRep e ρ repL w σ).LorentzContinuous := by
  intro v φ
  show Continuous fun Λ : SL(2,ℂ) => φ (MatrixRep.repLorentz e repL Λ v)
  obtain ⟨t, rfl⟩ : ∃ t, v = e.symm t := ⟨e v, (e.symm_apply_apply v).symm⟩
  induction t using TensorProduct.inductionOn with
  | tmul s u =>
    -- the coefficient is a matrix coefficient of the Lorentz factor
    have := h s ((φ ∘ₗ e.symm.toLinearMap) ∘ₗ (TensorProduct.mk ℂ S (ι → ℂ)).flip u)
    simp only [MatrixRep.repLorentz_apply_symm_tmul]
    exact this
  | add a b ha hb =>
    simp only [map_add]
    exact (ha.add hb).congr fun Λ => (map_add φ _ _).symm

end MatterField

end GlobalGaugeGroup

/-!

### B.4. Continuity of the Weyl representations

-/

open GlobalGaugeGroup

/-- The entries of an element of `SL(2,ℂ)` are continuous. -/
lemma continuous_specialLinearGroup_apply (i j : Fin 2) :
    Continuous fun Λ : SL(2,ℂ) => (Λ : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  (continuous_apply j).comp (SpecialLinearGroup.continuous_apply _ continuous_id i)

namespace Fermion

/-- The matrix coefficients `Λ ↦ ψ (ρ(Λ) s)` of the left-handed Weyl representation are
continuous. -/
lemma LeftHandedWeyl.continuous_rep_apply (s : LeftHandedWeyl) (ψ : Module.Dual ℂ LeftHandedWeyl) :
    Continuous fun Λ : SL(2,ℂ) => ψ (LeftHandedWeyl.rep Λ s) := by
  have hψ : ∀ x : LeftHandedWeyl, ψ x = ∑ i, x.1 i * ψ (LeftHandedWeyl.basis i) := fun x => by
    have h := congrArg ψ (LeftHandedWeyl.eq_sum_basis x)
    rw [map_sum] at h
    simpa only [map_smul, smul_eq_mul] using h
  have hf : (fun Λ : SL(2,ℂ) => ψ (LeftHandedWeyl.rep Λ s)) = fun Λ =>
      ∑ i, (LeftHandedWeyl.rep Λ s).1 i * ψ (LeftHandedWeyl.basis i) := funext fun Λ => hψ _
  rw [hf]
  simp only [LeftHandedWeyl.rep_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun i _ => (continuous_finsetSum _ fun j _ =>
    (continuous_specialLinearGroup_apply i j).mul continuous_const).mul continuous_const

/-- The matrix coefficients `Λ ↦ ψ (ρ(Λ) s)` of the right-handed Weyl representation are
continuous. -/
lemma RightHandedWeyl.continuous_rep_apply (s : RightHandedWeyl)
    (ψ : Module.Dual ℂ RightHandedWeyl) :
    Continuous fun Λ : SL(2,ℂ) => ψ (RightHandedWeyl.rep Λ s) := by
  have hψ : ∀ x : RightHandedWeyl, ψ x = ∑ i, x.1 i * ψ (RightHandedWeyl.basis i) := fun x => by
    have h := congrArg ψ (RightHandedWeyl.eq_sum_basis x)
    rw [map_sum] at h
    simpa only [map_smul, smul_eq_mul] using h
  have hf : (fun Λ : SL(2,ℂ) => ψ (RightHandedWeyl.rep Λ s)) = fun Λ =>
      ∑ i, (RightHandedWeyl.rep Λ s).1 i * ψ (RightHandedWeyl.basis i) := funext fun Λ => hψ _
  rw [hf]
  simp only [RightHandedWeyl.rep_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun i _ => (continuous_finsetSum _ fun j _ =>
    (continuous_star.comp (continuous_specialLinearGroup_apply i j)).mul
      continuous_const).mul continuous_const

end Fermion

/-!

## C. Conditions on a field datum

-/

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-- The Lorentz representation of every species of the datum is continuous. -/
def LorentzContinuous : Prop :=
  (∀ i, (T.fermion i).LorentzContinuous) ∧ (∀ j, (T.boson j).LorentzContinuous)

end GaugeFieldData
