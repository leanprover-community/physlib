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
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# Lepton doublets

## i. Overview

The Standard Model lepton doublet is a left-handed Weyl spinor in the `(1, 2)_{-3}`
representation. Here charges are normalized as `6Y`, so `-3` is the usual hypercharge
`Y = -1/2`.

`LeptonDoublet` is the target vector space of one lepton multiplet. Its Weyl factor
carries the Lorentz index and its two-dimensional factor carries the weak index.
The absence of a colour factor makes it an `SU(3)` singlet.

The Lorentz and gauge actions are first defined separately. The gauge action is then
computed on a basis, used to identify its kernel, and descended to each supported global
form of the Standard Model gauge group.

## ii. Key results

- `LeptonDoublet` : the target space of the `(1, 2)_{-3}` multiplet.
- `repLorentzGroup` : the left-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_tmul_basis_eq_sum` : the gauge action in a tensor-product basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The lepton-doublet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. Jet gauge action
- H. Component transformation laws

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The lepton-doublet space

The Weyl factor carries the left-handed Lorentz index, while
`EuclideanSpace ℂ (Fin 2)` carries the weak index.
-/

/-- The target vector space of one Standard Model lepton doublet.
  It carries the `(1, 2)_{-3}` representation of the gauge group. -/
@[ext]
structure LeptonDoublet where
  /-- The left-handed Weyl spinor with its weak-doublet index. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace LeptonDoublet

/-!

## B. Linear structure

The wrapper distinguishes lepton doublets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the tensor product and expose
that model when defining representations.
-/

/-- Identifies a lepton doublet with its underlying tensor-product value. -/
def valEquiv : LeptonDoublet ≃ Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonDoublet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : LeptonDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (l : LeptonDoublet) : valLinEquiv l = l.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (l₁ l₂ : LeptonDoublet) : (l₁ + l₂).val = l₁.val + l₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (l : LeptonDoublet) : (r • l).val = r • l.val := rfl

/-!

## The basis of the lepton-doublet space

-/

/-- A basis on the lepton doublets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 2) ℂ LeptonDoublet :=
  (Fermion.LeftHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).map valLinEquiv.symm

instance : Module.Finite ℂ LeptonDoublet := Module.Finite.of_basis basis

instance : Module.Free ℂ LeptonDoublet := Module.Free.of_basis basis

/-!

## C. Lorentz action

The Lorentz group acts on the left-handed Weyl factor and leaves the weak index fixed.
-/

open Matrix MatrixGroups

open Representation in
/-- The left-handed Lorentz representation on lepton doublets. -/
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

/-!

## D. Gauge action

The colour factor acts trivially, while `SU(2)` acts on the weak index. The `U(1)` action
is `star z ^ 3`; since `z` is unitary, `star z = z⁻¹`, so this represents charge `-3`.

The tensor and basis formulas below expose the coefficients used to compare actions and
compute the kernel.
-/

/-- The `(1, 2)_{-3}` action of the unquotiented Standard Model gauge group. -/
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

/-- The gauge action on a pure spinor–weak tensor. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (v : Fermion.LeftHandedWeyl)
    (w : EuclideanSpace ℂ (Fin 2)) :
    repGaugeGroupI g ⟨v ⊗ₜ w⟩ =
      ⟨(star g.toU1.1 ^ 3) • v ⊗ₜ (g.toSU2.1.toEuclideanLin w)⟩ := rfl

open Fermion in
/-- Expands the gauge action in the spinor–weak basis. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k j : Fin 2) :
    repGaugeGroupI g ⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ]
      EuclideanSpace.basisFun (Fin 2) ℂ j⟩ =
      ∑ j' : Fin 2, (star g.toU1.1 ^ 3 * g.toSU2.1 j' j)
      • (⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ]
          EuclideanSpace.basisFun (Fin 2) ℂ j'⟩ : LeptonDoublet) := by
  apply valLinEquiv.injective
  apply (((LeftHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis)).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, valLinEquiv_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, ofLp_toLpLin, PiLp.ofLp_single, toLin'_apply, mulVec_single,
    MulOpposite.op_one, col_apply, one_smul, Module.Basis.repr_self, smul_eq_mul, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, PiLp.single_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

open Fermion in
/-- Two gauge elements induce the same action exactly when their weak-basis coefficients agree. -/
lemma repGaugeGroupI_eq_iff_mul_eq {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔ ∀ j j',
    star g₁.toU1.1 ^ 3 * g₁.toSU2.1 j' j =
      star g₂.toU1.1 ^ 3 * g₂.toSU2.1 j' j := by
  let b := (LeftHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  constructor
  · intro h j j'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f (0, j')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff
      (repGaugeGroupI g₁) (repGaugeGroupI g₂)).mp
    apply b.ext
    rintro ⟨k, j⟩
    have h₁ := repGaugeGroupI_tmul_basis_eq_sum g₁ k j
    have h₂ := repGaugeGroupI_tmul_basis_eq_sum g₂ k j
    simp only [EuclideanSpace.basisFun_apply] at h₁ h₂
    have hj₀ : (starRingEnd ℂ) g₁.toU1.1 ^ 3 * g₁.toSU2.1 0 j =
        (starRingEnd ℂ) g₂.toU1.1 ^ 3 * g₂.toSU2.1 0 j := h j 0
    have hj₁ : (starRingEnd ℂ) g₁.toU1.1 ^ 3 * g₁.toSU2.1 1 j =
        (starRingEnd ℂ) g₂.toU1.1 ^ 3 * g₂.toSU2.1 1 j := h j 1
    simp [valLinEquiv_symm_apply, h₁, h₂, b, hj₀, hj₁]

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
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
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

The `(1, 2)_{-3}` representation extends verbatim to jets, in the same way as for the
quark singlets: the jet ring is absorbed into the weak index, and the `SU(2)`
power-series matrix of a jet of gauge transformations, scaled by the hypercharge power
series `star u ^ 3`, acts `JetRing`-linearly on the weak factor. On jets of constant
gauge transformations the action reduces to the global gauge action.

-/

@[simp]
lemma mk_zero : (⟨0⟩ : LeptonDoublet) = 0 := rfl

/-- Absorbs the jet ring into the weak index: a jet of a lepton doublet is the same
thing as a left-handed Weyl spinor tensored with a `JetRing`-valued weak vector,

  `JetRing ⊗[ℂ] LeptonDoublet ≃ LeftHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 2)`.

-/
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

/-- The `(1, 2)_{-3}` action of the jet gauge group on the jet space of the lepton
doublet. Through `jetValLinEquiv` the weak matrix of the gauge jet, carrying the `-3`
hypercharge phase `(star u) ^ 3`, acts `JetRing`-linearly on the weak factor by
matrix-vector multiplication, while the Weyl factor is untouched. -/
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
  map_one' := by
    have hres : (1 : Module.End JetRing (EuclideanSpace JetRing (Fin 2))).restrictScalars ℂ
        = 1 := rfl
    rw [show (((star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 3) •
          (((1 : JetGaugeGroupI).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
            Matrix (Fin 2) (Fin 2) JetRing)) = 1 from by simp,
      map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End JetRing (EuclideanSpace JetRing (Fin 2)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    have hM : (((star (((U₁ * U₂).2.2 : unitary JetRing) : JetRing)) ^ 3) •
          (((U₁ * U₂).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
            Matrix (Fin 2) (Fin 2) JetRing)) =
        (((star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 3) •
            ((U₁.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
              Matrix (Fin 2) (Fin 2) JetRing)) *
          (((star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 3) •
            ((U₂.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
              Matrix (Fin 2) (Fin 2) JetRing)) := by
      rw [show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
            ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
            from rfl,
        show (((U₁ * U₂).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
              Matrix (Fin 2) (Fin 2) JetRing) =
            ((U₁.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) *
              ((U₂.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)
            from rfl,
        star_mul', mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hM, map_mul, hres, map_mul]
    ext d x
    simp

/-- The identification of the jets of the lepton doublet intertwines multiplication by
a scalar jet with the `JetRing`-scalar action on the weak coordinates. -/
lemma jetValLinEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] LeptonDoublet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 2))
          Fermion.LeftHandedWeyl
          ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 2)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : LeptonDoublet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : LeptonDoublet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (χ * f)) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : LeptonDoublet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        show Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 2))
            Fermion.LeftHandedWeyl
            ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 2)) χ).restrictScalars ℂ)
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f))
          = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun i => c.ofLp i • f) from rfl]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show c.ofLp i • (χ * f) = χ * (c.ofLp i • f)
      rw [Algebra.mul_smul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : LeptonDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the lepton doublet is fibrewise**: it commutes
with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] LeptonDoublet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End JetRing (EuclideanSpace JetRing (Fin 2)) :=
    LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 2)) χ with hS
  set M : Module.End JetRing (EuclideanSpace JetRing (Fin 2)) :=
    (Matrix.toLpLinAlgEquiv 2
      (((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 3) •
        ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
          Matrix (Fin 2) (Fin 2) JetRing)) :
      Module.End JetRing (EuclideanSpace JetRing (Fin 2))) with hM
  have hMS : M * S = S * M := LinearMap.ext fun e => by
    simp only [Module.End.mul_apply, hS, LinearMap.lsmul_apply, map_smul]
  apply jetValLinEquiv.injective
  rw [show repJetGaugeGroupI U (χ • z)
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.LeftHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv (χ • z))) from rfl,
    LinearEquiv.apply_symm_apply, jetValLinEquiv_smul,
    show repJetGaugeGroupI U z
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.LeftHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv z)) from rfl,
    jetValLinEquiv_smul, LinearEquiv.apply_symm_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show M.restrictScalars ℂ * S.restrictScalars ℂ = (M * S).restrictScalars ℂ from rfl,
    show S.restrictScalars ℂ * M.restrictScalars ℂ = (S * M).restrictScalars ℂ from rfl,
    hMS]

/-- On jets of constant gauge transformations the jet action reduces to the global
gauge action on the fibre: the `(1, 2)_{-3}` action on the lepton-doublet factor, and
the trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : LeptonDoublet) = 0 from rfl]
  | tmul psi c =>
      apply jetValLinEquiv.injective
      simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI]
      have hu : star (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((starRingEnd ℂ) (g.toU1.1 : ℂ)) := by
        rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl, JetRing.star_C]
        rfl
      have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).2.1 :
            specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) i j
          = MvPowerSeries.C (g.toSU2.1 i j) := fun _ _ => rfl
      have halg : ∀ A : Matrix (Fin 2) (Fin 2) JetRing,
          (Matrix.toLpLinAlgEquiv 2 A :
              Module.End JetRing (EuclideanSpace JetRing (Fin 2)))
            = Matrix.toLpLin 2 2 A := fun _ => rfl
      have hvec : ∀ i : Fin 2,
          (∑ x, MvPowerSeries.C ((g.toSU2.1) i x) * (MvPowerSeries.C (c.ofLp x) * d))
            = MvPowerSeries.C (∑ x, (g.toSU2.1) i x * c.ofLp x) * d := by
        intro i
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ← map_mul]
      rw [TensorProduct.liftAux_tmul, ← TensorProduct.tmul_smul]
      simp only [LinearMap.compl₂_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
        LinearMap.restrictScalars_apply, halg, Matrix.toLpLin_toLp]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      simp only [WithLp.ofLp_smul, Pi.smul_apply, Matrix.toLin'_apply,
        Matrix.mulVec_apply_eq_sum, hM, Algebra.smul_def, MvPowerSeries.algebraMap_apply,
        hu, map_pow, Algebra.algebraMap_self_apply]
      rw [hvec i]
  | add a b ha hb =>
      simp only [show ({ val := a + b } : LeptonDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

/-!

## H. Component transformation laws

The basis of `LeptonDoublet` splits as a left-handed Weyl index and a weak-isospin index.
The Lorentz group moves only the first, the gauge group only the second (up to the
hypercharge scalar), so both actions are recorded as a single sum over the index they move.
Dualising inverts and transposes the coefficient matrix, and conjugating stars it; the four
combinations below are what a component of a lepton-doublet symbol needs.

-/

/-- The lepton-doublet basis vector as an explicit spinor–weak tensor. -/
lemma basis_eq_mk (k j : Fin 2) : basis (k, j) =
    ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩ := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    OrthonormalBasis.coe_toBasis]
  rfl

/-- The Lorentz action on the lepton-doublet basis: the weak index is inert and the
  spinor index transforms by the matrix itself. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 2) :
    repLorentzGroup Λ (basis j) = ∑ β, Λ.1 β j.1 • basis (β, j.2) := by
  obtain ⟨k, w⟩ := j
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    repLorentzGroup, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.map_tmul, Fermion.LeftHandedWeyl.rep_apply_basis,
    Representation.trivial_apply, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]

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

/-- The gauge action on the lepton-doublet basis: the spinor index is inert and the weak
  index transforms by the `SU(2)` matrix, scaled by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 2) :
    repGaugeGroupI g (basis j) =
      ∑ w, (star g.toU1.1 ^ 3 * g.toSU2.1 w j.2) • basis (j.1, w) := by
  obtain ⟨k, w⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k w

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
  have hb : LeptonDoublet.basis (k, s)
      = ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ s⟩ := by
    simp only [LeptonDoublet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, LeptonDoublet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      LeptonDoublet.valueGaugeWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, starRingEnd_expI_pow] <;>
  (try congr 1)

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
  simp [LeptonDoublet.basis, LeptonDoublet.repLorentzGroup, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, leftHandedWeyl_rep_boostAxis_two_basis]
  rw [← TensorProduct.smul_tmul', map_smul]

end StandardModel
