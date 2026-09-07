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
public import Physlib.Particles.StandardModel.GaugeAlgebra.InfinitesimalAction
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# Down-type singlets

## i. Overview

The Standard Model down-type singlet is a right-handed Weyl spinor in the `(3, 1)_{-2}`
representation. Here charges are normalized as `6Y`, so `-2` is the usual hypercharge
`Y = -1/3`.

`DownSinglet` is the target vector space of one down-type quark multiplet. Its Weyl factor
carries the Lorentz index and its three-dimensional factor carries the colour index. The absence
of a weak factor makes it an `SU(2)` singlet.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed on a
basis, used to identify its kernel, and descended to each supported global form of the Standard
Model gauge group.

## ii. Key results

- `DownSinglet` : the target space of the `(3, 1)_{-2}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_tmul_basis_eq_sum` : the gauge action in a tensor-product basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.
- `gaugeAlgebraAction` : the infinitesimal `(3, 1)_{-2}` action of the gauge algebra.
- `repJetGaugeGroupI` : the jet gauge action on jets of the down singlet.
- `isInfinitesimalActionOf` : the gauge-algebra action is the infinitesimal action
  underlying the jet gauge action.

## iii. Table of contents

- A. The down-singlet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. The action of the gauge algebra
- H. The representation of the jet gauge group
- I. The infinitesimal action underlies the jet gauge action
- J. Component transformation laws

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The down-singlet space

The Weyl factor carries the right-handed Lorentz index, while
`EuclideanSpace ℂ (Fin 3)` carries the colour index.
-/

/-- The target vector space of one Standard Model down-type singlet quark.
It carries the `(3, 1)_{-2}` representation of the gauge group. -/
@[ext]
structure DownSinglet where
  /-- The right-handed Weyl spinor with its colour index. -/
  val : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)

namespace DownSinglet

/-!

## B. Linear structure

`DownSinglet` wraps its tensor-product carrier as a distinct type. The equivalences below identify
the two types and transport the additive and complex module structures to `DownSinglet`.
-/

/-- Identifies a down-type singlet with its underlying tensor-product value. -/
def valEquiv : DownSinglet ≃ Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup DownSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ DownSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : DownSinglet ≃ₗ[ℂ]
    Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : DownSinglet) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : DownSinglet) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (d : DownSinglet) : (r • d).val = r • d.val := rfl

/-!

## The basis of the down-singlet space

-/

/-- A basis on the down singlets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3) ℂ DownSinglet :=
  (Fermion.RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).map valLinEquiv.symm

instance : Module.Finite ℂ DownSinglet := Module.Finite.of_basis basis

instance : Module.Free ℂ DownSinglet := Module.Free.of_basis basis

/-!

## C. Lorentz action

The Lorentz group acts on the right-handed Weyl factor and leaves the colour index fixed.
-/

open Matrix MatrixGroups

open Representation in
/-- The right-handed Lorentz representation on down-type singlet quarks. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) DownSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ
      TensorProduct.map (Fermion.RightHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ) ∘ₗ
      valLinEquiv
  map_one' := by
    ext d
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 d
    simp [TensorProduct.map_map, Module.End.mul_eq_comp]

/-!

## D. Gauge action

The `SU(3)` component acts on the colour index, while the `SU(2)` component acts trivially. The
`U(1)` action is `star z ^ 2`; since `z` is unitary, `star z = z⁻¹`, so this represents charge
`-2`.

The tensor and basis formulas below expose the coefficients used to compare actions and compute the
kernel.
-/

/-- The `(3, 1)_{-2}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI DownSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (LinearMap.id (M := Fermion.RightHandedWeyl))
        g.toSU3.1.toEuclideanLin ∘ₗ
      LinearMap.lsmul ℂ _ (star g.toU1.1 ^ 2 : ℂ) ∘ₗ
      valLinEquiv
  map_one' := by
    ext d
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext d
    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge action on a pure spinor–colour tensor. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v⟩ =
      ⟨(star g.toU1.1 ^ 2) • ψ ⊗ₜ g.toSU3.1.toEuclideanLin v⟩ := rfl

open Fermion in
/-- Expands the gauge action in the spinor–colour basis. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k : Fin 2) (i : Fin 3) :
    repGaugeGroupI g
      ⟨RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i⟩ =
      ∑ i' : Fin 3, (star g.toU1.1 ^ 2 * g.toSU3.1 i' i) •
        (⟨RightHandedWeyl.basis k ⊗ₜ[ℂ]
          EuclideanSpace.basisFun (Fin 3) ℂ i'⟩ : DownSinglet) := by
  apply valLinEquiv.injective
  apply (((RightHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis)).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, valLinEquiv_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, ofLp_toLpLin,
    PiLp.ofLp_single, toLin'_apply, mulVec_single, MulOpposite.op_one, col_apply, one_smul,
    Module.Basis.repr_self, smul_eq_mul, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    PiLp.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  ring

open Fermion in
/-- Two gauge elements induce the same action exactly when their hypercharge–colour coefficients
agree. -/
lemma repGaugeGroupI_eq_iff_mul_eq {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔ ∀ i i',
      star g₁.toU1.1 ^ 2 * g₁.toSU3.1 i' i =
        star g₂.toU1.1 ^ 2 * g₂.toSU3.1 i' i := by
  let b := RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis
  constructor
  · intro h i i'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨RightHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f (0, i')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff
      (repGaugeGroupI g₁) (repGaugeGroupI g₂)).mp
    apply b.ext
    rintro ⟨k, i⟩
    have h₁ := repGaugeGroupI_tmul_basis_eq_sum g₁ k i
    have h₂ := repGaugeGroupI_tmul_basis_eq_sum g₂ k i
    simp only [EuclideanSpace.basisFun_apply] at h₁ h₂
    simp [valLinEquiv_symm_apply, h₁, h₂, b]
    apply Finset.sum_congr rfl
    intro i' _
    have hi' : (starRingEnd ℂ) g₁.toU1.1 ^ 2 * g₁.toSU3.1 i' i =
        (starRingEnd ℂ) g₂.toU1.1 ^ 2 * g₂.toSU3.1 i' i := h i i'
    rw [hi']

/-!

## E. Kernel of the gauge action

An element acts trivially when its colour action is scalar and that scalar cancels its `U(1)`
phase. Its weak component is unrestricted because the down-type singlet is an `SU(2)` singlet.
-/

/-- Characterizes the full-group elements acting trivially on the down-type singlet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a : ℂ,
      g.toSU3.1 = a • 1 ∧ a * star g.toU1.1 ^ 2 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor
  · intro h
    have hc : star g.toU1.1 ^ 2 ≠ 0 := by
      apply pow_ne_zero
      rw [star_ne_zero]
      intro hzero
      have hu := Unitary.star_mul_self_of_mem g.toU1.2
      simp [hzero] at hu
    use g.toSU3.1 0 0
    simp only [map_one, OneMemClass.coe_one, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, ne_eq,
      one_ne_zero, not_false_eq_true, one_apply_ne, mul_eq_zero, zero_ne_one,
      Fin.succ_one_eq_two, Fin.reduceEq, star_one, one_pow, one_mul] at h
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind
    · grind
  · rintro ⟨a, h₁, h₂⟩ i i'
    simp only [Matrix.smul_apply, smul_eq_mul, h₁, map_one, OneMemClass.coe_one,
      star_one, one_pow, one_mul]
    linear_combination h₂ * (1 : Matrix _ _ ℂ) i' i

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel. For
the central `ℤ₆`, the colour phase is `x²` while the charge `-2` phase is `(star x)² = x⁻²`, so
their product is one.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(3, 1)_{-2}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  use x ^ 2
  simp only [gaugeGroupℤ₆OfRoot_toSU3, gaugeGroupℤ₆SU3OfRoot_eq_mul_id,
    gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe, true_and, RCLike.star_def,
    Complex.conj_rootsOfUnity hx, Units.val_inv_eq_inv_val, inv_pow]
  field_simp

/-- Every supported quotient subgroup acts trivially on the down-type singlet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(3, 1)_{-2}` representation for every supported global form of the
Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) DownSinglet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## The representation of the jet gauge group
-/

/-- Absorbs the jet ring into the colour index: a jet of a down-type singlet is the
same thing as a right-handed Weyl spinor tensored with a `JetRing`-valued colour
vector,

  `JetRing ⊗[ℂ] DownSinglet ≃ RightHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3)`.

-/
noncomputable def jetValLinEquiv :
    JetRing ⊗[ℂ] DownSinglet ≃ₗ[ℂ]
      Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) valLinEquiv).trans <|
    (TensorProduct.leftComm ℂ JetRing Fermion.RightHandedWeyl
        (EuclideanSpace ℂ (Fin 3))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.RightHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
            (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))).trans <|
          ((TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 3)).trans
            (WithLp.linearEquiv 2 JetRing (Fin 3 → JetRing)).symm).restrictScalars ℂ

/-- The `(3, 1)_{-2}` action of the jet gauge group on the jet space of the down-type
singlet. Through `jetValLinEquiv` the colour matrix of the gauge jet, carrying the
`-2` hypercharge phase `(star u) ^ 2`, acts `JetRing`-linearly on the colour factor by
matrix-vector multiplication, while the Weyl factor is untouched.

Both monoid laws come from bundled algebra maps — `Matrix.toLpLinAlgEquiv` and
`Module.End.lTensorAlgHom` are morphisms of algebras — so only the multiplicativity of
the colour-times-hypercharge matrix itself is checked. Note `Matrix.toLpLinAlgEquiv 2`
is the same map as the `Matrix.toEuclideanLin` used by `repGaugeGroupI`, which is an
abbreviation for `Matrix.toLpLin 2 2`, taken at the `CommRing` generality that
`JetRing` needs. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] DownSinglet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3)) Fermion.RightHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2
            (((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
              ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
                Matrix (Fin 3) (Fin 3) JetRing))).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres : (1 : Module.End JetRing (EuclideanSpace JetRing (Fin 3))).restrictScalars ℂ
        = 1 := rfl
    rw [show (((star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 2) •
          (((1 : JetGaugeGroupI).1 : specialUnitaryGroup (Fin 3) JetRing) :
            Matrix (Fin 3) (Fin 3) JetRing)) = 1 from by simp,
      map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End JetRing (EuclideanSpace JetRing (Fin 3)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    have hM : (((star (((U₁ * U₂).2.2 : unitary JetRing) : JetRing)) ^ 2) •
          (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
            Matrix (Fin 3) (Fin 3) JetRing)) =
        (((star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 2) •
            ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing)) *
          (((star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 2) •
            ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing)) := by
      rw [show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
            ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
            from rfl,
        show (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing) =
            ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) *
              ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)
            from rfl,
        star_mul', mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hM, map_mul, hres, map_mul]
    ext d x
    simp

/-- The identification of the jets of the down-type singlet intertwines multiplication by
a scalar jet with the `JetRing`-scalar action on the colour coordinates. -/
lemma jetValLinEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
          Fermion.RightHandedWeyl
          ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (χ * f)) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        show Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
            Fermion.RightHandedWeyl
            ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ).restrictScalars ℂ)
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f))
          = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun i => c.ofLp i • f) from rfl]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show c.ofLp i • (χ * f) = χ * (c.ofLp i • f)
      rw [Algebra.mul_smul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the down-type singlet is fibrewise**: it
commutes with multiplication by scalar jets, acting on the values of the field over the
identity on spacetime. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] DownSinglet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End JetRing (EuclideanSpace JetRing (Fin 3)) :=
    LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ with hS
  set M : Module.End JetRing (EuclideanSpace JetRing (Fin 3)) :=
    (Matrix.toLpLinAlgEquiv 2
      (((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
        ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing)) :
      Module.End JetRing (EuclideanSpace JetRing (Fin 3))) with hM
  have hMS : M * S = S * M := LinearMap.ext fun e => by
    simp only [Module.End.mul_apply, hS, LinearMap.lsmul_apply, map_smul]
  apply jetValLinEquiv.injective
  rw [show repJetGaugeGroupI U (χ • z)
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.RightHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv (χ • z))) from rfl,
    LinearEquiv.apply_symm_apply, jetValLinEquiv_smul,
    show repJetGaugeGroupI U z
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.RightHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv z)) from rfl,
    jetValLinEquiv_smul, LinearEquiv.apply_symm_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show M.restrictScalars ℂ * S.restrictScalars ℂ = (M * S).restrictScalars ℂ from rfl,
    show S.restrictScalars ℂ * M.restrictScalars ℂ = (S * M).restrictScalars ℂ from rfl,
    hMS]

/-- On jets of constant gauge transformations the jet action reduces to the global
gauge action on the fibre: the `(3, 1)_{-2}` action on the down-singlet factor, and the
trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : DownSinglet) = 0 from rfl]
  | tmul psi c =>
      apply jetValLinEquiv.injective
      simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI]
      have hu : star (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((starRingEnd ℂ) (g.toU1.1 : ℂ)) := by
        rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl, JetRing.star_C]
        rfl
      have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).1 :
            specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) i j
          = MvPowerSeries.C (g.toSU3.1 i j) := fun _ _ => rfl
      have halg : ∀ A : Matrix (Fin 3) (Fin 3) JetRing,
          (Matrix.toLpLinAlgEquiv 2 A :
              Module.End JetRing (EuclideanSpace JetRing (Fin 3)))
            = Matrix.toLpLin 2 2 A := fun _ => rfl
      have hvec : ∀ i : Fin 3,
          (∑ x, MvPowerSeries.C ((g.toSU3.1) i x) * (MvPowerSeries.C (c.ofLp x) * d))
            = MvPowerSeries.C (∑ x, (g.toSU3.1) i x * c.ofLp x) * d := by
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
      simp only [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

/-!

## J. Component transformation laws

The basis of `DownSinglet` splits as a right-handed Weyl index and a colour index. The
Lorentz group moves only the first, the gauge group only the second (up to the hypercharge
scalar), so both actions are recorded as a single sum over the index they move. Dualising
inverts and transposes the coefficient matrix, and conjugating stars it; the four
combinations below are what a component of a down-singlet symbol needs.

-/

/-- The down-singlet basis vector as an explicit spinor–colour tensor. -/
lemma basis_eq_mk (k : Fin 2) (c : Fin 3) : basis (k, c) =
    ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    OrthonormalBasis.coe_toBasis]
  rfl

/-- The Lorentz action on the down-singlet basis: the colour index is inert and the
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

/-- The down-singlet coordinate functionals transform contragrediently, by the entrywise
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

/-- The Lorentz action on the conjugate down-singlet basis: the coefficients are the
  conjugates of those of the down-singlet action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj Λ (basis.conj j) = ∑ β, Λ.1 β j.1 • basis.conj (β, j.2) := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Module.Basis.conj_apply]

/-- The conjugate down-singlet coordinate functionals transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj.dual Λ (basis.conj.dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • basis.conj.dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj basis.conj Λ j
    (Matrix.of fun p q => if p.2 = q.2 then ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the down-singlet basis: the spinor index is inert and the colour
  index transforms by the `SU(3)` matrix, scaled by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI g (basis j) =
      ∑ c, (star g.toU1.1 ^ 2 * g.toSU3.1 c j.2) • basis (j.1, c) := by
  obtain ⟨k, c⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k c

/-- The down-singlet coordinate functionals carry the contragredient gauge action: the
  hypercharge and `SU(3)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ c, (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) • basis.dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 p.2 q.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate down-singlet basis: the coefficients of the
  down-singlet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj g (basis.conj j) =
      ∑ c, star (star g.toU1.1 ^ 2 * g.toSU3.1 c j.2) • basis.conj (j.1, c) := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Module.Basis.conj_apply]

/-- The conjugate down-singlet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj.dual g (basis.conj.dualBasis j) =
      ∑ c, star (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) •
        basis.conj.dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj basis.conj g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 p.2 q.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

end DownSinglet

/-!

## The gauge weight of the DownSinglet components

The gauge torus acts diagonally on the basis of `DownSinglet`; the weights are recorded by
`DownSinglet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the down-singlet basis: the colour weights and hypercharge
  `-2`. -/
def DownSinglet.valueGaugeWeight (j : Fin 2 × Fin 3) : GaugeWeight :=
  ((colourWeight j.2).1, (colourWeight j.2).2, 0, -2)

/-- The gauge torus acts diagonally on the basis of `DownSinglet`, with the weights
  `DownSinglet.valueGaugeWeight`. -/
lemma DownSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI (gaugeTorusGen i) (DownSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) •
        DownSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  have hb : DownSinglet.basis (k, c)
      = ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
    simp only [DownSinglet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, DownSinglet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo,
      Fin.sum_univ_three,
      Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, starRingEnd_expI_pow] <;>
  (try congr 1)

/-- The dual action of the gauge torus on the coordinate functionals of
  `DownSinglet`: the weights are negated. -/
lemma DownSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (DownSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i))) •
        DownSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => DownSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `DownSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma DownSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((DownSinglet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) •
        (DownSinglet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord DownSinglet.repGaugeGroupI.conj (DownSinglet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (DownSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => DownSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## The boost weight of the DownSinglet components

-/

open Lorentz in
/-- The down-singlet basis diagonalises the `z`-boost: the colour index is inert, so the
  weight is the Weyl weight of the spinor index. -/
lemma downSinglet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0)
    (j : Fin 2 × Fin 3) :
    DownSinglet.repLorentzGroup (SL2C.boostAxis 2 t ht) (DownSinglet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j.1) • DownSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  simp [DownSinglet.basis, DownSinglet.repLorentzGroup, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, rightHandedWeyl_rep_boostAxis_two_basis]
  rw [← TensorProduct.smul_tmul', map_smul]

end StandardModel
