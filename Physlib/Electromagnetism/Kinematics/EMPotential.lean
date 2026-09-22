/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice
public import Physlib.Mathematics.Calculus.ParametricIntegration
/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a function from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `ElectromagneticPotential` : is the type of electromagnetic potentials.
- `ElectromagneticPotential.deriv` : the derivative tensor `∂_μ A^ν`.
- `ElectromagneticPotential.contDiff_deriv_deriv_component` : the second derivatives
  `∂_μ ∂_ν A^ρ` are `C^n` if the potential is `C^{n+2}`.
- `ElectromagneticPotential.contDiff_deriv` : the derivative tensor is `C^n` if the potential
  is `C^{n+1}`.

## iii. Table of contents

- A. The electromagnetic potential
  - A.1. Basic instances on the type of electromagnetic potentials
  - A.2. Basic constructors of the electromagnetic potential
  - A.3. The group action on the ElectromagneticPotential
  - A.4. Differentiability
    - A.4.1. Differentiability of the derivative of the potential
  - A.5. Differentiability in terms of constructors
  - A.6. The action on the space-time derivatives
  - A.7. Variational adjoint derivative of component
  - A.8. Variational adjoint derivative of derivatives of the potential
- B. The derivative tensor of the electromagnetic potential
  - B.1. Equivariance of the derivative tensor
  - B.2. The elements of the derivative tensor in terms of the basis
  - B.3. Differentiability of the derivative tensor

## iv. References

* https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html. [ref: ucsd_ph130a_node452]
* https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf. [ref: qmul_emt10_notes]
-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential

We define the electromagnetic potential as a function from spacetime to
contravariant Lorentz vectors, and prove some simple results about it.

-/
/-- The electromagnetic potential is a tensor `A^μ`. -/
structure ElectromagneticPotential (d : ℕ := 3) where
  /-- The underlying map from `SpaceTime d` to `Lorentz.Vector d` associated
    with an electromagnetic potential. -/
  val : SpaceTime d → Lorentz.Vector d

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

@[ext]
lemma eq_of_val_eq (A B : ElectromagneticPotential d) (h : A.val = B.val) : A = B :=
  congrArg ElectromagneticPotential.mk h

/-!

## A.1. Basic instances on the type of electromagnetic potentials

-/

instance {d} : CoeFun (ElectromagneticPotential d)
    (fun _ => SpaceTime d → Lorentz.Vector d) where
  coe A := A.val

instance {d} : Zero (ElectromagneticPotential d) where
  zero := ⟨fun _ => 0⟩

@[simp]
lemma zero_val {d} : (0 : ElectromagneticPotential d).val = 0 := rfl

@[simp]
lemma zero_apply {d} (x : SpaceTime d) : (0 : ElectromagneticPotential d) x = 0 := rfl

instance {d} : Add (ElectromagneticPotential d) where
  add A B := ⟨fun x => A x + B x⟩

@[simp]
lemma add_val {d} (A B : ElectromagneticPotential d) :
    (A + B).val = A.val + B.val := rfl

@[simp]
lemma add_apply {d} (A B : ElectromagneticPotential d) (x : SpaceTime d) :
    (A + B) x = A x + B x := by simp

instance {d} : Neg (ElectromagneticPotential d) where
  neg A := ⟨fun x => - A x⟩

@[simp]
lemma neg_val {d} (A : ElectromagneticPotential d) :
    (- A).val = - A.val := rfl

@[simp]
lemma neg_apply {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (- A) x = - A x := rfl

instance {d} : Sub (ElectromagneticPotential d) where
  sub A B := ⟨fun x => A x - B x⟩

@[simp]
lemma sub_val {d} (A B : ElectromagneticPotential d) :
    (A - B).val = A.val - B.val := rfl

@[simp]
lemma sub_apply {d} (A B : ElectromagneticPotential d) (x : SpaceTime d) :
    (A - B) x = A x - B x := rfl

instance {d} : AddCommGroup (ElectromagneticPotential d) where
  add_assoc A B C := by
    ext x μ
    simp [add_assoc]
  zero_add A := by
    ext x μ
    simp
  add_zero A := by
    ext x μ
    simp
  neg_add_cancel A := by
    ext x μ
    simp
  add_comm A B := by
    ext x μ
    simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable instance {d} : SMul ℝ (ElectromagneticPotential d) where
  smul r A := ⟨fun x => r • A x⟩

@[simp]
lemma smul_val {d} (r : ℝ) (A : ElectromagneticPotential d) :
    (r • A).val = r • A.val := rfl

@[simp]
lemma smul_apply {d} (r : ℝ) (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (r • A) x = r • A x := by simp

/-!

## A.2. Basic constructors of the electromagnetic potential

-/

/-- The electromagnetic potential from a scalar potential, where
  the vector potential is set to zero. -/
noncomputable def ofScalarPotential {d} (c : SpeedOfLight)
    (ϕ : Time → Space d → ℝ) : ElectromagneticPotential d where
  val x μ :=
    match μ with
    | Sum.inl 0 => ((timeSlice c).symm ϕ x) / c
    | Sum.inr _ => 0

/-- The creation of an electromagnetic potential from a static scalar potential. -/
noncomputable def ofStaticScalarPotential {d} (c : SpeedOfLight)
    (ϕ : Space d → ℝ) : ElectromagneticPotential d :=
  ofScalarPotential c (fun _ => ϕ)

/-- The electromagnetic potential from a vector potential, where
  the scalar potential is set equal to zero. -/
noncomputable def ofVectorPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    ElectromagneticPotential d where
  val x μ :=
    match μ with
    | Sum.inl 0 => 0
    | Sum.inr i => (timeSlice c).symm A x i

/-- The creation of an electromagnetic potential from a static vector potential. -/
noncomputable def ofStaticVectorPotential {d} (c : SpeedOfLight)
    (A : Space d → EuclideanSpace ℝ (Fin d)) : ElectromagneticPotential d :=
  ofVectorPotential c (fun _ => A)

/-- The creation of an electromagnetic potential from the non-relativistic potentials. -/
noncomputable def ofPotentials {d} (c : SpeedOfLight) (ϕ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    ElectromagneticPotential d where
  val x μ :=
    match μ with
    | Sum.inl 0 => ((timeSlice c).symm ϕ x) / c
    | Sum.inr i => (timeSlice c).symm A x i

lemma ofPotentials_eq_add {d} (c : SpeedOfLight) (ϕ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    ofPotentials c ϕ A = ofScalarPotential c ϕ + ofVectorPotential c A := by
  ext1
  ext1 x
  refine Lorentz.Vector.ext_of_apply (fun i => ?_)
  match i with
  | Sum.inl 0 | Sum.inr _ => simp [ofPotentials, ofScalarPotential, ofVectorPotential]

/-- The creation of of an electromagnetic potential from static potentials. -/
noncomputable def ofStaticPotentials {d} (c : SpeedOfLight) (ϕ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) : ElectromagneticPotential d :=
  ofStaticScalarPotential c ϕ + ofStaticVectorPotential c A

lemma ofStaticPotentials_eq_ofPotentials {d} (c : SpeedOfLight) (ϕ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    ofStaticPotentials c ϕ A = ofPotentials c (fun _ => ϕ) (fun _ => A) := by
  simp [ofStaticPotentials, ofStaticScalarPotential, ofStaticVectorPotential, ofPotentials_eq_add]

open MeasureTheory Matrix Space InnerProductSpace Time in
/-- The electromagnetic potential from an electric and a magnetic field.
  This defines the electromagnetic potential in the Poincare gauge. -/
noncomputable def ofElectromagneticField (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) :
    ElectromagneticPotential 3 :=
  let A := fun t (x : Space) => - ∫ u in 0..(1 : ℝ), (u • basis.repr x) ⨯ₑ₃ B t (u • x) ∂(volume)
  let φ := fun t (x : Space) => - ∫ u in (0 : ℝ)..1, ⟪E t (u • x), basis.repr x⟫_ℝ ∂(volume)
  ofPotentials c φ A

TODO "Write lemmas for the various properties (e.g. the electric field) of
  the electromagnetic potential from the various constructors."

/-!

## A.3. The group action on the ElectromagneticPotential

-/

noncomputable instance {d} : SMul (LorentzGroup d) (ElectromagneticPotential d) where
  smul Λ A := ⟨fun x => Λ • A (Λ⁻¹ • x)⟩

lemma action_val {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d) :
    (Λ • A).val = fun x => Λ • A (Λ⁻¹ • x) := rfl

@[simp]
lemma action_apply {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (x : SpaceTime d) :
    (Λ • A) x = Λ • A (Λ⁻¹ • x) := rfl

noncomputable instance {d} : MulAction (LorentzGroup d) (ElectromagneticPotential d) where
  mul_smul Λ₁ Λ₂ A := by
    ext i
    simp [mul_smul]
  one_smul A := by
    ext i
    simp [one_smul]

noncomputable instance {d} :
    DistribMulAction (LorentzGroup d) (ElectromagneticPotential d) where
  smul_zero Λ := by
    ext x μ
    simp
  smul_add Λ A B := by
    ext x μ
    simp

/-!

### A.4. Differentiability

We show that the potential and its derivatives are differentiable (or smooth) if the potential
is, in the forms `fun_prop` cannot derive on its own. Differentiability of a component
`fun x => A x μ` of a differentiable potential is found by `fun_prop` directly.
-/

open ContDiff

@[fun_prop]
lemma differentiable_action {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ (fun x => Λ • A (Λ⁻¹ • x)) := by
  exact (ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ)).comp
    (hA.comp (ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)))

@[fun_prop]
lemma contDiff_action {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (fun x => Λ • A (Λ⁻¹ • x)) := by
  exact (ContinuousLinearMap.contDiff (Lorentz.Vector.actionCLM Λ)).comp
    (hA.comp (ContinuousLinearMap.contDiff (Lorentz.Vector.actionCLM Λ⁻¹)))

@[fun_prop]
lemma differentiable_deriv_component_of_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μ ν : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => ∂_ μ A x ν) := by
  have h : ContDiff ℝ 2 A := hA.of_le ENat.LEInfty.out
  fun_prop

@[fun_prop]
lemma contDiff_deriv_component_of_smooth {n : ℕ} {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μ ν : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun x => ∂_ μ A x ν) := by
  have h : ContDiff ℝ (n + 1) A := hA.of_le (mod_cast le_top)
  fun_prop

/-!

#### A.4.1. Differentiability of the derivative of the potential

The derivatives `∂_ μ A x ν` of the potential are `C^n` if the potential is `C^{n+2}`.
This is what is needed to make sense of second derivatives of the potential, as appear for
example in Maxwell's equations. Differentiability for a `C^3` potential follows by `fun_prop`
from these lemmas and `SpaceTime.differentiable_deriv`, so is not stated separately.

A second derivative of a component can be written in two ways: as `∂_ μ (fun x => ∂_ ν A x ρ) x`,
the derivative of the real-valued component `∂_ ν A x ρ` (the `_component` lemmas), or as
`∂_ μ (∂_ ν A) x ρ`, the component of the derivative of the vector-valued `∂_ ν A`
(the `_apply` lemmas). The two agree for a `C^2` potential by `SpaceTime.deriv_apply_eq`.

The differentiability of the first-derivative components `∂_ μ A x ν` for a `C^2` (or
`C^{n+1}`) potential is found by `fun_prop` directly, so only the smooth variants are stated.

-/

/-- The second derivatives `∂_ μ ∂_ ν A^ρ` of a `C^{n+2}` potential are `C^n`. -/
@[fun_prop]
lemma contDiff_deriv_deriv_component {n} {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 2) A) (μ ν ρ : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun x => ∂_ μ (fun x => ∂_ ν A x ρ) x) := by
  have h : ContDiff ℝ (n + 1 + 1) A := by rw [add_assoc, one_add_one_eq_two]; exact hA
  fun_prop

/-- The `ρ` component of `∂_ μ (∂_ ν A)` is `C^n` for a `C^{n+2}` potential. -/
@[fun_prop]
lemma contDiff_deriv_deriv_apply {n} {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 2) A) (μ ν ρ : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun x => ∂_ μ (∂_ ν A) x ρ) := by
  have h : ContDiff ℝ (n + 1 + 1) A := by rw [add_assoc, one_add_one_eq_two]; exact hA
  have hd : Differentiable ℝ (∂_ ν A) :=
    SpaceTime.differentiable_deriv ν A (hA.of_le le_add_self)
  conv => enter [3, x]; rw [SpaceTime.deriv_apply_eq μ ρ _ hd, ← SpaceTime.deriv_eq]
  fun_prop

@[fun_prop]
lemma differentiable_deriv_deriv_apply_of_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μ ν ρ : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => ∂_ μ (∂_ ν A) x ρ) := by
  have h : ContDiff ℝ 3 A := hA.of_le ENat.LEInfty.out
  fun_prop

/-!

### A.5. Differentiability in terms of constructors

-/

lemma differentiable_ofScalarPotential {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (hϕ : Differentiable ℝ ↿φ) : Differentiable ℝ (ofScalarPotential c φ) := by
  simp [ofScalarPotential]
  rw [← SpaceTime.differentiable_vector]
  intro μ
  match μ with
  | Sum.inl 0 | Sum.inr _ => fun_prop

lemma contDiff_ofScalarPotential {n} {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (hϕ : ContDiff ℝ n ↿φ) : ContDiff ℝ n (ofScalarPotential c φ) := by
  simp [ofScalarPotential]
  rw [← SpaceTime.contDiff_vector]
  intro μ
  match μ with
  | Sum.inl 0 | Sum.inr _ => fun_prop

lemma differentiable_ofVectorPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d))
    (hA : Differentiable ℝ ↿A) : Differentiable ℝ (ofVectorPotential c A) := by
  simp [ofVectorPotential]
  rw [← SpaceTime.differentiable_vector]
  intro μ
  match μ with
  | Sum.inl 0 | Sum.inr _ => fun_prop

lemma contDiff_ofVectorPotential {n} {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d))
    (hA : ContDiff ℝ n ↿A) : ContDiff ℝ n (ofVectorPotential c A) := by
  simp [ofVectorPotential]
  rw [← SpaceTime.contDiff_vector]
  intro μ
  match μ with
  | Sum.inl 0 | Sum.inr _ => fun_prop

lemma differentiable_ofPotentials {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) (hϕ : Differentiable ℝ ↿φ)
    (hA : Differentiable ℝ ↿A) : Differentiable ℝ (ofPotentials c φ A) := by
  simp [ofPotentials]
  rw [← SpaceTime.differentiable_vector]
  intro μ
  match μ with
  | Sum.inl 0 | Sum.inr _ => fun_prop

lemma contDiff_ofPotentials {n} {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) (hϕ : ContDiff ℝ n ↿φ)
    (hA : ContDiff ℝ n ↿A) : ContDiff ℝ n (ofPotentials c φ A) := by
  simp [ofPotentials]
  rw [← SpaceTime.contDiff_vector]
  intro μ
  match μ with
  | Sum.inl 0 | Sum.inr _ => fun_prop

open MeasureTheory Matrix Space InnerProductSpace Time in
lemma contDiff_ofElectromagneticField {n : ℕ} (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) (hE : ContDiff ℝ n ↿E)
    (hB : ContDiff ℝ n ↿B) : ContDiff ℝ n (ofElectromagneticField c E B) := by
  let A : Time → Space → EuclideanSpace ℝ (Fin 3) := fun t x =>
    - ∫ u in 0..(1 : ℝ), (u • basis.repr x) ⨯ₑ₃ B t (u • x) ∂(volume)
  have h1 : ContDiff ℝ n ↿A := by
    simp only [WithLp.equiv_apply, A]
    apply ContDiff.neg
    apply contDiff_parametric_intervalIntegral_of_contDiff
    refine contDiff_euclidean.mpr ?_
    intro i
    let C : (Time × Space) × ℝ → EuclideanSpace ℝ (Fin 3) := fun p =>
      let (t, x) := p.1
      let u := p.2
      (u • basis.repr x) ⨯ₑ₃ B t (u • x)
    change ContDiff ℝ n (fun x => C x i)
    fin_cases i
    all_goals
    · simp [C, crossProduct]
      fun_prop
  rw [← SpaceTime.contDiff_vector]
  intro μ
  match μ with
  | Sum.inr i =>
    change ContDiff ℝ n (fun x => (timeSlice c).symm A x i)
    fun_prop
  | Sum.inl 0 =>
    simp only [ofElectromagneticField, ofPotentials, map_smul, WithLp.equiv_apply,
      WithLp.ofLp_smul, LinearMap.smul_apply, WithLp.equiv_symm_apply, WithLp.toLp_smul,
      Fin.isValue]
    apply ContDiff.div _ (by fun_prop) (by simp)
    apply timeSlice_symm_contDiff
    apply ContDiff.neg
    apply contDiff_parametric_intervalIntegral_of_contDiff
    fun_prop

/-!

### A.6. The action on the space-time derivatives

Given a ElectromagneticPotential `A^μ`, we can consider its derivative `∂_μ A^ν`.
Under a Lorentz transformation `Λ`, this transforms as
`∂_ μ (Λ • A)`, we write an expression for this in terms of the tensor.
`∂_ ρ A (Λ⁻¹ • x) κ`.

-/

lemma spaceTime_deriv_action_eq_sum {d} {μ ν : Fin 1 ⊕ Fin d} {x : SpaceTime d}
    (Λ : LorentzGroup d) (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) :
    ∂_ μ (Λ • A) x ν = ∑ κ, ∑ ρ, (Λ.1 ν κ * Λ⁻¹.1 ρ μ) * ∂_ ρ A (Λ⁻¹ • x) κ := by
  rw [action_val, SpaceTime.deriv_equivariant A.val Λ x hA μ, Lorentz.Vector.apply_sum,
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [Lorentz.Vector.apply_smul, Lorentz.Vector.smul_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  ring

/-!

### A.7. Variational adjoint derivative of component

We find the variational adjoint derivative of the components of the potential.
This will be used to find e.g. the variational derivative of the kinetic term,
and derive the equations of motion.

-/

open ContDiff
lemma hasVarAdjDerivAt_component {d : ℕ} (μ : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
        HasVarAdjDerivAt (fun (A' : SpaceTime d → Lorentz.Vector d) x => A' x μ)
          (fun (A' : SpaceTime d → ℝ) x => A' x • Lorentz.Vector.basis μ) A := by
  let f : SpaceTime d → Lorentz.Vector d → ℝ := fun x v => v μ
  let f' : SpaceTime d → Lorentz.Vector d → ℝ → Lorentz.Vector d := fun x _ c =>
    c • Lorentz.Vector.basis μ
  change HasVarAdjDerivAt (fun A' x => f x (A' x)) (fun ψ x => f' x (A x) (ψ x)) A
  apply HasVarAdjDerivAt.fmap
  · fun_prop
  · fun_prop
  intro x A
  refine { differentiableAt := ?_, hasAdjoint_fderiv := ?_ }
  · fun_prop
  refine { adjoint_inner_left := ?_ }
  intro u v
  simp [f, f', inner_smul_left, Lorentz.Vector.basis_inner, Lorentz.Vector.coordCLM_apply]
  ring

/-!

### A.8. Variational adjoint derivative of derivatives of the potential

We find the variational adjoint derivative of the derivatives of the components of the potential.
This will again be used to find the variational derivative of the kinetic term,
and derive the equations of motion (Maxwell's equations).

-/

lemma deriv_hasVarAdjDerivAt {d} (μ ν : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
    HasVarAdjDerivAt (fun (A : SpaceTime d → Lorentz.Vector d) x => ∂_ μ A x ν)
      (fun ψ x => - (fderiv ℝ ψ x) (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν) A := by
  have h0' := HasVarAdjDerivAt.fderiv' _ _
        (hF := hasVarAdjDerivAt_component ν A hA) A (Lorentz.Vector.basis μ)
  refine HasVarAdjDerivAt.congr (G := (fun (A : SpaceTime d →
    Lorentz.Vector d) x => ∂_ μ A x ν)) h0' ?_
  intro φ hφ
  funext x
  rw [deriv_apply_eq μ ν φ]
  exact hφ.differentiable (by simp)

/-!

## B. The derivative tensor of the electromagnetic potential

We define the derivative as a tensor in `Lorentz.CoVector ⊗[ℝ] Lorentz.Vector` for the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/

/-- The derivative of the electric potential, `∂_μ A^ν`. -/
noncomputable def deriv {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  ∑ μ, ∑ ν, (∂_ μ A x ν) • Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν

lemma deriv_eq_tensorDeriv {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    A.deriv x = tensorDeriv A.val x := by
  rw [deriv, tensorDeriv_eq_sum_tensor_basis (by fun_prop)]
  /- Match the basis sum. -/
  let e : ComponentIdx (Fin.append ![Color.down] ![Color.up])
      ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) := ComponentIdx.prod.trans <|
    Lorentz.CoVector.indexEquiv.prodCongr Lorentz.Vector.indexEquiv
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  /- Getting rid of the sums -/
  refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
  congr
  /- The coefficients. -/
  · simp [e]
    rw [deriv_apply_eq _ _ _ (by fun_prop)]
    congr
    simp [Lorentz.Vector.tensor_basis_repr_toTensor_apply]
  /- The basis elements. -/
  · change _ = ((Tensor.basis (S := realLorentzTensor d) (Fin.append ![Color.down] ![Color.up])).map
      (Tensorial.toTensor (M := (Lorentz.CoVector d) ⊗[ℝ] (Lorentz.Vector d))).symm) (e.symm (μ, ν))
    rw [Tensorial.basis_map_prod, ← Lorentz.Vector.toTensor_symm_basis,
      ← Lorentz.CoVector.toTensor_symm_basis]
    simp [e]

/-!

### B.1. Equivariance of the derivative tensor

We show that the derivative tensor is equivariant under the action of the Lorentz group.
That is, `∂_μ (fun x => Λ • A (Λ⁻¹ • x)) = Λ • (∂_μ A (Λ⁻¹ • x))`, or in words:
applying the Lorentz transformation to the potential and then taking the derivative is the same
as taking the derivative and then applying the Lorentz transformation to the resulting tensor.

-/
lemma deriv_equivariant {d} {x : SpaceTime d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) : deriv (Λ • A) x = Λ • (deriv A (Λ⁻¹ • x)) := by
  rw [deriv_eq_tensorDeriv, deriv_eq_tensorDeriv, action_val, tensorDeriv_equivariant]
  all_goals fun_prop

/-!

### B.2. The elements of the derivative tensor in terms of the basis

We show that in the standard basis, the elements of the derivative tensor
are just equal to `∂_ μ A x ν`.

-/

open Tensorial
/-- Evaluation of the tensor components of `∂_ μ A x ν`. -/
lemma tensorDeriv_eval_eq {d} {A : ElectromagneticPotential d} (hA : Differentiable ℝ A)
    (x : SpaceTime d) (μ ν : Fin 1 ⊕ Fin d) :
    toScalar {tensorDeriv A.val x | [μ] [ν]}ᵀ = ∂_ μ A x ν := by
  trans (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) (μ, ν); swap
  · simp [deriv, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  rw [deriv_eq_tensorDeriv _ hA]
  generalize (tensorDeriv A.val x) = t
  obtain ⟨t, rfl⟩ := toTensor.symm.surjective t
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · simp only [LinearEquiv.apply_symm_apply, basis_apply, evalT_pure, Pure.evalP, map_smul,
      toScalar_pure, smul_eq_mul, mul_one, Pure.evalPCoeff]
    change _ * (Lorentz.contrBasis d).repr (Lorentz.contrBasis d (b 1)) ν = _
    /- Transforming the basis -/
    let e : ComponentIdx (Fin.append ![Color.down] ![Color.up])
      ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) := ComponentIdx.prod.trans <|
      Lorentz.CoVector.indexEquiv.prodCongr Lorentz.Vector.indexEquiv
    have h1 : Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis =
        (((Tensor.basis (Fin.append ![Color.down] ![Color.up]))).map toTensor.symm).reindex e := by
      ext ⟨i, j⟩
      simp_rw [Tensorial.basis_map_prod, Basis.tensorProduct_apply,
        ← Lorentz.Vector.toTensor_symm_basis, ← Lorentz.CoVector.toTensor_symm_basis, e]
      simp
    simp [Pure.basisVector, h1, Finsupp.single_apply]
    by_cases hμ : b 0 = μ <;> by_cases hν : b 1 = ν <;>
    simp_all [Equiv.eq_symm_apply, show e b = (b 0, b 1) from rfl]
  · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  · simp only [map_smul, h, smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
  · simp only [map_add, h1, h2, Finsupp.coe_add, Pi.add_apply]

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) μν =
    ∂_ μν.1 A x μν.2 := by
  rcases μν with ⟨μ, ν⟩
  simp [deriv, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]

lemma toTensor_deriv_basis_repr_apply {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A x)) b =
    ∂_ (b 0) A x (b 1) := by
  rw [Tensorial.basis_toTensor_apply, Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext ⟨i, j⟩
    simp
  rw [hb, Finsupp.equivMapDomain_apply, Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

/-!

### B.3. Differentiability of the derivative tensor

We show that the derivative tensor `∂_μ A^ν`, as a function on spacetime, is differentiable
(or `C^n`) if the potential is `C^2` (or `C^{n+1}`).

-/

/-- The derivative tensor of a `C^2` potential is differentiable. -/
@[fun_prop]
lemma differentiable_deriv {d} {A : ElectromagneticPotential d} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ A.deriv := by
  unfold deriv
  fun_prop

@[fun_prop]
lemma differentiable_deriv_of_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) : Differentiable ℝ A.deriv :=
  differentiable_deriv (hA.of_le ENat.LEInfty.out)

/-- The derivative tensor of a `C^{n+1}` potential is `C^n`. -/
@[fun_prop]
lemma contDiff_deriv {n} {d} {A : ElectromagneticPotential d} (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n A.deriv := by
  unfold deriv
  fun_prop

end ElectromagneticPotential

end Electromagnetism
