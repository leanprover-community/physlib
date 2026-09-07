/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.Basic
/-!
# The transformation law of a derivative symbol

## i. Overview

`StandardModel.TransformsIn` demands of a family of component functions that each
derivative symbol transform by the all-orders Leibniz convolution of the base-point Taylor
coefficients `IsGaugeField.repDualCoeff` of the gauge jet. What the gauge action on the jet
component space is *built* from is `symbolAction`, the action of the coefficient
`jetCoeff rep U⁻¹ : JetRing ⊗ End V` through `DerivAlgebraComplex.jetRingAction` on the
derivative label. This file identifies the two.

The bridge is `DerivAlgebraComplex.jetRingAction_basis_multiset`, which puts the action of
a jet on a derivative monomial into the convolution form that `TransformsIn` wants. What
remains is to recognise the scalars it produces — the base-point Taylor coefficients of the
jet-ring factor of the gauge coefficient — as `IsGaugeField.repCoeff`. That is done by
`jetCoeffAt`, the base-point Taylor coefficient of a jet of endomorphisms, which on the
gauge coefficient reproduces `repCoeff` because `jetCoeff` reproduces `rep U` on constant
jets.

The result, `repDual_basis_tmul`, is stated for an arbitrary fibrewise gauge action `rep`.
The conjugate half of the component space is the same construction at `repConj rep`, so it
is an instance of the same lemma rather than a second proof.

## ii. Key results

- `StandardModel.jetCoeffAt` : the base-point Taylor coefficient of a jet of endomorphisms.
- `StandardModel.jetCoeffAt_jetCoeff` : on the gauge coefficient it is
  `IsGaugeField.repCoeff`.
- `StandardModel.symbolAction_basis_tmul` : a coefficient acts on a derivative monomial by
  the Leibniz convolution of its base-point Taylor coefficients.
- `StandardModel.repDual_basis_tmul` : the transformation law of the derivative symbol
  `∂_s ψ_φ`, in the form demanded by `StandardModel.TransformsIn`.

## iii. Table of contents

- A. Taylor coefficients of a jet of endomorphisms
  - A.1. Iterated derivatives of a pure tensor
  - A.2. The coefficient at a multiset of directions
- B. The transformation law of a derivative symbol
  - B.1. Bookkeeping for transposes and multiset sums
  - B.2. The action of a coefficient on a derivative monomial
  - B.3. The gauge action on a derivative symbol

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups TensorProduct MvPowerSeries

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. Taylor coefficients of a jet of endomorphisms

-/

/-!

### A.1. Iterated derivatives of a pure tensor

-/

/-- The iterated formal derivative of a `V`-valued jet acts on the jet-ring factor of a
  pure tensor: the value factor carries no spacetime dependence. -/
lemma jetIteratedDeriv_tmul (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) (v : V) :
    jetIteratedDeriv x (f ⊗ₜ[ℂ] v) = (x.foldl (fun h ρ => pderiv ℂ ρ h) f) ⊗ₜ[ℂ] v := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rw [jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
    rw [jetIteratedDeriv_cons, LinearMap.comp_apply, ih, jetDeriv_tmul,
      Multiset.foldl_cons, JetRing.foldl_pderiv_pderiv]

/-!

### A.2. The coefficient at a multiset of directions

-/

/-- The base-point Taylor coefficient at `x` derivatives of a jet of endomorphisms of `V`:
  differentiate `x` times and evaluate at the base point. It is the `V`-valued jet toolkit
  applied to the value space `Module.End ℂ V`, and it is what a coefficient in
  `JetRing ⊗ End V` contributes to the derivative symbol `∂_x`. -/
noncomputable def jetCoeffAt (x : Multiset (Fin 1 ⊕ Fin 3)) :
    JetRing ⊗[ℂ] Module.End ℂ V →ₗ[ℂ] Module.End ℂ V :=
  jetEval ∘ₗ jetIteratedDeriv x

/-- On a pure coefficient `f ⊗ T` the Taylor coefficient is the base-point Taylor
  coefficient of `f` times `T`. -/
@[simp]
lemma jetCoeffAt_tmul (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) (T : Module.End ℂ V) :
    jetCoeffAt x (f ⊗ₜ[ℂ] T)
      = constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f) • T := by
  rw [jetCoeffAt, LinearMap.comp_apply, jetIteratedDeriv_tmul, jetEval_tmul]

/-- The Taylor coefficient of a jet of endomorphisms, evaluated at a vector, is the Taylor
  coefficient of the `V`-valued jet obtained by feeding that vector to the coefficient. -/
lemma jetCoeffAt_apply (x : Multiset (Fin 1 ⊕ Fin 3))
    (c : JetRing ⊗[ℂ] Module.End ℂ V) (v : V) :
    jetCoeffAt x c v = jetEval (jetIteratedDeriv x (TensorProduct.lift
      ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) c v)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.add_apply, map_add,
      map_add]
  | tmul f T =>
    rw [jetCoeffAt_tmul, LinearMap.smul_apply,
      show TensorProduct.lift ((LinearMap.llcomp ℂ V V (JetRing ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ JetRing V)) (f ⊗ₜ[ℂ] T) v = f ⊗ₜ[ℂ] T v from rfl,
      jetIteratedDeriv_tmul, jetEval_tmul]

/-- The Taylor coefficients of the gauge coefficient are the Taylor coefficients of the
  representation: `jetCoeff rep U` reproduces `rep U` on constant jets, and both sides of
  this identity read off the same derivative of that. -/
lemma jetCoeffAt_jetCoeff [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)) (U : JetGaugeGroupI)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    jetCoeffAt x (jetCoeff rep U) = IsGaugeField.repCoeff rep U x := by
  refine LinearMap.ext fun v => ?_
  rw [jetCoeffAt_apply, jetCoeff_spec]
  rfl

/-!

## B. The transformation law of a derivative symbol

-/

/-!

### B.1. Bookkeeping for transposes and multiset sums

-/

/-- The transpose is additive in the endomorphism. -/
private lemma dualMap_add_apply (A B : Module.End ℂ V) (φ : Module.Dual ℂ V) :
    (A + B).dualMap φ = A.dualMap φ + B.dualMap φ := by
  ext v
  simp

/-- The transpose is homogeneous in the endomorphism. -/
private lemma dualMap_smul_apply (c : ℂ) (T : Module.End ℂ V) (φ : Module.Dual ℂ V) :
    (c • T).dualMap φ = c • T.dualMap φ := by
  ext v
  simp

/-- A multiset sum in the derivative label distributes out of a pure symbol. -/
private lemma sum_tmul_right (m : Multiset DerivAlgebraComplex) (w : Module.Dual ℂ V) :
    m.sum ⊗ₜ[ℂ] w = (m.map fun a => a ⊗ₜ[ℂ] w).sum := by
  rw [show m.sum ⊗ₜ[ℂ] w
      = ((TensorProduct.mk ℂ DerivAlgebraComplex (Module.Dual ℂ V)).flip w) m.sum from rfl,
    map_multiset_sum]
  rfl

/-!

### B.2. The action of a coefficient on a derivative monomial

-/

/-- A coefficient acts on the derivative symbol `∂_s ψ_φ` by the all-orders Leibniz
  convolution of its base-point Taylor coefficients: each splitting `s = s₁ + s₂` of the
  derivative multiset contributes the Taylor coefficient at `s₁` acting on the target index
  of the lower symbol `∂_{s₂} ψ_φ`.

  This is `DerivAlgebraComplex.jetRingAction_basis_multiset` in the derivative label,
  together with the identification of the scalars it produces as `jetCoeffAt`; both sides
  are additive in the coefficient, so it suffices to check it on a pure tensor. -/
lemma symbolAction_basis_tmul (c : JetRing ⊗[ℂ] Module.End ℂ V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    symbolAction c (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ)
      = (s.antidiagonal.map fun p =>
          DerivAlgebraComplex.basis p.2 ⊗ₜ[ℂ] (jetCoeffAt p.1 c).dualMap φ).sum := by
  induction c using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, LinearMap.zero_apply]
    refine (Multiset.sum_eq_zero fun x hx => ?_).symm
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
    rw [map_zero, show (0 : Module.End ℂ V).dualMap φ = 0 from LinearMap.ext fun v => by simp,
      TensorProduct.tmul_zero]
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [map_add, dualMap_add_apply, TensorProduct.tmul_add]
  | tmul f T =>
    rw [symbolAction_tmul, TensorProduct.map_tmul,
      DerivAlgebraComplex.jetRingAction_basis_multiset, sum_tmul_right, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [Function.comp_apply, TensorProduct.smul_tmul, jetCoeffAt_tmul, dualMap_smul_apply]
    rfl

/-!

### B.3. The gauge action on a derivative symbol

-/

/-- The transformation law of the derivative symbol `∂_s ψ_φ` under the jet gauge group:
  the all-orders Leibniz convolution of the dual representation coefficients
  `IsGaugeField.repDualCoeff` against lower symbols, with no inhomogeneous term. This is
  the identity the `StandardModel.TransformsIn` obligations of a matter field rest on.

  Nothing here is special to the unconjugated half of the component space: the conjugate
  half is this lemma at `repConj rep`. -/
lemma repDual_basis_tmul [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repDual rep hlin U (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ)
      = (s.antidiagonal.map fun p =>
          DerivAlgebraComplex.basis p.2 ⊗ₜ[ℂ]
            IsGaugeField.repDualCoeff rep U⁻¹ p.1 φ).sum := by
  rw [show repDual rep hlin U = symbolAction (jetCoeff rep U⁻¹) from rfl,
    symbolAction_basis_tmul]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => by
    rw [jetCoeffAt_jetCoeff, IsGaugeField.repDualCoeff])

end StandardModel
