/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module


public import Physlib.Relativity.JetRing.Basic
public import Physlib.Relativity.DerivAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
/-!
# `V`-valued jets

## i. Overview

The jets of a field valued in a complex vector space `V` are `JetRing ⊗[ℂ] V`. This file
provides the basic toolkit for them, independent of any gauge group:

* `jetOfConstant` — the inclusion of constants, `v ↦ 1 ⊗ v`;
* `jetDeriv`/`jetIteratedDeriv` — the formal derivative, acting on the jet factor;
* `jetEval` — evaluation at the base point, `f ⊗ v ↦ (constant coefficient of f) • v`.

-/

@[expose] public section

open TensorProduct MvPowerSeries
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## `V`-valued jets

-/

/-- The constant-coefficient evaluation of a jet, as a `ℂ`-linear map. -/
noncomputable def _root_.JetRing.constantCoeffₗ : JetRing →ₗ[ℂ] ℂ where
  toFun := constantCoeff
  map_add' f g := by simp
  map_smul' c f := by simp [smul_eq_C_mul]

@[simp]
lemma _root_.JetRing.constantCoeffₗ_apply (f : JetRing) :
    JetRing.constantCoeffₗ f = constantCoeff f := rfl

/-- The inclusion of constants into `V`-valued jets: `v ↦ 1 ⊗ v`. -/
noncomputable def jetOfConstant : V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  TensorProduct.mk ℂ JetRing V 1

@[simp]
lemma jetOfConstant_apply (v : V) : jetOfConstant v = (1 : JetRing) ⊗ₜ[ℂ] v := rfl

/-- The formal derivative on `V`-valued jets in the direction `μ`, acting on the jet
  factor. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  LinearMap.rTensor V (pderiv ℂ μ).toLinearMap

@[simp]
lemma jetDeriv_tmul (μ : Fin 1 ⊕ Fin 3) (f : JetRing) (v : V) :
    jetDeriv μ (f ⊗ₜ[ℂ] v) = pderiv ℂ μ f ⊗ₜ[ℂ] v := rfl

/-- Formal derivatives on `V`-valued jets commute, since the partial derivatives of
  jets do. -/
lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (jetDeriv (V := V) μ).comp (jetDeriv ν) = (jetDeriv ν).comp (jetDeriv μ) := by
  rw [jetDeriv, jetDeriv, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
  exact congrArg (LinearMap.rTensor V)
    (LinearMap.ext fun f => JetRing.pderiv_comm μ ν f)

/-- Post-composition with `jetDeriv` is right-commutative, which is what allows
  iterated derivatives to be indexed by a `Multiset` of directions. -/
instance : RightCommutative (fun (L : JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V)
    (μ : Fin 1 ⊕ Fin 3) => L.comp (jetDeriv μ)) where
  right_comm L μ ν := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun (jetDeriv_comm μ ν) x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h ⊢
    exact congrArg L h

/-- The iterated formal derivative on `V`-valued jets, in the (unordered) directions
  given by the multiset `μs`. -/
noncomputable def jetIteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  μs.foldl (fun L μ => L.comp (jetDeriv μ)) LinearMap.id

@[simp]
lemma jetIteratedDeriv_zero :
    jetIteratedDeriv (V := V) (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [jetIteratedDeriv]

lemma jetIteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    jetIteratedDeriv (V := V) (μ ::ₘ μs) = (jetDeriv μ).comp (jetIteratedDeriv μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (L : JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V),
      s.foldl (fun L μ => L.comp (jetDeriv μ)) L = L.comp (jetIteratedDeriv s) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro L; simp [jetIteratedDeriv]
    | cons κ t ih =>
        intro L
        rw [jetIteratedDeriv, Multiset.foldl_cons, Multiset.foldl_cons, ih, ih]
        simp [LinearMap.comp_assoc]
  rw [jetIteratedDeriv, Multiset.foldl_cons, h]
  simp

/-- The iterated derivative is additive in the multiset of directions. -/
lemma jetIteratedDeriv_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    jetIteratedDeriv (V := V) (s + t) =
      (jetIteratedDeriv s).comp (jetIteratedDeriv t) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons μ s ih =>
      rw [Multiset.cons_add, jetIteratedDeriv_cons, jetIteratedDeriv_cons, ih,
        LinearMap.comp_assoc]

@[simp]
lemma jetIteratedDeriv_singleton (μ : Fin 1 ⊕ Fin 3) :
    jetIteratedDeriv (V := V) ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = jetDeriv μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, jetIteratedDeriv_cons,
    jetIteratedDeriv_zero, LinearMap.comp_id]

/-- Evaluation of a `V`-valued jet at the base point:
  `f ⊗ v ↦ (constant coefficient of f) • v`. This is a retraction of
  `jetOfConstant`. -/
noncomputable def jetEval : JetRing ⊗[ℂ] V →ₗ[ℂ] V :=
  TensorProduct.lift ((LinearMap.lsmul ℂ V).comp JetRing.constantCoeffₗ)

@[simp]
lemma jetEval_tmul (f : JetRing) (v : V) :
    jetEval (f ⊗ₜ[ℂ] v) = constantCoeff f • v := rfl

@[simp]
lemma jetEval_jetOfConstant (v : V) : jetEval (jetOfConstant v) = v := by
  simp
