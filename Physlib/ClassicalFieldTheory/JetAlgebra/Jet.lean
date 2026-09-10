/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module


public import Physlib.Relativity.JetRing.Basic
public import Physlib.Relativity.DerivAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Pi
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

/-!

## The jets of a product of value spaces

A field valued in `V × W` is a pair of fields, one valued in `V` and one in `W`, and the
identification `jetProdEquiv` of its jets with the pair of their jets intertwines every
piece of the jet toolkit: the inclusion of constants, the formal derivative and the
base-point evaluation all act componentwise.

-/

section Prod

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- **The jets of a product are the product of the jets**: `JetRing ⊗ (V × W)` splits as
  `(JetRing ⊗ V) × (JetRing ⊗ W)`, the jet-ring factor being shared. -/
noncomputable abbrev jetProdEquiv :
    JetRing ⊗[ℂ] (V × W) ≃ₗ[ℂ] (JetRing ⊗[ℂ] V) × (JetRing ⊗[ℂ] W) :=
  TensorProduct.prodRight ℂ ℂ JetRing V W

@[simp]
lemma jetProdEquiv_jetOfConstant (v : V) (w : W) :
    jetProdEquiv (jetOfConstant (v, w)) = (jetOfConstant v, jetOfConstant w) := rfl

lemma jetProdEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (z : JetRing ⊗[ℂ] (V × W)) :
    jetProdEquiv (jetDeriv μ z) =
      (jetDeriv μ (jetProdEquiv z).1, jetDeriv μ (jetProdEquiv z).2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [Prod.ext_iff]
  | tmul f p => rw [jetDeriv_tmul]; rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

lemma jetProdEquiv_jetIteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3))
    (z : JetRing ⊗[ℂ] (V × W)) :
    jetProdEquiv (jetIteratedDeriv s z) =
      (jetIteratedDeriv s (jetProdEquiv z).1, jetIteratedDeriv s (jetProdEquiv z).2) := by
  induction s using Multiset.induction_on generalizing z with
  | empty => rw [jetIteratedDeriv_zero, jetIteratedDeriv_zero, jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
      rw [jetIteratedDeriv_cons, LinearMap.comp_apply, jetProdEquiv_jetDeriv, ih,
        jetIteratedDeriv_cons, jetIteratedDeriv_cons, LinearMap.comp_apply,
        LinearMap.comp_apply]

/-- The identification is `JetRing`-linear: multiplication by a scalar jet acts on both
  components. -/
lemma jetProdEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] (V × W)) :
    jetProdEquiv (χ • z) = (χ • (jetProdEquiv z).1, χ • (jetProdEquiv z).2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [Prod.ext_iff]
  | tmul f p => rw [TensorProduct.smul_tmul', smul_eq_mul]; rfl
  | add a b ha hb =>
      simp only [smul_add, map_add, ha, hb, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

lemma jetProdEquiv_symm_smul (χ : JetRing) (a : JetRing ⊗[ℂ] V) (b : JetRing ⊗[ℂ] W) :
    (jetProdEquiv (V := V) (W := W)).symm (χ • a, χ • b)
      = χ • (jetProdEquiv (V := V) (W := W)).symm (a, b) := by
  refine (jetProdEquiv (V := V) (W := W)).injective ?_
  rw [LinearEquiv.apply_symm_apply, jetProdEquiv_smul, LinearEquiv.apply_symm_apply]

lemma jetEval_prod (z : JetRing ⊗[ℂ] (V × W)) :
    jetEval z = (jetEval (jetProdEquiv z).1, jetEval (jetProdEquiv z).2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [Prod.ext_iff]
  | tmul f p => rw [jetEval_tmul]; rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

end Prod

/-!

## The jets of an indexed product of value spaces

A field valued in a finite product `∀ i, E i` is a family of fields, one for each index,
and `jetPiEquiv` identifies its jets with the family of their jets. It intertwines the
whole jet toolkit index by index, exactly as `jetProdEquiv` does in the binary case. The
index type has to be finite for the identification to exist at all: a jet of a field
valued in an infinite product need not have all but finitely many of its components
constant, so `TensorProduct.piRightHom` is only an equivalence in the finite case.

-/

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]

/-- **The jets of a finite product are the product of the jets**:
  `JetRing ⊗ (∀ i, E i)` splits as `∀ i, JetRing ⊗ E i`, the jet-ring factor being
  shared. -/
noncomputable abbrev jetPiEquiv :
    JetRing ⊗[ℂ] (∀ i, E i) ≃ₗ[ℂ] ∀ i, JetRing ⊗[ℂ] E i :=
  TensorProduct.piRight ℂ ℂ JetRing E

lemma jetPiEquiv_jetOfConstant (v : ∀ i, E i) :
    jetPiEquiv E (jetOfConstant v) = fun i => jetOfConstant (v i) := rfl

lemma jetPiEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (z : JetRing ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E (jetDeriv μ z) i = jetDeriv μ (jetPiEquiv E z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f p => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

lemma jetPiEquiv_jetIteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3))
    (z : JetRing ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E (jetIteratedDeriv s z) i = jetIteratedDeriv s (jetPiEquiv E z i) := by
  induction s using Multiset.induction_on generalizing z with
  | empty => rw [jetIteratedDeriv_zero, jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
      rw [jetIteratedDeriv_cons, LinearMap.comp_apply, jetPiEquiv_jetDeriv, ih,
        jetIteratedDeriv_cons, LinearMap.comp_apply]

/-- The identification is `JetRing`-linear: multiplication by a scalar jet acts on every
  component. -/
lemma jetPiEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E (χ • z) i = χ • (jetPiEquiv E z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f p => rw [TensorProduct.smul_tmul', smul_eq_mul]; rfl
  | add a b ha hb => simp only [smul_add, map_add, Pi.add_apply, ha, hb]

lemma jetPiEquiv_symm_smul (χ : JetRing) (a : ∀ i, JetRing ⊗[ℂ] E i) :
    (jetPiEquiv E).symm (fun i => χ • a i) = χ • (jetPiEquiv E).symm a := by
  refine (jetPiEquiv E).injective (funext fun i => ?_)
  rw [LinearEquiv.apply_symm_apply, jetPiEquiv_smul, LinearEquiv.apply_symm_apply]

lemma jetEval_pi (z : JetRing ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetEval z i = jetEval (jetPiEquiv E z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f p => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

end Pi
