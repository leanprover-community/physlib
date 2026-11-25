/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module


public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# `V`-valued jets

The formal Taylor expansions of a field valued in a complex vector space, their derivatives
and their base-point values.

## i. Overview

The jets of a field valued in a complex vector space `V` are `SpaceTimeAlgebra ⊗[ℂ] V`. This file
provides the basic toolkit for them, independent of any gauge group.

* `jetOfConstant` is the inclusion of constants, `v ↦ 1 ⊗ v`.
* `jetDeriv` and `jetIteratedDeriv` are the formal derivatives, acting on the jet factor.
* `jetEval` is evaluation at the base point, `f ⊗ v ↦ (constant coefficient of f) • v`.

When `V` is finite-dimensional, a jet is determined by its base-point derivatives
`jetDerivValue s`, and any family of base-point derivatives is realised, `ofJetDerivValues`.
The Euler operator `E = ∑_ρ x_ρ ∂_ρ` multiplies the base-point derivative along `s` by `|s|`.

When `V = A` is a finite-dimensional algebra, the jets form an algebra on which the formal
derivatives are derivations, and the base-point derivatives of a product obey the Leibniz
rule. A family `Ω_μ` of `A`-valued jets that is flat,
`∂_μ Ω_ν − ∂_ν Ω_μ = Ω_μ Ω_ν − Ω_ν Ω_μ`, has a unique solution of `∂_μ T = Ω_μ T` with any
prescribed value. It is the radial transport, the solution of `E T = (∑_μ x_μ Ω_μ) T`, and
flatness makes it solve each equation and not only their radial combination. This is the
formal version of integrating a flat connection along rays from the base point.

## ii. Key results

- `jetOfConstant` : the inclusion of constants into `V`-valued jets, `v ↦ 1 ⊗ v`.
- `jetDeriv` : the formal derivative on `V`-valued jets in the direction `μ`, acting on the jet
  factor.
- `jetIteratedDeriv` : the iterated formal derivative on `V`-valued jets, in the (unordered)
  directions given by a multiset.
- `jetEval` : evaluation of a `V`-valued jet at the base point.
- `jetDerivValue` : the base-point derivative of a jet along a multiset of directions.
- `jet_ext_of_jetDerivValue` : a jet valued in a finite-dimensional space is determined by its
  base-point derivatives.
- `ofJetDerivValues` : the jet with prescribed base-point derivatives.
- `jetDerivValue_mul` : the Leibniz rule for the base-point derivatives of a product.
- `exists_jetDeriv_eq_mul` : a flat family `Ω_μ` has a solution of `∂_μ T = Ω_μ T` with any
  value.
- `eq_of_jetDeriv_eq_mul` : that solution is unique.

## iii. Table of contents

- A. `V`-valued jets
- B. The jets of a product of value spaces
- C. The jets of an indexed product of value spaces
- D. Base-point derivatives of `V`-valued jets
- E. The Euler operator on `V`-valued jets
- F. Jets valued in an algebra
- G. Flat connections on jets

## iv. References

* None.

-/

@[expose] public section

open TensorProduct MvPowerSeries
variable {V : Type} [AddCommGroup V] [Module ℂ V]


TODO "(2026-09-11) If we actually need anything in this file, it should
  be related to `FieldDerivSpace` of a `MatterField` and it should appear in there."

/-!

## A. `V`-valued jets

-/

/-- The inclusion of constants into `V`-valued jets, `v ↦ 1 ⊗ v`. -/
noncomputable def jetOfConstant : V →ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] V :=
  TensorProduct.mk ℂ SpaceTimeAlgebra V 1

@[simp]
lemma jetOfConstant_apply (v : V) : jetOfConstant v = (1 : SpaceTimeAlgebra) ⊗ₜ[ℂ] v := rfl

/-- The formal derivative on `V`-valued jets in the direction `μ`, acting on the jet
  factor. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] V :=
  LinearMap.rTensor V (pderiv μ).toLinearMap

@[simp]
lemma jetDeriv_tmul (μ : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) (v : V) :
    jetDeriv μ (f ⊗ₜ[ℂ] v) = pderiv μ f ⊗ₜ[ℂ] v := rfl

/-- Formal derivatives on `V`-valued jets commute, since the partial derivatives of
  jets do. -/
lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (jetDeriv (V := V) μ).comp (jetDeriv ν) = (jetDeriv ν).comp (jetDeriv μ) := by
  rw [jetDeriv, jetDeriv, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
  exact congrArg (LinearMap.rTensor V)
    (LinearMap.ext fun f => SpaceTimeAlgebra.pderiv_comm μ ν f)

/-- Post-composition with `jetDeriv` is right-commutative, which is what allows
  iterated derivatives to be indexed by a `Multiset` of directions. -/
instance : RightCommutative (fun (L : SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] V)
    (μ : Fin 1 ⊕ Fin 3) => L.comp (jetDeriv μ)) where
  right_comm L μ ν := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun (jetDeriv_comm μ ν) x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h ⊢
    exact congrArg L h

/-- The iterated formal derivative on `V`-valued jets, in the (unordered) directions
  given by the multiset `μs`. -/
noncomputable def jetIteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] V :=
  μs.foldl (fun L μ => L.comp (jetDeriv μ)) LinearMap.id

@[simp]
lemma jetIteratedDeriv_zero :
    jetIteratedDeriv (V := V) (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [jetIteratedDeriv]

lemma jetIteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    jetIteratedDeriv (V := V) (μ ::ₘ μs) = (jetDeriv μ).comp (jetIteratedDeriv μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3))
      (L : SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] V),
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

/-- Evaluation of a `V`-valued jet at the base point,
  `f ⊗ v ↦ (constant coefficient of f) • v`. This is a retraction of
  `jetOfConstant`. -/
noncomputable def jetEval : SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] V :=
  TensorProduct.lift ((LinearMap.lsmul ℂ V).comp SpaceTimeAlgebra.constantCoeffₗ)

@[simp]
lemma jetEval_tmul (f : SpaceTimeAlgebra) (v : V) :
    jetEval (f ⊗ₜ[ℂ] v) = constantCoeff f • v := rfl

lemma jetEval_jetOfConstant (v : V) : jetEval (jetOfConstant v) = v := by
  simp

/-- Evaluation at the base point is semilinear over the jet ring, since a scalar jet acts through
  its constant coefficient. -/
lemma jetEval_smul (f : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetEval (f • z) = constantCoeff f • jetEval z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul g v => rw [TensorProduct.smul_tmul', smul_eq_mul, jetEval_tmul, jetEval_tmul, map_mul,
      mul_smul]

/-!

## B. The jets of a product of value spaces

A field valued in `V × W` is a pair of fields, one valued in `V` and one in `W`, and the
identification `jetProdEquiv` of its jets with the pair of their jets intertwines every
piece of the jet toolkit: the inclusion of constants, the formal derivative and the
base-point evaluation all act componentwise.

-/

section Prod

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- The jets of a product are the product of the jets, as `SpaceTimeAlgebra ⊗ (V × W)` splits as
  `(SpaceTimeAlgebra ⊗ V) × (SpaceTimeAlgebra ⊗ W)`, the jet-ring factor being shared. -/
noncomputable abbrev jetProdEquiv :
    SpaceTimeAlgebra ⊗[ℂ] (V × W) ≃ₗ[ℂ] (SpaceTimeAlgebra ⊗[ℂ] V) × (SpaceTimeAlgebra ⊗[ℂ] W) :=
  TensorProduct.prodRight ℂ ℂ SpaceTimeAlgebra V W

@[simp]
lemma jetProdEquiv_jetOfConstant (v : V) (w : W) :
    jetProdEquiv (jetOfConstant (v, w)) = (jetOfConstant v, jetOfConstant w) := rfl

lemma jetProdEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (z : SpaceTimeAlgebra ⊗[ℂ] (V × W)) :
    jetProdEquiv (jetDeriv μ z) =
      (jetDeriv μ (jetProdEquiv z).1, jetDeriv μ (jetProdEquiv z).2) := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rw [jetDeriv_tmul]; rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

lemma jetProdEquiv_jetIteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3))
    (z : SpaceTimeAlgebra ⊗[ℂ] (V × W)) :
    jetProdEquiv (jetIteratedDeriv s z) =
      (jetIteratedDeriv s (jetProdEquiv z).1, jetIteratedDeriv s (jetProdEquiv z).2) := by
  induction s using Multiset.induction_on generalizing z with
  | empty => rw [jetIteratedDeriv_zero, jetIteratedDeriv_zero, jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
      rw [jetIteratedDeriv_cons, LinearMap.comp_apply, jetProdEquiv_jetDeriv, ih,
        jetIteratedDeriv_cons, jetIteratedDeriv_cons, LinearMap.comp_apply,
        LinearMap.comp_apply]

/-- The identification is `SpaceTimeAlgebra`-linear, so multiplication by a scalar jet acts on both
  components. -/
lemma jetProdEquiv_smul (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] (V × W)) :
    jetProdEquiv (χ • z) = (χ • (jetProdEquiv z).1, χ • (jetProdEquiv z).2) := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rw [TensorProduct.smul_tmul', smul_eq_mul]; rfl
  | add a b ha hb =>
      simp only [smul_add, map_add, ha, hb, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

lemma jetProdEquiv_symm_smul (χ : SpaceTimeAlgebra) (a : SpaceTimeAlgebra ⊗[ℂ] V)
    (b : SpaceTimeAlgebra ⊗[ℂ] W) :
    (jetProdEquiv (V := V) (W := W)).symm (χ • a, χ • b)
      = χ • (jetProdEquiv (V := V) (W := W)).symm (a, b) := by
  refine (jetProdEquiv (V := V) (W := W)).injective ?_
  rw [LinearEquiv.apply_symm_apply, jetProdEquiv_smul, LinearEquiv.apply_symm_apply]

lemma jetEval_prod (z : SpaceTimeAlgebra ⊗[ℂ] (V × W)) :
    jetEval z = (jetEval (jetProdEquiv z).1, jetEval (jetProdEquiv z).2) := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rw [jetEval_tmul]; rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

end Prod

/-!

## C. The jets of an indexed product of value spaces

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

/-- The jets of a finite product are the product of the jets, as
  `SpaceTimeAlgebra ⊗ (∀ i, E i)` splits as `∀ i, SpaceTimeAlgebra ⊗ E i`, the jet-ring factor being
  shared. -/
noncomputable abbrev jetPiEquiv :
    SpaceTimeAlgebra ⊗[ℂ] (∀ i, E i) ≃ₗ[ℂ] ∀ i, SpaceTimeAlgebra ⊗[ℂ] E i :=
  TensorProduct.piRight ℂ ℂ SpaceTimeAlgebra E

lemma jetPiEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E (jetDeriv μ z) i = jetDeriv μ (jetPiEquiv E z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

lemma jetPiEquiv_jetIteratedDeriv (s : Multiset (Fin 1 ⊕ Fin 3))
    (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E (jetIteratedDeriv s z) i = jetIteratedDeriv s (jetPiEquiv E z i) := by
  induction s using Multiset.induction_on generalizing z with
  | empty => rw [jetIteratedDeriv_zero, jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
      rw [jetIteratedDeriv_cons, LinearMap.comp_apply, jetPiEquiv_jetDeriv, ih,
        jetIteratedDeriv_cons, LinearMap.comp_apply]

/-- The identification is `SpaceTimeAlgebra`-linear, so multiplication by a scalar jet acts on every
  component. -/
lemma jetPiEquiv_smul (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E (χ • z) i = χ • (jetPiEquiv E z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rw [TensorProduct.smul_tmul', smul_eq_mul]; rfl
  | add a b ha hb => simp only [smul_add, map_add, Pi.add_apply, ha, hb]

lemma jetPiEquiv_symm_smul (χ : SpaceTimeAlgebra) (a : ∀ i, SpaceTimeAlgebra ⊗[ℂ] E i) :
    (jetPiEquiv E).symm (fun i => χ • a i) = χ • (jetPiEquiv E).symm a := by
  refine (jetPiEquiv E).injective (funext fun i => ?_)
  rw [LinearEquiv.apply_symm_apply, jetPiEquiv_smul, LinearEquiv.apply_symm_apply]

lemma jetEval_pi (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetEval z i = jetEval (jetPiEquiv E z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/-- The component of the splitting is the projection on the value factor. Reading off
  the summand `i` of a jet of a `(∀ i, E i)`-valued field is applying the projection onto
  that summand to the value factor, the jet-ring factor being untouched. This is the form
  in which the splitting meets the naturality statements, which are all phrased in terms of
  linear maps of value spaces. -/
lemma jetPiEquiv_eq_lTensor_proj (z : SpaceTimeAlgebra ⊗[ℂ] (∀ i, E i)) (i : ι) :
    jetPiEquiv E z i = LinearMap.lTensor SpaceTimeAlgebra (LinearMap.proj i) z := by
  induction z using TensorProduct.inductionOn with
  | tmul f p => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

end Pi

/-!

## D. Base-point derivatives of `V`-valued jets

-/

section DerivValue

/-- The base-point value `(∂^s z)(0)` of the iterated derivative of a `V`-valued jet. -/
noncomputable def jetDerivValue (s : Multiset (Fin 1 ⊕ Fin 3)) :
    SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] V :=
  jetEval ∘ₗ jetIteratedDeriv s

lemma jetIteratedDeriv_tmul (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) (v : V) :
    jetIteratedDeriv s (f ⊗ₜ[ℂ] v) = SpaceTimeAlgebra.iteratedPDeriv s f ⊗ₜ[ℂ] v := by
  induction s using Multiset.induction_on with
  | empty => simp [SpaceTimeAlgebra.iteratedPDeriv_zero]
  | cons μ s ih =>
    rw [jetIteratedDeriv_cons, LinearMap.comp_apply, ih, jetDeriv_tmul,
      SpaceTimeAlgebra.iteratedPDeriv_cons, SpaceTimeAlgebra.iteratedPDeriv_pderiv]

@[simp]
lemma jetDerivValue_tmul (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) (v : V) :
    jetDerivValue s (f ⊗ₜ[ℂ] v) = constantCoeff (SpaceTimeAlgebra.iteratedPDeriv s f) • v := by
  rw [jetDerivValue, LinearMap.comp_apply, jetIteratedDeriv_tmul, jetEval_tmul]

@[simp]
lemma jetDerivValue_zero : jetDerivValue (V := V) 0 = jetEval := by
  simp [jetDerivValue]

/-- The base-point derivative along `μ :: s` is that along `s` of the derivative `∂_μ`. -/
lemma jetDerivValue_cons (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetDerivValue (μ ::ₘ s) z = jetDerivValue s (jetDeriv μ z) := by
  rw [jetDerivValue, jetDerivValue, ← Multiset.singleton_add, add_comm, jetIteratedDeriv_add,
    jetIteratedDeriv_singleton]
  rfl

/-- The base-point derivatives of the jet of a constant vanish, except its value. -/
lemma jetDerivValue_jetOfConstant (s : Multiset (Fin 1 ⊕ Fin 3)) (v : V) :
    jetDerivValue s (jetOfConstant v) = if s = 0 then v else 0 := by
  rw [jetOfConstant_apply, jetDerivValue_tmul]
  split_ifs with hs
  · simp [hs, SpaceTimeAlgebra.iteratedPDeriv_zero]
  · rw [show (1 : SpaceTimeAlgebra) = MvPowerSeries.C 1 from map_one _ |>.symm,
      SpaceTimeAlgebra.iteratedPDeriv_C_of_ne_zero hs, map_zero, zero_smul]

variable [FiniteDimensional ℂ V]

/-- The coordinates of a jet in the basis `Module.finBasis ℂ V` of the value space. -/
private noncomputable def jetCoord (i : Fin (Module.finrank ℂ V)) :
    SpaceTimeAlgebra ⊗[ℂ] V →ₗ[ℂ] SpaceTimeAlgebra :=
  (TensorProduct.rid ℂ SpaceTimeAlgebra).toLinearMap ∘ₗ
    LinearMap.lTensor SpaceTimeAlgebra ((Module.finBasis ℂ V).coord i)

private lemma sum_jetCoord_tmul (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    ∑ i, jetCoord i z ⊗ₜ[ℂ] Module.finBasis ℂ V i = z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, ha, hb]
  | tmul f v =>
    simp only [jetCoord, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Module.Basis.coord_apply]
    rw [← (Module.finBasis ℂ V).sum_repr v, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul, Module.Basis.sum_repr]

private lemma constantCoeff_iteratedPDeriv_jetCoord (s : Multiset (Fin 1 ⊕ Fin 3))
    (i : Fin (Module.finrank ℂ V)) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    constantCoeff (SpaceTimeAlgebra.iteratedPDeriv s (jetCoord i z)) =
      (Module.finBasis ℂ V).repr (jetDerivValue s z) i := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, SpaceTimeAlgebra.iteratedPDeriv_add, ha, hb,
      Finsupp.add_apply]
  | tmul f v =>
    simp [jetCoord, SpaceTimeAlgebra.iteratedPDeriv_smul, mul_comm]

/-- A jet valued in a finite-dimensional space is determined by its base-point
  derivatives. -/
lemma jet_ext_of_jetDerivValue {z w : SpaceTimeAlgebra ⊗[ℂ] V}
    (h : ∀ s, jetDerivValue s z = jetDerivValue s w) : z = w := by
  rw [← sum_jetCoord_tmul z, ← sum_jetCoord_tmul w]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact SpaceTimeAlgebra.ext_of_constantCoeff_iteratedPDeriv fun s => by
    rw [constantCoeff_iteratedPDeriv_jetCoord, constantCoeff_iteratedPDeriv_jetCoord, h s]

/-- The jet valued in a finite-dimensional space with prescribed base-point derivatives. -/
noncomputable def ofJetDerivValues (c : Multiset (Fin 1 ⊕ Fin 3) → V) :
    SpaceTimeAlgebra ⊗[ℂ] V :=
  ∑ i, SpaceTimeAlgebra.ofDerivValues (fun s => (Module.finBasis ℂ V).repr (c s) i) ⊗ₜ[ℂ]
    Module.finBasis ℂ V i

@[simp]
lemma jetDerivValue_ofJetDerivValues (c : Multiset (Fin 1 ⊕ Fin 3) → V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : jetDerivValue s (ofJetDerivValues c) = c s := by
  simp [ofJetDerivValues, map_sum, SpaceTimeAlgebra.constantCoeff_iteratedPDeriv_ofDerivValues,
    Module.Basis.sum_repr]

end DerivValue

/-!

## E. The Euler operator on `V`-valued jets

-/

section Euler

/-- The derivative of a jet multiplied by a coordinate,
  `∂_μ (x_ν z) = δ_{μν} z + x_ν ∂_μ z`. -/
lemma jetDeriv_X_smul (μ ν : Fin 1 ⊕ Fin 3) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetDeriv μ ((X ν : SpaceTimeAlgebra) • z) =
      (if μ = ν then z else 0) + (X ν : SpaceTimeAlgebra) • jetDeriv μ z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    rw [smul_add, map_add, ha, hb, map_add, smul_add]
    split_ifs <;> abel
  | tmul f v =>
    rw [TensorProduct.smul_tmul', jetDeriv_tmul, jetDeriv_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      TensorProduct.add_tmul]
    split_ifs with h
    · subst h
      rw [pderiv_X_self, mul_one, add_comm]
    · rw [pderiv_X_of_ne (Ne.symm h), mul_zero, TensorProduct.zero_tmul, add_zero, zero_add]

/-- The Euler operator `E = ∑_ρ x_ρ ∂_ρ` multiplies the base-point derivative along `s` by the
  order `|s|` of `s`. -/
lemma jetDerivValue_euler (s : Multiset (Fin 1 ⊕ Fin 3)) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetDerivValue s (∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ z) =
      (s.card : ℂ) • jetDerivValue s z := by
  induction s using Multiset.induction_on generalizing z with
  | empty => simp [map_sum, jetEval_smul]
  | cons μ s ih =>
    have hcomm (ρ : Fin 1 ⊕ Fin 3) : jetDeriv μ (jetDeriv ρ z) = jetDeriv ρ (jetDeriv μ z) :=
      LinearMap.congr_fun (jetDeriv_comm μ ρ) z
    rw [jetDerivValue_cons, jetDerivValue_cons, map_sum]
    simp only [jetDeriv_X_smul, hcomm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, map_add, ih, Multiset.card_cons, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

/-- The derivative of a radial combination, `∂_μ (∑_ν x_ν F_ν) = F_μ + ∑_ν x_ν ∂_μ F_ν`. -/
lemma jetDeriv_sum_X_smul (μ : Fin 1 ⊕ Fin 3) (F : Fin 1 ⊕ Fin 3 → SpaceTimeAlgebra ⊗[ℂ] V) :
    jetDeriv μ (∑ ν, (X ν : SpaceTimeAlgebra) • F ν) =
      F μ + ∑ ν, (X ν : SpaceTimeAlgebra) • jetDeriv μ (F ν) := by
  simp only [map_sum, jetDeriv_X_smul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- The derivative `∂_μ` and the Euler operator commute up to `∂_μ` itself,
  `∂_μ (E z) = E (∂_μ z) + ∂_μ z`. -/
lemma jetDeriv_euler (μ : Fin 1 ⊕ Fin 3) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetDeriv μ (∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ z) =
      ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ (jetDeriv μ z) + jetDeriv μ z := by
  rw [jetDeriv_sum_X_smul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h := LinearMap.congr_fun (jetDeriv_comm μ ρ) z
  simp only [LinearMap.comp_apply] at h
  rw [h]

end Euler

/-!

## F. Jets valued in an algebra

The jets of a field valued in a complex algebra `E` form the algebra `SpaceTimeAlgebra ⊗[ℂ] E`.
The formal derivatives are derivations of it, evaluation at the base point is multiplicative,
and the base-point derivatives of a product obey the Leibniz rule. When `E` is
finite-dimensional, the radial system `E T = R T` has a solution with `T(0) = 1`, and solutions
of the homogeneous radial systems vanish.

-/

section AlgebraValued

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The formal derivatives are derivations of the algebra of `A`-valued jets. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : SpaceTimeAlgebra ⊗[ℂ] A) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    abel
  | tmul f a =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd =>
      simp only [mul_add, map_add, hc, hd]
      abel
    | tmul g b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, jetDeriv_tmul, jetDeriv_tmul, jetDeriv_tmul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul, TensorProduct.add_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm g,
        add_comm]

/-- Evaluation at the base point is multiplicative on `A`-valued jets. -/
lemma jetEval_mul (x y : SpaceTimeAlgebra ⊗[ℂ] A) : jetEval (x * y) = jetEval x * jetEval y := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
  | tmul f a =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => rw [mul_add, map_add, hc, hd, map_add, mul_add]
    | tmul g b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, jetEval_tmul, jetEval_tmul, jetEval_tmul, map_mul,
        smul_mul_smul_comm]

@[simp]
lemma jetEval_one : jetEval (1 : SpaceTimeAlgebra ⊗[ℂ] A) = 1 := by
  rw [Algebra.TensorProduct.one_def, jetEval_tmul, map_one, one_smul]

/-- The Leibniz rule for the base-point derivatives of a product of `A`-valued jets. The
  derivative along `s` of `x y` is the sum over the splittings `s = t₁ + t₂` of the products of
  the derivatives along `t₁` and `t₂`. -/
lemma jetDerivValue_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (x y : SpaceTimeAlgebra ⊗[ℂ] A) :
    jetDerivValue s (x * y) =
      (s.antidiagonal.map fun p => jetDerivValue p.1 x * jetDerivValue p.2 y).sum := by
  induction s using Multiset.induction_on generalizing x y with
  | empty => simp [Multiset.antidiagonal_zero, jetEval_mul]
  | cons μ s ih =>
    rw [jetDerivValue_cons, jetDeriv_mul, map_add, ih, ih, Multiset.antidiagonal_cons,
      Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_map, add_comm]
    simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, jetDerivValue_cons]

/-- The Leibniz rule for the base-point derivatives of a commutator of `A`-valued jets, which
  are sums of commutators of base-point derivatives. -/
lemma jetDerivValue_commutator (s : Multiset (Fin 1 ⊕ Fin 3)) (x y : SpaceTimeAlgebra ⊗[ℂ] A) :
    jetDerivValue s (x * y - y * x) = (s.antidiagonal.map fun p =>
      jetDerivValue p.1 x * jetDerivValue p.2 y -
        jetDerivValue p.2 y * jetDerivValue p.1 x).sum := by
  have h2 := jetDerivValue_mul s y x
  rw [← Multiset.map_swap_antidiagonal s, Multiset.map_map] at h2
  rw [map_sub, jetDerivValue_mul, h2, ← Multiset.sum_map_sub]
  rfl

/-- The base-point derivatives of a jet times a constant. -/
lemma jetDerivValue_mul_jetOfConstant (s : Multiset (Fin 1 ⊕ Fin 3)) (x : SpaceTimeAlgebra ⊗[ℂ] A)
    (a : A) : jetDerivValue s (x * jetOfConstant a) = jetDerivValue s x * a := by
  induction x using TensorProduct.inductionOn with
  | add b c hb hc => rw [add_mul, map_add, hb, hc, map_add, add_mul]
  | tmul f b =>
    rw [jetOfConstant_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, jetDerivValue_tmul,
      jetDerivValue_tmul, smul_mul_assoc]

/-- The base-point derivative of `R z` along `s` vanishes when `R` vanishes at the base point and
  the base-point derivatives of `z` of lower order vanish. -/
lemma jetDerivValue_mul_eq_zero {R z : SpaceTimeAlgebra ⊗[ℂ] A} (hR : jetEval R = 0)
    {s : Multiset (Fin 1 ⊕ Fin 3)} (hz : ∀ t : Multiset (Fin 1 ⊕ Fin 3), t.card < s.card →
      jetDerivValue t z = 0) : jetDerivValue s (R * z) = 0 := by
  rw [jetDerivValue_mul]
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  rcases eq_or_ne p.1 0 with h1 | h1
  · rw [h1, jetDerivValue_zero, hR, zero_mul]
  · have hc : p.2.card < s.card := by
      rw [← Multiset.mem_antidiagonal.mp hp, Multiset.card_add]
      have := Multiset.card_pos.mpr h1
      omega
    rw [hz _ hc, mul_zero]

variable [FiniteDimensional ℂ A]

/-- The vanishing principle for the Euler operator. An `A`-valued jet `z` vanishing at the base
  point with `E z = R z`, for `R` vanishing at the base point, is zero. -/
lemma eq_zero_of_euler_eq_mul {R z : SpaceTimeAlgebra ⊗[ℂ] A} (hR : jetEval R = 0)
    (h0 : jetEval z = 0) (h : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ z = R * z) : z = 0 := by
  refine jet_ext_of_jetDerivValue fun s => ?_
  rw [map_zero]
  induction hs : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  rcases eq_or_ne s 0 with rfl | hs0
  · rwa [jetDerivValue_zero]
  · have hE := congrArg (jetDerivValue s) h
    rw [jetDerivValue_euler, jetDerivValue_mul_eq_zero hR fun t ht => ih _ (hs ▸ ht) t rfl] at hE
    exact (smul_eq_zero.mp hE).resolve_left (by simpa [Multiset.card_eq_zero] using hs0)

/-- The vanishing principle for the shifted Euler operator. An `A`-valued jet `z` with
  `E z + z = R z`, for `R` vanishing at the base point, is zero. -/
lemma eq_zero_of_euler_add_eq_mul {R z : SpaceTimeAlgebra ⊗[ℂ] A} (hR : jetEval R = 0)
    (h : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ z + z = R * z) : z = 0 := by
  refine jet_ext_of_jetDerivValue fun s => ?_
  rw [map_zero]
  induction hs : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  have hE := congrArg (jetDerivValue s) h
  rw [map_add, jetDerivValue_euler, jetDerivValue_mul_eq_zero hR fun t ht => ih _ (hs ▸ ht) t rfl]
    at hE
  have hE' : ((s.card : ℂ) + 1) • jetDerivValue s z = 0 := by rw [add_smul, one_smul]; exact hE
  exact (smul_eq_zero.mp hE').resolve_left (Nat.cast_add_one_ne_zero s.card)

/-- The radial (Euler) transport. For an `A`-valued jet `R` vanishing at the base point, the
  radial system `E T = R T` has a solution with `T(0) = 1`. Its base-point derivatives are
  fixed order by order, the derivative along `s ≠ 0` being `1/|s|` times the sum over the
  splittings `s = t₁ + t₂` of `(∂^{t₁} R)(0) (∂^{t₂} T)(0)`, which involves only lower orders of
  `T`. -/
lemma exists_euler_eq_mul (R : SpaceTimeAlgebra ⊗[ℂ] A) (hR : jetEval R = 0) :
    ∃ T : SpaceTimeAlgebra ⊗[ℂ] A, jetEval T = 1 ∧
      ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ T = R * T := by
  classical
  set Φ : (Multiset (Fin 1 ⊕ Fin 3) → A) → Multiset (Fin 1 ⊕ Fin 3) → A := fun c s =>
    if s = 0 then 1 else
      ((s.card : ℂ)⁻¹) • (s.antidiagonal.map fun p => jetDerivValue p.1 R * c p.2).sum with hΦ
  -- `Φ c s` only depends on the values of `c` of lower order.
  have hlow (a b : Multiset (Fin 1 ⊕ Fin 3) → A) (s : Multiset (Fin 1 ⊕ Fin 3))
      (h : ∀ t : Multiset (Fin 1 ⊕ Fin 3), t.card < s.card → a t = b t) : Φ a s = Φ b s := by
    simp only [hΦ]
    split_ifs
    · rfl
    · congr 2
      refine Multiset.map_congr rfl fun p hp => ?_
      rcases eq_or_ne p.1 0 with h1 | h1
      · rw [h1, jetDerivValue_zero, hR, zero_mul, zero_mul]
      · have hc : p.2.card < s.card := by
          rw [← Multiset.mem_antidiagonal.mp hp, Multiset.card_add]
          have := Multiset.card_pos.mpr h1
          omega
        rw [h _ hc]
  set c : Multiset (Fin 1 ⊕ Fin 3) → A := fun s => Φ^[s.card + 1] (fun _ => 0) s with hc
  have hmain : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)), s.card = n → ∀ k, n < k →
      Φ^[k] (fun _ => 0) s = Φ c s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s hs k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply']
    refine hlow _ _ s fun t ht => ?_
    rw [ih t.card (hs ▸ ht) t rfl k (by omega),
      show c t = Φ^[t.card + 1] (fun _ => 0) t from rfl,
      ih t.card (hs ▸ ht) t rfl (t.card + 1) (by omega)]
  have hfix (s : Multiset (Fin 1 ⊕ Fin 3)) : c s = Φ c s := hmain _ s rfl _ (Nat.lt_succ_self _)
  refine ⟨ofJetDerivValues c, ?_, jet_ext_of_jetDerivValue fun s => ?_⟩
  · rw [← jetDerivValue_zero, jetDerivValue_ofJetDerivValues, hfix]
    simp [hΦ]
  · rw [jetDerivValue_euler, jetDerivValue_ofJetDerivValues, jetDerivValue_mul]
    simp only [jetDerivValue_ofJetDerivValues]
    rcases eq_or_ne s 0 with rfl | hs
    · simp [Multiset.antidiagonal_zero, hR]
    · rw [hfix s]
      simp only [hΦ, hs, ↓reduceIte, smul_smul]
      rw [mul_inv_cancel₀ (by simpa [Multiset.card_eq_zero] using hs), one_smul]

end AlgebraValued

/-!

## G. Flat connections on jets

A family `Ω_μ` of `A`-valued jets is flat when `∂_μ Ω_ν − ∂_ν Ω_μ = Ω_μ Ω_ν − Ω_ν Ω_μ`. The
system `∂_μ T = Ω_μ T` then has a unique solution with any prescribed value: the radial
transport of `R = ∑_μ x_μ Ω_μ` solves its radial combination, and flatness makes the defect
`∂_μ T − Ω_μ T` solve `E D + D = R D`, so vanish.

-/

section Flat

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The Euler operator is a derivation of the algebra of `A`-valued jets. -/
lemma euler_mul (x y : SpaceTimeAlgebra ⊗[ℂ] A) :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ (x * y) =
      (∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ x) * y +
        x * ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ y := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [jetDeriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]

/-- The derivative of a conjugation defect `a J − J b`, for `J` with `∂_μ J = Ω J` and `a`
  with `∂_μ a = a' + [Ω, a]`, is `(a' J − J ∂_μ b) + Ω (a J − J b)`. -/
lemma jetDeriv_mul_sub_mul {a a' b J Ω : SpaceTimeAlgebra ⊗[ℂ] A} (μ : Fin 1 ⊕ Fin 3)
    (ha : jetDeriv μ a = a' + (Ω * a - a * Ω)) (hJ : jetDeriv μ J = Ω * J) :
    jetDeriv μ (a * J - J * b) = (a' * J - J * jetDeriv μ b) + Ω * (a * J - J * b) := by
  rw [map_sub, jetDeriv_mul, jetDeriv_mul, ha, hJ]
  simp only [add_mul, sub_mul, mul_sub, mul_assoc]
  abel

variable [FiniteDimensional ℂ A] (Ω : Fin 1 ⊕ Fin 3 → SpaceTimeAlgebra ⊗[ℂ] A)

/-- The radial transport solves every equation `∂_μ T = Ω_μ T` of a flat family, not only
  their radial combination. -/
lemma jetDeriv_eq_mul_of_euler
    (hΩ : ∀ μ ν, jetDeriv μ (Ω ν) - jetDeriv ν (Ω μ) = Ω μ * Ω ν - Ω ν * Ω μ)
    {T : SpaceTimeAlgebra ⊗[ℂ] A}
    (hT : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ T =
      (∑ ν, (X ν : SpaceTimeAlgebra) • Ω ν) * T) (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv μ T = Ω μ * T := by
  set R := ∑ ν, (X ν : SpaceTimeAlgebra) • Ω ν with hRdef
  have hR0 : jetEval R = 0 := by simp [hRdef, map_sum, jetEval_smul]
  -- The Euler operator on `∂_μ T` and on `Ω_μ T`.
  have hE1 : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ (jetDeriv μ T) =
      (Ω μ + ∑ ν, (X ν : SpaceTimeAlgebra) • jetDeriv μ (Ω ν)) * T + R * jetDeriv μ T -
        jetDeriv μ T := by
    have h := jetDeriv_euler μ T
    rw [hT, jetDeriv_mul, hRdef, jetDeriv_sum_X_smul] at h
    rw [eq_sub_iff_add_eq]
    exact h.symm
  have hE2 : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ (Ω μ * T) =
      (∑ ν, (X ν : SpaceTimeAlgebra) • jetDeriv ν (Ω μ)) * T + Ω μ * (R * T) := by
    rw [euler_mul, hT]
  -- The flatness, contracted with `x_ν`.
  have hflat : ∑ ν, (X ν : SpaceTimeAlgebra) • jetDeriv μ (Ω ν) =
      ∑ ν, (X ν : SpaceTimeAlgebra) • jetDeriv ν (Ω μ) + (Ω μ * R - R * Ω μ) := by
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, hRdef, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
    exact (smul_sub _ _ _).symm.trans ((congrArg _ (hΩ μ ν)).trans (smul_sub _ _ _))
  have hD : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ (jetDeriv μ T - Ω μ * T) +
      (jetDeriv μ T - Ω μ * T) = R * (jetDeriv μ T - Ω μ * T) := by
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib]
    rw [hE1, hE2, hflat]
    simp only [add_mul, sub_mul, mul_sub, mul_assoc]
    abel
  exact sub_eq_zero.mp (eq_zero_of_euler_add_eq_mul hR0 hD)

/-- A flat family `Ω_μ` of `A`-valued jets has, for every `a`, a solution of
  `∂_μ T = Ω_μ T` with value `a`, the radial transport of `∑_μ x_μ Ω_μ` times the constant
  `a`. -/
lemma exists_jetDeriv_eq_mul
    (hΩ : ∀ μ ν, jetDeriv μ (Ω ν) - jetDeriv ν (Ω μ) = Ω μ * Ω ν - Ω ν * Ω μ) (a : A) :
    ∃ T : SpaceTimeAlgebra ⊗[ℂ] A, jetEval T = a ∧ ∀ μ, jetDeriv μ T = Ω μ * T := by
  obtain ⟨T, hT1, hT⟩ := exists_euler_eq_mul (∑ ν, (X ν : SpaceTimeAlgebra) • Ω ν)
    (by simp [map_sum, jetEval_smul])
  refine ⟨T * jetOfConstant a, by rw [jetEval_mul, hT1, one_mul, jetEval_jetOfConstant],
    fun μ => ?_⟩
  rw [jetDeriv_mul, jetDeriv_eq_mul_of_euler Ω hΩ hT μ, mul_assoc, jetOfConstant_apply,
    jetDeriv_tmul, show (1 : SpaceTimeAlgebra) = MvPowerSeries.C 1 from (map_one _).symm,
    pderiv_C, TensorProduct.zero_tmul, mul_zero, add_zero]

/-- A solution of `∂_μ T = Ω_μ T` is determined by its value, since the difference of two solutions
  vanishes at the base point and solves the radial system `E D = R D`. -/
lemma eq_of_jetDeriv_eq_mul {Y Z : SpaceTimeAlgebra ⊗[ℂ] A}
    (hY : ∀ μ, jetDeriv μ Y = Ω μ * Y) (hZ : ∀ μ, jetDeriv μ Z = Ω μ * Z)
    (h0 : jetEval Y = jetEval Z) : Y = Z := by
  have hE : ∑ ρ, (X ρ : SpaceTimeAlgebra) • jetDeriv ρ (Y - Z) =
      (∑ ν, (X ν : SpaceTimeAlgebra) • Ω ν) * (Y - Z) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_sub, hY, hZ, ← mul_sub, smul_mul_assoc]
  exact sub_eq_zero.mp (eq_zero_of_euler_eq_mul (by simp [map_sum, jetEval_smul])
    (by rw [map_sub, h0, sub_self]) hE)

/-- A family `F i` of `A`-valued jets vanishing at the base point, whose derivatives are
  `∂_μ F i = F (d_μ i) + Ω_μ F i`, vanishes, since its base-point derivatives vanish by induction on
  their order. -/
lemma eq_zero_of_jetDeriv_eq_add_mul {ι : Type} (F : ι → SpaceTimeAlgebra ⊗[ℂ] A)
    (d : Fin 1 ⊕ Fin 3 → ι → ι) (hF : ∀ μ i, jetDeriv μ (F i) = F (d μ i) + Ω μ * F i)
    (h0 : ∀ i, jetEval (F i) = 0) (i : ι) : F i = 0 := by
  suffices h : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)), s.card = n → ∀ i,
      jetDerivValue s (F i) = 0 from
    jet_ext_of_jetDerivValue fun s => by rw [h _ s rfl i, map_zero]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs i
  induction s using Multiset.induction_on with
  | empty => rw [jetDerivValue_zero]; exact h0 i
  | cons μ t _ =>
    rw [Multiset.card_cons] at hs
    rw [jetDerivValue_cons, hF, map_add, ih t.card (by omega) t rfl _, zero_add, jetDerivValue_mul]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
    have hle : q.2.card ≤ t.card := by
      rw [← Multiset.mem_antidiagonal.mp hq, Multiset.card_add]
      omega
    rw [ih q.2.card (by omega) q.2 rfl i, mul_zero]

end Flat
