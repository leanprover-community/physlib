/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
/-!
# The derivative of a representation of a global gauge group

A continuous representation `ρ : G → GL(W)` of a global gauge group differentiates to a
representation `dρ` of its Lie algebra by linear maps on `W`.

## i. Overview

A continuous representation `ρ` of the global gauge group `G` on a finite-dimensional complex
normed space `W` is differentiated to the corresponding representation of the Lie algebra, which
is how gauge fields act on matter. For a generator `X` of `G` this is the derivative
`dρ(X) = d/dt ρ (exp (t X))` at `t = 0`, a linear map on `W`. The matter field `M` of a gauge
theory carries such a representation `M.rep`, and its Lie algebra representation is the
derivative of `M.rep`.

The linear maps `W →L[ℂ] W` form a Banach algebra, and the image `t ↦ ρ (exp (t X))` of a
one-parameter subgroup is a continuous one-parameter subgroup of it. So it is
`t ↦ exp (t dρ(X))`, by `OneParameterSubgroup.apply_eq_exp_smul_deriv`, and `dρ(X)` is the
only linear map with this property, by `OneParameterSubgroup.generator_unique`. The map `dρ`
is a homomorphism of Lie algebras.

* It is real-linear. Compatibility with scalars is a reparametrisation of `t`, and
  additivity follows by applying `ρ` to the Lie product formula
  `exp (t (X + Y)) = lim (exp (t X / n) exp (t Y / n)) ^ n`.
* It intertwines the adjoint actions, `dρ(g X g⁻¹) = ρ(g) dρ(X) ρ(g)⁻¹`, since `ρ` maps
  the one-parameter subgroup of `g X g⁻¹` to the conjugate of that of `X`.
* It preserves the commutator. With `g = exp (s X)`, the intertwining property reads
  `dρ(exp (s X) Y exp (−s X)) = exp (s dρ(X)) dρ(Y) exp (−s dρ(X))`. Both sides are
  differentiable in `s`, `dρ` being linear on a finite-dimensional space. Their derivatives
  at `s = 0` are `dρ(X Y − Y X)` and `dρ(X) dρ(Y) − dρ(Y) dρ(X)`.

The one-parameter subgroups `GlobalGaugeGroup.oneParameterSubgroup` and the adjoint action
`GlobalGaugeGroup.adjoint` of `G` are set up in the `LieAlgebra` directory.

## ii. Key results

- `GlobalGaugeGroup.derivRepFun` : the derivative `dρ(X)` of a representation along a
  generator.
- `GlobalGaugeGroup.derivRep` : the Lie algebra representation.
- `GlobalGaugeGroup.apply_eq_exp_derivRep` : `ρ (exp (t X)) = exp (t dρ(X))`.
- `GlobalGaugeGroup.derivRep_eq_of` : `dρ(X)` is the unique linear map with this property.
- `GlobalGaugeGroup.derivRep_adjoint` : `dρ` intertwines the adjoint actions.
- `GlobalGaugeGroup.commute_derivRep` : a linear map commuting with `ρ` commutes with `dρ`.
- `GlobalGaugeGroup.MatterField.lieAlgebraRep` : the Lie algebra representation of a matter
  field, the derivative of its representation.

## iii. Table of contents

- A. The derivative of a representation along a generator
- B. Linearity
- C. The adjoint action and the commutator
- D. The Lie algebra representation
- E. Matter fields

## iv. References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

open Matrix NormedSpace Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : G.group →ₜ* (W →L[ℂ] W)ˣ)

/-- A finite-dimensional complex normed space is complete. -/
local instance instCompleteSpaceW : CompleteSpace W := FiniteDimensional.completeSpace ℂ W

/-!

## A. The derivative of a representation along a generator

-/

/-- The derivative `dρ(X) = d/dt ρ (exp (t X))` at `t = 0` of the representation along a
  generator `X` of the global gauge group, a linear map on the target space. -/
noncomputable def derivRepFun (X : G.lieAlgebra) : W →L[ℂ] W :=
  deriv (fun t : ℝ => ((ρ (G.oneParameterSubgroup X t) : (W →L[ℂ] W)ˣ) :
    W →L[ℂ] W)) 0

/-- The representation maps the one-parameter subgroup of a generator `X` to that of its
  derivative `dρ(X)`, `ρ (exp (t X)) = exp (t dρ(X))`. -/
lemma derivRep_oneParameterSubgroup (X : G.lieAlgebra) (t : ℝ) :
    ((ρ (G.oneParameterSubgroup X t) : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) =
      exp (t • derivRepFun ρ X) :=
  OneParameterSubgroup.apply_eq_exp_smul_deriv
    ⟨fun t => ((ρ (G.oneParameterSubgroup X t) : (W →L[ℂ] W)ˣ) : W →L[ℂ] W),
      by simp, fun s t => by simp [oneParameterSubgroup_add]⟩
    (Units.continuous_val.comp ((map_continuous ρ).comp (continuous_oneParameterSubgroup X))) t

/-- The inverse of the image of a one-parameter subgroup, `ρ (exp (t X))⁻¹ = exp (−t dρ(X))`. -/
lemma derivRep_oneParameterSubgroup_inv (X : G.lieAlgebra) (t : ℝ) :
    (↑(ρ (G.oneParameterSubgroup X t) : (W →L[ℂ] W)ˣ)⁻¹ : W →L[ℂ] W) =
      exp (t • -derivRepFun ρ X) := by
  let _ : NormedAlgebra ℚ (W →L[ℂ] W) := .restrictScalars ℚ ℝ _
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [derivRep_oneParameterSubgroup, ← NormedSpace.exp_add_of_commute
    (((Commute.refl _).neg_right.smul_left t).smul_right t), smul_neg, add_neg_cancel, exp_zero]

/-- The derivative `dρ(X)` is the unique linear map `Z` with `ρ (exp (t X)) = exp (t Z)` for
  all `t`. -/
lemma derivRepFun_eq {X : G.lieAlgebra} {Z : W →L[ℂ] W}
    (hZ : ∀ t : ℝ, ((ρ (G.oneParameterSubgroup X t) : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) =
      exp (t • Z)) : derivRepFun ρ X = Z :=
  (OneParameterSubgroup.generator_unique
    ⟨fun t => ((ρ (G.oneParameterSubgroup X t) : (W →L[ℂ] W)ˣ) : W →L[ℂ] W),
      by simp, fun s t => by simp [oneParameterSubgroup_add]⟩ Z hZ).symm

/-!

## B. Linearity

-/

lemma derivRepFun_smul (r : ℝ) (X : G.lieAlgebra) :
    derivRepFun ρ (r • X) = r • derivRepFun ρ X := by
  refine derivRepFun_eq ρ fun t => ?_
  have h : G.oneParameterSubgroup (r • X) t = G.oneParameterSubgroup X (t * r) :=
    eq_oneParameterSubgroup (by rw [oneParameterSubgroup_val, Submodule.coe_smul, smul_smul])
  rw [h, derivRep_oneParameterSubgroup, smul_smul]

/-- The derivative of a representation is additive. Applying the representation to the Lie
  product formula for `exp (t (X + Y))` gives the Lie product formula for
  `exp (t dρ(X) + t dρ(Y))`. -/
lemma derivRepFun_add (X Y : G.lieAlgebra) :
    derivRepFun ρ (X + Y) = derivRepFun ρ X + derivRepFun ρ Y := by
  rcases subsingleton_or_nontrivial W with hV | hV
  · exact Subsingleton.elim _ _
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- The group is trivial, so the derivative vanishes.
    have h0 (W : G.lieAlgebra) : derivRepFun ρ W = 0 :=
      derivRepFun_eq ρ fun t => by
        rw [Subsingleton.elim (G.oneParameterSubgroup W t) 1, map_one, Units.val_one,
          smul_zero, exp_zero]
    rw [h0, h0, h0, add_zero]
  refine derivRepFun_eq ρ fun t => ?_
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : NormOneClass (Matrix κ κ ℂ) := Matrix.linfty_opNormOneClass
  set g : ℕ → G.group := fun n =>
    (G.oneParameterSubgroup X ((n : ℝ)⁻¹ * t) * G.oneParameterSubgroup Y ((n : ℝ)⁻¹ * t)) ^ n
  -- The products `g n` converge in the group to `exp (t (X + Y))`.
  have hg : Tendsto g atTop (𝓝 (G.oneParameterSubgroup (X + Y) t)) := by
    rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply]
    refine Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · rw [oneParameterSubgroup_val, Submodule.coe_add, smul_add]
      refine (tendsto_exp_mul_exp_pow (t • (X : Matrix κ κ ℂ)) (t • (Y : Matrix κ κ ℂ))).congr
        fun n => ?_
      simp [g, smul_smul]
      rfl
    · rw [oneParameterSubgroup_inv_val, Submodule.coe_add, neg_add_rev, smul_add]
      refine (tendsto_exp_mul_exp_pow (t • -(Y : Matrix κ κ ℂ))
        (t • -(X : Matrix κ κ ℂ))).congr fun n => ?_
      simp only [g, Subgroup.coe_pow, Subgroup.coe_mul, ← inv_pow, _root_.mul_inv_rev,
        Units.val_pow_eq_pow_val, Units.val_mul, oneParameterSubgroup_inv_val, smul_smul]
      rfl
  -- Their images under `ρ` converge to `ρ (exp (t (X + Y)))`, and to
  -- `exp (t dρ(X) + t dρ(Y))` by the Lie product formula.
  have h₁ := ((Units.continuous_val.comp (map_continuous ρ)).tendsto _).comp hg
  have h₂ := tendsto_exp_mul_exp_pow (t • derivRepFun ρ X) (t • derivRepFun ρ Y)
  rw [smul_add]
  refine tendsto_nhds_unique h₁ (h₂.congr fun n => ?_)
  simp [g, derivRep_oneParameterSubgroup, smul_smul]

/-- The derivative of the representation, as a real-linear map on the Lie algebra. -/
noncomputable def derivRepLinear : G.lieAlgebra →ₗ[ℝ] W →L[ℂ] W where
  toFun := derivRepFun ρ
  map_add' := derivRepFun_add ρ
  map_smul' := derivRepFun_smul ρ

/-!

## C. The adjoint action and the commutator

-/

/-- The derivative of the representation intertwines the adjoint actions,
  `dρ(g X g⁻¹) = ρ(g) dρ(X) ρ(g)⁻¹`. -/
lemma derivRepFun_adjoint (g : G.group) (X : G.lieAlgebra) :
    derivRepFun ρ (G.adjoint g X) =
      ((ρ g : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) * derivRepFun ρ X *
        (↑(ρ g : (W →L[ℂ] W)ˣ)⁻¹ : W →L[ℂ] W) := by
  let _ : NormedAlgebra ℚ (W →L[ℂ] W) := .restrictScalars ℚ ℝ _
  refine derivRepFun_eq ρ fun t => ?_
  rw [oneParameterSubgroup_adjoint, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
    derivRep_oneParameterSubgroup, ← smul_mul_assoc, ← mul_smul_comm, NormedSpace.exp_units_conj]

/-- The derivative of the representation preserves the commutator. Differentiating the
  intertwining property `dρ(exp (s X) Y exp (−s X)) = exp (s dρ(X)) dρ(Y) exp (−s dρ(X))` at
  `s = 0` gives `dρ(X Y − Y X) = dρ(X) dρ(Y) − dρ(Y) dρ(X)`. -/
lemma derivRepFun_commutator (X Y : G.lieAlgebra) :
    derivRepFun ρ ⟨X.1 * Y.1 - Y.1 * X.1, commutator_mem_lieAlgebraOfIsClosed X.2 Y.2⟩ =
      derivRepFun ρ X * derivRepFun ρ Y -
        derivRepFun ρ Y * derivRepFun ρ X := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  -- Extend the derivative to a continuous linear map on all matrices.
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (derivRepLinear ρ (G := G))
  have hLX (W : G.lieAlgebra) : L W = derivRepFun ρ W := LinearMap.congr_fun hL W
  let L' : Matrix κ κ ℂ →L[ℝ] W →L[ℂ] W :=
    ⟨L, LinearMap.continuous_of_finiteDimensional L⟩
  set ZX := derivRepFun ρ X
  set ZY := derivRepFun ρ Y
  -- The two sides of the intertwining property, as functions of `s`.
  have hc : HasDerivAt (fun s : ℝ => L (exp (s • X.1) * Y.1 * exp (s • -X.1)))
      (L (X.1 * Y.1 - Y.1 * X.1)) 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X.1 0).mul_const Y.1).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X.1) 0)
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg] at h
    rw [sub_eq_add_neg]
    exact L'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have hd : HasDerivAt (fun s : ℝ => exp (s • ZX) * ZY * exp (s • -ZX)) (ZX * ZY - ZY * ZX) 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) ZX 0).mul_const ZY).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-ZX) 0)
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg] at h
    rw [sub_eq_add_neg]
    exact h
  have hcd : (fun s : ℝ => L (exp (s • X.1) * Y.1 * exp (s • -X.1))) =
      fun s : ℝ => exp (s • ZX) * ZY * exp (s • -ZX) := by
    funext s
    have h := derivRepFun_adjoint ρ (G.oneParameterSubgroup X s) Y
    rw [derivRep_oneParameterSubgroup, derivRep_oneParameterSubgroup_inv] at h
    rw [← h, ← hLX, adjoint_val, oneParameterSubgroup_val, ← oneParameterSubgroup_inv_val]
  rw [hcd] at hc
  rw [← hLX]
  exact hc.unique hd

/-!

## D. The Lie algebra representation

-/

/-- The Lie algebra representation `dρ : 𝔤 → 𝔤𝔩(W)` of the continuous representation
  `ρ : G → GL(W)` of with `ρ (exp (t X)) = exp (t dρ(X))`. -/
noncomputable def derivRep : G.lieSubalgebra →ₗ⁅ℝ⁆ W →L[ℂ] W where
  toFun X := derivRepFun ρ ⟨X.1, X.2⟩
  map_add' X Y := derivRepFun_add ρ ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩
  map_smul' r X := derivRepFun_smul ρ r ⟨X.1, X.2⟩
  map_lie' {X Y} := by
    rw [Ring.lie_def]
    exact derivRepFun_commutator ρ ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩

/-- The representation maps the one-parameter subgroup of a generator `X` to that of `dρ(X)`,
  `ρ (exp (t X)) = exp (t dρ(X))`. -/
lemma apply_eq_exp_derivRep {X : G.lieSubalgebra} {t : ℝ} {g : G.group}
    (hg : ((g : GeneralLinearGroup κ ℂ) : Matrix κ κ ℂ) = exp (t • (X : Matrix κ κ ℂ))) :
    ((ρ g : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) = exp (t • derivRep ρ X) := by
  rw [eq_oneParameterSubgroup (X := ⟨X.1, X.2⟩) hg]
  exact derivRep_oneParameterSubgroup ρ _ t

/-- The Lie algebra representation at a generator `X` is the unique linear map `Z` with
  `ρ (exp (t X)) = exp (t Z)` for all `t`. -/
lemma derivRep_eq_of {X : G.lieSubalgebra} {Z : W →L[ℂ] W}
    (hZ : ∀ (t : ℝ) (g : G.group),
      ((g : GeneralLinearGroup κ ℂ) : Matrix κ κ ℂ) = exp (t • (X : Matrix κ κ ℂ)) →
        ((ρ g : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) = exp (t • Z)) :
    derivRep ρ X = Z :=
  derivRepFun_eq ρ fun t => hZ t _ (oneParameterSubgroup_val _ t)

/-- The Lie algebra representation intertwines the adjoint actions,
  `dρ(g X g⁻¹) = ρ(g) dρ(X) ρ(g)⁻¹`. -/
lemma derivRep_adjoint (g : G.group) (X : G.lieSubalgebra) :
    derivRep ρ ⟨(g.1 : Matrix κ κ ℂ) * X * (↑g.1⁻¹ : Matrix κ κ ℂ),
      conj_mem_lieAlgebraOfIsClosed (hH := G.isClosed) g X.2⟩ =
      ((ρ g : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) * derivRep ρ X *
        (↑(ρ g : (W →L[ℂ] W)ˣ)⁻¹ : W →L[ℂ] W) :=
  derivRepFun_adjoint ρ g ⟨X.1, X.2⟩

/-- A linear map commuting with every `ρ(g)` commutes with every `dρ(X)`. Both
  `exp (t dρ(X)) L` and `L exp (t dρ(X))` are the same function of `t`, and their derivatives at
  `t = 0` are `dρ(X) L` and `L dρ(X)`. -/
lemma commute_derivRep {L : W →L[ℂ] W}
    (hL : ∀ g, Commute ((ρ g : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) L) (X : G.lieSubalgebra) :
    Commute (derivRep ρ X) L := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (derivRep ρ X) 0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have he : (fun t : ℝ => exp (t • derivRep ρ X) * L) =
      fun t : ℝ => L * exp (t • derivRep ρ X) := funext fun t => by
    have h' := hL (G.oneParameterSubgroup ⟨X.1, X.2⟩ t)
    rw [derivRep_oneParameterSubgroup] at h'
    exact h'.eq
  have h₁ := h.mul_const L
  rw [he] at h₁
  exact h₁.unique (h.const_mul L)

namespace MatterField

variable (M : G.MatterField)

/-!

## E. Matter fields

The Lie algebra representation of a matter field is the derivative of its representation.

-/

/-- The derivative `dρ(X) = d/dt ρ (exp (t X))` at `t = 0` of the representation of a matter
  field along a generator `X` of the global gauge group. -/
noncomputable def lieAlgebraRepFun (X : G.lieAlgebra) : M.V →L[ℂ] M.V := derivRepFun M.rep X

lemma lieAlgebraRepFun_smul (r : ℝ) (X : G.lieAlgebra) :
    lieAlgebraRepFun M (r • X) = r • lieAlgebraRepFun M X :=
  derivRepFun_smul M.rep r X

lemma lieAlgebraRepFun_add (X Y : G.lieAlgebra) :
    lieAlgebraRepFun M (X + Y) = lieAlgebraRepFun M X + lieAlgebraRepFun M Y :=
  derivRepFun_add M.rep X Y

/-- The derivative of the representation, as a real-linear map on the Lie algebra. -/
noncomputable def lieAlgebraRepLinear : G.lieAlgebra →ₗ[ℝ] M.V →L[ℂ] M.V :=
  derivRepLinear M.rep

/-- The derivative of the representation intertwines the adjoint actions,
  `dρ(g X g⁻¹) = ρ(g) dρ(X) ρ(g)⁻¹`. -/
lemma lieAlgebraRepFun_adjoint (g : G.group) (X : G.lieAlgebra) :
    lieAlgebraRepFun M (G.adjoint g X) =
      ((M.rep g : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V) * lieAlgebraRepFun M X *
        (↑(M.rep g : (M.V →L[ℂ] M.V)ˣ)⁻¹ : M.V →L[ℂ] M.V) :=
  derivRepFun_adjoint M.rep g X

/-- The derivative of the representation preserves the commutator. -/
lemma lieAlgebraRepFun_commutator (X Y : G.lieAlgebra) :
    lieAlgebraRepFun M ⟨X.1 * Y.1 - Y.1 * X.1, commutator_mem_lieAlgebraOfIsClosed X.2 Y.2⟩ =
      lieAlgebraRepFun M X * lieAlgebraRepFun M Y -
        lieAlgebraRepFun M Y * lieAlgebraRepFun M X :=
  derivRepFun_commutator M.rep X Y

/-- The Lie algebra representation `dρ : 𝔤 → 𝔤𝔩(V)` of the continuous representation
  `ρ : G → GL(V)` of a matter field, with `ρ (exp (t X)) = exp (t dρ(X))`. -/
noncomputable def lieAlgebraRep : G.lieSubalgebra →ₗ⁅ℝ⁆ M.V →L[ℂ] M.V := derivRep M.rep

/-- The representation maps the one-parameter subgroup of a generator `X` to that of `dρ(X)`,
  `ρ (exp (t X)) = exp (t dρ(X))`. -/
lemma rep_eq_exp_lieAlgebraRep {X : G.lieSubalgebra} {t : ℝ} {g : G.group}
    (hg : ((g : GeneralLinearGroup κ ℂ) : Matrix κ κ ℂ) = exp (t • (X : Matrix κ κ ℂ))) :
    ((M.rep g : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V) = exp (t • lieAlgebraRep M X) :=
  apply_eq_exp_derivRep M.rep hg

/-- The Lie algebra representation at a generator `X` is the unique linear map `Z` with
  `ρ (exp (t X)) = exp (t Z)` for all `t`. -/
lemma lieAlgebraRep_eq_of {X : G.lieSubalgebra} {Z : M.V →L[ℂ] M.V}
    (hZ : ∀ (t : ℝ) (g : G.group),
      ((g : GeneralLinearGroup κ ℂ) : Matrix κ κ ℂ) = exp (t • (X : Matrix κ κ ℂ)) →
        ((M.rep g : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V) = exp (t • Z)) :
    lieAlgebraRep M X = Z :=
  derivRep_eq_of M.rep hZ

/-- A linear map commuting with the representation of every group element commutes with the
  Lie algebra representation. -/
lemma commute_lieAlgebraRep {L : M.V →L[ℂ] M.V}
    (hL : ∀ g, Commute ((M.rep g : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V) L) (X : G.lieSubalgebra) :
    Commute (lieAlgebraRep M X) L :=
  commute_derivRep M.rep hL X

end MatterField

end GlobalGaugeGroup
