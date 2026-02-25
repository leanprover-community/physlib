/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Slices of space

## i. Overview

In this module we will define the equivalence between `Space d.succ` and `ℝ × Space d` which
extracts the `i`th coordinate on `Space d.succ`.

## ii. Key results

- `slice` : The continuous linear equivalence between `Space d.succ` and `ℝ × Space d` extracting
  the `i`th coordinate.

## iii. Table of contents

- A. Slicing spaces
  - A.1. Basic applications of the slicing map
  - A.2. Slice as a measurable embedding
  - A.3. The norm of the slice map
  - A.4. Derivative of the slice map
  - A.5. Basis in terms of slices

## iv. References

- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/API.20around.20.60Space.20.28d1.20.2B.20d2.29.60.20to.20.60Space.20d1.20x.20Space.20d2.60/with/556754634

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. Slicing spaces

-/

/-- The linear equivalence between `Space d.succ` and `ℝ × Space d`
  extracting the `i`th coordinate. -/
def slice {d} (i : Fin d.succ) : Space d.succ ≃L[ℝ] ℝ × Space d where
  toFun x := ⟨x i, ⟨fun j => x (Fin.succAbove i j)⟩⟩
  invFun p := ⟨fun j => Fin.insertNthEquiv (fun _ => ℝ) i (p.fst, p.snd) j⟩
  map_add' x y := by
    simp only [Nat.succ_eq_add_one, Prod.mk_add_mk, Prod.mk.injEq]
    apply And.intro
    · simp
    · ext j
      simp
  map_smul' c x := by
    simp only [Nat.succ_eq_add_one, smul_eq_mul, RingHom.id_apply, Prod.smul_mk,
      Prod.mk.injEq]
    apply And.intro
    · simp
    · ext j
      simp
  left_inv p := by
    simp only [Nat.succ_eq_add_one, Fin.insertNthEquiv_apply]
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp
    · simp only [Fin.insertNth_apply_succAbove]
  right_inv p := by
    match p with
    | (p1, p2) =>
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.comp
    · fun_prop
    apply continuous_pi
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp
      fun_prop
    · simp
      fun_prop

/-!

### A.1. Basic applications of the slicing map

-/

lemma slice_symm_apply {d : ℕ} (i : Fin d.succ) (r : ℝ) (x : Space d) :
    (slice i).symm (r, x) = fun j =>
      Fin.insertNthEquiv (fun _ => ℝ) i (r, x) j := by rfl

@[simp]
lemma slice_symm_apply_self {d : ℕ} (i : Fin d.succ) (r : ℝ) (x : Space d) :
    (slice i).symm (r, x) i = r := by
  simp [slice_symm_apply]

@[simp]
lemma slice_symm_apply_succAbove {d : ℕ} (i : Fin d.succ) (r : ℝ) (x : Space d) (j : Fin d) :
    (slice i).symm (r, x) (Fin.succAbove i j) = x j := by
  simp [slice_symm_apply]

/-!

### A.2. Slice as a measurable embedding

-/

lemma slice_symm_measurableEmbedding {d : ℕ} (i : Fin d.succ) :
    MeasurableEmbedding (slice i).symm := by
  change MeasurableEmbedding (fun (p : ℝ × Space d) => (Space.equivPi d.succ).symm
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm (p.fst, p.snd)))
  apply MeasurableEmbedding.comp
  · apply Measurable.measurableEmbedding
    · fun_prop
    · exact ContinuousLinearEquiv.injective (equivPi d.succ).symm
  apply MeasurableEmbedding.comp
  · exact MeasurableEquiv.measurableEmbedding (MeasurableEquiv.piFinSuccAbove (fun x => ℝ) i).symm
  · apply Measurable.measurableEmbedding
    · fun_prop
    · intro a b h
      match a, b with
      | (r1, x1), (r2, x2) =>
      simp_all
/-!

### A.3. The norm of the slice map

-/

lemma norm_slice_symm_eq {d : ℕ} (i : Fin d.succ) (r : ℝ) (x : Space d) :
    ‖(slice i).symm (r, x)‖ = √(‖r‖ ^ 2 + ‖x‖ ^ 2) := by
  simp [Nat.succ_eq_add_one, norm_eq]
  congr
  rw [Fin.sum_univ_succAbove _ i]
  simp [slice_symm_apply_succAbove]
  refine Eq.symm (Real.sq_sqrt ?_)
  positivity

lemma abs_right_le_norm_slice_symm {d : ℕ} (i : Fin d.succ) (r : ℝ) (x : Space d) :
    |r| ≤ ‖(slice i).symm (r, x)‖ := by
  rw [norm_slice_symm_eq]
  refine (le_sqrt (by positivity) (by positivity)).mpr ?_
  simp

@[simp]
lemma norm_left_le_norm_slice_symm {d : ℕ} (i : Fin d.succ) (r : ℝ) (x : Space d) :
    ‖x‖ ≤ ‖(slice i).symm (r, x)‖ := by
  rw [norm_slice_symm_eq]
  refine (le_sqrt (by positivity) (by positivity)).mpr ?_
  simp only [norm_eq_abs, sq_abs, le_add_iff_nonneg_left]
  positivity

/-!

### A.4. Derivative of the slice map

-/

@[simp]
lemma fderiv_slice_symm {d : ℕ} (i : Fin d.succ) (p1 : ℝ × Space d) :
    fderiv ℝ (slice i).symm p1 = (slice i).symm := by
  rw [ContinuousLinearEquiv.fderiv]

lemma fderiv_slice_symm_left_apply {d : ℕ} (i : Fin d.succ) (x : Space d) (r1 r2 : ℝ) :
    (fderiv ℝ (fun r => (slice i).symm (r, x))) r1 r2 = (slice i).symm (r2, 0) := by
  rw [fderiv_comp', DifferentiableAt.fderiv_prodMk (by fun_prop)]
  simp only [Nat.succ_eq_add_one, fderiv_slice_symm, fderiv_id', fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.zero_apply]
  repeat' fun_prop

@[simp]
lemma fderiv_slice_symm_right_apply {d : ℕ} (i : Fin d.succ) (r : ℝ)
    (x1 x2 : Space d) :
    (fderiv ℝ (fun x => (slice i).symm (r, x))) x1 x2 = (slice i).symm (0, x2) := by
  rw [fderiv_comp', DifferentiableAt.fderiv_prodMk (by fun_prop)]
  simp only [Nat.succ_eq_add_one, fderiv_slice_symm, fderiv_fun_const, Pi.zero_apply, fderiv_id',
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id',
    id_eq]
  repeat' fun_prop

lemma fderiv_fun_slice_symm_right_apply {d : ℕ} (i : Fin d.succ) (r : ℝ)
    (x1 x2 : Space d) (f : Space d.succ → F) (hf : DifferentiableAt ℝ f ((slice i).symm (r, x1))) :
    (fderiv ℝ (fun x => f ((slice i).symm (r, x)))) x1 x2 =
    fderiv ℝ f ((slice i).symm (r, x1)) ((slice i).symm (0, x2)) := by
  rw [fderiv_comp' _ _ (by fun_prop)]
  simp only [Nat.succ_eq_add_one, ContinuousLinearMap.coe_comp', Function.comp_apply,
    fderiv_slice_symm_right_apply]
  fun_prop

lemma fderiv_fun_slice_symm_left_apply {d : ℕ} (i : Fin d.succ) (r1 r2 : ℝ)
    (x : Space d) (f : Space d.succ → F) (hf : DifferentiableAt ℝ f ((slice i).symm (r1, x))) :
    (fderiv ℝ (fun r => f ((slice i).symm (r, x)))) r1 r2 =
    fderiv ℝ f ((slice i).symm (r1, x)) ((slice i).symm (r2, 0)) := by
  rw [fderiv_comp' _ _ (by fun_prop)]
  simp only [Nat.succ_eq_add_one, ContinuousLinearMap.coe_comp', Function.comp_apply,
    fderiv_slice_symm_left_apply]
  fun_prop

/-!

### A.5. Basis in terms of slices

-/

lemma basis_self_eq_slice {d : ℕ} (i : Fin d.succ) :
    basis i = (slice i).symm (1, 0) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [slice_symm_apply_self]
  · simp [basis_apply]

@[simp]
lemma slice_basis_self {d : ℕ} (i : Fin d.succ) :
    slice i (basis i) = (1, 0) := by
  rw [basis_self_eq_slice]
  simp

lemma basis_succAbove_eq_slice {d : ℕ} (i : Fin d.succ) (j : Fin d) :
    basis (Fin.succAbove i j) = (slice i).symm (0, basis j) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · simp [basis_apply, slice_symm_apply_self]
  · simp [basis_apply, slice_symm_apply_succAbove]

@[simp]
lemma slice_basis_succAbove {d : ℕ} (i : Fin d.succ) (j : Fin d) :
    slice i (basis (Fin.succAbove i j)) = (0, basis j) := by
  rw [basis_succAbove_eq_slice]
  simp

/-!

### A.6. Measures

-/

lemma volume_map_slice_eq_prod {d : ℕ} (i : Fin d.succ) :
    MeasureTheory.Measure.map (slice i) volume = volume.prod volume := by
  have h1 : volume (α := ℝ) = (OrthonormalBasis.singleton (Fin 1) ℝ).toBasis.addHaar :=
     (OrthonormalBasis.addHaar_eq_volume _).symm
  rw [volume_eq_addHaar, Module.Basis.map_addHaar, volume_eq_addHaar, h1,
    ← Module.Basis.prod_addHaar]
  let e : Fin 1 ⊕ Fin d →  Fin d.succ := fun x => match x with
      | Sum.inl 0 => i
      | Sum.inr j => Fin.succAbove i j
  have e_injective : Function.Injective e := by
    intro x y h
    match x, y with
    | Sum.inl 0, Sum.inl 0 => rfl
    | Sum.inl 0, Sum.inr j => simp [e] at h
    | Sum.inr j, Sum.inl 0 =>simp [e] at h
    | Sum.inr j1, Sum.inr j2 => simp [e] at h; simp [h]
  have e_surjective : Function.Surjective e := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, h⟩
    · use Sum.inl 0
      simp [e, h]
    · use Sum.inr k
      simp [e, h]
  have e_bijective : Function.Bijective e := ⟨e_injective, e_surjective⟩
  let eEquiv : Fin 1 ⊕ Fin d ≃ Fin d.succ := Equiv.ofBijective e e_bijective
  let b' : Module.Basis (Fin (d.succ)) ℝ (ℝ × Space d) :=
    Module.Basis.reindex
    ((OrthonormalBasis.singleton (Fin 1) ℝ).toBasis.prod basis.toBasis) eEquiv
  trans b'.addHaar
  · congr
    ext1 j
    simp [b']
    obtain ⟨k, rfl⟩ := eEquiv.surjective j
    simp [eEquiv]
    match k with
    | Sum.inl 0 =>
      simp [e]
    | Sum.inr j =>
      simp [e]
  simp [b']



end Space
