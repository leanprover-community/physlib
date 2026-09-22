/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Rotations
public import Physlib.Relativity.SpeedOfLight
public import Physlib.SpaceAndTime.Space.EuclideanGroup.Action
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Physlib.SpaceAndTime.Time.InnerProductSpace
public import Physlib.Meta.Informal.Basic
/-!
# Spacetime

## i. Overview

In this file we define the type `SpaceTime d` which corresponds to `d+1` dimensional
spacetime. This is equipped with an instance of the action of a Lorentz group,
corresponding to Minkowski-spacetime.

It is defined through `Lorentz.Vector d`, and carries the tensorial instance,
allowing it to be used in tensorial expressions.

## ii. Key results

- `SpaceTime d` : The type corresponding to `d+1` dimensional spacetime.
- `space_equivariant` : Spatial projection intertwines the Lorentz and Euclidean actions
  of the same rotation about the coordinate origin.
- `toTimeAndSpace` : A continuous linear equivalence between `SpaceTime d`
  and `Time × Space d`.

## iii. Table of contents

- A. The definition of `SpaceTime d`
- C. Continuous linear map to coordinates
- D. Measures on `SpaceTime d`
  - D.1. Instance of a measurable space
  - D.2. Instance of a borel space
  - D.4. Instance of a measure space
  - D.5. Volume measure is positive on non-empty open sets
  - D.6. Volume measure is a finite measure on compact sets
  - D.7. Volume measure is an additive Haar measure
- B. Maps to and from `Space` and `Time`
  - B.1. Linear map to `Space d`
    - B.1.1. Explicit expansion of map to space
    - B.1.2. Equivariance of the to space under rotations
  - B.2. Linear map to `Time`
    - B.2.1. Explicit expansion of map to time in terms of coordinates
  - B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`
    - B.3.1. Derivative of `toTimeAndSpace`
    - B.3.2. Derivative of the inverse of `toTimeAndSpace`
    - B.3.3. `toTimeAndSpace` acting on spatial basis vectors
    - B.3.4. `toTimeAndSpace` acting on the temporal basis vectors
  - B.4. Time space basis
    - B.4.1. Elements of the basis
    - B.4.2. Equivalence adjusting time basis vector
    - B.4.3. Determinant of the equivalence
    - B.4.4. Time space basis expressed in terms of the Lorentz basis
    - B.4.5. The additive Haar measure associated to the time space basis
  - B.5. Integrals over `SpaceTime d`
    - B.5.1. Measure preserving property of `toTimeAndSpace.symm`
    - B.5.2. Integrals over `SpaceTime d` expressed as integrals over `Time` and `Space d`

## iv. References

* None.
-/

@[expose] public section

noncomputable section

/-!

## A. The definition of `SpaceTime d`

-/

TODO "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- `SpaceTime d` corresponds to `d+1` dimensional space-time.
  This is equipped with an instance of the action of a Lorentz group,
  corresponding to Minkowski-spacetime. -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies

/-!

## C. Continuous linear map to coordinates

-/

/-- For a given `μ : Fin (1 + d)` `coord μ p` is the coordinate of
  `p` in the direction `μ`.

  This is denoted `𝔁 μ p`, where `𝔁` is typed with `\MCx`. -/
def coord {d : ℕ} (μ : Fin (1 + d)) : SpaceTime d →ₗ[ℝ] ℝ where
  toFun x := x (finSumFinEquiv.symm μ)
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp

@[inherit_doc coord]
scoped notation "𝔁" => coord

lemma coord_apply {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    𝔁 μ y = y (finSumFinEquiv.symm μ) := by
  rfl

/-- The continuous linear map from a point in space time to one of its coordinates. -/
def coordCLM (μ : Fin 1 ⊕ Fin d) : SpaceTime d →L[ℝ] ℝ where
  toFun x := x μ
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp
  cont := by
    fun_prop

/-!

## D. Measures on `SpaceTime d`

-/
open MeasureTheory

/-!

### D.1. Instance of a measurable space

-/

instance {d : ℕ} : MeasurableSpace (SpaceTime d) := borel (SpaceTime d)

/-!

### D.2. Instance of a borel space

-/

instance {d : ℕ} : BorelSpace (SpaceTime d) where
  measurable_eq := by rfl

/-!

### D.4. Instance of a measure space

-/

instance {d : ℕ} : MeasureSpace (SpaceTime d) where
  volume := Lorentz.Vector.basis.addHaar

/-!

### D.5. Volume measure is positive on non-empty open sets

-/

instance {d : ℕ} : (volume (α := SpaceTime d)).IsOpenPosMeasure :=
  inferInstanceAs ((Lorentz.Vector.basis.addHaar).IsOpenPosMeasure)

/-!

### D.6. Volume measure is a finite measure on compact sets

-/

instance {d : ℕ} : IsFiniteMeasureOnCompacts (volume (α := SpaceTime d)) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Lorentz.Vector.basis.addHaar))

/-!

### D.7. Volume measure is an additive Haar measure

-/

instance {d : ℕ} : Measure.IsAddHaarMeasure (volume (α := SpaceTime d)) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (Lorentz.Vector.basis.addHaar))

/-!

## B. Maps to and from `Space` and `Time`

-/

/-!

### B.1. Linear map to `Space d`

-/

/-- The space part of spacetime. -/
def space {d : ℕ} : SpaceTime d →L[ℝ] Space d where
  toFun x := ⟨Lorentz.Vector.spatialPart x⟩
  map_add' x1 x2 := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  cont := by
    fun_prop

/-!

#### B.1.1. Explicit expansion of map to space

-/

lemma space_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    space f = fun i => f (Sum.inr i) := by
  funext i
  simp [space]

/-!

#### B.1.2. Equivariance of the to space under rotations

-/

/-- Spatial projection intertwines a rotation's Lorentz action on spacetime with its
Euclidean action on space, using the same special orthogonal matrix on both sides.
These are rotations about the coordinate origin; no boosts or translations are included. -/
lemma space_equivariant {d : ℕ}
    (R : Matrix.specialOrthogonalGroup (Fin d) ℝ) (x : SpaceTime d) :
    space ((LorentzGroup.ofSpecialOrthogonal R : LorentzGroup d) • x) =
      EuclideanGroup.ofRotation R • space x := by
  ext i
  rw [Lorentz.Vector.smul_eq_mulVec, EuclideanGroup.smul_apply]
  -- The Lorentz spatial block is R; the Euclidean action has zero translation.
  change (Matrix.fromBlocks 1 0 0 R.val *ᵥ x) (Sum.inr i) =
    (R.val *ᵥ (fun j => x (Sum.inr j) - 0)) i + 0
  simp [Matrix.fromBlocks_mulVec, Function.comp_def]

/-!

### B.2. Linear map to `Time`

-/

/-- The time part of spacetime. -/
def time {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d →ₗ[ℝ] Time where
  toFun x := ⟨Lorentz.Vector.timeComponent x / c⟩
  map_add' x1 x2 := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind
  map_smul' c x := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind

/-!

#### B.2.1. Explicit expansion of map to time in terms of coordinates

-/

@[simp]
lemma time_val_toCoord_symm {d : ℕ} (c : SpeedOfLight) (f : Fin 1 ⊕ Fin d → ℝ) :
    (time c f).val = f (Sum.inl 0) / c := by
  simp [time, Lorentz.Vector.timeComponent]

/-!

### B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`

-/

/-- A continuous linear equivalence between `SpaceTime d` and
  `Time × Space d`. -/
def toTimeAndSpace {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d ≃L[ℝ] Time × Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun x := (x.time c, x.space)
    invFun tx := (fun i =>
      match i with
      | Sum.inl _ => c * tx.1.val
      | Sum.inr i => tx.2 i)
    left_inv x := by
      simp only [time, LinearMap.coe_mk, AddHom.coe_mk, space]
      funext i
      match i with
      | Sum.inl 0 =>
        simp [Lorentz.Vector.timeComponent]
        field_simp
      | Sum.inr i => simp
    right_inv tx := by
      simp only [time, Lorentz.Vector.timeComponent, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
        ne_eq, SpeedOfLight.val_ne_zero, not_false_eq_true, mul_div_cancel_left₀, space,
        ContinuousLinearMap.coe_mk']
    map_add' x y := by
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · ext
        simp
      ext i
      simp
    map_smul' := by
      simp
  }

@[simp]
lemma toTimeAndSpace_symm_apply_time_space {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    (toTimeAndSpace c).symm (x.time c, x.space) = x :=
  (toTimeAndSpace c).left_inv x

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma space_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).space = s := by
  simp [space, toTimeAndSpace]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma time_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).time c = t := by
  simp [time, toTimeAndSpace]

@[simp]
lemma toTimeAndSpace_symm_apply_inl {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    (toTimeAndSpace c).symm (t, s) (Sum.inl 0) = c * t := by rfl

@[simp]
lemma toTimeAndSpace_symm_apply_inr {d : ℕ} {c : SpeedOfLight} (t : Time) (x : Space d)
    (i : Fin d) :
    (toTimeAndSpace c).symm (t, x) (Sum.inr i) = x i := by rfl
/-!

#### B.3.1. Derivative of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_fderiv {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    fderiv ℝ (toTimeAndSpace c) x = (toTimeAndSpace c).toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.2. Derivative of the inverse of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_symm_fderiv {d : ℕ} {c : SpeedOfLight} (x : Time × Space d) :
    fderiv ℝ (toTimeAndSpace c).symm x = (toTimeAndSpace c).symm.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.3. `toTimeAndSpace` acting on spatial basis vectors

-/
set_option backward.isDefEq.respectTransparency false in
lemma toTimeAndSpace_basis_inr {d : ℕ} {c : SpeedOfLight} (i : Fin d) :
    toTimeAndSpace c (Lorentz.Vector.basis (Sum.inr i))
    = (0, Space.basis i) := by
  refine Prod.ext ?_ ?_
  · simp [toTimeAndSpace, time]
  · ext j
    simp [toTimeAndSpace, space, Space.basis_apply]

/-!

#### B.3.4. `toTimeAndSpace` acting on the temporal basis vectors

-/

set_option backward.isDefEq.respectTransparency false in
lemma toTimeAndSpace_basis_inl {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (⟨1/c.val⟩, 0) := by
  refine Prod.ext ?_ ?_
  · simp [toTimeAndSpace, time]
  · ext j
    simp [toTimeAndSpace, space]

lemma toTimeAndSpace_basis_inl' {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (1/c.val) • (1, 0) := by
  rw [toTimeAndSpace_basis_inl]
  simp [Prod.ext_iff, Time.ext_iff, Time.smul_real_val, Time.one_val]

/-!

### B.4. Time space basis

-/

/-- The basis of `SpaceTime` where the first component is `(c, 0, 0, ...)` instead
of `(1, 0, 0, ....).`-/
def timeSpaceBasis {d : ℕ} (c : SpeedOfLight := 1) :
    Module.Basis (Fin 1 ⊕ Fin d) ℝ (SpaceTime d) where
  repr := (toTimeAndSpace (d := d) c).toLinearEquiv.trans <|
      (Time.basis.toBasis.prod (Space.basis (d := d)).toBasis).repr

/-!

#### B.4.1. Elements of the basis

-/

@[simp]
lemma timeSpaceBasis_apply_inl {d : ℕ} (c : SpeedOfLight) :
    timeSpaceBasis (d := d) c (Sum.inl 0) = c.val • Lorentz.Vector.basis (Sum.inl 0) := by
  simp [timeSpaceBasis]
  apply (toTimeAndSpace (d := d) c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_smul, toTimeAndSpace_basis_inl]
  ext <;> simp

@[simp]
lemma timeSpaceBasis_apply_inr {d : ℕ} (c : SpeedOfLight) (i : Fin d) :
    timeSpaceBasis (d := d) c (Sum.inr i) = Lorentz.Vector.basis (Sum.inr i) := by
  simp [timeSpaceBasis]
  apply (toTimeAndSpace (d := d) c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, toTimeAndSpace_basis_inr]

/-!

#### B.4.2. Equivalence adjusting time basis vector

-/

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence on of `SpaceTime` taking `(1, 0, 0, ...)` to
of `(c, 0, 0, ....)` and keeping all other components the same. -/
def timeSpaceBasisEquiv {d : ℕ} (c : SpeedOfLight) :
    SpaceTime d ≃L[ℝ] SpaceTime d where
  toFun x := fun μ =>
    match μ with
    | Sum.inl 0 => c.val * x (Sum.inl 0)
    | Sum.inr i => x (Sum.inr i)
  invFun x := fun μ =>
    match μ with
    | Sum.inl 0 => (1 / c.val) * x (Sum.inl 0)
    | Sum.inr i => x (Sum.inr i)
  left_inv x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      field_simp
    | Sum.inr i =>
      rfl
  right_inv x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      field_simp
    | Sum.inr i =>
      rfl
  map_add' x y := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue, Lorentz.Vector.apply_add]
      ring
    | Sum.inr i =>
      simp
  map_smul' c x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue, Lorentz.Vector.apply_smul, RingHom.id_apply]
      ring
    | Sum.inr i =>
      simp
  continuous_invFun := by
    simp only [one_div, Fin.isValue]
    apply Lorentz.Vector.continuous_of_apply
    intro μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue]
      fun_prop
    | Sum.inr i =>
      simp only
      fun_prop
  continuous_toFun := by
    apply Lorentz.Vector.continuous_of_apply
    intro μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue]
      fun_prop
    | Sum.inr i =>
      simp only
      fun_prop

/-!

#### B.4.3. Determinant of the equivalence

-/

set_option backward.isDefEq.respectTransparency false in
lemma det_timeSpaceBasisEquiv {d : ℕ} (c : SpeedOfLight) :
    (timeSpaceBasisEquiv (d := d) c).det = c.val := by
  rw [@LinearEquiv.coe_det]
  let e := toTimeAndSpace (d := d) c
  trans LinearMap.det (e.toLinearMap ∘ₗ (timeSpaceBasisEquiv (d := d) c).toLinearMap ∘ₗ
    e.symm.toLinearMap)
  · simp only [ContinuousLinearEquiv.toLinearEquiv_symm, LinearMap.det_conj]
  have h1 : e.toLinearMap ∘ₗ (timeSpaceBasisEquiv (d := d) c).toLinearMap ∘ₗ
    e.symm.toLinearMap = (c.val • LinearMap.id).prodMap LinearMap.id := by
    ext tx <;> simp [e, timeSpaceBasisEquiv, toTimeAndSpace, space]
  rw [h1, LinearMap.det_prodMap]
  simp

/-!

#### B.4.4. Time space basis expressed in terms of the Lorentz basis

-/

set_option backward.isDefEq.respectTransparency false in
lemma timeSpaceBasis_eq_map_basis {d : ℕ} (c : SpeedOfLight) :
    timeSpaceBasis (d := d) c =
    Module.Basis.map (Lorentz.Vector.basis (d := d)) (timeSpaceBasisEquiv c).toLinearEquiv := by
  ext1 μ
  match μ with
  | Sum.inl 0 =>
    simp [timeSpaceBasisEquiv]
    funext ν
    rcases ν with _ | j <;> simp [Fin.fin_one_eq_zero]
  | Sum.inr i =>
    simp [timeSpaceBasisEquiv]
    funext ν
    rcases ν with _ | j <;> simp [Fin.fin_one_eq_zero]

/-!

#### B.4.5. The additive Haar measure associated to the time space basis

-/

lemma timeSpaceBasis_addHaar {d : ℕ} (c : SpeedOfLight := 1) :
    (timeSpaceBasis (d := d) c).addHaar = (ENNReal.ofReal (c⁻¹)) • volume := by
  rw [timeSpaceBasis_eq_map_basis c, ← Module.Basis.map_addHaar]
  have h1 := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (f := (timeSpaceBasisEquiv (d := d) c).toLinearMap) (μ := Lorentz.Vector.basis.addHaar)
    (by simp [← LinearEquiv.coe_det, det_timeSpaceBasisEquiv])
  simp at h1
  rw [h1]
  simp [← LinearEquiv.coe_det, det_timeSpaceBasisEquiv]
  congr
  simp

/-!
### B.5. Integrals over `SpaceTime d`

-/

/-!

#### B.5.1. Measure preserving property of `toTimeAndSpace.symm`

-/

open MeasureTheory
lemma toTimeAndSpace_symm_measurePreserving {d : ℕ} (c : SpeedOfLight) :
    MeasurePreserving (toTimeAndSpace c).symm (volume.prod (volume (α := Space d)))
    (ENNReal.ofReal c⁻¹ • volume) := by
  refine { measurable := ?_, map_eq := ?_ }
  · fun_prop
  rw [Space.volume_eq_addHaar, Time.volume_eq_basis_addHaar, ← Module.Basis.prod_addHaar,
    Module.Basis.map_addHaar, ← timeSpaceBasis_addHaar c]
  rfl

/-!

#### B.5.2. Integrals over `SpaceTime d` expressed as integrals over `Time` and `Space d`

-/

lemma spaceTime_integral_eq_time_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M) :
    ∫ x : SpaceTime d, f x ∂(volume) =
    c.val • ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume) := by
  symm
  have h1 : ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume)
    = ∫ x : SpaceTime d, f x ∂((ENNReal.ofReal (c⁻¹)) • volume) := by
    apply MeasureTheory.MeasurePreserving.integral_comp
    · exact toTimeAndSpace_symm_measurePreserving c
    · exact (toTimeAndSpace c).symm.toHomeomorph.measurableEmbedding
  rw [h1]
  simp

lemma spaceTime_integrable_iff_space_time_integrable {M} [NormedAddCommGroup M]
    {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M) :
    Integrable f volume ↔ Integrable (f ∘ ((toTimeAndSpace c).symm)) (volume.prod volume) := by
  symm
  trans Integrable f (ENNReal.ofReal (c⁻¹) • volume); swap
  · rw [MeasureTheory.integrable_smul_measure]
    · simp
    · simp
  apply MeasureTheory.MeasurePreserving.integrable_comp_emb
  · exact toTimeAndSpace_symm_measurePreserving c
  · exact (toTimeAndSpace c).symm.toHomeomorph.measurableEmbedding

lemma spaceTime_integral_eq_time_integral_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M)
    (h : Integrable f volume) :
    ∫ x : SpaceTime d, f x =
    c.val • ∫ t : Time, ∫ x : Space d, f ((toTimeAndSpace c).symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod]
  exact (spaceTime_integrable_iff_space_time_integrable c f).mp h

lemma spaceTime_integral_eq_space_integral_time_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M)
    (h : Integrable f volume) :
    ∫ x : SpaceTime d, f x =
    c.val • ∫ x : Space d, ∫ t : Time, f ((toTimeAndSpace c).symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod_symm]
  exact (spaceTime_integrable_iff_space_time_integrable c f).mp h

end SpaceTime

end
