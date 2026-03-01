/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Basic
/-!
# Time

## i. Overview

In this module we define the type `Time`, corresponding to time in a given
(but arbitrary) set of units, with a given (but arbitrary) choice of origin (time zero),
and a choice of orientation (i.e. a positive time direction).

We note that this is the version of time most often used in undergraduate and
non-mathematical physics.

The choice of units or origin can be made on a case-by-case basis, as
long as they are done consistently. However, since the choice of units and origin is
left implicit, Lean will not catch inconsistencies in the choice of units or origin when
working with `Time`.

For example, for the classical mechanics system corresponding to the harmonic oscillator,
one can take the origin of time to be the time at which the initial conditions are specified,
and the units can be taken as anything as long as the units chosen for time `t` and
the angular frequency `ω` are consistent.

With this notion of `Time`, becomes a 1d vector space over `ℝ` with an inner product.

Within other modules e.g. `TimeMan` and `TimeTransMan`, we define
versions of time with less choices made, and relate them to `Time` via a choice of units
or origin.

## ii. Key results

- `Time` : The type representing time with a choice of units and origin.

## iii. Table of contents

- A. The definition of `Time`
- B. Instances on Time
  - B.1. Natural numbers as elements of `Time`
  - B.2. Real numbers as elements of `Time`
  - B.3. Time is inhabited
  - B.4. The order on `Time`
  - B.5. Addition of times
  - B.6. Negation of times
  - B.7. Subtraction of times
  - B.8. Scalar multiplication of time
  - B.9. Module on `Time`
  - B.10. Norm of time
  - B.11. Inner product on `Time`
  - B.12. Decidability of `Time`
  - B.13. Measurability of `Time`
- C. Basis of `Time`
- D. Maps from `Time` to `ℝ`

## iv. References

-/

/-!

## A. The definition of `Time`

-/

/-- The type `Time` represents the time in a given (but arbitrary) set of units, and
  with a given (but arbitrary) choice of origin. -/
@[ext]
structure Time where
  /-- The underlying real number associated with a point in time. -/
  val : ℝ

namespace Time

lemma val_injective : Function.Injective val := by
  intro t1 t2 h
  ext
  exact h

/-!

## B. Instances on Time

-/

/-!

### B.1. Natural numbers as elements of `Time`

-/

instance : NatCast Time where
  natCast n := ⟨n⟩

/-- The casting of a natural number to an element of `Time`. This corresponds to a choice of
(1) zero point in time, and (2) a choice of metric on time (defining `1`). -/
instance {n : ℕ} : OfNat Time n where
  ofNat := ⟨n⟩

@[simp]
lemma natCast_val {n : ℕ} : val n = n := rfl

@[simp]
lemma natCast_zero : ((0 : ℕ) : Time) = 0 := rfl

@[simp]
lemma natCast_one : ((1 : ℕ) : Time) = 1 := rfl

@[simp]
lemma ofNat_val {n : ℕ} : val (OfNat.ofNat n : Time) = n := rfl

lemma one_ne_zero : (1 : Time) ≠ (0 : Time) := by
  by_contra h
  rw [Time.ext_iff, ofNat_val, ofNat_val] at h
  norm_cast at h

@[simp]
lemma zero_val : val 0 = 0 := by
  rw [ofNat_val]
  norm_cast

@[simp]
lemma eq_zero_iff (t : Time) : t = 0 ↔ t.val = 0 := by
  aesop

@[simp]
lemma one_val : val 1 = 1 := by
  rw [ofNat_val]
  norm_cast

@[simp]
lemma eq_one_iff (t : Time) : t = 1 ↔ t.val = 1 := by
  aesop

/-!

### B.2. Real numbers as elements of `Time`

-/

instance : Coe ℝ Time where
  coe r := ⟨r⟩

instance : Coe Time ℝ where
  coe := Time.val

lemma realCast_val {r : ℝ} : (r : Time).val = r := rfl

@[simp]
lemma realCast_of_natCast {n : ℕ} : ((n : ℝ) : Time) = n := rfl

/-!

### B.3. Time is inhabited

-/

instance : Inhabited Time where
  default := 0

@[simp]
lemma default_eq_zero : default = 0 := rfl

/-!

### B.4. The order on `Time`

-/

/-- The choice of an orientation on `Time`. -/
instance : LE Time where
  le t1 t2 := t1.val ≤ t2.val

lemma le_def (t1 t2 : Time) :
    t1 ≤ t2 ↔ t1.val ≤ t2.val := Iff.rfl

instance : PartialOrder Time where
  le_refl t := by simp [le_def]
  le_trans t1 t2 t3 := by simp [le_def]; exact le_trans
  le_antisymm t1 t2 h1 h2 := by simp_all [le_def]; ext; exact le_antisymm h1 h2

lemma lt_def (t1 t2 : Time) :
    t1 < t2 ↔ t1.val < t2.val := by
  constructor
  · intro h
    exact lt_iff_le_not_ge.mpr h
  · intro h
    apply lt_iff_le_not_ge.mpr
    simp_all [le_def]
    apply le_of_lt h

/-!

### B.5. Addition of times

-/

instance : Add Time where
  add t1 t2 := ⟨t1.val + t2.val⟩

@[simp]
lemma add_val (t1 t2 : Time) :
    (t1 + t2).val = t1.val + t2.val := rfl

/-!

### B.6. Negation of times

-/

instance : Neg Time where
  neg t := ⟨-t.val⟩

@[simp]
lemma neg_val (t : Time) :
    (-t).val = -t.val := rfl

/-!

### B.7. Subtraction of times

-/

instance : Sub Time where
  sub t1 t2 := ⟨t1.val - t2.val⟩

@[simp]
lemma sub_val (t1 t2 : Time) :
    (t1 - t2).val = t1.val - t2.val := rfl

/-!

### B.8. Scalar multiplication of time

-/

instance : SMul ℝ Time where
  smul k t := ⟨k * t.val⟩

@[simp]
lemma smul_real_val (k : ℝ) (t : Time) :
    (k • t).val = k * t.val := rfl

/-!

### B.9. Module on `Time`

-/

instance : AddGroup Time where
  add_assoc t1 t2 t3 := by ext; simp [add_assoc]
  zero_add t := by ext; simp [zero_add]
  add_zero t := by ext; simp [add_zero]
  neg_add_cancel t := by ext; simp [neg_add_cancel]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddCommGroup Time where
  add_comm := by intros; ext; simp [add_comm]

instance : Module ℝ Time where
  one_smul t := by ext; simp
  smul_add k t1 t2 := by ext; simp [mul_add]
  smul_zero k := by ext; simp [mul_zero]
  add_smul k1 k2 t := by ext; simp [add_mul]
  mul_smul k1 k2 t := by ext; simp [mul_assoc]
  zero_smul t := by ext; simp

/-!

### B.10. Norm of time

-/

instance : Norm Time where
  norm t := ‖t.val‖

instance : Dist Time where
  dist t1 t2 := ‖t1 - t2‖

lemma dist_eq_val (t1 t2 : Time) :
    dist t1 t2 = ‖t1.val - t2.val‖ := rfl

lemma dist_eq_real_dist (t1 t2 : Time) :
    dist t1 t2 = dist t1.val t2.val := by rfl

instance : SeminormedAddCommGroup Time where
  dist_self t := by simp [dist_eq_real_dist]
  dist_comm t1 t2 := by simp [dist_eq_real_dist, dist_comm]
  dist_triangle := by simp [dist_eq_real_dist, dist_triangle]

instance : NormedAddCommGroup Time where
  eq_of_dist_eq_zero := by
    intro a b h
    simp [dist, norm] at h
    ext
    rw [sub_eq_zero] at h
    exact h

instance : NormedSpace ℝ Time where
  norm_smul_le k t := by simp [abs_mul, norm]

/-!

### B.11. Inner product on `Time`

-/

open InnerProductSpace

instance : Inner ℝ Time where
  inner t1 t2 := t1.val * t2.val

@[simp]
lemma inner_def (t1 t2 : Time) :
    ⟪t1, t2⟫_ℝ = t1.val * t2.val := rfl

noncomputable instance : InnerProductSpace ℝ Time where
  norm_sq_eq_re_inner := by intros; simp [norm]; ring
  conj_inner_symm := by intros; simp [inner_def]; ring
  add_left := by intros; simp [inner_def, add_mul]
  smul_left := by intros; simp [inner_def]; ring

/-!

### B.12. Decidability of `Time`

-/

noncomputable instance : DecidableEq Time := fun t1 t2 =>
  decidable_of_iff (t1.val = t2.val) (Time.ext_iff.symm)

/-!

### B.13. Measurability of `Time`

-/
instance : MeasurableSpace Time := borel Time

instance : BorelSpace Time where
  measurable_eq := by rfl

/-!

## C. Basis of `Time`

-/
open MeasureTheory

/-- The orthonomral basis on `Time` defined by `1`. -/
noncomputable def basis : OrthonormalBasis (Fin 1) ℝ Time where
  repr := {
    toFun := fun x => WithLp.toLp 2 (fun _ => x)
    invFun := fun f => ⟨f 0⟩
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro f
      ext i
      fin_cases i
      rfl
    map_add' := by
      intro f g
      ext i
      fin_cases i
      rfl
    map_smul' := by
      intro c f
      ext i
      fin_cases i
      rfl
    norm_map' := by
      intro x
      simp only [Fin.isValue, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [@PiLp.norm_eq_of_L2]
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Real.norm_eq_abs, sq_abs,
        Finset.sum_const, Finset.card_singleton, one_smul]
      rw [Real.sqrt_sq_eq_abs]
      rfl
  }

@[simp]
lemma basis_apply_eq_one (i : Fin 1) :
    basis i = 1 := by
  fin_cases i
  simp [basis]
  rfl

@[simp]
lemma rank_eq_one : Module.rank ℝ Time = 1 := by
  rw [@rank_eq_one_iff]
  use 1
  constructor
  · simp
  · intro v
    use v.val
    ext
    simp [one_val]

@[simp]
lemma finRank_eq_one : Module.finrank ℝ Time = 1 := by
  rw [@finrank_eq_one_iff']
  use 1
  constructor
  · simp
  · intro v
    use v.val
    ext
    simp [one_val]

instance : FiniteDimensional ℝ Time := by
  refine Module.finite_of_rank_eq_one ?_
  simp

lemma volume_eq_basis_addHaar :
    (volume (α := Time)) = basis.toBasis.addHaar := by
  exact (OrthonormalBasis.addHaar_eq_volume _).symm

/-!

## D. Maps from `Time` to `ℝ`

-/

/-- The continuous linear map from `Time` to `ℝ`. -/
noncomputable def toRealCLM : Time →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  {
  toFun := Time.val
  map_add' := by simp
  map_smul' := by simp }

/-- The continuous linear equivalence from `Time` to `ℝ`. -/
noncomputable def toRealCLE : Time ≃L[ℝ] ℝ := LinearEquiv.toContinuousLinearEquiv
  {
  toFun := Time.val
  invFun := fun x => ⟨x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' := by simp
  map_smul' := by simp
  }

/-- The linear isometry equivalence from `Time` to `ℝ`. -/
noncomputable def toRealLIE : Time ≃ₗᵢ[ℝ] ℝ where
  toFun := Time.val
  invFun := fun x => ⟨x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' := by simp
  map_smul' := by simp
  norm_map' x := by
    simp
    rfl

lemma eq_one_smul (t : Time) :
    t = t.val • 1 := by
  ext
  simp [one_val]

@[fun_prop]
lemma val_measurable : Measurable Time.val := by
  change Measurable toRealCLE
  fun_prop

lemma val_measurableEmbedding : MeasurableEmbedding Time.val where
  injective := val_injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑toRealCLE '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    exact toRealCLE.symm.continuous.measurable hs

lemma val_measurePreserving : MeasurePreserving Time.val volume volume :=
  LinearIsometryEquiv.measurePreserving toRealLIE

@[fun_prop]
lemma val_differentiable : Differentiable ℝ Time.val := by
  change Differentiable ℝ toRealCLM
  fun_prop

@[simp]
lemma fderiv_val (t : Time) : fderiv ℝ Time.val t 1 = 1 := by
  change (fderiv ℝ toRealCLM t 1) = 1
  rw [ContinuousLinearMap.fderiv, toRealCLM]
  simp

end Time
