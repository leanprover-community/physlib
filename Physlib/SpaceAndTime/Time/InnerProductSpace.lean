/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Physlib.SpaceAndTime.Time.Basic
/-!
# Time as an inner product space

## i. Overview

In this module we equip the affine type `Time` with a real inner product space structure,
choosing the implicit origin represented by `Time.mk 0`. The units and orientation agree with the
real-valued displacements defined in `Physlib.SpaceAndTime.Time.Basic`.

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

With this choice, `Time` becomes a 1d vector space over `ℝ` with an inner product.

## ii. Key results

- `toRealCLE` : The continuous linear equivalence from `Time` to `ℝ`.

## iii. Table of contents

- A. Instances on Time
  - A.1. Natural numbers as elements of `Time`
  - A.2. Real numbers as elements of `Time`
  - A.3. Time is inhabited
  - A.4. The order on `Time`
  - A.5. Addition of times
  - A.6. Negation of times
  - A.7. Subtraction of times
  - A.8. Scalar multiplication of time
  - A.9. Module on `Time`
  - A.10. Norm of time
  - A.11. Inner product on `Time`
  - A.12. Decidability of `Time`
  - A.13. Measurability of `Time`
- B. Basis of `Time`
- C. Maps from `Time` to `ℝ`

## iv. References

* None.
-/

@[expose] public section

namespace Time

/-!

## A. Instances on Time

-/

/-!

### A.1. Natural numbers as elements of `Time`

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

lemma one_ne_zero : (1 : Time) ≠ (0 : Time) :=
  mt (congrArg val) (Nat.cast_injective.ne Nat.one_ne_zero)

@[simp]
lemma zero_val : val 0 = 0 := by exact_mod_cast ofNat_val (n := 0)

@[simp]
lemma eq_zero_iff (t : Time) : t = 0 ↔ t.val = 0 := by simp [Time.ext_iff]

@[simp]
lemma one_val : val 1 = 1 := by exact_mod_cast ofNat_val (n := 1)

@[simp]
lemma eq_one_iff (t : Time) : t = 1 ↔ t.val = 1 := by simp [Time.ext_iff]

/-!

### A.2. Real numbers as elements of `Time`

-/

instance : Coe ℝ Time where
  coe r := ⟨r⟩

instance : Coe Time ℝ where
  coe := Time.val

lemma realCast_val {r : ℝ} : (r : Time).val = r := rfl

@[simp]
lemma realCast_of_natCast {n : ℕ} : ((n : ℝ) : Time) = n := rfl

/-!

### A.3. Time is inhabited

-/

instance : Inhabited Time where
  default := 0

@[simp]
lemma default_eq_zero : default = 0 := rfl

/-!

### A.4. The order on `Time`

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
    t1 < t2 ↔ t1.val < t2.val := by simp only [lt_iff_le_not_ge, le_def]

/-!

### A.5. Addition of times

-/

instance : Add Time where
  add t1 t2 := ⟨t1.val + t2.val⟩

@[simp]
lemma add_val (t1 t2 : Time) :
    (t1 + t2).val = t1.val + t2.val := rfl

/-!

### A.6. Negation of times

-/

instance : Neg Time where
  neg t := ⟨-t.val⟩

@[simp]
lemma neg_val (t : Time) :
    (-t).val = -t.val := rfl

/-!

### A.7. Subtraction of times

-/

instance : Sub Time where
  sub t1 t2 := ⟨t1.val - t2.val⟩

@[simp]
lemma sub_val (t1 t2 : Time) :
    (t1 - t2).val = t1.val - t2.val := rfl

/-!

### A.8. Scalar multiplication of time

-/

instance : SMul ℝ Time where
  smul k t := ⟨k * t.val⟩

@[simp]
lemma smul_real_val (k : ℝ) (t : Time) :
    (k • t).val = k * t.val := rfl

/-!

### A.9. Module on `Time`

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

### A.10. Norm of time

-/

instance : Norm Time where
  norm t := ‖t.val‖

lemma norm_eq_val (t : Time) :
    ‖t‖ = ‖t.val‖ := rfl

lemma dist_eq_val (t1 t2 : Time) :
    dist t1 t2 = ‖t1.val - t2.val‖ := rfl

lemma dist_eq_real_dist (t1 t2 : Time) :
    dist t1 t2 = dist t1.val t2.val := by rfl

instance : SeminormedAddCommGroup Time where
  dist_eq t1 t2 := by
    simp [dist_eq_val, norm_eq_val]
    rw [abs_eq_iff_mul_self_eq]
    ring

instance : NormedAddCommGroup Time where
  dist_eq t1 t2 := by
    simp [dist_eq_val, norm_eq_val]
    rw [abs_eq_iff_mul_self_eq]
    ring

instance : NormedSpace ℝ Time where
  norm_smul_le k t := by simp [abs_mul, norm]

/-!

### A.11. Inner product on `Time`

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

### A.12. Decidability of `Time`

-/

noncomputable instance : DecidableEq Time := fun t1 t2 =>
  decidable_of_iff (t1.val = t2.val) (Time.ext_iff.symm)

/-!

### A.13. Measurability of `Time`

-/
instance : MeasurableSpace Time := borel Time

instance : BorelSpace Time where
  measurable_eq := by rfl

/-!

## B. Basis of `Time`

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
lemma rank_eq_one : Module.rank ℝ Time = 1 :=
  rank_eq_one_iff.mpr ⟨1, one_ne_zero, fun v => ⟨v.val, Time.ext (by simp)⟩⟩

@[simp]
lemma finRank_eq_one : Module.finrank ℝ Time = 1 :=
  Module.rank_eq_one_iff_finrank_eq_one.mp rank_eq_one

instance : FiniteDimensional ℝ Time := Module.finite_of_rank_eq_one rank_eq_one

lemma volume_eq_basis_addHaar :
    (volume (α := Time)) = basis.toBasis.addHaar := basis.addHaar_eq_volume.symm

/-!

## C. Maps from `Time` to `ℝ`

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
    t = t.val • 1 := Time.ext (by simp)

@[fun_prop]
lemma val_measurable : Measurable Time.val := toRealCLE.continuous.measurable

lemma val_measurableEmbedding : MeasurableEmbedding Time.val :=
  toRealCLE.toHomeomorph.measurableEmbedding

lemma val_measurePreserving : MeasurePreserving Time.val volume volume :=
  LinearIsometryEquiv.measurePreserving toRealLIE

@[fun_prop]
lemma val_differentiable : Differentiable ℝ Time.val := toRealCLM.differentiable

@[simp]
lemma fderiv_val (t : Time) : fderiv ℝ Time.val t 1 = 1 := by
  rw [show Time.val = ⇑toRealCLM from rfl, ContinuousLinearMap.fderiv]
  simp [toRealCLM]

end Time
