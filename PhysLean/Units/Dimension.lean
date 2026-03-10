/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
/-!

# Dimension

In this module we define the type `Dimension` which carries the dimension
of a physical quantity.

-/

@[expose] public section

open NNReal

/-!

## Defining dimensions

-/

/-- The foundational dimensions.
  Defined in the order ⟨length, time, mass, charge, temperature⟩ -/
structure Dimension where
  /-- The length dimension. -/
  length : ℚ
  /-- The time dimension. -/
  time : ℚ
  /-- The mass dimension. -/
  mass : ℚ
  /-- The charge dimension. -/
  charge : ℚ
  /-- The temperature dimension. -/
  temperature : ℚ

namespace Dimension

@[ext]
lemma ext {d1 d2 : Dimension}
    (h1 : d1.length = d2.length)
    (h2 : d1.time = d2.time)
    (h3 : d1.mass = d2.mass)
    (h4 : d1.charge = d2.charge)
    (h5 : d1.temperature = d2.temperature) :
    d1 = d2 := by
  cases d1
  cases d2
  congr

instance : Mul Dimension where
  mul d1 d2 := ⟨d1.length + d2.length,
    d1.time + d2.time,
    d1.mass + d2.mass,
    d1.charge + d2.charge,
    d1.temperature + d2.temperature⟩

@[simp]
lemma time_mul (d1 d2 : Dimension) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_mul (d1 d2 : Dimension) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

instance : One Dimension where
  one := ⟨0, 0, 0, 0, 0⟩

@[simp]
lemma one_length : (1 : Dimension).length = 0 := rfl
@[simp]
lemma one_time : (1 : Dimension).time = 0 := rfl

@[simp]
lemma one_mass : (1 : Dimension).mass = 0 := rfl

@[simp]
lemma one_charge : (1 : Dimension).charge = 0 := rfl

@[simp]
lemma one_temperature : (1 : Dimension).temperature = 0 := rfl

instance : CommGroup Dimension where
  mul_assoc a b c := by
    ext
    all_goals
      simp only [length_mul, time_mul, mass_mul, charge_mul, temperature_mul]
      ring
  one_mul a := by
    ext
    all_goals
      simp
  mul_one a := by
    ext
    all_goals
      simp
  inv d := ⟨-d.length, -d.time, -d.mass, -d.charge, -d.temperature⟩
  inv_mul_cancel a := by
    ext
    all_goals simp
  mul_comm a b := by
    ext
    all_goals
      simp only [length_mul, time_mul, mass_mul, charge_mul, temperature_mul]
      ring

@[simp]
lemma inv_length (d : Dimension) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension) : d⁻¹.temperature = -d.temperature := rfl

@[simp]
lemma div_length (d1 d2 : Dimension) : (d1 / d2).length = d1.length - d2.length := by
  rw [div_eq_mul_inv, length_mul, inv_length]
  ring

@[simp]
lemma div_time (d1 d2 : Dimension) : (d1 / d2).time = d1.time - d2.time := by
  rw [div_eq_mul_inv, time_mul, inv_time]
  ring

@[simp]
lemma div_mass (d1 d2 : Dimension) : (d1 / d2).mass = d1.mass - d2.mass := by
  rw [div_eq_mul_inv, mass_mul, inv_mass]
  ring

@[simp]
lemma div_charge (d1 d2 : Dimension) : (d1 / d2).charge = d1.charge - d2.charge := by
  rw [div_eq_mul_inv, charge_mul, inv_charge]
  ring

@[simp]
lemma div_temperature (d1 d2 : Dimension) :
    (d1 / d2).temperature = d1.temperature - d2.temperature := by
  rw [div_eq_mul_inv, temperature_mul, inv_temperature]
  ring

@[simp]
lemma npow_length (d : Dimension) (n : ℕ) : (d ^ n).length = n • d.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@pow_add]
    simp [ih]
    ring

@[simp]
lemma npow_time (d : Dimension) (n : ℕ) : (d ^ n).time = n • d.time := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@pow_add]
    simp [ih]
    ring

@[simp]
lemma npow_mass (d : Dimension) (n : ℕ) : (d ^ n).mass = n • d.mass := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@pow_add]
    simp [ih]
    ring

@[simp]
lemma npow_charge (d : Dimension) (n : ℕ) : (d ^ n).charge = n • d.charge := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@pow_add]
    simp [ih]
    ring

@[simp]
lemma npow_temperature (d : Dimension) (n : ℕ) : (d ^ n).temperature = n • d.temperature := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@pow_add]
    simp [ih]
    ring

instance : Pow Dimension ℚ where
  pow d n := ⟨d.length * n, d.time * n, d.mass * n, d.charge * n, d.temperature * n⟩

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension := ⟨1, 0, 0, 0, 0⟩

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension := ⟨0, 1, 0, 0, 0⟩

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension := ⟨0, 0, 1, 0, 0⟩

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension := ⟨0, 0, 0, 1, 0⟩

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension := ⟨0, 0, 0, 0, 1⟩

end Dimension
