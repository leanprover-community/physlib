/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.WignerEckart

/-!

# The invariant form and the normalised basis of the standard modules

The contravariant form on `V(n)` and the orthonormal basis `|j, m⟩` with the textbook matrix
elements of `J₊`, `J₋` and `Jz`.

## i. Overview

The basis `v_a = f^a v_0` of `V(n)` used throughout is not normalised. There is a symmetric
bilinear form on `V(n)`, unique up to a scalar, for which the raising and lowering operators are
adjoint and the weight operator is symmetric:
`⟨e x, y⟩ = ⟨x, f y⟩`, `⟨h x, y⟩ = ⟨x, h y⟩`. In the basis `v_a` it is diagonal with
`⟨v_a, v_a⟩ = a! · n!/(n - a)!`.

Over `ℝ` the rescaled vectors `u_a = v_a / √⟨v_a, v_a⟩` are orthonormal. With `j = n/2` and
`m = j - a` they are the states `|j, m⟩`, and the operators act by the textbook formulas
(Condon–Shortley phases):

- `J₊ |j, m⟩ = √((j - m)(j + m + 1)) |j, m + 1⟩`, i.e. `e u_{a+1} = √((a+1)(n-a)) u_a`;
- `J₋ |j, m⟩ = √((j + m)(j - m + 1)) |j, m - 1⟩`, i.e. `f u_a = √((a+1)(n-a)) u_{a+1}`;
- `2Jz |j, m⟩ = 2m |j, m⟩`, i.e. `h u_a = (n - 2a) u_a`.

## ii. Key results

- `normSq` is `⟨v_a, v_a⟩` and `invForm` the contravariant form.
- `invForm_comp_ρE` and `invForm_comp_ρH` express that `e, f` are adjoint and `h` is symmetric.
- `normVec` is the normalised basis over `ℝ`; `invForm_normVec` is orthonormality.
- `ρE_normVec_succ`, `ρF_normVec` and `ρH_normVec` are the textbook matrix elements.

## iii. Table of contents

- A. The contravariant form
  - A.1. Squared norms
  - A.2. Definition and values
  - A.3. Contravariance
- B. The normalised basis over ℝ

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.5.

## A. The contravariant form

### A.1. Squared norms

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

/-- The squared norm `⟨v_a, v_a⟩ = a! · n!/(n - a)!` of the basis vector `v_a` of `V(n)`. -/
def normSq (n a : ℕ) : ℕ := a.factorial * n.descFactorial a

lemma normSq_succ (n a : ℕ) : normSq n (a + 1) = normSq n a * ((a + 1) * (n - a)) := by
  simp only [normSq, Nat.factorial_succ, Nat.descFactorial_succ]
  ring

lemma normSq_pos {n a : ℕ} (ha : a ≤ n) : 0 < normSq n a :=
  Nat.mul_pos (Nat.factorial_pos a)
    (Nat.pos_of_ne_zero fun h => by rw [Nat.descFactorial_eq_zero_iff_lt] at h; omega)

/-!

### A.2. Definition and values

-/

variable {K : Type*} [Field K] {n : ℕ}

variable (K n) in
/-- The contravariant form on `V(n)`: diagonal in the basis `v_a` with entries `normSq n a`. -/
def invForm : StandardSl2Module K n →ₗ[K] StandardSl2Module K n →ₗ[K] K :=
  Matrix.toLinearMap₂ (Pi.basisFun K (Fin (n + 1))) (Pi.basisFun K (Fin (n + 1)))
    (Matrix.diagonal fun a => (normSq n a : K))

lemma invForm_v (i j : Fin (n + 1)) :
    invForm K n (v i) (v j) = if i = j then (normSq n i : K) else 0 := by
  have hi : (v i : StandardSl2Module K n) = Pi.basisFun K (Fin (n + 1)) i := by
    rw [Pi.basisFun_apply]; rfl
  have hj : (v j : StandardSl2Module K n) = Pi.basisFun K (Fin (n + 1)) j := by
    rw [Pi.basisFun_apply]; rfl
  rw [hi, hj, invForm, Matrix.toLinearMap₂_apply_basis, Matrix.diagonal_apply]

lemma invForm_vNat (a b : ℕ) :
    invForm K n (vNat n a) (vNat n b) = if a = b ∧ a ≤ n then (normSq n a : K) else 0 := by
  rcases le_or_gt a n with ha | ha
  · rcases le_or_gt b n with hb | hb
    · rw [vNat_eq_v ha, vNat_eq_v hb, invForm_v]
      simp only [Fin.mk.injEq, ha, and_true]
    · rw [vNat_of_lt hb, map_zero]
      have : a ≠ b := by omega
      simp [this]
  · rw [vNat_of_lt ha, map_zero, LinearMap.zero_apply]
    have : ¬ a ≤ n := by omega
    simp [this]

/-- Two bilinear forms on `V(n)` agree if they agree on all pairs `v_a, v_b`. -/
lemma bilin_ext_vNat {B B' : StandardSl2Module K n →ₗ[K] StandardSl2Module K n →ₗ[K] K}
    (h : ∀ a b, B (vNat n a) (vNat n b) = B' (vNat n a) (vNat n b)) : B = B' :=
  linearMap_ext_vNat fun a => linearMap_ext_vNat fun b => h a b

/-!

### A.3. Contravariance

-/

variable [CharZero K]

/-- The raising and lowering operators are adjoint: `⟨e x, y⟩ = ⟨x, f y⟩`. -/
lemma invForm_comp_ρE : (invForm K n).comp ρE = (invForm K n).compl₂ ρF := by
  refine bilin_ext_vNat fun a b => ?_
  simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, ρF_vNat]
  rcases a with _ | a
  · rw [ρE_vNat_zero, map_zero, LinearMap.zero_apply, invForm_vNat]
    simp
  · rw [ρE_vNat_succ, map_smul, LinearMap.smul_apply, invForm_vNat, invForm_vNat, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a + 1 ≤ n
      · simp only [true_and, ha, ite_true, show a ≤ n by omega, normSq_succ]
        push_cast
        rw [Nat.cast_sub (by omega)]
        ring
      · by_cases ha' : a ≤ n
        · have hna : (n : K) - a = 0 := by
            rw [sub_eq_zero]
            exact_mod_cast (by omega : n = a)
          simp [ha, hna]
        · simp [ha, ha']
    · simp [hab]

omit [CharZero K] in
/-- The weight operator is symmetric: `⟨h x, y⟩ = ⟨x, h y⟩`. -/
lemma invForm_comp_ρH : (invForm K n).comp ρH = (invForm K n).compl₂ ρH := by
  refine bilin_ext_vNat fun a b => ?_
  simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, ρH_vNat, map_smul,
    LinearMap.smul_apply, invForm_vNat, smul_eq_mul]
  by_cases hab : a = b
  · subst hab; ring
  · simp [hab]

omit [CharZero K] in
/-- The form is symmetric. -/
lemma invForm_comm (x y : StandardSl2Module K n) : invForm K n x y = invForm K n y x := by
  have : invForm K n = (invForm K n).flip := bilin_ext_vNat fun a b => by
    rw [LinearMap.flip_apply, invForm_vNat, invForm_vNat]
    by_cases hab : a = b
    · subst hab; rfl
    · simp [hab, Ne.symm hab]
  rw [this, LinearMap.flip_apply, ← this]

/-!

## B. The normalised basis over ℝ

-/

/-- The normalised basis vector `u_a = v_a / √(normSq n a)` of `V(n)` over `ℝ`; for `a ≤ n` it
is the state `|j, m⟩` with `j = n/2`, `m = j - a`. -/
def normVec (n a : ℕ) : StandardSl2Module ℝ n :=
  (Real.sqrt (normSq n a))⁻¹ • vNat n a

lemma sqrt_normSq_succ (n a : ℕ) :
    Real.sqrt (normSq n (a + 1)) =
      Real.sqrt (normSq n a) * Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) := by
  rcases le_or_gt a n with ha | ha
  · rw [normSq_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    congr 2
    push_cast
    rw [Nat.cast_sub ha]
  · have h0 : normSq n (a + 1) = 0 := by
      simp only [normSq, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < a + 1), mul_zero]
    have h1 : normSq n a = 0 := by
      simp only [normSq, Nat.descFactorial_eq_zero_iff_lt.mpr ha, mul_zero]
    simp [h0, h1, Real.sqrt_zero]

/-- Orthonormality: `⟨u_a, u_b⟩ = δ_ab` for `a, b ≤ n`. -/
lemma invForm_normVec {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    invForm ℝ n (normVec n a) (normVec n b) = if a = b then 1 else 0 := by
  simp only [normVec, map_smul, LinearMap.smul_apply, invForm_vNat, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    have hpos : (0 : ℝ) < normSq n a := by exact_mod_cast normSq_pos ha
    have hs := Real.mul_self_sqrt hpos.le
    have hs0 : Real.sqrt (normSq n a) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    simp only [true_and, ha, ite_true]
    field_simp
    linarith
  · simp [hab]

/-- The weight operator on the normalised basis: `h u_a = (n - 2a) u_a`, i.e.
`Jz |j, m⟩ = m |j, m⟩`. -/
lemma ρH_normVec (a : ℕ) :
    (ρH : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n a) =
      ((n : ℝ) - 2 * a) • normVec n a := by
  rw [normVec, map_smul, ρH_vNat, smul_comm]

/-- The lowering operator on the normalised basis: `f u_a = √((a+1)(n-a)) u_{a+1}` for `a < n`,
i.e. `J₋ |j, m⟩ = √((j + m)(j - m + 1)) |j, m - 1⟩`. -/
lemma ρF_normVec {a : ℕ} (ha : a < n) :
    (ρF : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n a) =
      Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) • normVec n (a + 1) := by
  have hpos : (0 : ℝ) < normSq n a := by exact_mod_cast normSq_pos ha.le
  have hc : (0 : ℝ) < ((a : ℝ) + 1) * ((n : ℝ) - a) := by
    have : (a : ℝ) < n := by exact_mod_cast ha
    positivity
  have hs0 : Real.sqrt (normSq n a) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hr0 : Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  rw [normVec, normVec, map_smul, ρF_vNat, smul_smul, sqrt_normSq_succ]
  congr 1
  field_simp

/-- The raising operator on the normalised basis: `e u_{a+1} = √((a+1)(n-a)) u_a` for `a < n`,
i.e. `J₊ |j, m⟩ = √((j - m)(j + m + 1)) |j, m + 1⟩`. -/
lemma ρE_normVec_succ {a : ℕ} (ha : a < n) :
    (ρE : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n (a + 1)) =
      Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) • normVec n a := by
  have hpos : (0 : ℝ) < normSq n a := by exact_mod_cast normSq_pos ha.le
  have hc : (0 : ℝ) < ((a : ℝ) + 1) * ((n : ℝ) - a) := by
    have : (a : ℝ) < n := by exact_mod_cast ha
    positivity
  have hs0 : Real.sqrt (normSq n a) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hr := Real.mul_self_sqrt hc.le
  have hr0 : Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  rw [normVec, normVec, map_smul, ρE_vNat_succ, smul_smul, smul_smul, sqrt_normSq_succ]
  congr 1
  field_simp
  linarith

end PhyslibAlpha.Sl2
