/-
Copyright (c) 2026 Ruth Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruth Wang
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp

/-!

# Products of functions on a finite product

With at least one coordinate, a function `T` on a finite product `(i : ι) → κ i` is a product of
functions of one variable exactly when it satisfies the exchange relations.

## i. Overview

For a function `T : ((i : ι) → κ i) → K` with values in a field, the exchange relations say
that for every coordinate `i`, values `a b : κ i` and points `x y`,
`T (x[i ← a]) * T (y[i ← b]) = T (x[i ← b]) * T (y[i ← a])`, where `x[i ← a]` is `x` with
coordinate `i` replaced by `a`. They say that all `2 × 2` minors of the one-coordinate
flattenings of `T` vanish. The flattening at `i` has rows indexed by `κ i` and columns indexed
by assignments to the remaining coordinates.

If the index type `ι` is finite and nonempty, the exchange relations hold exactly when
`T x = ∏ i, v i (x i)` for some functions `v i : κ i → K`. Nonemptiness is necessary: if `ι` is
empty, the exchange relations are vacuous, so every function satisfies them, but an empty
product is always `1`.

For finite-dimensional tensors, these equations characterize the tensors of rank at most one,
which form the affine cone over the Segre variety.

This file is a temporary copy of results intended for Mathlib.

## ii. Key results

- `exists_prod_iff_mul_update` : with at least one coordinate, `T` is a product of functions of
  one variable if and only if it satisfies the exchange relations.

## iii. Table of contents

- A. Product identities
- B. Factorization from the exchange relations

## iv. References

- M. Michałek and B. Sturmfels, Invitation to Nonlinear Algebra, §9.2, p. 141.
  [ref: michalek_sturmfels_2021]

-/

@[expose] public section

open Function

/-!

## A. Product identities

-/

section Exchange

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid K] {κ : ι → Type*}

/-- Changing coordinate `i` of `x` to `a` changes only the factor indexed by `i` in
`∏ j, v j (x j)`. -/
lemma Finset.prod_apply_update (v : (i : ι) → κ i → K) (x : (i : ι) → κ i) (i : ι)
    (a : κ i) : ∏ j, v j (update x i a j) = v i a * ∏ j ∈ Finset.univ.erase i, v j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj ↦ by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Multiplying the function indexed by `i₀` by `c` multiplies `∏ i, v i (x i)` by `c`. -/
lemma Finset.prod_update_const_mul (v : (i : ι) → κ i → K) (c : K) (i₀ : ι)
    (x : (i : ι) → κ i) :
    ∏ i, update v i₀ (fun a ↦ c * v i₀ a) i (x i) = c * ∏ i, v i (x i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀),
    ← Finset.mul_prod_erase _ (fun i ↦ v i (x i)) (Finset.mem_univ i₀), update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj ↦ by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

/-- A product `x ↦ ∏ i, v i (x i)` of functions of one variable satisfies the exchange
relations. -/
lemma prod_apply_update_mul_prod_apply_update (v : (i : ι) → κ i → K) (x y : (i : ι) → κ i)
    (i : ι) (a b : κ i) :
    (∏ j, v j (update x i a j)) * ∏ j, v j (update y i b j) =
      (∏ j, v j (update x i b j)) * ∏ j, v j (update y i a j) := by
  simp only [Finset.prod_apply_update]
  ac_rfl

end Exchange

/-!

## B. Factorization from the exchange relations

-/

section Field

variable {ι K : Type*} [DecidableEq ι] [Field K] {κ : ι → Type*}

/-- If `T` satisfies the exchange relations and `T x₀ ≠ 0`, then every `x` that agrees with `x₀`
outside a finite set `s` of coordinates satisfies
`T x = T x₀ * ∏ j ∈ s, T (update x₀ j (x j)) / T x₀`. -/
lemma eq_mul_prod_of_mul_update {T : ((i : ι) → κ i) → K}
    (hT : ∀ i (a b : κ i) x y, T (update x i a) * T (update y i b) =
      T (update x i b) * T (update y i a))
    {x₀ : (i : ι) → κ i} (h₀ : T x₀ ≠ 0) (s : Finset ι) :
    ∀ x : (i : ι) → κ i, (∀ j ∉ s, x j = x₀ j) →
      T x = T x₀ * ∏ j ∈ s, T (update x₀ j (x j)) / T x₀ := by
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    rw [funext fun j ↦ hx j (Finset.notMem_empty j), Finset.prod_empty, mul_one]
  | insert i s hi ih =>
    intro x hx
    have hx' : ∀ j ∉ s, update x i (x₀ i) j = x₀ j := by
      intro j hj
      rcases eq_or_ne j i with rfl | hji
      · exact update_self ..
      · rw [update_of_ne hji]
        exact hx j (by simp [hji, hj])
    have hprod := ih _ hx'
    have hprod_update : ∏ j ∈ s, T (update x₀ j (update x i (x₀ i) j)) / T x₀ =
        ∏ j ∈ s, T (update x₀ j (x j)) / T x₀ :=
      Finset.prod_congr rfl fun j hj ↦ by rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
    have hexchange := hT i (x i) (x₀ i) x x₀
    rw [update_eq_self, update_eq_self, hprod, hprod_update] at hexchange
    rw [Finset.prod_insert hi]
    apply mul_right_cancel₀ h₀
    rw [hexchange]
    field_simp

/-- If `ι` is nonempty, a function on a finite product that satisfies the exchange relations
factors as a product of functions of one variable. -/
lemma exists_prod_of_mul_update [Fintype ι] [Nonempty ι] {T : ((i : ι) → κ i) → K}
    (hT : ∀ i (a b : κ i) x y, T (update x i a) * T (update y i b) =
      T (update x i b) * T (update y i a)) :
    ∃ v : (i : ι) → κ i → K, ∀ x, T x = ∏ i, v i (x i) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rcases em (∃ x₀, T x₀ ≠ 0) with ⟨x₀, h₀⟩ | hzero
  · -- Normalize each factor at `x₀` and absorb `T x₀` into the factor indexed by `i₀`.
    refine ⟨update (fun j a ↦ T (update x₀ j a) / T x₀) i₀
      (fun a ↦ T x₀ * (T (update x₀ i₀ a) / T x₀)), fun x ↦ ?_⟩
    rw [Finset.prod_update_const_mul]
    exact eq_mul_prod_of_mul_update hT h₀ Finset.univ x (by simp)
  · simp only [not_exists, not_not] at hzero
    exact ⟨fun _ _ ↦ 0, fun x ↦ by simp [hzero x, Finset.prod_eq_zero (Finset.mem_univ i₀)]⟩

/-- If `ι` is nonempty, a function on a finite product factors as a product of functions of one
variable if and only if it satisfies the exchange relations. -/
lemma exists_prod_iff_mul_update [Fintype ι] [Nonempty ι] {T : ((i : ι) → κ i) → K} :
    (∃ v : (i : ι) → κ i → K, ∀ x, T x = ∏ i, v i (x i)) ↔
      ∀ i (a b : κ i) x y, T (update x i a) * T (update y i b) =
        T (update x i b) * T (update y i a) := by
  refine ⟨?_, exists_prod_of_mul_update⟩
  rintro ⟨v, hv⟩ i a b x y
  simp only [hv]
  exact prod_apply_update_mul_prod_apply_update v x y i a b

end Field
