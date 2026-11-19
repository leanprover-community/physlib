/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
/-!
# Matrices acting slot by slot on coefficient functions

A matrix acting on each index of a coefficient function, and its infinitesimal version.

## i. Overview

A coefficient function `C : (ι → κ) → ℂ` has one index of type `κ` in each slot `s : ι`. A matrix
`K` on `κ` acts on it one factor per slot, `(act K C) a = ∑_b C_b ∏_s K_{a_s b_s}`, which is how a
group acts on the components of a tensor with `|ι|` indices of the same kind (A). A matrix `T`
from `κ` to `κ'` likewise changes every index at once (`transform`). It intertwines the actions of
`K` and `K'` as soon as it does so on a single slot, and it is injective as soon as it has a left
inverse on a single slot (B).

For a family `K t` with `K 0 = 1` and derivative `N` at `0`, the derivative of `act (K t) C` is the
infinitesimal action `infAct N C`, which applies `N` to one slot at a time. So a coefficient
function fixed by every `K t` is killed by `infAct N` (C). With two indices `κ × κ'` in a slot and
a product family `K₁ t ⊗ K₂ t`, the infinitesimal action splits into one on each kind of
index (D).

## ii. Key results

- `SlotAction.act` : a matrix acting on every slot of a coefficient function.
- `SlotAction.transform` : a change of every index, as a linear map.
- `SlotAction.act_transform` : the change intertwines two actions if it does so on one slot.
- `SlotAction.transform_injective` : the change is injective if it has a left inverse on one slot.
- `SlotAction.infAct` : the infinitesimal action of a matrix, one slot at a time.
- `SlotAction.infAct_eq_zero_of_act_eq` : a coefficient function fixed by a one-parameter family
  is killed by its derivative at the identity.
- `SlotAction.act_pairMatrix` : a product of matrices acts on a product of coefficient functions
  factor by factor.
- `SlotAction.infAct_pair` : on two kinds of index the infinitesimal action of a product family
  splits into one action on each.

## iii. Table of contents

- A. The action of a matrix on every slot
- B. Changing every index
- C. The infinitesimal action
- D. Two kinds of index in each slot

## iv. References

* None.

-/

@[expose] public section

namespace SlotAction

open Finset

variable {ι κ κ' κ'' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype κ']
  [Fintype κ'']

/-!

## A. The action of a matrix on every slot

-/

/-- A matrix `K` acting on every slot of a coefficient function, one factor per slot,
  `(act K C) a = ∑_b C_b ∏_s K_{a_s b_s}`, with `a` free and `b` summed. -/
def act (K : κ → κ → ℂ) (C : (ι → κ) → ℂ) (a : ι → κ) : ℂ := ∑ b, C b * ∏ s, K (a s) (b s)

/-!

## B. Changing every index

-/

/-- A matrix `T` from `κ` to `κ'` changing every index of a coefficient function,
  `(transform T C) α = ∑_d C_d ∏_s T_{d_s α_s}`. -/
def transform (T : κ → κ' → ℂ) : ((ι → κ) → ℂ) →ₗ[ℂ] ((ι → κ') → ℂ) where
  toFun C α := ∑ d, C d * ∏ s, T (d s) (α s)
  map_add' C C' := by
    funext α
    simp [add_mul, sum_add_distrib]
  map_smul' k C := by
    funext α
    simp [mul_sum, mul_assoc]

omit [Fintype κ'] in
/-- The change of every index by `T`, entrywise. -/
lemma transform_apply (T : κ → κ' → ℂ) (C : (ι → κ) → ℂ) (α : ι → κ') :
    transform T C α = ∑ d, C d * ∏ s, T (d s) (α s) := rfl

/-- The action of `K` is the change by the transposed matrix. -/
lemma act_eq_transform (K : κ → κ → ℂ) (C : (ι → κ) → ℂ) :
    act K C = transform (fun d a => K a d) C := rfl

/-- Contracting a changed coefficient function against a product over the slots is a sum over
  the old indices, slot by slot. -/
lemma sum_transform_mul_prod (T : κ → κ' → ℂ) (C : (ι → κ) → ℂ) (F : ι → κ' → ℂ) :
    ∑ β, transform T C β * ∏ s, F s (β s) = ∑ d, C d * ∏ s, ∑ p, T (d s) p * F s p := by
  simp only [transform_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [prod_univ_sum, Fintype.piFinset_univ, mul_sum]
  refine sum_congr rfl fun β _ => ?_
  rw [prod_mul_distrib, mul_assoc]

/-- A change of every index intertwines the actions of `K` and `K'` as soon as it does so on a
  single slot. -/
lemma act_transform {T : κ → κ' → ℂ} {K : κ → κ → ℂ} {K' : κ' → κ' → ℂ}
    (hT : ∀ μ q, ∑ p, T μ p * K' q p = ∑ ν, K ν μ * T ν q) (C : (ι → κ) → ℂ) :
    act K' (transform T C) = transform T (act K C) := by
  funext α
  rw [act, sum_transform_mul_prod, act_eq_transform, transform_apply,
    sum_transform_mul_prod _ _ fun s p => T p (α s)]
  exact sum_congr rfl fun d _ => by simp only [hT]

omit [Fintype κ''] in
/-- Two changes of every index compose slot by slot. -/
lemma transform_transform (T : κ → κ' → ℂ) (T' : κ' → κ'' → ℂ) (C : (ι → κ) → ℂ) :
    transform T' (transform T C) = transform (fun μ ν => ∑ p, T μ p * T' p ν) C := by
  funext α
  rw [transform_apply, sum_transform_mul_prod _ _ fun s p => T' p (α s)]
  rfl

/-- The identity matrix changes nothing. -/
lemma transform_one [DecidableEq κ] (C : (ι → κ) → ℂ) :
    transform (fun μ ν : κ => if μ = ν then (1 : ℂ) else 0) C = C := by
  funext α
  rw [transform_apply, sum_eq_single α]
  · simp
  · intro d _ hd
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hd
    rw [prod_eq_zero (mem_univ s) (ite_eq_right hs), mul_zero]
  · exact fun h => absurd (mem_univ α) h

/-- A change of every index with a left inverse on a single slot is injective. -/
lemma transform_injective [DecidableEq κ] {T : κ → κ' → ℂ} {T' : κ' → κ → ℂ}
    (hT : ∀ μ ν, ∑ p, T μ p * T' p ν = if μ = ν then 1 else 0) :
    Function.Injective (transform (ι := ι) T) := by
  intro C C' h
  have h' := congrArg (transform T') h
  simp only [transform_transform, hT, transform_one] at h'
  exact h'

/-!

## C. The infinitesimal action

-/

/-- The infinitesimal action of a matrix `N`, applied to one slot at a time,
  `(infAct N C) a = ∑_s ∑_q N_{a_s q} C_{a[s ↦ q]}`. -/
def infAct (N : κ → κ → ℂ) (C : (ι → κ) → ℂ) (a : ι → κ) : ℂ :=
  ∑ s, ∑ q, N (a s) q * C (Function.update a s q)

/-- The infinitesimal action is additive in the matrix. -/
lemma infAct_add (N N' : κ → κ → ℂ) (C : (ι → κ) → ℂ) :
    infAct (N + N') C = infAct N C + infAct N' C := by
  funext a
  simp [infAct, add_mul, sum_add_distrib]

/-- The infinitesimal action commutes with scaling the matrix. -/
lemma infAct_smul (k : ℂ) (N : κ → κ → ℂ) (C : (ι → κ) → ℂ) :
    infAct (k • N) C = k • infAct N C := by
  funext a
  simp [infAct, mul_sum, mul_assoc]

/-- Summing over the index vectors that agree with `a` off the slot `s`. -/
lemma sum_prod_erase_ite_mul [DecidableEq κ] (a : ι → κ) (s : ι) (G : (ι → κ) → ℂ) :
    ∑ b, (∏ j ∈ univ.erase s, if a j = b j then (1 : ℂ) else 0) * G b
      = ∑ q, G (Function.update a s q) := by
  rw [← sum_fiberwise univ (fun b => b s)]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_eq_single (Function.update a s q)]
  · rw [prod_eq_one fun j hj => ite_eq_left (Function.update_of_ne (ne_of_mem_erase hj) _ _).symm,
      one_mul]
  · intro b hb hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have hjs : j ≠ s := fun h => hj (by subst h; simpa using (mem_filter.1 hb).2)
    rw [prod_eq_zero (mem_erase.2 ⟨hjs, mem_univ j⟩), zero_mul]
    exact ite_eq_right fun h => hj (by rw [Function.update_of_ne hjs]; exact h.symm)
  · intro h
    simp at h

/-- The derivative at the identity of the action of a one-parameter family `K t` is the
  infinitesimal action of its derivative `N`. -/
lemma hasDerivAt_act [DecidableEq κ] {K : ℝ → κ → κ → ℂ} {N : κ → κ → ℂ}
    (h0 : ∀ p q, K 0 p q = if p = q then 1 else 0)
    (hK : ∀ p q, HasDerivAt (fun t => K t p q) (N p q) 0) (C : (ι → κ) → ℂ) (a : ι → κ) :
    HasDerivAt (fun t => act (K t) C a) (infAct N C a) 0 := by
  have h := HasDerivAt.fun_sum (u := univ) fun b _ =>
    (HasDerivAt.fun_finsetProd (u := univ) (f := fun s t => K t (a s) (b s))
      fun s _ => hK (a s) (b s)).const_mul (C b)
  refine h.congr_deriv ?_
  simp only [h0, smul_eq_mul, mul_sum, infAct]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_congr rfl fun b _ => mul_left_comm (C b) _ (N (a s) (b s)), sum_prod_erase_ite_mul]
  simp [mul_comm]

/-- A coefficient function fixed by every member of a one-parameter family through the identity
  is killed by the infinitesimal action of its derivative there. -/
lemma infAct_eq_zero_of_act_eq [DecidableEq κ] {K : ℝ → κ → κ → ℂ} {N : κ → κ → ℂ}
    (h0 : ∀ p q, K 0 p q = if p = q then 1 else 0)
    (hK : ∀ p q, HasDerivAt (fun t => K t p q) (N p q) 0) {C : (ι → κ) → ℂ}
    (hC : ∀ t, act (K t) C = C) : infAct N C = 0 := by
  funext a
  refine (hasDerivAt_act h0 hK C a).unique ?_
  simp only [hC]
  exact hasDerivAt_const 0 (C a)

/-!

## D. Two kinds of index in each slot

With an index of `κ × κ'` in each slot, a product family `K₁ t ⊗ K₂ t` has derivative
`N₁ ⊗ 1 + 1 ⊗ N₂` at the identity. Its infinitesimal action is that of `N₁` on the first kind of
index plus that of `N₂` on the second.

-/

/-- The product of two matrices, acting on an index of each kind. -/
def pairMatrix (K₁ : κ → κ → ℂ) (K₂ : κ' → κ' → ℂ) (p q : κ × κ') : ℂ := K₁ p.1 q.1 * K₂ p.2 q.2

/-- The coefficient function with the first kind of index `x` and the second `y`. -/
def zip (x : ι → κ) (y : ι → κ') : ι → κ × κ' := fun s => (x s, y s)

omit [Fintype ι] [Fintype κ] [Fintype κ'] in
/-- Updating the first entry of one slot of a zipped index vector. -/
lemma update_zip_fst (x : ι → κ) (y : ι → κ') (s : ι) (q : κ) :
    Function.update (zip x y) s (q, y s) = zip (Function.update x s q) y := by
  funext j
  by_cases h : j = s
  · subst h
    simp [zip]
  · simp [zip, Function.update_of_ne h]

omit [Fintype ι] [Fintype κ] [Fintype κ'] in
/-- Updating the second entry of one slot of a zipped index vector. -/
lemma update_zip_snd (x : ι → κ) (y : ι → κ') (s : ι) (q : κ') :
    Function.update (zip x y) s (x s, q) = zip x (Function.update y s q) := by
  funext j
  by_cases h : j = s
  · subst h
    simp [zip]
  · simp [zip, Function.update_of_ne h]

/-- A product of two matrices acts on a product of two coefficient functions, one for each kind
  of index, factor by factor. -/
lemma act_pairMatrix (K₁ : κ → κ → ℂ) (K₂ : κ' → κ' → ℂ) (f : (ι → κ) → ℂ) (g : (ι → κ') → ℂ)
    (x : ι → κ) (y : ι → κ') :
    act (pairMatrix K₁ K₂) (fun α => f (fun s => (α s).1) * g (fun s => (α s).2)) (zip x y)
      = act K₁ f x * act K₂ g y := by
  rw [act, ← (Equiv.arrowProdEquivProdArrow ι (fun _ => κ) fun _ => κ').symm.sum_comp,
    Fintype.sum_prod_type, act, act, sum_mul_sum]
  refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  simp [Equiv.arrowProdEquivProdArrow, pairMatrix, zip, prod_mul_distrib]
  ring

omit [Fintype κ] [Fintype κ'] in
/-- The derivative of a product family at the identity. -/
lemma hasDerivAt_pairMatrix [DecidableEq κ] [DecidableEq κ'] {K₁ : ℝ → κ → κ → ℂ}
    {K₂ : ℝ → κ' → κ' → ℂ} {N₁ : κ → κ → ℂ} {N₂ : κ' → κ' → ℂ}
    (h₁ : ∀ p q, K₁ 0 p q = if p = q then 1 else 0)
    (h₂ : ∀ p q, K₂ 0 p q = if p = q then 1 else 0)
    (hK₁ : ∀ p q, HasDerivAt (fun t => K₁ t p q) (N₁ p q) 0)
    (hK₂ : ∀ p q, HasDerivAt (fun t => K₂ t p q) (N₂ p q) 0) (p q : κ × κ') :
    HasDerivAt (fun t => pairMatrix (K₁ t) (K₂ t) p q)
      (pairMatrix N₁ (fun p q => if p = q then 1 else 0) p q
        + pairMatrix (fun p q => if p = q then 1 else 0) N₂ p q) 0 := by
  have h := (hK₁ p.1 q.1).mul (hK₂ p.2 q.2)
  rw [h₁, h₂] at h
  exact h

/-- The infinitesimal action of `N₁ ⊗ 1 + 1 ⊗ N₂` is that of `N₁` on the first kind of index
  plus that of `N₂` on the second. -/
lemma infAct_pair [DecidableEq κ] [DecidableEq κ'] (N₁ : κ → κ → ℂ) (N₂ : κ' → κ' → ℂ)
    (C : (ι → κ × κ') → ℂ) (x : ι → κ) (y : ι → κ') :
    infAct (pairMatrix N₁ (fun p q => if p = q then 1 else 0)
        + pairMatrix (fun p q => if p = q then 1 else 0) N₂) C (zip x y)
      = infAct N₁ (fun x' => C (zip x' y)) x + infAct N₂ (fun y' => C (zip x y')) y := by
  simp only [infAct, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [Pi.add_apply, pairMatrix, add_mul, sum_add_distrib, zip]
  congr 1
  · refine sum_congr rfl fun q _ => ?_
    rw [sum_eq_single (y s)]
    · rw [ite_eq_left rfl, mul_one, update_zip_fst]
    · intro q' _ hq'
      rw [ite_eq_right (Ne.symm hq'), mul_zero, zero_mul]
    · exact fun h => absurd (mem_univ _) h
  · rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    rw [sum_eq_single (x s)]
    · rw [ite_eq_left rfl, one_mul, update_zip_snd]
    · intro q' _ hq'
      rw [ite_eq_right (Ne.symm hq'), zero_mul, zero_mul]
    · exact fun h => absurd (mem_univ _) h

end SlotAction
