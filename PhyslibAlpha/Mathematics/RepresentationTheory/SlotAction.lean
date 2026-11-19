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
infinitesimal action `infinitesimalAct N C`, which applies `N` to one slot at a time. The same
holds with a different matrix, and even a different kind of index, in each slot. So a coefficient
function fixed by every `K t` is killed by `infinitesimalAct N` (C). With two indices `κ × κ'` in a
slot, a pair of matrices acts on them one factor per kind, `pairMatrix` (D).

## ii. Key results

- `SlotAction.act` : a matrix acting on every slot of a coefficient function.
- `SlotAction.transform` : a change of every index, as a linear map.
- `SlotAction.act_transform` : the change intertwines two actions if it does so on one slot.
- `SlotAction.transform_injective` : the change is injective if it has a left inverse on one slot.
- `SlotAction.infinitesimalAct` : the infinitesimal action of a matrix, one slot at a time.
- `SlotAction.hasDerivAt_sum_mul_prod` : the derivative of the action of a one-parameter family,
  with a matrix for each slot, is its infinitesimal action.
- `SlotAction.infinitesimalAct_eq_zero_of_act_eq` : a coefficient function fixed by a
  one-parameter family is killed by its derivative at the identity.
- `SlotAction.pairMatrix` : a pair of matrices acting on two kinds of index.

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
  `(infinitesimalAct N C) a = ∑_s ∑_q N_{a_s q} C_{a[s ↦ q]}`. -/
def infinitesimalAct (N : κ → κ → ℂ) (C : (ι → κ) → ℂ) (a : ι → κ) : ℂ :=
  ∑ s, ∑ q, N (a s) q * C (Function.update a s q)

/-- Summing over the index vectors that agree with `a` off the slot `s`, for a kind of index
  `κ s` that may depend on the slot. -/
lemma sum_prod_erase_ite_mul {κ : ι → Type*} [∀ s, Fintype (κ s)] [∀ s, DecidableEq (κ s)]
    (a : ∀ s, κ s) (s : ι) (G : (∀ s, κ s) → ℂ) :
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

/-- The derivative at the identity of the action of a one-parameter family of matrices `K t s`,
  one for each slot `s` and acting on a kind of index `κ s` that may depend on the slot, is the
  infinitesimal action of their derivatives `N s`, applied to one slot at a time. -/
lemma hasDerivAt_sum_mul_prod {κ : ι → Type*} [∀ s, Fintype (κ s)] [∀ s, DecidableEq (κ s)]
    {K : ℝ → ∀ s, κ s → κ s → ℂ} {N : ∀ s, κ s → κ s → ℂ}
    (h0 : ∀ s p q, K 0 s p q = if p = q then 1 else 0)
    (hK : ∀ s p q, HasDerivAt (fun t => K t s p q) (N s p q) 0) (C : (∀ s, κ s) → ℂ)
    (a : ∀ s, κ s) :
    HasDerivAt (fun t => ∑ b, C b * ∏ s, K t s (a s) (b s))
      (∑ s, ∑ q, N s (a s) q * C (Function.update a s q)) 0 := by
  have h := HasDerivAt.fun_sum (u := univ) fun b _ =>
    (HasDerivAt.fun_finsetProd (u := univ) (f := fun s t => K t s (a s) (b s))
      fun s _ => hK s (a s) (b s)).const_mul (C b)
  refine h.congr_deriv ?_
  simp only [h0, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_congr rfl fun b _ => mul_left_comm (C b) _ (N s (a s) (b s)),
    sum_prod_erase_ite_mul a s fun b => C b * N s (a s) (b s)]
  simp [mul_comm]

/-- The derivative at the identity of the action of a one-parameter family `K t` is the
  infinitesimal action of its derivative `N`. -/
lemma hasDerivAt_act [DecidableEq κ] {K : ℝ → κ → κ → ℂ} {N : κ → κ → ℂ}
    (h0 : ∀ p q, K 0 p q = if p = q then 1 else 0)
    (hK : ∀ p q, HasDerivAt (fun t => K t p q) (N p q) 0) (C : (ι → κ) → ℂ) (a : ι → κ) :
    HasDerivAt (fun t => act (K t) C a) (infinitesimalAct N C a) 0 :=
  hasDerivAt_sum_mul_prod (K := fun t _ => K t) (N := fun _ => N) (fun _ => h0) (fun _ => hK) C a

/-- A coefficient function fixed by every member of a one-parameter family through the identity
  is killed by the infinitesimal action of its derivative there. -/
lemma infinitesimalAct_eq_zero_of_act_eq [DecidableEq κ] {K : ℝ → κ → κ → ℂ} {N : κ → κ → ℂ}
    (h0 : ∀ p q, K 0 p q = if p = q then 1 else 0)
    (hK : ∀ p q, HasDerivAt (fun t => K t p q) (N p q) 0) {C : (ι → κ) → ℂ}
    (hC : ∀ t, act (K t) C = C) : infinitesimalAct N C = 0 := by
  funext a
  refine (hasDerivAt_act h0 hK C a).unique ?_
  simp only [hC]
  exact hasDerivAt_const 0 (C a)

/-!

## D. Two kinds of index in each slot

With an index of `κ × κ'` in each slot, a pair of matrices acts on it one factor per kind.

-/

/-- The product of two matrices, acting on an index of each kind. -/
def pairMatrix (K₁ : κ → κ → ℂ) (K₂ : κ' → κ' → ℂ) (p q : κ × κ') : ℂ := K₁ p.1 q.1 * K₂ p.2 q.2

end SlotAction
