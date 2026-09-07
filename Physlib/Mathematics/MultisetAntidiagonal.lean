/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.LinearAlgebra.TensorProduct.Basic
/-!
# Sums over the antidiagonal of a multiset

Combinatorial identities for sums indexed by `Multiset.antidiagonal`: associativity and
exchange of nested antidiagonal sums, collapsing a sum whose terms vanish off one slot, and
the interaction with linear maps and tensor products. These are the bookkeeping behind the
all-orders Leibniz rules of the jet calculus.
-/

@[expose] public section

namespace Multiset

/-- Coassociativity of antidiagonal sums: summing over `s = u + v` and then `u = x + y`
  is summing over `s = x + t` and then `t = y + v`. -/
lemma sum_antidiagonal_assoc {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q => h q.1 q.2 p.2).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun q => h p.1 q.1 q.2).sum).sum := by
  induction s using Multiset.induction_on generalizing h with
  | empty => simp
  | cons κ s ih =>
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Multiset.sum_map_add]
      rw [ih (fun x y v => h x y (κ ::ₘ v)), ih (fun x y v => h x (κ ::ₘ y) v),
        ih (fun x y v => h (κ ::ₘ x) y v)]
      abel

/-- The exchange law of doubly-split antidiagonal sums: splitting `s = u + v` and then
  `u = x + y`, `v = z + w` is, with the middle parts exchanged, splitting `s = u' + v'`
  and then `u' = x + z`, `v' = y + w`. -/
lemma sum_antidiagonal_exchange {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        (p.2.antidiagonal.map fun r => h q.1 q.2 r.1 r.2).sum).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        (p.2.antidiagonal.map fun r => h q.1 r.1 q.2 r.2).sum).sum).sum := by
  induction s using Multiset.induction_on generalizing h with
  | empty => simp
  | cons κ s ih =>
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Multiset.sum_map_add]
      rw [ih (fun x y z w => h x y z (κ ::ₘ w)), ih (fun x y z w => h x y (κ ::ₘ z) w),
        ih (fun x y z w => h x (κ ::ₘ y) z w), ih (fun x y z w => h (κ ::ₘ x) y z w)]
      abel

/-- A multiset sum of linear maps, applied: the sum of the applications. -/
lemma sum_linearMap_apply {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (S : Multiset (M →ₗ[R] N)) (x : M) :
    S.sum x = (S.map fun f => f x).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons f S ih => simp [ih]

/-- A pure tensor against a multiset sum distributes over the sum. -/
lemma tmul_sum {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (m : M) (S : Multiset N) :
    m ⊗ₜ[R] S.sum = (S.map fun n => m ⊗ₜ[R] n).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons n S ih => simp [TensorProduct.tmul_add, ih]

/-- Antidiagonal sums are symmetric under swapping the two parts. -/
lemma sum_antidiagonal_swap {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p => h p.1 p.2).sum =
    (s.antidiagonal.map fun p => h p.2 p.1).sum := by
  induction s using Multiset.induction_on generalizing h with
  | empty => simp
  | cons κ s ih =>
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      rw [ih (fun a b => h a (κ ::ₘ b)), ih (fun a b => h (κ ::ₘ a) b)]
      abel

/-- A multiset sum of negations is the negation of the sum. -/
lemma sum_map_neg'' {ι M : Type*} [AddCommGroup M]
    (s : Multiset ι) (f : ι → M) :
    (s.map fun i => -f i).sum = -(s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih]
      abel

/-- The exchange of a finite sum with a multiset sum. -/
lemma sum_map_finsetSum {α β M : Type*} [AddCommMonoid M]
    (m : Multiset α) (t : Finset β) (f : β → α → M) :
    (m.map fun a => ∑ b ∈ t, f b a).sum = ∑ b ∈ t, (m.map (f b)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [Multiset.map_cons, Multiset.sum_cons]

/-- A sum over the antidiagonal of a family vanishing off `p.1 = 0` collapses to the
  single term at `(0, s)`. -/
lemma sum_antidiagonal_eq_of_fst_ne_zero {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (F : Multiset ι × Multiset ι → M)
    (hF : ∀ p : Multiset ι × Multiset ι, p.1 ≠ 0 → F p = 0) :
    (s.antidiagonal.map F).sum = F (0, s) := by
  induction s using Multiset.induction_on generalizing F with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons a t ih =>
    rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map,
      show ((t.antidiagonal.map (F ∘ Prod.map (Multiset.cons a) id)).sum) = 0 from
        Multiset.sum_eq_zero fun x hx => by
          obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
          exact hF _ (Multiset.cons_ne_zero),
      add_zero, ih (F ∘ Prod.map id (Multiset.cons a)) fun p hp => hF _ hp]
    rfl

/-- A sum over the antidiagonal of a family vanishing off `p.2 = 0` collapses to the
  single term at `(s, 0)`. -/
lemma sum_antidiagonal_eq_of_snd_ne_zero {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (F : Multiset ι × Multiset ι → M)
    (hF : ∀ p : Multiset ι × Multiset ι, p.2 ≠ 0 → F p = 0) :
    (s.antidiagonal.map F).sum = F (s, 0) := by
  rw [show (s.antidiagonal.map F).sum
      = (s.antidiagonal.map fun p => (fun a b => F (b, a)) p.2 p.1).sum from rfl,
    ← Multiset.sum_antidiagonal_swap s (fun a b => F (b, a))]
  exact Multiset.sum_antidiagonal_eq_of_fst_ne_zero s (fun p => F (p.2, p.1))
    fun p hp => hF _ hp

/-- The exchange of the second and third slot in a nested antidiagonal sum. -/
lemma sum_antidiagonal_middle_exchange {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (h : Multiset ι → Multiset ι → Multiset ι → M) :
    (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q => h q.1 q.2 p.2).sum).sum
      = (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q => h q.1 p.2 q.2).sum).sum := by
  rw [Multiset.sum_antidiagonal_assoc s h,
    Multiset.sum_antidiagonal_assoc s (fun a b c => h a c b)]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  exact Multiset.sum_antidiagonal_swap p.2 (fun a b => h p.1 a b)

end Multiset
