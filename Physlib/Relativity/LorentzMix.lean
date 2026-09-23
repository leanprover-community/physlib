/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.Fin
public import Physlib.Mathematics.MultisetAntidiagonal
/-!
# The Lorentz mixing of derivative slots

## i. Overview

A Lorentz transformation mixes each derivative slot of a symbol through a column `Λ_{b a}`
of the Lorentz matrix. On families indexed by multisets of directions this is the operator
`lorentzMix`: peel one direction `a`, put it back as every direction `b` weighted by
`Λ_{b a}`, and mix what is left; peeling commutes, so the operator descends to multisets,
and `lorentzMix_ofFn` is its tuple form. The correction terms of a covariant derivative are
Leibniz convolutions `derivConv` over the multiset antidiagonal, and `lorentzMix` is a
morphism for the convolution. The Lorentz law of any covariant tower built one slot at a
time from a covariant correction is then one induction, `repLorentz_tower`. Nothing here
depends on a gauge group.

## ii. Key results

- `Lorentz.lorentzMix`, `Lorentz.lorentzMix_ofFn` : the mixing operator and its tuple form.
- `Lorentz.derivConv`, `Lorentz.lorentzMix_derivConv` : the Leibniz convolution, and the
  mixing operator as a morphism for it.
- `Lorentz.repLorentz_tower` : the Lorentz law of an abstract covariant tower.

## iii. Table of contents

- A. The Lorentz mixing of derivative slots
- B. The Leibniz convolution
- C. The Lorentz law of a covariant tower

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`, as a complex scalar.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => (((SL2C.toLorentzGroup Λ).1 b a : ℝ) : ℂ)

/-!

## A. The Lorentz mixing of derivative slots

-/

section LorentzMix

variable {M N : Type*} [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]

/-- One peeling step of the Lorentz mixing: the direction `a` is removed from the multiset
  index of the family and put back as every direction `b`, weighted by `Λ_{b a}`. -/
noncomputable def lorentzMixStep (Λ : SL(2,ℂ)) (a : Fin 1 ⊕ Fin 3)
    (G : Multiset (Fin 1 ⊕ Fin 3) → M) : Multiset (Fin 1 ⊕ Fin 3) → M :=
  fun t => ∑ b, L[Λ] b a • G (b ::ₘ t)

/-- Peeling two directions commutes, so the mixing is well defined on a multiset. -/
instance (Λ : SL(2,ℂ)) : LeftCommutative (lorentzMixStep (M := M) Λ) where
  left_comm a₁ a₂ G := by
    funext t
    simp only [lorentzMixStep, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by
      rw [mul_comm, Multiset.cons_swap]

/-- The Lorentz mixing of a multiset-indexed family along a multiset `s` of directions:
  every direction of `s` is peeled and replaced by all directions, weighted by the
  corresponding column of the Lorentz matrix. -/
noncomputable def lorentzMix (Λ : SL(2,ℂ)) (G : Multiset (Fin 1 ⊕ Fin 3) → M)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : Multiset (Fin 1 ⊕ Fin 3) → M :=
  s.foldr (lorentzMixStep Λ) G

variable (Λ : SL(2,ℂ)) (G : Multiset (Fin 1 ⊕ Fin 3) → M)

@[simp]
lemma lorentzMix_zero : lorentzMix Λ G 0 = G := Multiset.foldr_zero _ _

/-- Mixing along `a ::ₘ s` peels `a` after mixing along `s`. -/
lemma lorentzMix_cons_apply (a : Fin 1 ⊕ Fin 3) (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ G (a ::ₘ s) t = ∑ b, L[Λ] b a • lorentzMix Λ G s (b ::ₘ t) :=
  congrFun (Multiset.foldr_cons _ _ _ _) t

/-- Evaluating a mixed family away from the empty multiset is mixing the translated
  family at the empty multiset. -/
lemma lorentzMix_apply_add (s : Multiset (Fin 1 ⊕ Fin 3)) :
    ∀ (G : Multiset (Fin 1 ⊕ Fin 3) → M) (t : Multiset (Fin 1 ⊕ Fin 3)),
      lorentzMix Λ G s t = lorentzMix Λ (fun r => G (r + t)) s 0 := by
  induction s using Multiset.induction_on with
  | empty => intro G t; rw [lorentzMix_zero, lorentzMix_zero, zero_add]
  | cons a s ih =>
      intro G t
      simp only [lorentzMix_cons_apply, ih G, ih (fun r => G (r + t)), Multiset.add_cons,
        Multiset.cons_add, add_zero]

/-- Peeling at the empty multiset: the peeled direction is pushed into the family. -/
lemma lorentzMix_cons_zero (a : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ G (a ::ₘ s) 0 = ∑ b, L[Λ] b a • lorentzMix Λ (fun t => G (b ::ₘ t)) s 0 := by
  simp only [lorentzMix_cons_apply, lorentzMix_apply_add Λ s G, Multiset.add_cons, add_zero]

/-- The mixing operator commutes with any linear map applied to the values. -/
lemma lorentzMix_map (Φ : M →ₗ[ℂ] N) (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    Φ (lorentzMix Λ G s t) = lorentzMix Λ (fun r => Φ (G r)) s t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [lorentzMix_zero, lorentzMix_zero]
  | cons a s ih => simp only [lorentzMix_cons_apply, map_sum, map_smul, ih]

/-- The mixing operator is homogeneous in the family. -/
lemma lorentzMix_smul_fam (c : ℂ) (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ (fun r => c • G r) s t = c • lorentzMix Λ G s t :=
  (lorentzMix_map Λ G (c • LinearMap.id) s t).symm

/-- The mixing operator is additive in the family. -/
lemma lorentzMix_add_fam (G₁ G₂ : Multiset (Fin 1 ⊕ Fin 3) → M)
    (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ (fun r => G₁ r + G₂ r) s t = lorentzMix Λ G₁ s t + lorentzMix Λ G₂ s t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [lorentzMix_zero, lorentzMix_zero, lorentzMix_zero]
  | cons a s ih =>
      simp only [lorentzMix_cons_apply, ih, smul_add, Finset.sum_add_distrib]

/-- The mixing operator commutes with finite sums of families. -/
lemma lorentzMix_sum_fam {ι : Type*} [Fintype ι] (H : ι → Multiset (Fin 1 ⊕ Fin 3) → M)
    (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ (fun r => ∑ i, H i r) s t = ∑ i, lorentzMix Λ (H i) s t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => simp only [lorentzMix_zero]
  | cons a s ih =>
      simp only [lorentzMix_cons_apply, ih, Finset.smul_sum]
      exact Finset.sum_comm

/-- The mixing operator agrees with the tuple form of the Lorentz law: along an ordered
  tuple of directions it is the sum over all tuples with one Lorentz matrix factor per
  slot. -/
lemma lorentzMix_ofFn {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ G (List.ofFn l) t =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, L[Λ] (p i) (l i)) • G ((List.ofFn p : List (Fin 1 ⊕ Fin 3)) + t) := by
  induction n generalizing t with
  | zero => rw [Fintype.sum_unique]; simp
  | succ n ih =>
      rw [List.ofFn_succ, ← Multiset.cons_coe, lorentzMix_cons_apply,
        Physlib.Fin.sum_pi_succ_prod_smul (fun i b => L[Λ] b (l i))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ih (fun i => l i.succ) (b ::ₘ t), Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [smul_smul, List.ofFn_succ, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
      simp only [Fin.cons_zero, Fin.cons_succ]

end LorentzMix

/-!

## B. The Leibniz convolution

-/

section DerivConv

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The Leibniz convolution of two families of derivative symbols: the sum over the
  splittings of the multiset of the products of the two symbols. -/
noncomputable def derivConv (f g : Multiset (Fin 1 ⊕ Fin 3) → B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) : B :=
  (s.antidiagonal.map fun p => f p.1 * g p.2).sum

omit [Algebra ℂ B] in
/-- One derivative peeled off a convolution lands on one factor or the other. -/
lemma derivConv_cons (f g : Multiset (Fin 1 ⊕ Fin 3) → B) (a : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    derivConv f g (a ::ₘ s) =
      derivConv f (fun r => g (a ::ₘ r)) s + derivConv (fun r => f (a ::ₘ r)) g s := by
  simp only [derivConv, Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map]
  rfl

/-- The convolution is linear in its right-hand family. -/
lemma derivConv_sum_right {ι : Type*} [Fintype ι] (f : Multiset (Fin 1 ⊕ Fin 3) → B)
    (c : ι → ℂ) (g : ι → Multiset (Fin 1 ⊕ Fin 3) → B) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    derivConv f (fun r => ∑ i, c i • g i r) s = ∑ i, c i • derivConv f (g i) s := by
  simp only [derivConv, Finset.mul_sum, mul_smul_comm, Multiset.sum_map_finsetSum,
    Multiset.smul_sum, Multiset.map_map, Function.comp_def]

/-- The convolution is linear in its left-hand family. -/
lemma derivConv_sum_left {ι : Type*} [Fintype ι] (g : Multiset (Fin 1 ⊕ Fin 3) → B)
    (c : ι → ℂ) (f : ι → Multiset (Fin 1 ⊕ Fin 3) → B) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    derivConv (fun r => ∑ i, c i • f i r) g s = ∑ i, c i • derivConv (f i) g s := by
  simp only [derivConv, Finset.sum_mul, smul_mul_assoc, Multiset.sum_map_finsetSum,
    Multiset.smul_sum, Multiset.map_map, Function.comp_def]

/-- The Lorentz mixing operator is a morphism for the Leibniz convolution: mixing the two
  factors separately and convolving is the same as convolving and then mixing. -/
lemma lorentzMix_derivConv (Λ : SL(2,ℂ)) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    ∀ (f g : Multiset (Fin 1 ⊕ Fin 3) → B),
      derivConv (fun x => lorentzMix Λ f x 0) (fun y => lorentzMix Λ g y 0) s =
        lorentzMix Λ (derivConv f g) s 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [derivConv]
  | cons a s ih =>
      intro f g
      rw [derivConv_cons, lorentzMix_cons_zero]
      simp only [lorentzMix_cons_zero, derivConv_sum_right, derivConv_sum_left,
        derivConv_cons, lorentzMix_add_fam, ← ih, smul_add, Finset.sum_add_distrib]

/-- The Lorentz law of a Leibniz convolution: the mixing operator is a morphism for the
  convolution, so a convolution of two families with Lorentz laws has one too. -/
lemma repLorentz_derivConv {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hmul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    (Λ : SL(2,ℂ)) (f f' g g' : Multiset (Fin 1 ⊕ Fin 3) → B)
    (hf : ∀ x, repLorentz Λ (f x) = lorentzMix Λ f' x 0)
    (hg : ∀ y, repLorentz Λ (g y) = lorentzMix Λ g' y 0) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repLorentz Λ (derivConv f g s) = lorentzMix Λ (derivConv f' g') s 0 := by
  rw [derivConv, map_multiset_sum, Multiset.map_map, ← lorentzMix_derivConv, derivConv]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => by
    rw [Function.comp_apply, hmul, hf, hg])

end DerivConv

/-!

## C. The Lorentz law of a covariant tower

A covariant tower is built one slot at a time: the tower along `l 0 :: l'` is the tower
along `l'` with one more plain derivative, plus a correction `C (l 0)` applied to the tower
along `l'`. The induction is run once, for an abstract tower with a Lorentz covariant
correction that is linear in the family it corrects and lets a twist of the value index
through.

-/

section Tower

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The Lorentz law of a covariant tower `T` built by the step `hstep` from a correction
  `C`, transforming into a tower `T'` built by the same step: the seed of `T` transforms
  into the seed of `T'` with the value index twisted by `τ` (`hzero`), and the correction is
  Lorentz covariant (`hC`), linear in the family it corrects (`hClin`) and lets the twist
  through (`hCτ`). Then the covariant slots mix by their own columns of the Lorentz matrix,
  the plain slots by `lorentzMix`, and the value index by `τ`. -/
theorem repLorentz_tower {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [Module K B] [SMulCommClass K ℂ B] (Λ : SL(2,ℂ))
    (T T' : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) → Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[K] B)
    (C : (Fin 1 ⊕ Fin 3) → (Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[K] B) →
      Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[K] B)
    (τ : W →ₗ[K] W)
    (hstep : ∀ (n : ℕ) (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)),
      T (n + 1) l s = T n (fun i => l i.succ) (l 0 ::ₘ s) + C (l 0) (T n fun i => l i.succ) s)
    (hstep' : ∀ (n : ℕ) (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)),
      T' (n + 1) l s = T' n (fun i => l i.succ) (l 0 ::ₘ s) + C (l 0) (T' n fun i => l i.succ) s)
    (hzero : ∀ (l : Fin 0 → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : W),
      repLorentz Λ (T 0 l s φ) = lorentzMix Λ (fun t => T' 0 l t (τ φ)) s 0)
    (hC : ∀ (ρ : Fin 1 ⊕ Fin 3) (G G' : Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[K] B),
      (∀ y χ, repLorentz Λ (G y χ) = lorentzMix Λ (fun t => G' t χ) y 0) →
      ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : W), repLorentz Λ (C ρ G s φ) =
        ∑ a, L[Λ] a ρ • lorentzMix Λ (fun t => C a G' t φ) s 0)
    (hClin : ∀ (ρ : Fin 1 ⊕ Fin 3) {ι : Type} [Fintype ι] (c : ι → ℂ)
      (G : ι → Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[K] B) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : W), C ρ (fun t => ∑ i, c i • G i t) s φ = ∑ i, c i • C ρ (G i) s φ)
    (hCτ : ∀ (ρ : Fin 1 ⊕ Fin 3) (G : Multiset (Fin 1 ⊕ Fin 3) → W →ₗ[K] B)
      (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : W),
      C ρ (fun t => G t ∘ₗ τ) s φ = C ρ G s (τ φ)) :
    ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : W),
      repLorentz Λ (T n l s φ) =
        ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
          (∏ i, L[Λ] (p i) (l i)) • lorentzMix Λ (fun t => T' n p t (τ φ)) s 0 := by
  intro n
  induction n with
  | zero =>
      intro l s φ
      rw [Fintype.sum_eq_single l fun p hp => absurd (Subsingleton.elim p l) hp]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
      exact hzero l s φ
  | succ n ih =>
      intro l s φ
      -- the Lorentz law of the lower tower, in the form the correction term consumes
      have hG : ∀ y χ, repLorentz Λ (T n (fun i => l i.succ) y χ) =
          lorentzMix Λ (fun t => (∑ p : Fin n → (Fin 1 ⊕ Fin 3),
            (∏ i, L[Λ] (p i) (l i.succ)) • (T' n p t ∘ₗ τ)) χ) y 0 := by
        intro y χ
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          lorentzMix_sum_fam, lorentzMix_smul_fam]
        exact ih _ y χ
      rw [hstep, LinearMap.add_apply, map_add, ih _ (l 0 ::ₘ s) φ, hC (l 0) _ _ hG s φ,
        Physlib.Fin.sum_pi_succ_prod_smul (fun i b => L[Λ] b (l i))]
      -- both sides as double sums over the first direction and the lower tuple
      simp only [lorentzMix_cons_zero, hClin, hCτ, hstep', Fin.cons_zero, Fin.cons_succ,
        LinearMap.add_apply, lorentzMix_add_fam, lorentzMix_sum_fam, lorentzMix_smul_fam,
        Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => by rw [mul_comm]

end Tower

end Lorentz
