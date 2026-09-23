/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Mathematics.Fin
public import Physlib.Particles.StandardModel.AlgebraRealization.Commutations
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
/-!
# The covariant derivatives of a Standard Model

## i. Overview

The fields of a Standard Model are the bare derivative symbols `[∂_s A_μ^a]`, `[∂_s H^i]`
and `[∂_s ψ^α]` of [`Basic.lean`](Basic.lean), with the statistics proved in
[`Commutations.lean`](Commutations.lean). The whole jet gauge group acts on those — a gauge
transformation together with all of its derivatives at the base point — and the
transformation of a matter symbol carries an inhomogeneous term built from the gauge field.
This file replaces them by the covariant towers `∇_l H`, `∇_l ψ` and `∇_l F_{μν}`, on which
a gauge jet acts through its base point alone, and shows that nothing is lost in the
exchange: the two sets of generators generate the same algebra.

Sections A to E are the Lorentz machinery the towers need, stated for an arbitrary
`GaugeAlgebraRealization`. A Lorentz transformation mixes each derivative slot of a symbol through a
column of the Lorentz matrix; the bare symbols are indexed by multisets of directions, so
that mixing is written as an operator `lorentzMix` on multiset-indexed families, a morphism
for the Leibniz convolution out of which the correction terms of a covariant derivative are
built. The Lorentz law of a covariant tower is then a single induction, `repLorentz_tower`,
instantiated for the matter towers, where the value index carries the contragredient action
and the gauge action has to commute with the Lorentz action, and for the field-strength
tower, where the adjoint index carries no Lorentz weight.

Sections F onwards work inside a Standard Model: the field algebra is the algebra generated
by every symbol of the theory, the covariant towers are the iterated covariant derivatives
of the twelve matter families and of the field strength, and `fieldAlgebra_eq_covDeriv` says
that swapping the bare matter symbols for their towers, the gauge-field symbols being kept
in both, does not change the algebra generated. The towers transform through the base point
of a gauge jet alone and are fixed by a pure gauge jet — the facts
`AlgebraRealization.CovFieldAlgebra.Basic` combines into the classification of jet-gauge
invariants — and the last section records their Lorentz laws, which the covariant form of
the theory consumes.

## ii. Key results

- `StandardModel.lorentzMix` : the Lorentz mixing operator on multiset-indexed families of
  derivative symbols, a morphism for the Leibniz convolution (`lorentzMix_derivConv`).
- `StandardModel.repLorentz_tower` : the Lorentz law of an abstract covariant tower.
- `GaugeAlgebraRealization.isLorentzCovDerivTransforms_covDerivIter` and
  `GaugeAlgebraRealization.repLorentz_iteratedCovDerivAdjoint_fieldStrength` : the Lorentz
  laws of the covariant matter towers and of the covariant field-strength tower.
- `AlgebraRealization.fieldAlgebra` : the algebra the fields generate.
- `AlgebraRealization.covDerivH`, `AlgebraRealization.covDerivFieldStrength` and their
  companions : the covariant derivative towers.
- `AlgebraRealization.fieldAlgebra_eq_covDeriv` : the covariant towers generate the field
  algebra.
- `AlgebraRealization.repLorentz_covDerivH` and its companions : the Lorentz laws of the
  covariant matter towers.

## iii. Table of contents

- A. The Lorentz mixing of derivative slots
- B. The Leibniz convolution
- C. The Lorentz law of a covariant tower
- D. The covariant tower of a matter family
- E. The covariant tower of the field strength
- F. What a covariant tower inherits from its family
- G. The field algebra and the covariant towers
- H. The covariant towers generate the field algebra
- I. Gauge covariance of the covariant towers
- J. The Lorentz laws of the covariant matter towers

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`, as a complex scalar.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => (((SL2C.toLorentzGroup Λ).1 b a : ℝ) : ℂ)

/-!

## A. The Lorentz mixing of derivative slots

A Lorentz transformation mixes every derivative slot of a symbol through a column
`L[Λ] · a` of the Lorentz matrix. For symbols indexed by an ordered tuple the mixing is a
sum over tuples; the covariant derivative symbols carry multisets of directions, so the
mixing is an operator on multiset-indexed families: peel one direction `a`, replace it by
every direction `b` weighted by `L[Λ] b a`, and mix what is left. Peeling two directions
commutes, so the recursion descends to multisets; `lorentzMix_ofFn` identifies the operator
with the tuple form, and the remaining lemmas record that it is linear in the family.

-/

section LorentzMix

variable {M N : Type*} [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]

/-- One peeling step of the Lorentz mixing: the direction `a` is removed from the multiset
  index of the family and put back as every direction `b`, weighted by `L[Λ] b a`. -/
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
lemma lorentzMix_add_fam (G₁ G₂ : Multiset (Fin 1 ⊕ Fin 3) → M) (s t : Multiset (Fin 1 ⊕ Fin 3)) :
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

/-- A sum over tuples of directions, with one Lorentz matrix factor per slot, split into
  its first slot and the remaining ones. -/
lemma sum_fin_succ_prod_smul {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3))
    (X : (Fin (n + 1) → (Fin 1 ⊕ Fin 3)) → M) :
    ∑ q : Fin (n + 1) → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (q i) (l i)) • X q =
      ∑ b, ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (L[Λ] b (l 0) * ∏ i, L[Λ] (p i) (l i.succ)) • X (Fin.cons b p) :=
  Physlib.Fin.sum_pi_succ_prod_smul (fun i b => L[Λ] b (l i)) X

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
      rw [List.ofFn_succ, ← Multiset.cons_coe, lorentzMix_cons_apply, sum_fin_succ_prod_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ih (fun i => l i.succ) (b ::ₘ t), Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [smul_smul, List.ofFn_succ, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
      simp only [Fin.cons_zero, Fin.cons_succ]

end LorentzMix

section LorentzMixGroup

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (Λ : SL(2,ℂ))

/-- The mixing operator commutes with negation of the family. -/
lemma lorentzMix_neg_fam (G : Multiset (Fin 1 ⊕ Fin 3) → M) (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ (fun r => -G r) s t = -lorentzMix Λ G s t := by
  simpa only [neg_one_smul] using lorentzMix_smul_fam Λ G (-1) s t

/-- The mixing operator is additive in the family, in subtracted form. -/
lemma lorentzMix_sub_fam (G₁ G₂ : Multiset (Fin 1 ⊕ Fin 3) → M) (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    lorentzMix Λ (fun r => G₁ r - G₂ r) s t = lorentzMix Λ G₁ s t - lorentzMix Λ G₂ s t := by
  simp only [sub_eq_add_neg, lorentzMix_add_fam Λ G₁ (fun r => -G₂ r), lorentzMix_neg_fam]

end LorentzMixGroup

/-!

## B. The Leibniz convolution

The correction terms of a covariant derivative are Leibniz convolutions over the multiset
antidiagonal: a gauge-field symbol carrying `x` derivatives against a matter symbol
carrying `y`, summed over all splittings `s = x + y`. Expanded in bases, both correction
terms of this file are scalar combinations of such convolutions of plain products in `B`,
which is why `lorentzMix_derivConv` — the mixing operator is a morphism for the
convolution — is what carries a Lorentz law through a covariant derivative.

-/

section DerivConv

variable {B : Type} [Ring B] [Algebra ℂ B]

omit [Algebra ℂ B] in
/-- A finite sum inside a multiset sum may be taken outside. -/
lemma multiset_sum_map_sum {α ι : Type*} [Fintype ι] (m : Multiset α) (F : ι → α → B) :
    (m.map fun x => ∑ i, F i x).sum = ∑ i, (m.map (F i)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih, Finset.sum_add_distrib]

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
  simp only [derivConv, Finset.mul_sum, mul_smul_comm, multiset_sum_map_sum,
    Multiset.smul_sum, Multiset.map_map, Function.comp_def]

/-- The convolution is linear in its left-hand family. -/
lemma derivConv_sum_left {ι : Type*} [Fintype ι] (g : Multiset (Fin 1 ⊕ Fin 3) → B)
    (c : ι → ℂ) (f : ι → Multiset (Fin 1 ⊕ Fin 3) → B) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    derivConv (fun r => ∑ i, c i • f i r) g s = ∑ i, c i • derivConv (f i) g s := by
  simp only [derivConv, Finset.sum_mul, smul_mul_assoc, multiset_sum_map_sum,
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

end DerivConv

/-!

## C. The Lorentz law of a covariant tower

A covariant tower is built one slot at a time: the tower along `l 0 :: l'` is the tower
along `l'` with one more plain derivative, plus a correction term `C (l 0)` applied to the
tower along `l'`. Both towers of this file have that shape, with the derived action of the
gauge field or the derived bracket as correction, and both corrections are Lorentz
covariant, linear in the family they correct, and compatible with a twist of the value
index. That is all the induction uses, so it is run once, for an abstract tower `T`
transforming into a possibly different tower `T'`: the covariant slots mix by their own
columns of the Lorentz matrix, the plain slots by `lorentzMix`, and the value index by `τ`.

-/

section Tower

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The Lorentz law of a Leibniz convolution: the mixing operator is a morphism for the
  convolution, so a convolution of two families with Lorentz laws has one too. -/
lemma repLorentz_derivConv
    (hmul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B), repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    (Λ : SL(2,ℂ)) (f f' g g' : Multiset (Fin 1 ⊕ Fin 3) → B)
    (hf : ∀ x, repLorentz Λ (f x) = lorentzMix Λ f' x 0)
    (hg : ∀ y, repLorentz Λ (g y) = lorentzMix Λ g' y 0) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repLorentz Λ (derivConv f g s) = lorentzMix Λ (derivConv f' g') s 0 := by
  rw [derivConv, map_multiset_sum, Multiset.map_map, ← lorentzMix_derivConv, derivConv]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => by
    rw [Function.comp_apply, hmul, hf, hg])

/-- The Lorentz law of a covariant tower. The tower `T` is built by the step `hstep` out of
  a correction `C`, and so is the tower `T'` it transforms into; the seed of `T` transforms
  into the seed of `T'` with the value index twisted by `τ` (`hzero`); and the correction is
  Lorentz covariant (`hC`), linear in the family it corrects (`hClin`), and lets the twist
  through (`hCτ`). Then the covariant slots mix by their own columns, the plain slots by
  `lorentzMix`, and the value index by `τ`. -/
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
        sum_fin_succ_prod_smul]
      -- both sides as double sums over the first direction and the lower tuple
      simp only [lorentzMix_cons_zero, hClin, hCτ, hstep', Fin.cons_zero, Fin.cons_succ,
        LinearMap.add_apply, lorentzMix_add_fam, lorentzMix_sum_fam, lorentzMix_smul_fam,
        Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => by rw [mul_comm]

end Tower

/-!

## D. The covariant tower of a matter family

The covariant derivative of a matter family adds one ordered derivative slot and a Leibniz
correction `A_ρ · F`, the derived action of the gauge field on the value index through the
infinitesimal action `act`. Expanded in bases, the correction is a scalar combination of
Leibniz convolutions of gauge-field symbols against matter symbols, which gives its Lorentz
law and its linearity in the matter family. The twist of the value index is the
contragredient action `rep.dual Λ`, and it passes through the correction because the gauge
action commutes with the Lorentz action on the value space: that is the one hypothesis
about the species that the Lorentz law needs, and conjugation transports it to the
conjugate families.

-/

namespace GaugeAlgebraRealization

open _root_.GaugeAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
  Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
variable {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V}
variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ JetGaugeGroupI B}
variable (h : GaugeAlgebraRealization localGaugeData B repGauge repLorentz)

/-- Rotating a triple sum so that the innermost index comes first. -/
lemma sum_comm₃ {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (X : α → β → γ → M) : (∑ a, ∑ b, ∑ c, X a b c) = ∑ c, ∑ a, ∑ b, X a b c :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- A scalar combination of convolutions against the gauge field is linear in the
  right-hand families. -/
lemma sum_derivConv_sum_fam {ι κ ι' : Type} [Fintype ι] [Fintype κ] [Fintype ι']
    (f : ι → Multiset (Fin 1 ⊕ Fin 3) → B) (coef : ι → κ → ℂ) (c : ι' → ℂ)
    (g : ι' → κ → Multiset (Fin 1 ⊕ Fin 3) → B) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    ∑ j, ∑ k, coef j k • derivConv (f j) (fun y => ∑ i, c i • g i k y) s =
      ∑ i, c i • ∑ j, ∑ k, coef j k • derivConv (f j) (g i k) s := by
  simp only [derivConv_sum_right, Finset.smul_sum, smul_smul, mul_comm]
  exact sum_comm₃ _

/-- A Lorentz law in the tuple form, read on the underlying multisets: the transformed
  family mixes by `lorentzMix`. -/
lemma repLorentz_eq_lorentzMix (Λ : SL(2,ℂ)) (f g : Multiset (Fin 1 ⊕ Fin 3) → B)
    (hfg : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)), repLorentz Λ (f (List.ofFn l)) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i)) • g (List.ofFn p))
    (x : Multiset (Fin 1 ⊕ Fin 3)) : repLorentz Λ (f x) = lorentzMix Λ g x 0 := by
  obtain ⟨n, l, rfl⟩ : ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)), x = List.ofFn l :=
    ⟨_, x.toList.get, by rw [List.ofFn_get, Multiset.coe_toList]⟩
  rw [hfg n l, lorentzMix_ofFn]
  exact Finset.sum_congr rfl fun p _ => by rw [add_zero]

/-- The Lorentz law of the gauge-field symbols, in the multiset form. -/
lemma repLorentz_apply_mix (Λ : SL(2,ℂ))
    (x : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (χ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (h.A x μ χ) = lorentzMix Λ (fun t => ∑ a, L[Λ] a μ • h.A t a χ) x 0 :=
  repLorentz_eq_lorentzMix Λ (fun x => h.A x μ χ) (fun t => ∑ a, L[Λ] a μ • h.A t a χ)
    (fun n l => h.lorentz_apply Λ n l μ χ) x

omit [FiniteDimensional ℂ V] in
/-- The Lorentz law of a family of derivative symbols, in the multiset form. -/
lemma isLorentzDerivTransforms_mix {rep : Representation ℂ SL(2,ℂ) V}
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : IsLorentzDerivTransforms repLorentz rep F) (Λ : SL(2,ℂ))
    (x : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V) :
    repLorentz Λ (F x χ) = lorentzMix Λ (fun t => F t (rep.dual Λ χ)) x 0 :=
  repLorentz_eq_lorentzMix Λ (fun x => F x χ) (fun t => F t (rep.dual Λ χ))
    (fun n l => hF Λ n l χ) x

/-- The Lorentz law of a scalar combination of convolutions against the gauge field: the
  direction of the gauge field mixes by its own column, the derivative slots by
  `lorentzMix`, and the right-hand families are replaced by their transforms. -/
lemma repLorentz_sum_derivConv (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    {ι κ : Type} [Fintype ι] [Fintype κ] (bg : Module.Basis ι ℝ GaugeAlgebra) (coef : ι → κ → ℂ)
    (g g' : κ → Multiset (Fin 1 ⊕ Fin 3) → B)
    (hg : ∀ k y, repLorentz Λ (g k y) = lorentzMix Λ (g' k) y 0) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repLorentz Λ (∑ j, ∑ k, coef j k • derivConv (fun x => h.A x ρ (bg.coord j)) (g k) s) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ
        (fun t => ∑ j, ∑ k, coef j k • derivConv (fun x => h.A x a (bg.coord j)) (g' k) t) s 0 := by
  have h1 : ∀ j k, repLorentz Λ (derivConv (fun x => h.A x ρ (bg.coord j)) (g k) s) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ (derivConv (fun x => h.A x a (bg.coord j)) (g' k)) s 0 := by
    intro j k
    rw [repLorentz_derivConv h.repLorentz_mul Λ _
      (fun t => ∑ a, L[Λ] a ρ • h.A t a (bg.coord j)) _ (g' k)
      (fun x => repLorentz_apply_mix h Λ x ρ _) (hg k)]
    simp only [← lorentzMix_smul_fam, ← lorentzMix_sum_fam]
    exact congrArg (fun G => lorentzMix Λ G s 0) (funext fun r => derivConv_sum_left _ _ _ r)
  simp only [map_sum, map_smul, h1, lorentzMix_sum_fam, lorentzMix_smul_fam, Finset.smul_sum,
    smul_smul, mul_comm]
  exact sum_comm₃ _

/-- The action of families expanded in bases of the gauge algebra and the value space. -/
lemma actionFam_apply_eq_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (bg : Module.Basis ι ℝ GaugeAlgebra) (bv : Module.Basis κ ℂ V)
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B)
    (φ : Module.Dual ℂ V) :
    actionFam act f g φ =
      ∑ j, ∑ k, φ (act (bg j) (bv k)) • (f (bg.coord j) * g (bv.coord k)) := by
  rw [actionFam, dualPairEquiv_symm_eq_sum bg f, dualPairEquivC_symm_eq_sum bv g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul]
  rw [Finset.sum_comm]

/-- The derived action family expanded in bases. -/
lemma actionFamConv_eq_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (bg : Module.Basis ι ℝ GaugeAlgebra) (bv : Module.Basis κ ℂ V)
    (ρ : Fin 1 ⊕ Fin 3) (G : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    actionFamConv A act ρ G s φ = ∑ j, ∑ k, φ (act (bg j) (bv k)) •
      derivConv (fun x => A x ρ (bg.coord j)) (fun y => G y (bv.coord k)) s := by
  simp only [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_def,
    actionFam_apply_eq_sum bg bv, multiset_sum_map_sum, derivConv, Multiset.smul_sum]

/-- The derived action family is linear in the matter family. -/
lemma actionFamConv_sum_fam {ι : Type} [Fintype ι] (ρ : Fin 1 ⊕ Fin 3) (c : ι → ℂ)
    (H : ι → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    actionFamConv A act ρ (fun t => ∑ i, c i • H i t) s φ =
      ∑ i, c i • actionFamConv A act ρ (H i) s φ := by
  classical
  simp only [actionFamConv_eq_sum (Module.finBasis ℝ GaugeAlgebra) (Module.finBasis ℂ V),
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact sum_derivConv_sum_fam _ _ _ _ s

/-- The Lorentz law of the derived action family: the derivative slots mix, the direction
  of the gauge field mixes by its own column, and the value index is carried by the
  transformed matter family. -/
lemma repLorentz_actionFamConv (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (G G' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (hG : ∀ y χ, repLorentz Λ (G y χ) = lorentzMix Λ (fun t => G' t χ) y 0)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repLorentz Λ (actionFamConv h.A act ρ G s φ) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ (fun t => actionFamConv h.A act a G' t φ) s 0 := by
  classical
  set bg := Module.finBasis ℝ GaugeAlgebra
  set bv := Module.finBasis ℂ V
  simp only [actionFamConv_eq_sum bg bv]
  exact repLorentz_sum_derivConv h Λ ρ bg (fun j k => φ (act (bg j) (bv k)))
    (fun k y => G y (bv.coord k)) (fun k t => G' t (bv.coord k)) (fun k y => hG y _) s

omit [FiniteDimensional ℂ V] in
/-- The twist of the value index past the gauge action: an endomorphism commuting with
  the gauge action may be moved from the dual basis onto the dual vector. -/
lemma dual_twist {κ : Type} [Fintype κ] (bv : Module.Basis κ ℂ V) (T : V →ₗ[ℂ] V)
    (hT : ∀ (c : GaugeAlgebra) (v : V), act c (T v) = T (act c v))
    (ψ : Module.Dual ℂ V →ₗ[ℂ] B) (c : GaugeAlgebra) (φ : Module.Dual ℂ V) :
    ∑ k, φ (act c (bv k)) • ψ (T.dualMap (bv.coord k)) =
      ∑ k, (T.dualMap φ) (act c (bv k)) • ψ (bv.coord k) := by
  simp only [← map_smul, ← map_sum]
  rw [show (∑ k, φ (act c (bv k)) • bv.coord k) = φ ∘ₗ act c from
      bv.sum_dual_apply_smul_coord (φ ∘ₗ act c),
    show (∑ k, (T.dualMap φ) (act c (bv k)) • bv.coord k) = (T.dualMap φ) ∘ₗ act c from
      bv.sum_dual_apply_smul_coord ((T.dualMap φ) ∘ₗ act c)]
  exact congrArg ψ (LinearMap.ext fun v => congrArg φ (hT c v))

/-- The contragredient action may be pulled out of an action of families, provided the
  gauge action commutes with it on the value space. -/
lemma actionFam_comp_dual (T : V →ₗ[ℂ] V)
    (hT : ∀ (c : GaugeAlgebra) (v : V), act c (T v) = T (act c v))
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B)
    (φ : Module.Dual ℂ V) :
    actionFam act f (g ∘ₗ T.dualMap) φ = actionFam act f g (T.dualMap φ) := by
  classical
  simp only [actionFam_apply_eq_sum (Module.finBasis ℝ GaugeAlgebra) (Module.finBasis ℂ V),
    LinearMap.comp_apply, ← mul_smul_comm, ← Finset.mul_sum, dual_twist _ T hT g]

/-- The contragredient action may be pulled out of a derived action family. -/
lemma actionFamConv_comp_dual (T : V →ₗ[ℂ] V)
    (hT : ∀ (c : GaugeAlgebra) (v : V), act c (T v) = T (act c v)) (ρ : Fin 1 ⊕ Fin 3)
    (K : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    actionFamConv A act ρ (fun t => K t ∘ₗ T.dualMap) s φ =
      actionFamConv A act ρ K s (T.dualMap φ) := by
  simp only [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_def,
    actionFam_comp_dual T hT]

/-- The Lorentz law of the iterated covariant derivative of a matter family: the ordered
  covariant slots mix by their own columns and the multiset of plain derivative slots
  mixes by `lorentzMix`, while the value index transforms contragrediently. -/
lemma repLorentz_covDerivIter {rep : Representation ℂ SL(2,ℂ) V}
    (hcomm : ∀ (c : GaugeAlgebra) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (hF : IsLorentzDerivTransforms repLorentz rep F) (Λ : SL(2,ℂ))
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repLorentz Λ (covDerivIter h.A act F n l s φ) = ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
      (∏ i, L[Λ] (p i) (l i)) •
        lorentzMix Λ (fun t => covDerivIter h.A act F n p t (rep.dual Λ φ)) s 0 :=
  repLorentz_tower Λ (covDerivIter h.A act F) (covDerivIter h.A act F) (actionFamConv h.A act)
    (rep.dual Λ) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ s φ => isLorentzDerivTransforms_mix hF Λ s φ)
    (fun ρ G G' hG s φ => repLorentz_actionFamConv h Λ ρ G G' hG s φ)
    (fun ρ _ _ c G s φ => actionFamConv_sum_fam ρ c G s φ)
    (fun ρ G s φ => actionFamConv_comp_dual (rep Λ⁻¹) (fun c v => hcomm c Λ⁻¹ v) ρ G s φ)
    n l s φ

/-- The iterated covariant derivative of a matter family transforms as the covariant
  derivatives of a Lorentz-covariant field, given the Lorentz law of the bare symbols,
  the Lorentz law of the gauge field, and the commutation of the infinitesimal gauge
  action with the Lorentz action on the value space. -/
theorem isLorentzCovDerivTransforms_covDerivIter {rep : Representation ℂ SL(2,ℂ) V}
    (hcomm : ∀ (c : GaugeAlgebra) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (hF : IsLorentzDerivTransforms repLorentz rep F) :
    IsLorentzCovDerivTransforms repLorentz rep (fun {n} l => covDerivIter h.A act F n l 0) := by
  intro Λ n l φ
  rw [repLorentz_covDerivIter h hcomm F hF Λ n l 0 φ]
  simp only [lorentzMix_zero]

omit [FiniteDimensional ℂ V] in
/-- Conjugation preserves the commutation of the gauge action with the Lorentz action:
  both are read on the conjugate module through the same underlying maps. -/
lemma actionConj_comm_repConj (rep : Representation ℂ SL(2,ℂ) V)
    (hcomm : ∀ (c : GaugeAlgebra) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (c : GaugeAlgebra) (Λ : SL(2,ℂ)) (v : ConjModule V) :
    LocalGaugeData.actionConj act c (rep.conj Λ v) =
      rep.conj Λ (LocalGaugeData.actionConj act c v) :=
  congrArg (conjEquiv (k := ℂ) (M := V)) (hcomm c Λ _)

/-- The Lorentz law of the covariant tower of a conjugate family, from the commutation of
  the gauge action with the Lorentz action of the unconjugated species. -/
theorem isLorentzCovDerivTransforms_covDerivIter_conj {rep : Representation ℂ SL(2,ℂ) V}
    (hcomm : ∀ (c : GaugeAlgebra) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule V) →ₗ[ℂ] B)
    (hF : IsLorentzDerivTransforms repLorentz rep.conj F) :
    IsLorentzCovDerivTransforms repLorentz rep.conj
      (fun {n} l => covDerivIter h.A (LocalGaugeData.actionConj act) F n l 0) :=
  isLorentzCovDerivTransforms_covDerivIter h (actionConj_comm_repConj rep hcomm) F hF

/-!

## E. The covariant tower of the field strength

The covariant derivative of an adjoint family has the shape of that of a matter family,
with the bracket `⁅A_ρ, ·⁆` in place of the action on the value index; the gauge index
carries no Lorentz weight, so the twist is the identity, and the induction of section C
applies with `bracketFamConv` in place of `actionFamConv`. What is new is the seed: the
field strength carries two covector indices, and its Lorentz law
(`repLorentz_fieldStrength_mix`) mixes both. The tower is linear in its seed, so it
inherits the antisymmetry of the field strength.

-/

/-- The derived bracket family expanded in a basis of the gauge algebra. -/
lemma bracketFamConv_eq_sum (ρ : Fin 1 ⊕ Fin 3)
    (G : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    bracketFamConv A ρ G s φ =
      ∑ j, ∑ k, ((φ ⁅Module.Free.chooseBasis ℝ GaugeAlgebra j,
            Module.Free.chooseBasis ℝ GaugeAlgebra k⁆ : ℝ) : ℂ) •
        derivConv (fun x => A x ρ ((Module.Free.chooseBasis ℝ GaugeAlgebra).coord j))
          (fun y => G y ((Module.Free.chooseBasis ℝ GaugeAlgebra).coord k)) s := by
  simp only [bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_def,
    bracketFam_apply_eq_sum, multiset_sum_map_sum, derivConv, Multiset.smul_sum,
    Complex.coe_smul]

/-- The derived bracket family is linear in the second family. -/
lemma bracketFamConv_sum_fam {ι : Type} [Fintype ι] (ρ : Fin 1 ⊕ Fin 3) (c : ι → ℂ)
    (H : ι → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    bracketFamConv A ρ (fun t => ∑ i, c i • H i t) s φ =
      ∑ i, c i • bracketFamConv A ρ (H i) s φ := by
  simp only [bracketFamConv_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply]
  exact sum_derivConv_sum_fam _ _ _ _ s

/-- The Lorentz law of the derived bracket family. -/
lemma repLorentz_bracketFamConv (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (G G' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (hG : ∀ y χ, repLorentz Λ (G y χ) = lorentzMix Λ (fun t => G' t χ) y 0)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (bracketFamConv h.A ρ G s φ) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ (fun t => bracketFamConv h.A a G' t φ) s 0 := by
  set bg := Module.Free.chooseBasis ℝ GaugeAlgebra
  simp only [bracketFamConv_eq_sum]
  exact repLorentz_sum_derivConv h Λ ρ bg (fun j k => ((φ ⁅bg j, bg k⁆ : ℝ) : ℂ))
    (fun k y => G y (bg.coord k)) (fun k t => G' t (bg.coord k)) (fun k y => hG y _) s

/-- The Lorentz law of the iterated covariant derivative in the adjoint: the covariant
  slots mix by their own columns and the seed family is replaced by its transform. -/
lemma repLorentz_iteratedCovDerivAdjoint (Λ : SL(2,ℂ))
    (F F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (hF : ∀ x χ, repLorentz Λ (F x χ) = lorentzMix Λ (fun t => F' t χ) x 0)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (x : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (iteratedCovDerivAdjoint h.A (List.ofFn l) F x φ) = ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
      (∏ i, L[Λ] (p i) (l i)) •
        lorentzMix Λ (fun t => iteratedCovDerivAdjoint h.A (List.ofFn p) F' t φ) x 0 := by
  have := repLorentz_tower Λ (fun n l => iteratedCovDerivAdjoint h.A (List.ofFn l) F)
    (fun n l => iteratedCovDerivAdjoint h.A (List.ofFn l) F') (bracketFamConv h.A) LinearMap.id
    (fun _ l _ => by rw [List.ofFn_succ]; rfl) (fun _ l _ => by rw [List.ofFn_succ]; rfl)
    (fun _ x φ => hF x φ) (fun ρ G G' hG s φ => repLorentz_bracketFamConv h Λ ρ G G' hG s φ)
    (fun ρ _ _ c G s φ => bracketFamConv_sum_fam ρ c G s φ)
    (fun _ _ _ _ => by simp only [LinearMap.comp_id, LinearMap.id_apply]) n l x φ
  simpa only [LinearMap.id_apply] using this

/-- The iterated covariant derivative in the adjoint is linear in the seed family. -/
lemma iteratedCovDerivAdjoint_sum_fam {ι : Type} [Fintype ι] (c : ι → ℂ)
    (H : ι → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) :
    ∀ (l : List (Fin 1 ⊕ Fin 3)) (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra),
      iteratedCovDerivAdjoint A l (fun t => ∑ i, c i • H i t) x φ =
        ∑ i, c i • iteratedCovDerivAdjoint A l (H i) x φ
  | [], x, φ => by simp only [iteratedCovDerivAdjoint, LinearMap.sum_apply, LinearMap.smul_apply]
  | ρ :: l, x, φ => by
      have hfam : iteratedCovDerivAdjoint A l (fun t => ∑ i, c i • H i t) =
          fun t => ∑ i, c i • iteratedCovDerivAdjoint A l (H i) t :=
        funext fun t => LinearMap.ext fun χ => by
          simp only [iteratedCovDerivAdjoint_sum_fam c H l t χ, LinearMap.sum_apply,
            LinearMap.smul_apply]
      simp only [iteratedCovDerivAdjoint, covDerivAdjoint_apply, hfam, bracketFamConv_sum_fam,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_add, Finset.sum_add_distrib]

/-- The iterated covariant derivative is odd in the family it differentiates: the case of
  a one-element index in `iteratedCovDerivAdjoint_sum_fam`. -/
lemma iteratedCovDerivAdjoint_neg_fam
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (l : List (Fin 1 ⊕ Fin 3)) (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    iteratedCovDerivAdjoint A l (fun t => - F t) x φ = - iteratedCovDerivAdjoint A l F x φ := by
  simpa using iteratedCovDerivAdjoint_sum_fam (A := A) (fun _ : Fin 1 => (-1 : ℂ)) (fun _ => F) l x
    φ

/-- The Lorentz law of the field strength: both covector indices mix by their columns,
  and the derivative slots mix by `lorentzMix`. -/
lemma repLorentz_fieldStrength_mix (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (fieldStrength h.A μ ν x φ) =
      lorentzMix Λ (fun t => ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • fieldStrength h.A a b t φ) x 0 := by
  -- the derivative terms
  have hder : ∀ κ σ, repLorentz Λ (h.A (κ ::ₘ x) σ φ) =
      lorentzMix Λ (fun t => ∑ a, L[Λ] a κ • ∑ b, L[Λ] b σ • h.A (a ::ₘ t) b φ) x 0 := by
    intro κ σ
    simp only [repLorentz_apply_mix h Λ (κ ::ₘ x) σ φ, lorentzMix_cons_zero, lorentzMix_sum_fam,
      lorentzMix_smul_fam]
  -- the commutator term
  have hcomm : repLorentz Λ (commutatorFam h.A μ ν x φ) =
      lorentzMix Λ (fun t => ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • commutatorFam h.A a b t φ) x 0 := by
    have hG : ∀ y χ, repLorentz Λ (h.A y ν χ) =
        lorentzMix Λ (fun t => (∑ b, L[Λ] b ν • h.A t b) χ) y 0 := fun y χ => by
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using repLorentz_apply_mix h Λ y ν χ
    rw [show commutatorFam h.A μ ν x = bracketFamConv h.A μ (fun r => h.A r ν) x from rfl,
      repLorentz_bracketFamConv h Λ μ _ _ hG x φ]
    simp only [lorentzMix_sum_fam, lorentzMix_smul_fam, bracketFamConv_sum_fam]
    rfl
  -- the second derivative term, with its two sums exchanged
  have hswap : (fun t => ∑ a, L[Λ] a ν • ∑ b, L[Λ] b μ • h.A (a ::ₘ t) b φ) =
      fun t => ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • h.A (b ::ₘ t) a φ := by
    funext t
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  rw [fieldStrength_apply, map_add, map_sub, hder μ ν, hder ν μ, hswap, hcomm,
    ← lorentzMix_sub_fam, ← lorentzMix_add_fam]
  refine congrArg (fun G => lorentzMix Λ G x 0) (funext fun t => ?_)
  simp only [fieldStrength_apply, smul_sub, smul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

/-- The Lorentz law of the covariant tower of the field strength: the covariant slots
  mix by their own columns and the two covector indices of the field strength mix by
  theirs. -/
lemma repLorentz_iteratedCovDerivAdjoint_fieldStrength (Λ : SL(2,ℂ)) (n : ℕ)
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (iteratedCovDerivAdjoint h.A (List.ofFn l) (fieldStrength h.A μ ν) 0 φ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i)) • ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν •
        iteratedCovDerivAdjoint h.A (List.ofFn p) (fieldStrength h.A a b) 0 φ := by
  have hF' : ∀ y χ, repLorentz Λ (fieldStrength h.A μ ν y χ) =
      lorentzMix Λ (fun t => (∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • fieldStrength h.A a b t) χ) y 0 :=
    fun y χ => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using
      repLorentz_fieldStrength_mix h Λ μ ν y χ
  rw [repLorentz_iteratedCovDerivAdjoint h Λ (fieldStrength h.A μ ν) _ hF' n l 0 φ]
  simp only [lorentzMix_zero, iteratedCovDerivAdjoint_sum_fam]

end GaugeAlgebraRealization

/-!

## F. What a covariant tower inherits from its family

Facts about the covariant tower of a single matter family, in the form the field algebra
consumes. The span lemma
`GaugeAlgebraRealization.adjoin_symbols_eq_adjoin_covDerivIter` says that the
bare symbols and the tower generate the same algebra over the gauge-field symbols, so each
is a polynomial in the other; the tower commutes with the gauge-field symbols as soon as
the bare symbols do; and a pure gauge jet acts trivially through the dual base-point
coefficient of a representation whose zeroth Taylor coefficient it fixes.

-/

namespace GaugeAlgebraRealization

open _root_.GaugeAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V) (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)

/-- A bare matter symbol is a polynomial in the gauge-field symbols and the covariant
  tower of its family. -/
lemma symbol_mem_adjoin {X : Set B} (hA : ∀ s μ ψ, A s μ ψ ∈ X)
    (hF : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, covDerivIter A act F n l 0 φ ∈ X)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) : F s φ ∈ Algebra.adjoin ℂ X := by
  refine Algebra.adjoin_mono ?_ ((adjoin_symbols_eq_adjoin_covDerivIter (A := A) act F).le
    (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩)))
  rintro b (⟨s, μ, ψ, rfl⟩ | ⟨n, l, φ, rfl⟩)
  exacts [hA s μ ψ, hF n l φ]

/-- A symbol of a covariant tower is a polynomial in the gauge-field symbols and the bare
  symbols of its family. -/
lemma covDerivIter_mem_adjoin {X : Set B} (hA : ∀ s μ ψ, A s μ ψ ∈ X)
    (hF : ∀ s φ, F s φ ∈ X) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    covDerivIter A act F n l 0 φ ∈ Algebra.adjoin ℂ X := by
  refine Algebra.adjoin_mono ?_ (covDerivIter_mem_adjoin_symbols act F n l 0 φ)
  rintro b (⟨s, μ, ψ, rfl⟩ | ⟨s, φ, rfl⟩)
  exacts [hA s μ ψ, hF s φ]

/-- A symbol of a covariant tower commutes with the gauge-field symbols, as soon as the
  bare symbols of its family do. -/
lemma commute_covDerivIter
    (hAA : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
      (ψ ψ' : Module.Dual ℝ GaugeAlgebra), Commute (A s μ ψ) (A s' μ' ψ'))
    (hAF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V), Commute (A s μ ψ) (F s' φ))
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra) :
    Commute (covDerivIter A act F n l 0 φ) (A p μ ψ) := by
  refine commute_of_mem_adjoin ?_ (covDerivIter_mem_adjoin_symbols act F n l 0 φ)
  rintro y (⟨s, μ', ψ', rfl⟩ | ⟨s, φ', rfl⟩)
  exacts [hAA s p μ' μ ψ' ψ, (hAF p μ ψ s φ').symm]

omit [FiniteDimensional ℂ V] in
/-- A pure gauge jet acts trivially through the dual base-point coefficient of a
  representation whose zeroth Taylor coefficient is the identity on pure jets. -/
lemma repDualCoeff_zero_of_mem_truncationKer_zero
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    (hrep : ∀ {W : JetGaugeGroupI}, localGaugeData.eval W = 1 → repCoeff rep W 0 = LinearMap.id)
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ V) :
    repDualCoeff rep U.1⁻¹ 0 φ = φ := by
  have hU : localGaugeData.eval U.1⁻¹ = 1 := by
    rw [map_inv, localGaugeData.mem_truncationKer_zero_iff.mp U.2, inv_one]
  rw [show repDualCoeff rep U.1⁻¹ 0 = (repCoeff rep U.1⁻¹ 0).dualMap from rfl, hrep hU]
  rfl

end GaugeAlgebraRealization

/-!

## G. The field algebra and the covariant towers

The field algebra is the algebra generated by every derivative symbol of the theory. The
covariant towers are the iterated covariant derivatives of the twelve matter families along
ordered tuples of directions, evaluated at the empty multiset, each built with the
infinitesimal action of its species (`actionConj` of it for a conjugate family), together
with the iterated covariant derivative of the field strength along a list of directions.
The set `matterTowers` collects the matter towers, and `matterTowers_induction` is the case
split over them that the rest of the file runs.

-/

namespace AlgebraRealization

open _root_.GaugeAlgebraRealization _root_.StandardModel.GaugeAlgebraRealization
open LocalGaugeData JetComponentSpace

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-- The generators of the field algebra: every derivative symbol of the gauge field, of
  the Higgs and its conjugate, and of the three generations of each fermion species and
  their conjugates. -/
def symbols : Set B :=
  (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (h.A s μ)) ∪
    (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)), Set.range (h.H s) ∪ Set.range (h.barH s)) ∪
    (⋃ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)),
      Set.range (h.d i s) ∪ Set.range (h.bard i s) ∪
      Set.range (h.u i s) ∪ Set.range (h.baru i s) ∪
      Set.range (h.Q i s) ∪ Set.range (h.barQ i s) ∪
      Set.range (h.L i s) ∪ Set.range (h.barL i s) ∪
      Set.range (h.e i s) ∪ Set.range (h.bare i s))

/-- The algebra generated by all the fields of the Standard Model and their derivative
  symbols: the gauge field, the Higgs and its conjugate, and the three families of each
  fermion species with their conjugates. -/
def fieldAlgebra : Subalgebra ℂ B := Algebra.adjoin ℂ h.symbols

/-- The iterated covariant derivative of the Higgs field. -/
noncomputable def covDerivH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ HiggsVec →ₗ[ℂ] B :=
  covDerivIter h.A HiggsVec.gaugeAlgebraAction h.H n l 0

/-- The iterated covariant derivative of the conjugate Higgs field. -/
noncomputable def covDerivBarH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B :=
  covDerivIter h.A (actionConj HiggsVec.gaugeAlgebraAction) h.barH n l 0

/-- The iterated covariant derivative of the down-type quarks. -/
noncomputable def covDerivD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ DownSinglet →ₗ[ℂ] B :=
  covDerivIter h.A DownSinglet.gaugeAlgebraAction (h.d i) n l 0

/-- The iterated covariant derivative of the conjugate down-type quarks. -/
noncomputable def covDerivBarD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B :=
  covDerivIter h.A (actionConj DownSinglet.gaugeAlgebraAction) (h.bard i) n l 0

/-- The iterated covariant derivative of the up-type quarks. -/
noncomputable def covDerivU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ UpSinglet →ₗ[ℂ] B :=
  covDerivIter h.A UpSinglet.gaugeAlgebraAction (h.u i) n l 0

/-- The iterated covariant derivative of the conjugate up-type quarks. -/
noncomputable def covDerivBarU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B :=
  covDerivIter h.A (actionConj UpSinglet.gaugeAlgebraAction) (h.baru i) n l 0

/-- The iterated covariant derivative of the quark doublets. -/
noncomputable def covDerivQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B :=
  covDerivIter h.A QuarkDoublet.gaugeAlgebraAction (h.Q i) n l 0

/-- The iterated covariant derivative of the conjugate quark doublets. -/
noncomputable def covDerivBarQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B :=
  covDerivIter h.A (actionConj QuarkDoublet.gaugeAlgebraAction) (h.barQ i) n l 0

/-- The iterated covariant derivative of the lepton doublets. -/
noncomputable def covDerivL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B :=
  covDerivIter h.A LeptonDoublet.gaugeAlgebraAction (h.L i) n l 0

/-- The iterated covariant derivative of the conjugate lepton doublets. -/
noncomputable def covDerivBarL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B :=
  covDerivIter h.A (actionConj LeptonDoublet.gaugeAlgebraAction) (h.barL i) n l 0

/-- The iterated covariant derivative of the lepton singlets. -/
noncomputable def covDerivE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B :=
  covDerivIter h.A LeptonSinglet.gaugeAlgebraAction (h.e i) n l 0

/-- The iterated covariant derivative of the conjugate lepton singlets. -/
noncomputable def covDerivBarE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B :=
  covDerivIter h.A (actionConj LeptonSinglet.gaugeAlgebraAction) (h.bare i) n l 0

/-- The iterated covariant derivative `∇_{l₁} ⋯ ∇_{lₙ} F_{μν}` of the field strength of the
  gauge field, along an ordered list of directions. -/
noncomputable def covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  iteratedCovDerivAdjoint h.A l (fieldStrength h.A μ ν) 0

/-- The covariant towers of the twelve matter families: every symbol of every tower. -/
def matterTowers : Set B :=
  (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
    Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
  (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
    Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
    Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
    Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
    Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
    Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))

/-- A property of every symbol of every matter tower is proved tower by tower. -/
lemma matterTowers_induction (P : B → Prop) {b : B} (hb : b ∈ h.matterTowers)
    (hH : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivH l φ))
    (hbarH : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivBarH l φ))
    (hd : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivD i l φ))
    (hbard : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivBarD i l φ))
    (hu : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivU i l φ))
    (hbaru : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivBarU i l φ))
    (hQ : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivQ i l φ))
    (hbarQ : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivBarQ i l φ))
    (hL : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivL i l φ))
    (hbarL : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivBarL i l φ))
    (he : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivE i l φ))
    (hbare : ∀ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ, P (h.covDerivBarE i l φ)) :
    P b := by
  rcases hb with hb | hb
  · simp only [Set.mem_iUnion] at hb
    obtain ⟨n, l, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hb
    exacts [hH n l φ, hbarH n l φ]
  · simp only [Set.mem_iUnion] at hb
    obtain ⟨i, n, l, hb⟩ := hb
    rcases hb with (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
      ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)
    exacts [hd i n l φ, hbard i n l φ, hu i n l φ, hbaru i n l φ, hQ i n l φ, hbarQ i n l φ,
      hL i n l φ, hbarL i n l φ, he i n l φ, hbare i n l φ]

/-!

## H. The covariant towers generate the field algebra

The span lemma of section F, for the twelve families at once: each bare symbol is a
polynomial in the gauge-field symbols and its own tower, and each tower symbol is a
polynomial in the gauge-field symbols and its own bare symbols.

-/

/-- Every bare symbol is a polynomial in the gauge-field symbols and the matter towers. -/
lemma symbols_subset_adjoin_matterTowers :
    h.symbols ⊆ Algebra.adjoin ℂ
      ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (h.A s μ)) ∪
        h.matterTowers) := by
  have hA : ∀ s μ ψ, h.A s μ ψ ∈
      (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (h.A s μ)) ∪
        h.matterTowers :=
    fun s μ ψ => Or.inl (Set.mem_iUnion_of_mem s (Set.mem_iUnion_of_mem μ ⟨ψ, rfl⟩))
  have hH : ∀ {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (b : B),
      b ∈ Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l) → b ∈ h.matterTowers :=
    fun l b hb => Or.inl (Set.mem_iUnion_of_mem _ (Set.mem_iUnion_of_mem l hb))
  have hf : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (b : B),
      b ∈ Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l) → b ∈ h.matterTowers :=
    fun i {_} l b hb => Or.inr (Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem _
      (Set.mem_iUnion_of_mem l hb)))
  rintro b ((hb | hb) | hb)
  · exact Algebra.subset_adjoin (Or.inl hb)
  · simp only [Set.mem_iUnion] at hb
    obtain ⟨s, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hb
    · exact symbol_mem_adjoin HiggsVec.gaugeAlgebraAction h.H hA
        (fun n l φ => Or.inr (hH l _ (by simp [covDerivH]))) s φ
    · exact symbol_mem_adjoin (actionConj HiggsVec.gaugeAlgebraAction) h.barH hA
        (fun n l φ => Or.inr (hH l _ (by simp [covDerivBarH]))) s φ
  · simp only [Set.mem_iUnion] at hb
    obtain ⟨i, s, hb⟩ := hb
    rcases hb with (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
      ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)
    · exact symbol_mem_adjoin DownSinglet.gaugeAlgebraAction (h.d i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivD]))) s φ
    · exact symbol_mem_adjoin (actionConj DownSinglet.gaugeAlgebraAction) (h.bard i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivBarD]))) s φ
    · exact symbol_mem_adjoin UpSinglet.gaugeAlgebraAction (h.u i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivU]))) s φ
    · exact symbol_mem_adjoin (actionConj UpSinglet.gaugeAlgebraAction) (h.baru i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivBarU]))) s φ
    · exact symbol_mem_adjoin QuarkDoublet.gaugeAlgebraAction (h.Q i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivQ]))) s φ
    · exact symbol_mem_adjoin (actionConj QuarkDoublet.gaugeAlgebraAction) (h.barQ i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivBarQ]))) s φ
    · exact symbol_mem_adjoin LeptonDoublet.gaugeAlgebraAction (h.L i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivL]))) s φ
    · exact symbol_mem_adjoin (actionConj LeptonDoublet.gaugeAlgebraAction) (h.barL i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivBarL]))) s φ
    · exact symbol_mem_adjoin LeptonSinglet.gaugeAlgebraAction (h.e i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivE]))) s φ
    · exact symbol_mem_adjoin (actionConj LeptonSinglet.gaugeAlgebraAction) (h.bare i) hA
        (fun n l φ => Or.inr (hf i l _ (by simp [covDerivBarE]))) s φ

/-- The covariant towers generate the field algebra: replacing the plain derivative
  symbols of every matter field by their covariant derivative towers does not change the
  generated algebra; only the gauge-field symbols remain plain. -/
lemma fieldAlgebra_eq_covDeriv :
    h.fieldAlgebra = Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (h.A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
  rw [Set.union_assoc]
  refine le_antisymm (Algebra.adjoin_le h.symbols_subset_adjoin_matterTowers)
    (Algebra.adjoin_le ?_)
  have hA : ∀ s μ ψ, h.A s μ ψ ∈ h.symbols :=
    fun s μ ψ => Or.inl (Or.inl (Set.mem_iUnion_of_mem s (Set.mem_iUnion_of_mem μ ⟨ψ, rfl⟩)))
  -- every symbol of a tower is a polynomial in the gauge-field symbols and its bare symbols
  rintro b (hb | hb)
  · exact Algebra.subset_adjoin (Or.inl (Or.inl hb))
  · refine h.matterTowers_induction (· ∈ Algebra.adjoin ℂ h.symbols) hb
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun n l φ => covDerivIter_mem_adjoin _ _ hA (fun s φ =>
        Or.inl (Or.inr (Set.mem_iUnion_of_mem s (by simp)))) n l φ
    · exact fun n l φ => covDerivIter_mem_adjoin _ _ hA (fun s φ =>
        Or.inl (Or.inr (Set.mem_iUnion_of_mem s (by simp)))) n l φ
    all_goals exact fun i n l φ => covDerivIter_mem_adjoin _ _ hA (fun s φ =>
        Or.inr (Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem s (by simp)))) n l φ

/-!

## I. Gauge covariance of the covariant towers

Each matter tower transforms in the representation of its species, by
`TransformsIn.covDerivIter`, and the field-strength tower in the adjoint. At the base point
that is the action of the base-point value of the gauge jet alone (`repJet_covDerivIter`),
and a pure gauge jet — one with trivial base-point value — fixes every tower. The section
instantiates this species by species, the conjugate families through the conjugate action
and representation.

-/

/-- The covariant tower of a matter family transforms through the base point of a gauge
  jet alone, given the gauge law of the family and the infinitesimal action of its
  species. -/
lemma repJet_covDerivIter {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)} {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V}
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B} (hF : TransformsIn repJet rep F)
    (hact : localGaugeData.IsInfinitesimalActionOf act rep) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI) (φ : Module.Dual ℂ V) :
    repJet U (covDerivIter h.A act F n l 0 φ) =
      covDerivIter h.A act F n l 0 (repDualCoeff rep U⁻¹ 0 φ) :=
  (TransformsIn.covDerivIter h.gaugeRealization hF hact n l).repGauge_zero U φ

/-- The Higgs tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ HiggsVec) : repJet U (h.covDerivH l φ) =
      h.covDerivH l (repDualCoeff HiggsVec.repJetGaugeGroupI U⁻¹ 0 φ) :=
  h.repJet_covDerivIter h.repJet_H HiggsVec.isInfinitesimalActionOf l U φ

/-- The conjugate Higgs tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivBarH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) : repJet U (h.covDerivBarH l φ) =
      h.covDerivBarH l (repDualCoeff (repConj HiggsVec.repJetGaugeGroupI) U⁻¹ 0 φ) :=
  h.repJet_covDerivIter h.repJet_barH HiggsVec.isInfinitesimalActionOf.conj l U φ

/-- The down-type quark tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ DownSinglet) : repJet U (h.covDerivD i l φ) =
      h.covDerivD i l (repDualCoeff DownSinglet.repJetGaugeGroupI U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_d i) DownSinglet.isInfinitesimalActionOf l U φ

/-- The conjugate down-type quark tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivBarD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) : repJet U (h.covDerivBarD i l φ) =
      h.covDerivBarD i l (repDualCoeff (repConj DownSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_bard i) DownSinglet.isInfinitesimalActionOf.conj l U φ

/-- The up-type quark tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ UpSinglet) : repJet U (h.covDerivU i l φ) =
      h.covDerivU i l (repDualCoeff UpSinglet.repJetGaugeGroupI U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_u i) UpSinglet.isInfinitesimalActionOf l U φ

/-- The conjugate up-type quark tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivBarU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) : repJet U (h.covDerivBarU i l φ) =
      h.covDerivBarU i l (repDualCoeff (repConj UpSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_baru i) UpSinglet.isInfinitesimalActionOf.conj l U φ

/-- The quark doublet tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ QuarkDoublet) : repJet U (h.covDerivQ i l φ) =
      h.covDerivQ i l (repDualCoeff QuarkDoublet.repJetGaugeGroupI U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_Q i) QuarkDoublet.isInfinitesimalActionOf l U φ

/-- The conjugate quark doublet tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivBarQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) : repJet U (h.covDerivBarQ i l φ) =
      h.covDerivBarQ i l (repDualCoeff (repConj QuarkDoublet.repJetGaugeGroupI) U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_barQ i) QuarkDoublet.isInfinitesimalActionOf.conj l U φ

/-- The lepton doublet tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ LeptonDoublet) : repJet U (h.covDerivL i l φ) =
      h.covDerivL i l (repDualCoeff LeptonDoublet.repJetGaugeGroupI U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_L i) LeptonDoublet.isInfinitesimalActionOf l U φ

/-- The conjugate lepton doublet tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivBarL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) : repJet U (h.covDerivBarL i l φ) =
      h.covDerivBarL i l (repDualCoeff (repConj LeptonDoublet.repJetGaugeGroupI) U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_barL i) LeptonDoublet.isInfinitesimalActionOf.conj l U φ

/-- The lepton singlet tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ LeptonSinglet) : repJet U (h.covDerivE i l φ) =
      h.covDerivE i l (repDualCoeff LeptonSinglet.repJetGaugeGroupI U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_e i) LeptonSinglet.isInfinitesimalActionOf l U φ

/-- The conjugate lepton singlet tower transforms through the base point of a gauge jet. -/
lemma repJet_covDerivBarE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI)
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) : repJet U (h.covDerivBarE i l φ) =
      h.covDerivBarE i l (repDualCoeff (repConj LeptonSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) :=
  h.repJet_covDerivIter (h.repJet_bare i) LeptonSinglet.isInfinitesimalActionOf.conj l U φ

/-- A pure gauge jet fixes the Higgs tower. -/
lemma repJet_covDerivH_of_mem_truncationKer_zero {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ HiggsVec) :
    repJet U.1 (h.covDerivH l φ) = h.covDerivH l φ := by
  rw [h.repJet_covDerivH, repDualCoeff_zero_of_mem_truncationKer_zero
    HiggsVec.repCoeff_zero_of_eval_eq_one]

/-- A pure gauge jet fixes the conjugate Higgs tower. -/
lemma repJet_covDerivBarH_of_mem_truncationKer_zero {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    repJet U.1 (h.covDerivBarH l φ) = h.covDerivBarH l φ := by
  rw [h.repJet_covDerivBarH, repDualCoeff_zero_of_mem_truncationKer_zero fun hW =>
    repCoeff_repConj_zero_eq_id (HiggsVec.repCoeff_zero_of_eval_eq_one hW)]

/-- A pure gauge jet fixes the down-type quark tower. -/
lemma repJet_covDerivD_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ DownSinglet) :
    repJet U.1 (h.covDerivD i l φ) = h.covDerivD i l φ := by
  rw [h.repJet_covDerivD, repDualCoeff_zero_of_mem_truncationKer_zero
    DownSinglet.repCoeff_zero_of_eval_eq_one]

/-- A pure gauge jet fixes the conjugate down-type quark tower. -/
lemma repJet_covDerivBarD_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : localGaugeData.truncationKer 0)
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    repJet U.1 (h.covDerivBarD i l φ) = h.covDerivBarD i l φ := by
  rw [h.repJet_covDerivBarD, repDualCoeff_zero_of_mem_truncationKer_zero fun hW =>
    repCoeff_repConj_zero_eq_id (DownSinglet.repCoeff_zero_of_eval_eq_one hW)]

/-- A pure gauge jet fixes the up-type quark tower. -/
lemma repJet_covDerivU_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ UpSinglet) :
    repJet U.1 (h.covDerivU i l φ) = h.covDerivU i l φ := by
  rw [h.repJet_covDerivU, repDualCoeff_zero_of_mem_truncationKer_zero
    UpSinglet.repCoeff_zero_of_eval_eq_one]

/-- A pure gauge jet fixes the conjugate up-type quark tower. -/
lemma repJet_covDerivBarU_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : localGaugeData.truncationKer 0)
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    repJet U.1 (h.covDerivBarU i l φ) = h.covDerivBarU i l φ := by
  rw [h.repJet_covDerivBarU, repDualCoeff_zero_of_mem_truncationKer_zero fun hW =>
    repCoeff_repConj_zero_eq_id (UpSinglet.repCoeff_zero_of_eval_eq_one hW)]

/-- A pure gauge jet fixes the quark doublet tower. -/
lemma repJet_covDerivQ_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ QuarkDoublet) :
    repJet U.1 (h.covDerivQ i l φ) = h.covDerivQ i l φ := by
  rw [h.repJet_covDerivQ, repDualCoeff_zero_of_mem_truncationKer_zero
    QuarkDoublet.repCoeff_zero_of_eval_eq_one]

/-- A pure gauge jet fixes the conjugate quark doublet tower. -/
lemma repJet_covDerivBarQ_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : localGaugeData.truncationKer 0)
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    repJet U.1 (h.covDerivBarQ i l φ) = h.covDerivBarQ i l φ := by
  rw [h.repJet_covDerivBarQ, repDualCoeff_zero_of_mem_truncationKer_zero fun hW =>
    repCoeff_repConj_zero_eq_id (QuarkDoublet.repCoeff_zero_of_eval_eq_one hW)]

/-- A pure gauge jet fixes the lepton doublet tower. -/
lemma repJet_covDerivL_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ LeptonDoublet) :
    repJet U.1 (h.covDerivL i l φ) = h.covDerivL i l φ := by
  rw [h.repJet_covDerivL, repDualCoeff_zero_of_mem_truncationKer_zero
    LeptonDoublet.repCoeff_zero_of_eval_eq_one]

/-- A pure gauge jet fixes the conjugate lepton doublet tower. -/
lemma repJet_covDerivBarL_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : localGaugeData.truncationKer 0)
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    repJet U.1 (h.covDerivBarL i l φ) = h.covDerivBarL i l φ := by
  rw [h.repJet_covDerivBarL, repDualCoeff_zero_of_mem_truncationKer_zero fun hW =>
    repCoeff_repConj_zero_eq_id (LeptonDoublet.repCoeff_zero_of_eval_eq_one hW)]

/-- A pure gauge jet fixes the lepton singlet tower. -/
lemma repJet_covDerivE_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : localGaugeData.truncationKer 0) (φ : Module.Dual ℂ LeptonSinglet) :
    repJet U.1 (h.covDerivE i l φ) = h.covDerivE i l φ := by
  rw [h.repJet_covDerivE, repDualCoeff_zero_of_mem_truncationKer_zero
    LeptonSinglet.repCoeff_zero_of_eval_eq_one]

/-- A pure gauge jet fixes the conjugate lepton singlet tower. -/
lemma repJet_covDerivBarE_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : localGaugeData.truncationKer 0)
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    repJet U.1 (h.covDerivBarE i l φ) = h.covDerivBarE i l φ := by
  rw [h.repJet_covDerivBarE, repDualCoeff_zero_of_mem_truncationKer_zero fun hW =>
    repCoeff_repConj_zero_eq_id (LeptonSinglet.repCoeff_zero_of_eval_eq_one hW)]

/-- The covariant tower of the field strength is antisymmetric in its two covector
  indices: the field strength itself is, the gauge-field symbols commuting, and the
  iterated covariant derivative is odd in the family it differentiates. -/
lemma covDerivFieldStrength_swap (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    h.covDerivFieldStrength l ν μ φ = - h.covDerivFieldStrength l μ ν φ := by
  rw [covDerivFieldStrength, covDerivFieldStrength,
    show fieldStrength h.A ν μ = fun t => - fieldStrength h.A μ ν t from
      funext fun t => fieldStrength_swap h.A h.A_comm_A μ ν t,
    iteratedCovDerivAdjoint_neg_fam]

/-- The covariant tower of the field strength transforms through the base point of a gauge
  jet: no derivative of the gauge transformation enters. -/
lemma repJet_covDerivFieldStrength (U : JetGaugeGroupI) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repJet U (h.covDerivFieldStrength l μ ν φ) =
      h.covDerivFieldStrength l μ ν (localGaugeData.adjointDualCoeff U⁻¹ 0 φ) :=
  (transformsInAdjoint_iteratedCovDerivAdjoint h.gaugeRealization l μ ν).repGauge_zero U φ

/-- A pure gauge jet fixes the covariant tower of the field strength. -/
lemma repJet_covDerivFieldStrength_of_mem_truncationKer_zero
    (U : localGaugeData.truncationKer 0) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repJet U.1 (h.covDerivFieldStrength l μ ν φ) = h.covDerivFieldStrength l μ ν φ :=
  repGauge_iteratedCovDerivAdjoint_fieldStrength_of_mem_truncationKer_zero h.gaugeRealization
    U l μ ν φ

/-!

## J. The Lorentz laws of the covariant matter towers

`isLorentzCovDerivTransforms_covDerivIter` and its `_conj` form turn the bare Lorentz law
of each family, recorded by `AlgebraRealization`, into that of its covariant tower, given
the commutation of the infinitesimal gauge action of the species with its Lorentz action.
Each species proves that commutation next to its `gaugeAlgebraAction`
(`HiggsVec.gaugeAlgebraAction_comm_repLorentz` and, for the fermions,
`gaugeAlgebraAction_comm_repLorentzGroup` in its own `GaugeAlgebraAction.lean`).

-/

/-- The Higgs tower transforms as a Lorentz scalar. -/
lemma repLorentz_covDerivH : IsLorentzCovDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec) (fun {_n} l => h.covDerivH l) :=
  isLorentzCovDerivTransforms_covDerivIter h.gaugeRealization
    HiggsVec.gaugeAlgebraAction_comm_repLorentz h.H h.repLorentz_H

/-- The conjugate Higgs tower transforms as a Lorentz scalar. -/
lemma repLorentz_covDerivBarH : IsLorentzCovDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj (fun {_n} l => h.covDerivBarH l) :=
  isLorentzCovDerivTransforms_covDerivIter_conj h.gaugeRealization
    HiggsVec.gaugeAlgebraAction_comm_repLorentz h.barH h.repLorentz_barH

/-- The down-type quark tower transforms as a right-handed Weyl spinor. -/
lemma repLorentz_covDerivD (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    DownSinglet.repLorentzGroup (fun {_n} l => h.covDerivD i l) :=
  isLorentzCovDerivTransforms_covDerivIter h.gaugeRealization
    DownSinglet.gaugeAlgebraAction_comm_repLorentzGroup (h.d i) (h.repLorentz_d i)

/-- The conjugate down-type quark tower transforms in the conjugate Weyl representation. -/
lemma repLorentz_covDerivBarD (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    DownSinglet.repLorentzGroup.conj (fun {_n} l => h.covDerivBarD i l) :=
  isLorentzCovDerivTransforms_covDerivIter_conj h.gaugeRealization
    DownSinglet.gaugeAlgebraAction_comm_repLorentzGroup (h.bard i) (h.repLorentz_bard i)

/-- The up-type quark tower transforms as a right-handed Weyl spinor. -/
lemma repLorentz_covDerivU (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    UpSinglet.repLorentzGroup (fun {_n} l => h.covDerivU i l) :=
  isLorentzCovDerivTransforms_covDerivIter h.gaugeRealization
    UpSinglet.gaugeAlgebraAction_comm_repLorentzGroup (h.u i) (h.repLorentz_u i)

/-- The conjugate up-type quark tower transforms in the conjugate Weyl representation. -/
lemma repLorentz_covDerivBarU (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    UpSinglet.repLorentzGroup.conj (fun {_n} l => h.covDerivBarU i l) :=
  isLorentzCovDerivTransforms_covDerivIter_conj h.gaugeRealization
    UpSinglet.gaugeAlgebraAction_comm_repLorentzGroup (h.baru i) (h.repLorentz_baru i)

/-- The quark doublet tower transforms as a left-handed Weyl spinor. -/
lemma repLorentz_covDerivQ (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup (fun {_n} l => h.covDerivQ i l) :=
  isLorentzCovDerivTransforms_covDerivIter h.gaugeRealization
    QuarkDoublet.gaugeAlgebraAction_comm_repLorentzGroup (h.Q i) (h.repLorentz_Q i)

/-- The conjugate quark doublet tower transforms in the conjugate Weyl representation. -/
lemma repLorentz_covDerivBarQ (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup.conj (fun {_n} l => h.covDerivBarQ i l) :=
  isLorentzCovDerivTransforms_covDerivIter_conj h.gaugeRealization
    QuarkDoublet.gaugeAlgebraAction_comm_repLorentzGroup (h.barQ i) (h.repLorentz_barQ i)

/-- The lepton doublet tower transforms as a left-handed Weyl spinor. -/
lemma repLorentz_covDerivL (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup (fun {_n} l => h.covDerivL i l) :=
  isLorentzCovDerivTransforms_covDerivIter h.gaugeRealization
    LeptonDoublet.gaugeAlgebraAction_comm_repLorentzGroup (h.L i) (h.repLorentz_L i)

/-- The conjugate lepton doublet tower transforms in the conjugate Weyl representation. -/
lemma repLorentz_covDerivBarL (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup.conj (fun {_n} l => h.covDerivBarL i l) :=
  isLorentzCovDerivTransforms_covDerivIter_conj h.gaugeRealization
    LeptonDoublet.gaugeAlgebraAction_comm_repLorentzGroup (h.barL i) (h.repLorentz_barL i)

/-- The lepton singlet tower transforms as a right-handed Weyl spinor. -/
lemma repLorentz_covDerivE (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup (fun {_n} l => h.covDerivE i l) :=
  isLorentzCovDerivTransforms_covDerivIter h.gaugeRealization
    LeptonSinglet.gaugeAlgebraAction_comm_repLorentzGroup (h.e i) (h.repLorentz_e i)

/-- The conjugate lepton singlet tower transforms in the conjugate Weyl representation. -/
lemma repLorentz_covDerivBarE (i : Fin 3) : IsLorentzCovDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup.conj (fun {_n} l => h.covDerivBarE i l) :=
  isLorentzCovDerivTransforms_covDerivIter_conj h.gaugeRealization
    LeptonSinglet.gaugeAlgebraAction_comm_repLorentzGroup (h.bare i) (h.repLorentz_bare i)

end AlgebraRealization

end StandardModel
