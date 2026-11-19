/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.BiFund
/-!
# The Levi-Civita tensors of `SU(N)`

Up to scale, the Levi-Civita symbol is the only invariant with `N` fundamental indices of
`SU(N)`, and the only one with `N` anti-fundamental indices.

## i. Overview

The Levi-Civita symbol `ε_a`, for `a : Fin N → Fin N`, is the sign of `a` when `a` is a
permutation and zero when a label repeats (A). Contracting its indices with the rows `a` of a
matrix `M` gives `ε_a det M`. So the tensors with these components, `leviCivitaFund N` with `N`
fundamental indices and `leviCivitaAntiFund N` with `N` anti-fundamental indices, are invariant,
because `det g = 1` (B).

Conversely, let the components `c` of a tensor with `N` fundamental indices be fixed by `SU(N)`
(C). If a label of `a` repeats, some label `q` is missed by `a`. Take a label `p` that `a` hits
`m` times, and the diagonal element of `SU(N)` with a primitive `(N + 1)`-th root of unity `ω`
at `p`, its conjugate at `q` and one elsewhere. It scales `c a` by `ω ^ m` with `0 < m ≤ N`, so
`c a = 0`. The quarter turn in the plane of two labels `p` and `q` is a signed transposition, and
it gives `c (swap p q ∘ σ) = -c σ` for every permutation `σ`. By induction over transpositions
`c σ = sign σ * c id`, and so `c = c id • ε`. On anti-fundamental indices `g` acts through its
complex conjugate, itself an element of `SU(N)`, and the same holds (D).

In terms of Mathlib's invariants, the invariant tensors are the line through the Levi-Civita
tensor, and for an intertwining map out of the tensors the invariants in its range are the line
through its image (E). For `N = 2` the Levi-Civita tensors are the antisymmetric symbols
`epsilonFund` and `epsilonAntiFund` (F).

## ii. Key results

- `suTensor.leviCivitaCoeff` : the Levi-Civita symbol.
- `suTensor.sum_prod_mul_leviCivitaCoeff` : contracting it with the rows of a matrix gives the
  determinant.
- `suTensor.leviCivitaFund`, `suTensor.leviCivitaAntiFund` : the Levi-Civita tensors.
- `suTensor.exists_eq_smul_leviCivitaFund_of_invariant` : the invariant tensors with `N`
  fundamental indices are its multiples, and its anti-fundamental twin.
- `suTensor.invariants_tensorRep_eq_span_leviCivitaFund` : the invariant tensors are the line
  through it, and its anti-fundamental twin.
- `suTensor.leviCivitaFund_two` : for `SU(2)` it is the antisymmetric symbol.

## iii. Table of contents

- A. The Levi-Civita symbol
- B. The Levi-Civita tensors are invariant
- C. Components fixed by `SU(N)`
- D. The invariant tensors
- E. The invariants in Mathlib's form
- F. Two indices

## iv. References

* None.

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies Tensor SU Equiv
open GlobalGaugeGroup (rootOfUnity rootOfUnity_isPrimitiveRoot rootOfUnity_mul_star)

variable {N : ℕ}

/-!

## A. The Levi-Civita symbol

-/

/-- The Levi-Civita symbol `ε_a` of `N` labels. It is the sign of `a` when `a` is a permutation of
  `Fin N`, and zero when a label repeats. -/
def leviCivitaCoeff (a : Fin N → Fin N) : ℂ :=
  ∑ σ : Perm (Fin N), if ⇑σ = a then (Perm.sign σ : ℂ) else 0

/-- A sum against the Levi-Civita symbol is a signed sum over the permutations. -/
lemma sum_mul_leviCivitaCoeff (F : (Fin N → Fin N) → ℂ) :
    ∑ a, F a * leviCivitaCoeff a = ∑ σ : Perm (Fin N), (Perm.sign σ : ℂ) * F σ := by
  simp only [leviCivitaCoeff, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ => by simp [Finset.sum_ite_eq, mul_comm]

/-- The Levi-Civita symbol at a permutation is its sign. -/
@[simp]
lemma leviCivitaCoeff_perm (σ : Perm (Fin N)) : leviCivitaCoeff ⇑σ = (Perm.sign σ : ℂ) := by
  rw [leviCivitaCoeff, Finset.sum_eq_single σ (fun τ _ hτ => ?_) (by simp)]
  · simp
  · simp [show ⇑τ ≠ ⇑σ from fun h => hτ (DFunLike.coe_injective h)]

/-- The Levi-Civita symbol vanishes when a label repeats. -/
lemma leviCivitaCoeff_of_not_injective {a : Fin N → Fin N} (ha : ¬ Function.Injective a) :
    leviCivitaCoeff a = 0 :=
  Finset.sum_eq_zero fun σ _ => by
    simp only [ite_eq_right_iff]
    rintro rfl
    exact absurd σ.injective ha

/-- The Levi-Civita symbol at the identity is one. -/
@[simp]
lemma leviCivitaCoeff_id : leviCivitaCoeff (id : Fin N → Fin N) = 1 := by
  simpa using leviCivitaCoeff_perm (1 : Perm (Fin N))

/-- Contracting the indices of the Levi-Civita symbol with the rows `a` of a matrix `M` gives
  `ε_a det M`. -/
lemma sum_prod_mul_leviCivitaCoeff (M : Matrix (Fin N) (Fin N) ℂ) (a : Fin N → Fin N) :
    ∑ b, (∏ i, M (a i) (b i)) * leviCivitaCoeff b = leviCivitaCoeff a * M.det := by
  have h : ∑ σ : Perm (Fin N), (Perm.sign σ : ℂ) * ∏ i, M (a i) (σ i)
      = (M.submatrix a id).det := by
    rw [← det_transpose, det_apply']
    rfl
  rw [sum_mul_leviCivitaCoeff, h]
  by_cases ha : Function.Injective a
  · have hσ : a = ⇑(Equiv.ofBijective a (Finite.injective_iff_bijective.1 ha)) := rfl
    rw [hσ, det_permute, leviCivitaCoeff_perm]
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 ha
    rw [leviCivitaCoeff_of_not_injective ha, zero_mul]
    exact det_zero_of_row_eq hne (funext fun k => by simp [hij])

/-!

## B. The Levi-Civita tensors are invariant

-/

variable (N) in
/-- The Levi-Civita tensor `ε^{a₁ … a_N}` with `N` fundamental indices. -/
noncomputable def leviCivitaFund : (suTensor N).Tensor fun _ : Fin N => .fund :=
  ∑ a : Fin N → Fin N, leviCivitaCoeff a •
    Tensor.basis (S := suTensor N) (fun _ : Fin N => Color.fund) a

variable (N) in
/-- The Levi-Civita tensor `ε_{a₁ … a_N}` with `N` anti-fundamental indices. -/
noncomputable def leviCivitaAntiFund : (suTensor N).Tensor fun _ : Fin N => .antiFund :=
  ∑ a : Fin N → Fin N, leviCivitaCoeff a •
    Tensor.basis (S := suTensor N) (fun _ : Fin N => Color.antiFund) a

lemma basis_repr_leviCivitaFund (a : Fin N → Fin N) :
    (Tensor.basis _).repr (leviCivitaFund N) a = leviCivitaCoeff a := by
  rw [leviCivitaFund, Module.Basis.repr_sum_self]

lemma basis_repr_leviCivitaAntiFund (a : Fin N → Fin N) :
    (Tensor.basis _).repr (leviCivitaAntiFund N) a = leviCivitaCoeff a := by
  rw [leviCivitaAntiFund, Module.Basis.repr_sum_self]

lemma det_val (g : SU N) : g.1.det = 1 := (mem_specialUnitaryGroup_iff.mp g.2).2

/-- The complex conjugate of an element of `SU(N)` has determinant one. -/
lemma det_map_star_val (g : SU N) : (g.1.map star).det = 1 := by
  have h := RingHom.map_det (starRingEnd ℂ) g.1
  rw [det_val, map_one] at h
  exact h.symm

/-- The Levi-Civita tensor with `N` fundamental indices is invariant, since `g^{⊗N}` scales it by
  `det g = 1`. -/
lemma leviCivitaFund_invariant (g : SU N) : g • leviCivitaFund N = leviCivitaFund N := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun a => ?_)
  rw [basis_repr_smul_fund]
  simp only [basis_repr_leviCivitaFund]
  rw [sum_prod_mul_leviCivitaCoeff, det_val, mul_one]

/-- The Levi-Civita tensor with `N` anti-fundamental indices is invariant, since `ḡ^{⊗N}` scales it
  by the conjugate of `det g = 1`. -/
lemma leviCivitaAntiFund_invariant (g : SU N) :
    g • leviCivitaAntiFund N = leviCivitaAntiFund N := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun a => ?_)
  rw [basis_repr_smul_antiFund]
  simp only [basis_repr_leviCivitaAntiFund]
  exact (sum_prod_mul_leviCivitaCoeff (g.1.map star) a).trans (by rw [det_map_star_val, mul_one])

/-!

## C. Components fixed by `SU(N)`

-/

/-- The quarter turn in the plane of `p` and `q` is the signed transposition sending `e_p` to
  `e_q` and `e_q` to `-e_p`. -/
lemma quarterTurn_val_apply {p q : Fin N} (hpq : p ≠ q) (x y : Fin N) :
    (planeEmbed p q hpq (rotation 0 1 (by norm_num))).1 x y
      = (if x = p then -1 else 1) * (if swap p q x = y then 1 else 0) := by
  simp only [planeEmbed_val, rotation_val, planeMatrix, Matrix.add_apply, one_apply,
    Matrix.mul_apply, transpose_apply, planeInclusion_apply, Matrix.sub_apply, Fin.sum_univ_two,
    swap_apply_def]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hyp : y = p <;>
    by_cases hyq : y = q <;>
    simp_all [Ne.symm hpq, @eq_comm _ p y, @eq_comm _ q y]

section Components

variable {c : (Fin N → Fin N) → ℂ}
  (hc : ∀ (g : SU N) (a : Fin N → Fin N), c a = ∑ b, (∏ i, g.1 (a i) (b i)) * c b)

include hc in
/-- A diagonal element of `SU(N)` scales each component by the product of its diagonal entries at
  the labels. -/
lemma eq_prod_mul_of_diagonal {g : SU N} {d : Fin N → ℂ} (hg : g.1 = diagonal d)
    (a : Fin N → Fin N) : c a = (∏ i, d (a i)) * c a := by
  conv_lhs => rw [hc g a]
  rw [Finset.sum_eq_single a (fun b _ hb => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, Ne.symm hi]), zero_mul]) (by simp)]
  simp [hg]

include hc in
/-- A component with a repeated label vanishes. Some label `q` is then missed, and the diagonal
  element with `ω` at `p = a q`, `ω̄` at `q` and one elsewhere, for `ω` a primitive `(N + 1)`-th
  root of unity, scales the component by `ω ^ m`, with `m` the number of labels equal to `p`. -/
lemma eq_zero_of_not_injective {a : Fin N → Fin N} (ha : ¬ Function.Injective a) : c a = 0 := by
  obtain ⟨q, hq⟩ : ∃ q, ∀ i, a i ≠ q := by
    simpa [Function.Surjective] using mt Finite.injective_iff_surjective.2 ha
  have hpq : a q ≠ q := hq q
  set m := (Finset.univ.filter fun i => a i = a q).card
  set d : Fin N → ℂ := fun x =>
    if x = a q then rootOfUnity (N + 1) else if x = q then star (rootOfUnity (N + 1)) else 1
  have hg : (planeEmbed (a q) q hpq (diagPhase (rootOfUnity (N + 1)) rootOfUnity_mul_star)).1
      = diagonal d := by
    rw [planeEmbed_val, diagPhase_val, planeMatrix_diagonal hpq]
  have hprod : ∏ i, d (a i) = rootOfUnity (N + 1) ^ m := by
    rw [← Finset.prod_const, Finset.prod_filter]
    exact Finset.prod_congr rfl fun i _ => by simp [d, hq i]
  have hm0 : m ≠ 0 := Finset.card_ne_zero.2 ⟨q, by simp⟩
  have hmN : m < N + 1 := Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))
  have hne := (rootOfUnity_isPrimitiveRoot N.succ_ne_zero).pow_ne_one_of_pos_of_lt hm0 hmN
  have h := eq_prod_mul_of_diagonal hc hg a
  rw [hprod] at h
  have h' : (1 - rootOfUnity (N + 1) ^ m) * c a = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 (Ne.symm hne))

/-- The product of the quarter turn's entries along a permutation `σ` and labels `b` is `-1` when
  `b` is `swap p q ∘ σ` and zero otherwise. -/
lemma prod_quarterTurn_val {p q : Fin N} (hpq : p ≠ q) (σ : Perm (Fin N)) (b : Fin N → Fin N) :
    ∏ i, (planeEmbed p q hpq (rotation 0 1 (by norm_num))).1 (σ i) (b i)
      = if b = ⇑(swap p q * σ) then -1 else 0 := by
  simp only [quarterTurn_val_apply hpq, Finset.prod_mul_distrib, Finset.prod_boole,
    Finset.mem_univ, true_implies]
  rw [Equiv.prod_comp σ (fun x => if x = p then (-1 : ℂ) else 1), Finset.prod_ite_eq']
  by_cases hb : b = ⇑(swap p q * σ)
  · simp [hb]
  · have h : ¬ ∀ i, swap p q (σ i) = b i := fun h => hb (funext fun i => (h i).symm)
    rw [ite_eq_right h, ite_eq_right hb, mul_zero]

include hc in
/-- The quarter turn in the plane of `p` and `q` gives `c (swap p q ∘ σ) = -c σ`. -/
lemma swap_mul_eq_neg {p q : Fin N} (hpq : p ≠ q) (σ : Perm (Fin N)) :
    c ⇑(swap p q * σ) = -c σ := by
  have h := hc (planeEmbed p q hpq (rotation 0 1 (by norm_num))) σ
  simp only [prod_quarterTurn_val hpq, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  linear_combination h

include hc in
/-- The component at a permutation is its sign times the component at the identity. -/
lemma eq_sign_mul (σ : Perm (Fin N)) : c σ = (Perm.sign σ : ℂ) * c id := by
  induction σ using Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih =>
    rw [swap_mul_eq_neg hc hxy, ih, Perm.sign_mul, Perm.sign_swap hxy]
    push_cast
    ring

include hc in
/-- Components fixed by `SU(N)` are those of a multiple of the Levi-Civita symbol. -/
lemma eq_mul_leviCivitaCoeff (a : Fin N → Fin N) : c a = c id * leviCivitaCoeff a := by
  by_cases ha : Function.Injective a
  · have hσ : a = ⇑(Equiv.ofBijective a (Finite.injective_iff_bijective.1 ha)) := rfl
    rw [hσ, eq_sign_mul hc, leviCivitaCoeff_perm, mul_comm]
  · rw [eq_zero_of_not_injective hc ha, leviCivitaCoeff_of_not_injective ha, mul_zero]

end Components

/-!

## D. The invariant tensors

-/

/-- An invariant tensor with `N` fundamental indices of `SU(N)` is a multiple of the Levi-Civita
  tensor. -/
lemma exists_eq_smul_leviCivitaFund_of_invariant
    (t : (suTensor N).Tensor fun _ : Fin N => .fund) (ht : ∀ g : SU N, g • t = t) :
    ∃ z : ℂ, t = z • leviCivitaFund N := by
  have hc : ∀ (g : SU N) (a : Fin N → Fin N), (Tensor.basis _).repr t a
      = ∑ b, (∏ i, g.1 (a i) (b i)) * (Tensor.basis _).repr t b := fun g a => by
    rw [← basis_repr_smul_fund, ht]
  refine ⟨(Tensor.basis _).repr t id, (Tensor.basis _).repr.injective (Finsupp.ext fun a => ?_)⟩
  rw [map_smul, Finsupp.smul_apply, basis_repr_leviCivitaFund, smul_eq_mul]
  exact eq_mul_leviCivitaCoeff hc a

/-- The complex conjugate of an element of `SU(N)`, itself an element of `SU(N)`. -/
noncomputable def starElem (g : SU N) : SU N :=
  ⟨g.1.map star, mem_specialUnitaryGroup_iff.2
    ⟨map_star_mem_unitaryGroup_iff.2 (mem_specialUnitaryGroup_iff.1 g.2).1, det_map_star_val g⟩⟩

@[simp]
lemma starElem_val (g : SU N) : (starElem g).1 = g.1.map star := rfl

/-- An invariant tensor with `N` anti-fundamental indices of `SU(N)` is a multiple of the
  Levi-Civita tensor. Here `g` acts through its complex conjugate, which runs over `SU(N)` with
  `g`. -/
lemma exists_eq_smul_leviCivitaAntiFund_of_invariant
    (t : (suTensor N).Tensor fun _ : Fin N => .antiFund) (ht : ∀ g : SU N, g • t = t) :
    ∃ z : ℂ, t = z • leviCivitaAntiFund N := by
  have hc : ∀ (g : SU N) (a : Fin N → Fin N), (Tensor.basis _).repr t a
      = ∑ b, (∏ i, g.1 (a i) (b i)) * (Tensor.basis _).repr t b := fun g a => by
    have h := basis_repr_smul_antiFund (starElem g) t a
    rw [ht] at h
    simpa using h
  refine ⟨(Tensor.basis _).repr t id, (Tensor.basis _).repr.injective (Finsupp.ext fun a => ?_)⟩
  rw [map_smul, Finsupp.smul_apply, basis_repr_leviCivitaAntiFund, smul_eq_mul]
  exact eq_mul_leviCivitaCoeff hc a

/-!

## E. The invariants in Mathlib's form

-/

/-- The invariant tensors with `N` fundamental indices of `SU(N)` are the line through the
  Levi-Civita tensor. -/
lemma invariants_tensorRep_eq_span_leviCivitaFund :
    ((suTensor N).tensorRep fun _ : Fin N => .fund).invariants = ℂ ∙ leviCivitaFund N :=
  invariants_tensorRep_eq_span_singleton leviCivitaFund_invariant
    exists_eq_smul_leviCivitaFund_of_invariant

/-- The invariant tensors with `N` anti-fundamental indices of `SU(N)` are the line through the
  Levi-Civita tensor. -/
lemma invariants_tensorRep_eq_span_leviCivitaAntiFund :
    ((suTensor N).tensorRep fun _ : Fin N => .antiFund).invariants
      = ℂ ∙ leviCivitaAntiFund N :=
  invariants_tensorRep_eq_span_singleton leviCivitaAntiFund_invariant
    exists_eq_smul_leviCivitaAntiFund_of_invariant

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}

/-- For an intertwining map `f` out of the tensors with `N` fundamental indices, the invariants in
  the range of `f` are the line through the image of the Levi-Civita tensor. -/
lemma invariants_inf_range_eq_span_map_leviCivitaFund
    (f : ((suTensor N).tensorRep fun _ : Fin N => .fund).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f (leviCivitaFund N) :=
  (isAdjointClosed N _).invariants_inf_range_eq_span invariants_tensorRep_eq_span_leviCivitaFund f

/-- For an intertwining map `f` out of the tensors with `N` anti-fundamental indices, the
  invariants in the range of `f` are the line through the image of the Levi-Civita tensor. -/
lemma invariants_inf_range_eq_span_map_leviCivitaAntiFund
    (f : ((suTensor N).tensorRep fun _ : Fin N => .antiFund).IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = ℂ ∙ f (leviCivitaAntiFund N) :=
  (isAdjointClosed N _).invariants_inf_range_eq_span
    invariants_tensorRep_eq_span_leviCivitaAntiFund f

/-!

## F. Two indices

-/

/-- On two labels the Levi-Civita symbol is `1` at `01`, `-1` at `10` and `0` otherwise. -/
lemma leviCivitaCoeff_two (a : Fin 2 → Fin 2) :
    leviCivitaCoeff a = (if a = ![0, 1] then 1 else 0) - (if a = ![1, 0] then 1 else 0) := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin 2, a = ![x, y] := ⟨a 0, a 1, by
    funext i
    fin_cases i <;> rfl⟩
  have h01 : (![0, 1] : Fin 2 → Fin 2) = ⇑(1 : Perm (Fin 2)) := by
    funext i
    fin_cases i <;> rfl
  have h10 : (![1, 0] : Fin 2 → Fin 2) = ⇑(swap (0 : Fin 2) 1) := by
    funext i
    fin_cases i <;> simp
  have hd : ∀ z : Fin 2, ¬ Function.Injective ![z, z] := fun z h =>
    zero_ne_one (h (show ![z, z] 0 = ![z, z] 1 from rfl))
  have e01 : leviCivitaCoeff ![(0 : Fin 2), 1] = 1 := by
    rw [h01, leviCivitaCoeff_perm]
    simp
  have e10 : leviCivitaCoeff ![(1 : Fin 2), 0] = -1 := by
    rw [h10, leviCivitaCoeff_perm, Perm.sign_swap (by decide)]
    simp
  fin_cases x <;> fin_cases y
  · simp [leviCivitaCoeff_of_not_injective (hd 0)]
  · simp [e01]
  · simp [e10]
  · simp [leviCivitaCoeff_of_not_injective (hd 1)]

/-- For `SU(2)` the Levi-Civita tensor with two fundamental indices is the antisymmetric
  symbol. -/
lemma leviCivitaFund_two : leviCivitaFund 2 = epsilonFund :=
  (Tensor.basis _).repr.injective (Finsupp.ext fun a => by
    rw [basis_repr_leviCivitaFund, basis_repr_epsilonFund, leviCivitaCoeff_two])

/-- For `SU(2)` the Levi-Civita tensor with two anti-fundamental indices is the antisymmetric
  symbol. -/
lemma leviCivitaAntiFund_two : leviCivitaAntiFund 2 = epsilonAntiFund :=
  (Tensor.basis _).repr.injective (Finsupp.ext fun a => by
    rw [basis_repr_leviCivitaAntiFund, basis_repr_epsilonAntiFund, leviCivitaCoeff_two])

end suTensor
