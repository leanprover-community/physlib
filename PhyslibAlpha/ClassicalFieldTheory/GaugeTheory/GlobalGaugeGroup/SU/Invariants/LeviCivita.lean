/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU
public import PhyslibAlpha.Mathematics.ForMathlib.Fin
/-!
# The Levi-Civita tensors of `SU(N)`

Up to scale, the Levi-Civita symbol is the only invariant with `N` fundamental indices of
`SU(N)`, and the only one with `N` anti-fundamental indices.

## i. Overview

The tensors with `n` fundamental indices, or with `n` anti-fundamental indices, have the tuples
`Fin n → Fin N` as component indices, and `g` moves the components by one factor of `g`, or of
its complex conjugate, per index (A).

The Levi-Civita symbol `ε_a`, for `a : Fin N → Fin N`, is the sign of `a` when `a` is a
permutation and zero when a label repeats (B). Contracting its indices with the rows `a` of a
matrix `M` gives `ε_a det M`. So the tensors with these components, `leviCivitaFund N` with `N`
fundamental indices and `leviCivitaAntiFund N` with `N` anti-fundamental indices, are invariant,
because `det g = 1` (C).

Conversely, let the components `c` of a tensor with `N` fundamental indices be fixed by `SU(N)`
(D). If a label of `a` repeats, some label `q` is missed by `a`. Take a label `p` that `a` hits
`m` times, and the diagonal element of `SU(N)` with a primitive `(N + 1)`-th root of unity `ω`
at `p`, its conjugate at `q` and one elsewhere. It scales `c a` by `ω ^ m` with `0 < m ≤ N`, so
`c a = 0`. The quarter turn in the plane of two labels `p` and `q` is a signed transposition, and
it gives `c (swap p q ∘ σ) = -c σ` for every permutation `σ`. By induction over transpositions
`c σ = sign σ * c id`, and so `c = c id • ε`. On anti-fundamental indices `g` acts through its
complex conjugate, itself an element of `SU(N)`, and the same holds (E).

The invariant tensors are therefore the line through the Levi-Civita tensor. For `N = 2` the
Levi-Civita tensors are the antisymmetric symbols `epsilonFund` and `epsilonAntiFund`, so the
invariant tensors with two fundamental, or two anti-fundamental, indices of `SU(2)` are the line
through `ε` (F). For `N ≥ 3` there are none with two such indices, which is a centre argument
(`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.CentreEigenspace`).

A family indexed by `Fin n → Fin N` is the map `liftComponents T` out of these tensors, and for
`SU(2)` the invariants of the span of such a family with two indices reduce to the epsilon
contraction `T ![0, 1] - T ![1, 0]` (G).

## ii. Key results

- `suTensor.leviCivitaCoeff` : the Levi-Civita symbol.
- `suTensor.sum_prod_mul_leviCivitaCoeff` : contracting it with the rows of a matrix gives the
  determinant.
- `suTensor.leviCivitaFund`, `suTensor.leviCivitaAntiFund` : the Levi-Civita tensors.
- `suTensor.invariants_fund_pow_eq_span_leviCivitaFund` : the invariant tensors with `N`
  fundamental indices are the line through it, and its anti-fundamental twin.
- `suTensor.epsilonFund`, `suTensor.epsilonAntiFund` : the antisymmetric symbols of `SU(2)`.
- `suTensor.leviCivitaFund_two` : for `SU(2)` the Levi-Civita tensor is the antisymmetric symbol.
- `suTensor.invariants_fund_pow_two_eq_span_epsilonFund` : the invariant tensors with two
  fundamental indices of `SU(2)` are the line through `ε`, and its anti-fundamental twin.
- `suTensor.invariantReductionToEpsilonFund` : the reduction of the invariants of the span of a
  family to the epsilon contraction, and its anti-fundamental twin.

## iii. Table of contents

- A. Tensors with fundamental or with anti-fundamental indices
- B. The Levi-Civita symbol
- C. The Levi-Civita tensors are invariant
- D. Components fixed by `SU(N)`
- E. The invariant tensors
- F. Two indices of `SU(2)`: the antisymmetric symbol
- G. Maps from components

## iv. References

* None.

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies SU Equiv Physlib.Fin
open TensorSpecies.Tensor
open GlobalGaugeGroup (rootOfUnity rootOfUnity_isPrimitiveRoot rootOfUnity_mul_star)

variable {N : ℕ}

/-!

## A. Tensors with fundamental or with anti-fundamental indices

-/

/-- The components of `g • t` for a tensor with `n` fundamental indices, with one factor of `g` per
  index. -/
lemma basis_repr_smul_fund {n : ℕ} (g : SU N) (t : (suTensor N).Tensor fun _ : Fin n => .fund)
    (φ : Fin n → Fin N) :
    (Tensor.basis _).repr (g • t) φ
      = ∑ ψ : Fin n → Fin N, (∏ i, g.1 (φ i) (ψ i)) * (Tensor.basis _).repr t ψ := by
  rw [basis_repr_smul]
  refine Finset.sum_congr rfl fun ψ _ => congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)
  change LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (fundRep N g) _ _ = _
  rw [toMatrix_fundRep]

/-- The components of `g • t` for a tensor with `n` anti-fundamental indices, with one factor of the
  complex conjugate of `g` per index. -/
lemma basis_repr_smul_antiFund {n : ℕ} (g : SU N)
    (t : (suTensor N).Tensor fun _ : Fin n => .antiFund) (φ : Fin n → Fin N) :
    (Tensor.basis _).repr (g • t) φ = ∑ ψ : Fin n → Fin N,
      (∏ i, starRingEnd ℂ (g.1 (φ i) (ψ i))) * (Tensor.basis _).repr t ψ := by
  rw [basis_repr_smul]
  refine Finset.sum_congr rfl fun ψ _ => congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)
  change LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
    (antiFundRep N g) _ _ = _
  rw [toMatrix_antiFundRep, val_inv]
  rfl

/-!

## B. The Levi-Civita symbol

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

## C. The Levi-Civita tensors are invariant

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

## D. Components fixed by `SU(N)`

-/

/-- The quarter turn in the plane of `p` and `q` is the signed transposition sending `e_p` to
  `e_q` and `e_q` to `-e_p`. -/
lemma quarterTurn_val_apply {p q : Fin N} (hpq : p ≠ q) (x y : Fin N) :
    (planeEmbed p q hpq (rotation 0 1 (by norm_num))).1 x y
      = (if x = p then -1 else 1) * (if swap p q x = y then 1 else 0) := by
  simp only [planeEmbed_val, rotation_val, planeMatrix, Matrix.add_apply, Matrix.one_apply,
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

## E. The invariant tensors

-/

/-- The invariant tensors with `N` fundamental indices of `SU(N)` are the line through the
  Levi-Civita tensor. -/
lemma invariants_fund_pow_eq_span_leviCivitaFund :
    ((suTensor N).tensorRep fun _ : Fin N => .fund).invariants = ℂ ∙ leviCivitaFund N := by
  refine invariants_tensorRep_eq_span_singleton leviCivitaFund_invariant fun t ht => ?_
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

/-- The invariant tensors with `N` anti-fundamental indices of `SU(N)` are the line through the
  Levi-Civita tensor. Here `g` acts through its complex conjugate, which runs over `SU(N)` with
  `g`. -/
lemma invariants_antiFund_pow_eq_span_leviCivitaAntiFund :
    ((suTensor N).tensorRep fun _ : Fin N => .antiFund).invariants
      = ℂ ∙ leviCivitaAntiFund N := by
  refine invariants_tensorRep_eq_span_singleton leviCivitaAntiFund_invariant fun t ht => ?_
  have hc : ∀ (g : SU N) (a : Fin N → Fin N), (Tensor.basis _).repr t a
      = ∑ b, (∏ i, g.1 (a i) (b i)) * (Tensor.basis _).repr t b := fun g a => by
    have h := basis_repr_smul_antiFund (starElem g) t a
    rw [ht] at h
    simpa using h
  refine ⟨(Tensor.basis _).repr t id, (Tensor.basis _).repr.injective (Finsupp.ext fun a => ?_)⟩
  rw [map_smul, Finsupp.smul_apply, basis_repr_leviCivitaAntiFund, smul_eq_mul]
  exact eq_mul_leviCivitaCoeff hc a

/-!

## F. Two indices of `SU(2)`: the antisymmetric symbol

-/

/-- The antisymmetric symbol `ε^{ab}` with two fundamental indices of `SU(2)`. -/
noncomputable def epsilonFund : (suTensor 2).Tensor fun _ : Fin 2 => .fund :=
  Tensor.basis _ ![0, 1] - Tensor.basis _ ![1, 0]

/-- The antisymmetric symbol `ε_{ab}` with two anti-fundamental indices of `SU(2)`. -/
noncomputable def epsilonAntiFund : (suTensor 2).Tensor fun _ : Fin 2 => .antiFund :=
  Tensor.basis _ ![0, 1] - Tensor.basis _ ![1, 0]

/-- The components of the antisymmetric symbol. -/
lemma basis_repr_epsilonFund (φ : Fin 2 → Fin 2) :
    (Tensor.basis _).repr epsilonFund φ
      = (if φ = ![0, 1] then 1 else 0) - (if φ = ![1, 0] then 1 else 0) := by
  simp [epsilonFund, Finsupp.single_apply, eq_comm]

/-- The components of the antisymmetric symbol. -/
lemma basis_repr_epsilonAntiFund (φ : Fin 2 → Fin 2) :
    (Tensor.basis _).repr epsilonAntiFund φ
      = (if φ = ![0, 1] then 1 else 0) - (if φ = ![1, 0] then 1 else 0) := by
  simp [epsilonAntiFund, Finsupp.single_apply, eq_comm]

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

/-- The antisymmetric symbol with two fundamental indices is invariant, being the Levi-Civita
  tensor of `SU(2)`. -/
lemma epsilonFund_invariant (g : SU 2) : g • epsilonFund = epsilonFund := by
  rw [← leviCivitaFund_two]
  exact leviCivitaFund_invariant g

/-- The antisymmetric symbol with two anti-fundamental indices is invariant, being the Levi-Civita
  tensor of `SU(2)`. -/
lemma epsilonAntiFund_invariant (g : SU 2) : g • epsilonAntiFund = epsilonAntiFund := by
  rw [← leviCivitaAntiFund_two]
  exact leviCivitaAntiFund_invariant g

/-- The invariant tensors with two fundamental indices of `SU(2)` are the line through the
  antisymmetric symbol, the Levi-Civita tensor of `SU(2)`. -/
lemma invariants_fund_pow_two_eq_span_epsilonFund :
    ((suTensor 2).tensorRep fun _ : Fin 2 => .fund).invariants = ℂ ∙ epsilonFund := by
  rw [← leviCivitaFund_two]
  exact invariants_fund_pow_eq_span_leviCivitaFund

/-- The invariant tensors with two anti-fundamental indices of `SU(2)` are the line through the
  antisymmetric symbol, the Levi-Civita tensor of `SU(2)`. -/
lemma invariants_antiFund_pow_two_eq_span_epsilonAntiFund :
    ((suTensor 2).tensorRep fun _ : Fin 2 => .antiFund).invariants = ℂ ∙ epsilonAntiFund := by
  rw [← leviCivitaAntiFund_two]
  exact invariants_antiFund_pow_eq_span_leviCivitaAntiFund

/-!

## G. Maps from components

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}

/-- A linear map moving a family with `n` fundamental labels by one factor of `g` per label
  intertwines the map of the family with the action of `g`. -/
lemma liftComponents_fund_smul_of_law {n : ℕ} (T : (Fin n → Fin N) → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ l : Fin n → Fin N, σ (T l) = ∑ a : Fin n → Fin N, (∏ i, g.1 (a i) (l i)) • T a)
    (t : (suTensor N).Tensor fun _ : Fin n => .fund) :
    σ (liftComponents (S := suTensor N) (c := fun _ : Fin n => .fund) T t)
      = liftComponents (S := suTensor N) (c := fun _ : Fin n => .fund) T (g • t) :=
  liftComponents_smul_of_law (S := suTensor N) (c := fun _ : Fin n => .fund) T g
      (fun l => (hσ l).trans <|
    Finset.sum_congr rfl fun a _ => congrArg (· • T a) <| Finset.prod_congr rfl fun i _ => by
      change _ = LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
        (fundRep N g) _ _
      rw [toMatrix_fundRep]) t

/-- A linear map moving a family with `n` anti-fundamental labels by one factor of the complex
  conjugate of `g` per label intertwines the map of the family with the action of `g`. -/
lemma liftComponents_antiFund_smul_of_law {n : ℕ} (T : (Fin n → Fin N) → B) {σ : B →ₗ[ℂ] B}
    (g : SU N) (hσ : ∀ l : Fin n → Fin N, σ (T l)
      = ∑ a : Fin n → Fin N, (∏ i, starRingEnd ℂ (g.1 (a i) (l i))) • T a)
    (t : (suTensor N).Tensor fun _ : Fin n => .antiFund) :
    σ (liftComponents (S := suTensor N) (c := fun _ : Fin n => .antiFund) T t)
      = liftComponents (S := suTensor N) (c := fun _ : Fin n => .antiFund) T (g • t) :=
  liftComponents_smul_of_law (S := suTensor N) (c := fun _ : Fin n => .antiFund) T g
      (fun l => (hσ l).trans <|
    Finset.sum_congr rfl fun a _ => congrArg (· • T a) <| Finset.prod_congr rfl fun i _ => by
      change _ = LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
        (antiFundRep N g) _ _
      rw [toMatrix_antiFundRep, val_inv]
      rfl) t

/-- The map of a family with `n` fundamental labels is equivariant when the family moves by one
  factor of `g` per label, the summed label first. -/
lemma isEquivariant_liftComponents_fund {n : ℕ} (T : (Fin n → Fin N) → B)
    (hT : ∀ (g : SU N) (l : Fin n → Fin N), ρ g (T l)
      = ∑ a : Fin n → Fin N, (∏ i, g.1 (a i) (l i)) • T a) :
    (suTensor N).IsEquivariant (fun _ => .fund) ρ (liftComponents T) :=
  ⟨fun g t => (liftComponents_fund_smul_of_law T g (hT g) t).symm⟩

/-- The map of a family with `n` anti-fundamental labels is equivariant when the family moves by
  one factor of the complex conjugate of `g` per label, the summed label first. -/
lemma isEquivariant_liftComponents_antiFund {n : ℕ} (T : (Fin n → Fin N) → B)
    (hT : ∀ (g : SU N) (l : Fin n → Fin N), ρ g (T l)
      = ∑ a : Fin n → Fin N, (∏ i, starRingEnd ℂ (g.1 (a i) (l i))) • T a) :
    (suTensor N).IsEquivariant (fun _ => .antiFund) ρ (liftComponents T) :=
  ⟨fun g t => (liftComponents_antiFund_smul_of_law T g (hT g) t).symm⟩

/-- The map of a family with two fundamental labels sends the antisymmetric symbol to the
  epsilon contraction. -/
lemma liftComponents_epsilonFund (T : (Fin 2 → Fin 2) → B) :
    liftComponents (S := suTensor 2) (c := fun _ : Fin 2 => .fund) T epsilonFund
      = T ![0, 1] - T ![1, 0] := by
  simp [liftComponents, epsilonFund, sub_smul, Finset.sum_sub_distrib, Finsupp.single_apply]

/-- The map of a family with two anti-fundamental labels sends the antisymmetric symbol to the
  epsilon contraction. -/
lemma liftComponents_epsilonAntiFund (T : (Fin 2 → Fin 2) → B) :
    liftComponents (S := suTensor 2) (c := fun _ : Fin 2 => .antiFund) T epsilonAntiFund
      = T ![0, 1] - T ![1, 0] := by
  simp [liftComponents, epsilonAntiFund, sub_smul, Finset.sum_sub_distrib, Finsupp.single_apply]

/-- For a family with two fundamental labels of `SU(2)` whose map is equivariant, the invariants
  of the span reduce to the span of the epsilon contraction `T ![0, 1] - T ![1, 0]`. -/
noncomputable def invariantReductionToEpsilonFund {ρ : Representation ℂ (SU 2) B}
    {T : (Fin 2 → Fin 2) → B}
    (hT : (suTensor 2).IsEquivariant (fun _ => .fund) ρ (liftComponents T)) :
    InvariantReductionToSpan (fun g : SU 2 => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (hasReynolds 2 _) invariants_fund_pow_two_eq_span_epsilonFund
    (range_liftComponents (S := suTensor 2) (c := fun _ : Fin 2 => .fund) T) _
    (liftComponents_epsilonFund T)

/-- For a family with two anti-fundamental labels of `SU(2)` whose map is equivariant, the
  invariants of the span reduce to the span of the epsilon contraction
  `T ![0, 1] - T ![1, 0]`. -/
noncomputable def invariantReductionToEpsilonAntiFund {ρ : Representation ℂ (SU 2) B}
    {T : (Fin 2 → Fin 2) → B}
    (hT : (suTensor 2).IsEquivariant (fun _ => .antiFund) ρ (liftComponents T)) :
    InvariantReductionToSpan (fun g : SU 2 => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (hasReynolds 2 _)
    invariants_antiFund_pow_two_eq_span_epsilonAntiFund
    (range_liftComponents (S := suTensor 2) (c := fun _ : Fin 2 => .antiFund) T) _
    (liftComponents_epsilonAntiFund T)

end suTensor
