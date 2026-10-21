/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.CommutingActions
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorHighestWeight

/-!
# The equivariant Clebsch–Gordan decomposition

Decomposes `V(m) ⊗ V(n)` into standard modules, compatibly with the diagonal `sl₂` action.

## i. Overview

The lowering strings of the highest-weight vectors `hwVec m n k`, `k ≤ min m n`, are
eigenvectors of one operator built from the Casimir element and the Cartan operator, with
pairwise distinct eigenvalues. Hence they are linearly independent. Their number is
`∑_k (m + n - 2k + 1) = (m + 1)(n + 1)`, so they form a basis of `V(m) ⊗ V(n)`. Sending the
`l`-th vector of the `k`-th string to the coordinate vector `v_l` of the `k`-th summand gives a
linear equivalence `V(m) ⊗ V(n) ≃ ⨁_k V(m + n - 2k)` that intertwines the diagonal raising,
lowering and weight operators with the standard ones on each summand. This is the
equivariant form of `clebsch_gordan`.

## ii. Key results

- `stringVec_linearIndependent` shows that the lowering strings are linearly independent.
- `tensorStringBasis` is the resulting basis of `V(m) ⊗ V(n)`.
- `cgEquiv` is the Clebsch–Gordan equivalence `V(m) ⊗ V(n) ≃ ⨁_k V(m + n - 2k)`.
- `cgEquiv_tensorE`, `cgEquiv_tensorF` and `cgEquiv_tensorH` show that it intertwines the
  `sl₂` actions.

## iii. Table of contents

- A. Lowering strings of the highest-weight vectors
- B. Linear independence
  - B.1. A separating operator
  - B.2. The basis of lowering strings
- C. The decomposition
  - C.1. The direct sum of standard modules
  - C.2. The intertwining equivalence

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Lowering strings of the highest-weight vectors
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct DirectSum

open StandardSl2Module

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

/-- The `l`-th vector `f^l w_k` of the lowering string of `hwVec m n k`. -/
def stringVec (m n k l : ℕ) : StandardSl2Module K m ⊗[K] StandardSl2Module K n :=
  (tensorF m n ^ l) (hwVec m n k)

omit [CharZero K] in
lemma tensorF_stringVec (k l : ℕ) :
    tensorF (K := K) m n (stringVec m n k l) = stringVec m n k (l + 1) := by
  rw [stringVec, stringVec, pow_succ', Module.End.mul_apply]

section String

variable {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m) (hkn : k ≤ n)

include hmn hkm hkn

lemma tensorH_stringVec (l : ℕ) :
    tensorH (K := K) m n (stringVec m n k l) =
      (((m + n - 2 * k : ℕ) : K) - 2 * l) • stringVec m n k l :=
  prim_h_pow (hwVec_hasPrimitiveVectorWith hmn hkm hkn) l

lemma tensorE_stringVec_succ (l : ℕ) :
    tensorE (K := K) m n (stringVec m n k (l + 1)) =
      (((l : K) + 1) * (((m + n - 2 * k : ℕ) : K) - l)) • stringVec m n k l :=
  prim_e_pow_succ (hwVec_hasPrimitiveVectorWith hmn hkm hkn) l

lemma stringVec_ne_zero {l : ℕ} (hl : l ≤ m + n - 2 * k) :
    stringVec (K := K) m n k l ≠ 0 :=
  tensorF_pow_hwVec_ne_zero hmn hkm hkn hl

lemma stringVec_eq_zero {l : ℕ} (hl : m + n - 2 * k < l) :
    stringVec (K := K) m n k l = 0 :=
  pow_apply_eq_zero (tensorF_pow_hwVec_eq_zero hmn hkm hkn) hl

omit hmn in
lemma tensorE_stringVec_zero : tensorE (K := K) m n (stringVec m n k 0) = 0 := by
  rw [stringVec, pow_zero, Module.End.one_apply, tensorE_hwVec hkm hkn]

end String

/-! ## B. Linear independence

### B.1. A separating operator -/

/-- The operator `M (2EF + 2FE + H²) + H` with `M = 2(m + n) + 1`. The bracket is a multiple of
the Casimir element, which distinguishes the strings; the weight `H` distinguishes the vectors
within a string. -/
def separator (m n : ℕ) : Module.End K (StandardSl2Module K m ⊗[K] StandardSl2Module K n) :=
  ((2 * (m + n) + 1 : ℕ) : K) •
      ((2 : K) • (tensorE (K := K) m n * tensorF m n) +
        (2 : K) • (tensorF (K := K) m n * tensorE m n) + tensorH (K := K) m n * tensorH m n) +
    tensorH (K := K) m n

/-- The eigenvalue of `separator` on `stringVec m n k l`. -/
def sepVal (m n k l : ℕ) : K :=
  ((2 * (m + n) + 1 : ℕ) : K) *
      (((m + n - 2 * k : ℕ) : K) * (((m + n - 2 * k : ℕ) : K) + 2)) +
    (((m + n - 2 * k : ℕ) : K) - 2 * l)

lemma separator_stringVec {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m) (hkn : k ≤ n) (l : ℕ) :
    separator (K := K) m n (stringVec m n k l) =
      sepVal (K := K) m n k l • stringVec m n k l := by
  have hEF : tensorE (K := K) m n (tensorF (K := K) m n (stringVec m n k l)) =
      (((l : K) + 1) * (((m + n - 2 * k : ℕ) : K) - l)) • stringVec m n k l := by
    rw [tensorF_stringVec, tensorE_stringVec_succ hmn hkm hkn]
  have hFE : tensorF (K := K) m n (tensorE (K := K) m n (stringVec m n k l)) =
      ((l : K) * (((m + n - 2 * k : ℕ) : K) - l + 1)) • stringVec m n k l := by
    rcases l with _ | l
    · rw [tensorE_stringVec_zero hkm hkn, map_zero, Nat.cast_zero, zero_mul, zero_smul]
    · rw [tensorE_stringVec_succ hmn hkm hkn, map_smul, tensorF_stringVec]
      congr 1
      push_cast
      ring
  have hHH : tensorH (K := K) m n (tensorH (K := K) m n (stringVec m n k l)) =
      ((((m + n - 2 * k : ℕ) : K) - 2 * l) ^ 2) • stringVec m n k l := by
    rw [tensorH_stringVec hmn hkm hkn, map_smul, tensorH_stringVec hmn hkm hkn, smul_smul]
    congr 1
    ring
  simp only [separator, sepVal, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    hEF, hFE, hHH]
  rw [tensorH_stringVec hmn hkm hkn]
  module

/-- Index set of the lowering strings: `k ≤ min m n` and `l ≤ m + n - 2k`. -/
abbrev StringIndex (m n : ℕ) : Type := Σ k : Fin (min m n + 1), Fin (m + n - 2 * (k : ℕ) + 1)

instance : Nonempty (StringIndex m n) := ⟨⟨0, 0⟩⟩

lemma StringIndex.le_left (i : StringIndex m n) : (i.1 : ℕ) ≤ m := by
  have := i.1.isLt
  omega

lemma StringIndex.le_right (i : StringIndex m n) : (i.1 : ℕ) ≤ n := by
  have := i.1.isLt
  omega

/-- Integer core of `sepVal_injective`: with `M = 2s + 1`, the value `M N (N + 2) + N - 2l`
determines `N` and `l`, provided `N ≤ s` and `l ≤ N`. -/
lemma sepVal_int_injective {s N N' l l' : ℕ} (hN : N ≤ s) (hN' : N' ≤ s) (hl : l ≤ N)
    (hl' : l' ≤ N')
    (h : (2 * s + 1 : ℤ) * (N * (N + 2)) + N - 2 * l =
      (2 * s + 1 : ℤ) * (N' * (N' + 2)) + N' - 2 * l') : N = N' ∧ l = l' := by
  have hM : (0 : ℤ) ≤ 2 * s + 1 := by positivity
  have hNN : N = N' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : (N : ℤ) * (N + 2) + 1 ≤ (N' : ℤ) * (N' + 2) := by
        have : (N : ℤ) + 1 ≤ N' := by exact_mod_cast hlt
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hM]
    · have h1 : (N' : ℤ) * (N' + 2) + 1 ≤ (N : ℤ) * (N + 2) := by
        have : (N' : ℤ) + 1 ≤ N := by exact_mod_cast hlt
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hM]
  subst hNN
  exact ⟨rfl, by omega⟩

/-- The eigenvalues of `separator` on the lowering strings are pairwise distinct. -/
lemma sepVal_injective :
    Function.Injective (fun i : StringIndex m n => sepVal (K := K) m n i.1 i.2) := by
  rintro ⟨k, l⟩ ⟨k', l'⟩ h
  have hl := l.isLt
  have hl' := l'.isLt
  have hZ : (2 * (m + n) + 1 : ℤ) * (((m + n - 2 * k : ℕ) : ℤ) * ((m + n - 2 * k : ℕ) + 2)) +
        ((m + n - 2 * k : ℕ) : ℤ) - 2 * (l : ℕ) =
      (2 * (m + n) + 1 : ℤ) * (((m + n - 2 * k' : ℕ) : ℤ) * ((m + n - 2 * k' : ℕ) + 2)) +
        ((m + n - 2 * k' : ℕ) : ℤ) - 2 * (l' : ℕ) := by
    have h' : (((2 * (m + n) + 1 : ℤ) * (((m + n - 2 * k : ℕ) : ℤ) *
          ((m + n - 2 * k : ℕ) + 2)) + ((m + n - 2 * k : ℕ) : ℤ) - 2 * (l : ℕ) : ℤ) : K) =
        (((2 * (m + n) + 1 : ℤ) * (((m + n - 2 * k' : ℕ) : ℤ) *
          ((m + n - 2 * k' : ℕ) + 2)) + ((m + n - 2 * k' : ℕ) : ℤ) - 2 * (l' : ℕ) : ℤ) : K) := by
      simp only [sepVal] at h
      push_cast at h ⊢
      linear_combination h
    exact_mod_cast h'
  obtain ⟨hNN, hll⟩ := sepVal_int_injective (s := m + n) (by omega) (by omega) (by omega)
    (by omega) hZ
  have hk := k.isLt
  have hk' := k'.isLt
  obtain rfl : k = k' := Fin.ext (by omega)
  obtain rfl : l = l' := Fin.ext hll
  rfl

/-! ### B.2. The basis of lowering strings -/

/-- The lowering strings of the highest-weight vectors are linearly independent. -/
lemma stringVec_linearIndependent (hmn : 0 < m + n) :
    LinearIndependent K (fun i : StringIndex m n => stringVec (K := K) m n i.1 i.2) :=
  Module.End.eigenvectors_linearIndependent' (separator m n) _ sepVal_injective _ fun i =>
    Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (separator_stringVec hmn i.le_left i.le_right i.2),
        stringVec_ne_zero hmn i.le_left i.le_right (by have := i.2.isLt; omega)⟩

lemma card_stringIndex : Fintype.card (StringIndex m n) = (m + 1) * (n + 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun k => m + n - 2 * k + 1), clebsch_gordan_finrank]

omit [CharZero K] in
lemma finrank_standardSl2Module_tensor :
    Module.finrank K (StandardSl2Module K m ⊗[K] StandardSl2Module K n) = (m + 1) * (n + 1) := by
  rw [Module.finrank_tensorProduct, finrank_standardSl2Module, finrank_standardSl2Module]

/-- The basis of `V(m) ⊗ V(n)` formed by the lowering strings of the highest-weight vectors. -/
def tensorStringBasis (hmn : 0 < m + n) :
    Module.Basis (StringIndex m n) K (StandardSl2Module K m ⊗[K] StandardSl2Module K n) :=
  basisOfLinearIndependentOfCardEqFinrank (stringVec_linearIndependent hmn)
    (by rw [card_stringIndex, finrank_standardSl2Module_tensor])

lemma tensorStringBasis_apply (hmn : 0 < m + n) (i : StringIndex m n) :
    tensorStringBasis (K := K) hmn i = stringVec m n i.1 i.2 := by
  rw [tensorStringBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ## C. The decomposition

### C.1. The direct sum of standard modules -/

/-- The summand `V(m + n - 2k)` of the Clebsch–Gordan decomposition. -/
abbrev CGSummand (K : Type*) (m n : ℕ) (k : Fin (min m n + 1)) : Type _ :=
  StandardSl2Module K (m + n - 2 * (k : ℕ))

/-- The direct sum `⨁_k V(m + n - 2k)` of the Clebsch–Gordan decomposition. -/
abbrev CGSum (K : Type*) [Field K] (m n : ℕ) : Type _ := ⨁ k, CGSummand K m n k

/-- The coordinate vector `v_l` of the `k`-th summand of `CGSum`. -/
def sumVec (m n : ℕ) (k : Fin (min m n + 1)) (l : ℕ) : CGSum K m n :=
  DirectSum.lof K _ (CGSummand K m n) k (vNat _ l)

/-- The endomorphism of `CGSum` acting by `A k` on the `k`-th summand. -/
def sumEnd (A : ∀ k, Module.End K (CGSummand K m n k)) : Module.End K (CGSum K m n) :=
  DFinsupp.mapRange.linearMap A

omit [CharZero K] in
lemma sumEnd_lof (A : ∀ k, Module.End K (CGSummand K m n k)) (k : Fin (min m n + 1))
    (x : CGSummand K m n k) :
    sumEnd A (DirectSum.lof K _ (CGSummand K m n) k x) =
      DirectSum.lof K _ (CGSummand K m n) k (A k x) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (A i))

omit [CharZero K] in
lemma sumVec_linearIndependent :
    LinearIndependent K (fun i : StringIndex m n => sumVec (K := K) m n i.1 i.2) := by
  have h := DFinsupp.linearIndependent_single (R := K) (M := CGSummand K m n)
    (fun k (l : Fin (m + n - 2 * (k : ℕ) + 1)) => vNat (K := K) _ (l : ℕ))
    (fun k => by
      convert (Pi.basisFun K (Fin (m + n - 2 * (k : ℕ) + 1))).linearIndependent using 1
      funext l
      rw [vNat_eq_v (by have := l.isLt; omega), Pi.basisFun_apply]
      rfl)
  exact h

/-- The basis of `CGSum` formed by the coordinate vectors of the summands. -/
def sumBasis (m n : ℕ) : Module.Basis (StringIndex m n) K (CGSum K m n) :=
  basisOfLinearIndependentOfCardEqFinrank sumVec_linearIndependent (by
    rw [card_stringIndex, Module.finrank_directSum]
    simp only [CGSummand, finrank_standardSl2Module]
    rw [Fin.sum_univ_eq_sum_range (fun k => m + n - 2 * k + 1), clebsch_gordan_finrank])

omit [CharZero K] in
lemma sumBasis_apply (i : StringIndex m n) : sumBasis (K := K) m n i = sumVec m n i.1 i.2 := by
  rw [sumBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### C.2. The intertwining equivalence -/

/-- The Clebsch–Gordan equivalence `V(m) ⊗ V(n) ≃ ⨁_k V(m + n - 2k)`, sending the `l`-th
vector of the `k`-th lowering string to the coordinate vector `v_l` of the `k`-th summand. -/
def cgEquiv (hmn : 0 < m + n) :
    (StandardSl2Module K m ⊗[K] StandardSl2Module K n) ≃ₗ[K] CGSum K m n :=
  (tensorStringBasis hmn).equiv (sumBasis m n) (Equiv.refl _)

/-- `cgEquiv` on the lowering strings, for every `l : ℕ`. -/
lemma cgEquiv_stringVec (hmn : 0 < m + n) (k : Fin (min m n + 1)) (l : ℕ) :
    cgEquiv (K := K) hmn (stringVec m n k l) = sumVec m n k l := by
  have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
  have hkn : (k : ℕ) ≤ n := by have := k.isLt; omega
  rcases le_or_gt l (m + n - 2 * (k : ℕ)) with hl | hl
  · have h := (tensorStringBasis (K := K) hmn).equiv_apply ⟨k, ⟨l, by omega⟩⟩ (sumBasis m n)
      (Equiv.refl _)
    rw [tensorStringBasis_apply, sumBasis_apply] at h
    exact h
  · rw [stringVec_eq_zero hmn hkm hkn hl, map_zero, sumVec, vNat_of_lt hl, map_zero]

/-- `cgEquiv` intertwines the diagonal lowering operator with `ρF` on each summand. -/
lemma cgEquiv_tensorF (hmn : 0 < m + n) (x : StandardSl2Module K m ⊗[K] StandardSl2Module K n) :
    cgEquiv hmn (tensorF m n x) = sumEnd (fun _ => ρF) (cgEquiv hmn x) := by
  suffices h : (cgEquiv (K := K) hmn).toLinearMap ∘ₗ tensorF m n =
      sumEnd (fun _ => ρF) ∘ₗ (cgEquiv hmn).toLinearMap from LinearMap.congr_fun h x
  refine (tensorStringBasis hmn).ext fun i => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorStringBasis_apply,
    tensorF_stringVec, cgEquiv_stringVec, sumVec, sumEnd_lof, ρF_vNat]

/-- `cgEquiv` intertwines the diagonal weight operator with `ρH` on each summand. -/
lemma cgEquiv_tensorH (hmn : 0 < m + n) (x : StandardSl2Module K m ⊗[K] StandardSl2Module K n) :
    cgEquiv hmn (tensorH m n x) = sumEnd (fun _ => ρH) (cgEquiv hmn x) := by
  suffices h : (cgEquiv (K := K) hmn).toLinearMap ∘ₗ tensorH m n =
      sumEnd (fun _ => ρH) ∘ₗ (cgEquiv hmn).toLinearMap from LinearMap.congr_fun h x
  refine (tensorStringBasis hmn).ext fun i => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorStringBasis_apply,
    tensorH_stringVec hmn i.le_left i.le_right, map_smul, cgEquiv_stringVec, sumVec, sumEnd_lof,
    ρH_vNat]

/-- `cgEquiv` intertwines the diagonal raising operator with `ρE` on each summand. -/
lemma cgEquiv_tensorE (hmn : 0 < m + n) (x : StandardSl2Module K m ⊗[K] StandardSl2Module K n) :
    cgEquiv hmn (tensorE m n x) = sumEnd (fun _ => ρE) (cgEquiv hmn x) := by
  suffices h : (cgEquiv (K := K) hmn).toLinearMap ∘ₗ tensorE m n =
      sumEnd (fun _ => ρE) ∘ₗ (cgEquiv hmn).toLinearMap from LinearMap.congr_fun h x
  refine (tensorStringBasis hmn).ext fun ⟨k, l⟩ => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorStringBasis_apply]
  have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
  have hkn : (k : ℕ) ≤ n := by have := k.isLt; omega
  rcases l with ⟨_ | l, hl⟩
  · simp only [tensorE_stringVec_zero hkm hkn, map_zero, cgEquiv_stringVec, sumVec, sumEnd_lof,
      ρE_vNat_zero]
  · simp only [tensorE_stringVec_succ hmn hkm hkn, map_smul, cgEquiv_stringVec, sumVec,
      sumEnd_lof, ρE_vNat_succ]

end PhyslibAlpha.Sl2
