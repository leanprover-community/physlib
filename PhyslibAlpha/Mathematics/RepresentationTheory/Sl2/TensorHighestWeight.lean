/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.BivariateBasis
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.ClebschGordan

/-!
# Highest-weight vectors in tensor products of standard sl₂ modules

Equips `V(m) ⊗ V(n)` with the diagonal `sl₂` action and writes down its highest-weight vectors.

## i. Overview

The raising, lowering and weight operators of two standard modules act on their tensor
product by `A ⊗ 1 + 1 ⊗ A`. These diagonal operators form an `sl₂` triple as soon as
`m + n > 0`. For every `k ≤ min m n` the vector
`w_k = ∑_{a=0}^{k} (-1)^a (k choose a) (n-k+a)! (m-a)! • v_a ⊗ v_{k-a}`
is killed by the diagonal raising operator and has weight `m + n - 2k`. The lowering string of
`w_k` has exactly `m + n - 2k + 1` nonzero members.

In physics notation, with `m = 2j₁`, `n = 2j₂` and `J = j₁ + j₂ - k`, the coefficients of `w_k`
are, up to a common factor and the change from the bases `v_a = f^a v_0` to normalised bases,
the Clebsch–Gordan coefficients of the top state `|J, J⟩`. This file does not show that the
lowering strings of the `w_k` together form a basis of `V(m) ⊗ V(n)`.

## ii. Key results

- `isSl2Triple_tensor` shows that the diagonal operators form an `sl₂` triple.
- `tensorE_hwVec` and `tensorH_hwVec` show that `hwVec m n k` is a highest-weight vector.
- `hwVec_hasPrimitiveVectorWith` packages this as a primitive vector of weight `m + n - 2k`.
- `tensorF_pow_hwVec_ne_zero` and `tensorF_pow_hwVec_eq_zero` give the length of its
  lowering string.

## iii. Table of contents

- A. The diagonal action
  - A.1. Coordinate vectors indexed by natural numbers
  - A.2. The diagonal operators on `V(m) ⊗ V(n)`
- B. Highest-weight vectors
  - B.1. The coefficients
  - B.2. Weight and raising operator
  - B.3. Primitive vectors and lowering strings

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. The diagonal action
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K]

section Diagonal

variable {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The diagonal action `A ⊗ 1 + 1 ⊗ B` of two endomorphisms on `M ⊗ N`. -/
def diagEnd (A : Module.End K M) (B : Module.End K N) : Module.End K (M ⊗[K] N) :=
  A.rTensor N + B.lTensor M

lemma diagEnd_tmul (A : Module.End K M) (B : Module.End K N) (x : M) (y : N) :
    diagEnd A B (x ⊗ₜ y) = A x ⊗ₜ y + x ⊗ₜ B y := by
  simp [diagEnd]

/-- The diagonal action respects commutators. -/
lemma lie_diagEnd (A A' : Module.End K M) (B B' : Module.End K N) :
    ⁅diagEnd A B, diagEnd A' B'⁆ = diagEnd ⁅A, A'⁆ ⁅B, B'⁆ := by
  apply TensorProduct.ext'
  intro x y
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    diagEnd_tmul, map_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

lemma diagEnd_smul (c : K) (A : Module.End K M) (B : Module.End K N) :
    diagEnd (c • A) (c • B) = c • diagEnd A B := by
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.smul_apply, diagEnd_tmul, diagEnd_tmul, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- The diagonal action is additive in both endomorphisms. -/
lemma diagEnd_add (A A' : Module.End K M) (B B' : Module.End K N) :
    diagEnd (A + A') (B + B') = diagEnd A B + diagEnd A' B' := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.add_apply, diagEnd_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- The diagonal action respects differences. -/
lemma diagEnd_sub (A A' : Module.End K M) (B B' : Module.End K N) :
    diagEnd (A - A') (B - B') = diagEnd A B - diagEnd A' B' := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.sub_apply, diagEnd_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

end Diagonal

/-! ### A.1. Coordinate vectors indexed by natural numbers

`StandardSl2Module.vNat n i` is the coordinate vector `v_i` for `i ≤ n` and zero for `i > n`.
With this convention the raising, lowering and weight formulas hold for every `i : ℕ`, which
keeps the index bookkeeping in sums over `Finset.range` free of side conditions. -/

/-- The coordinate vector `v_i` of `StandardSl2Module K n`, indexed by a natural number;
it is zero for `i > n`. -/
def StandardSl2Module.vNat (n i : ℕ) : StandardSl2Module K n :=
  fun k => if (k : ℕ) = i then 1 else 0

namespace StandardSl2Module

variable {n : ℕ}

lemma vNat_apply (i : ℕ) (k : Fin (n + 1)) :
    vNat (K := K) n i k = if (k : ℕ) = i then 1 else 0 := rfl

lemma vNat_eq_v {i : ℕ} (hi : i ≤ n) : vNat (K := K) n i = v ⟨i, by omega⟩ := by
  funext k
  simp [vNat, v, Pi.single_apply, Fin.ext_iff]

lemma vNat_of_lt {i : ℕ} (hi : n < i) : vNat (K := K) n i = 0 := by
  funext k
  have := k.isLt
  simp only [vNat, Pi.zero_apply]
  split_ifs with h
  · omega
  · rfl

end StandardSl2Module

open StandardSl2Module

variable {n : ℕ}

lemma ρH_vNat (i : ℕ) :
    (ρH : Module.End K (StandardSl2Module K n)) (vNat n i) = ((n : K) - 2 * i) • vNat n i := by
  rcases le_or_gt i n with hi | hi
  · rw [vNat_eq_v hi, ρH_v]
  · rw [vNat_of_lt hi, map_zero, smul_zero]

lemma ρF_vNat (i : ℕ) :
    (ρF : Module.End K (StandardSl2Module K n)) (vNat n i) = vNat n (i + 1) := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · rw [vNat_eq_v hi.le, ρF_v_lt _ hi, vNat_eq_v (by omega)]
  · rw [vNat_eq_v le_rfl, vNat_of_lt (by omega)]
    exact ρF_v_last
  · rw [vNat_of_lt hi, vNat_of_lt (by omega), map_zero]

lemma ρE_vNat_zero :
    (ρE : Module.End K (StandardSl2Module K n)) (vNat n 0) = 0 := by
  rw [vNat_eq_v (Nat.zero_le n)]
  exact ρE_v_zero

lemma ρE_vNat_succ [CharZero K] (i : ℕ) :
    (ρE : Module.End K (StandardSl2Module K n)) (vNat n (i + 1)) =
      (((i : K) + 1) * ((n : K) - i)) • vNat n i := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · rw [vNat_eq_v (by omega : i + 1 ≤ n), ρE_v_pos _ (by simp), vNat_eq_v hi.le]
    have hidx : (⟨i + 1 - 1, by omega⟩ : Fin (n + 1)) = ⟨i, by omega⟩ := by
      ext; simp
    simp only [hidx]
    congr 1
    push_cast
    ring
  · rw [vNat_of_lt (by omega), map_zero, sub_self, mul_zero, zero_smul]
  · rw [vNat_of_lt (by omega), vNat_of_lt hi, map_zero, smul_zero]

/-! ### A.2. The diagonal operators on `V(m) ⊗ V(n)` -/

variable {m : ℕ}

/-- The diagonal raising operator on `V(m) ⊗ V(n)`. -/
def tensorE (m n : ℕ) : Module.End K (StandardSl2Module K m ⊗[K] StandardSl2Module K n) :=
  diagEnd ρE ρE

/-- The diagonal lowering operator on `V(m) ⊗ V(n)`. -/
def tensorF (m n : ℕ) : Module.End K (StandardSl2Module K m ⊗[K] StandardSl2Module K n) :=
  diagEnd ρF ρF

/-- The diagonal weight operator on `V(m) ⊗ V(n)`. -/
def tensorH (m n : ℕ) : Module.End K (StandardSl2Module K m ⊗[K] StandardSl2Module K n) :=
  diagEnd ρH ρH

/-- The coefficient of `v_i ⊗ v_j` in an element of `V(m) ⊗ V(n)`. -/
def tensorCoord (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] K :=
  TensorProduct.lift ((LinearMap.mul K K).compl₁₂
    (LinearMap.proj (R := K) (φ := fun _ : Fin (m + 1) => K) i)
    (LinearMap.proj (R := K) (φ := fun _ : Fin (n + 1) => K) j))

lemma tensorCoord_tmul (i : Fin (m + 1)) (j : Fin (n + 1)) (x : StandardSl2Module K m)
    (y : StandardSl2Module K n) : tensorCoord m n i j (x ⊗ₜ y) = x i * y j := by
  simp [tensorCoord]

/-- The diagonal weight operator on a product of coordinate vectors. -/
lemma tensorH_tmul_vNat (a b : ℕ) :
    tensorH (K := K) m n (vNat m a ⊗ₜ vNat n b) =
      ((m : K) + n - 2 * (a + b)) • (vNat m a ⊗ₜ vNat n b) := by
  rw [tensorH, diagEnd_tmul, ρH_vNat, ρH_vNat, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, ← add_smul]
  congr 1
  ring

/-- The diagonal operators on `V(m) ⊗ V(n)` form an `sl₂` triple when `m + n > 0`. -/
lemma isSl2Triple_tensor [CharZero K] (hmn : 0 < m + n) :
    IsSl2Triple (tensorH (K := K) m n) (tensorE m n) (tensorF m n) where
  h_ne_zero h0 := by
    have h1 := congrArg (fun T => tensorCoord m n 0 0 (T (vNat m 0 ⊗ₜ vNat n 0))) h0
    simp only [tensorH_tmul_vNat, map_smul, tensorCoord_tmul, vNat_apply, Fin.val_zero,
      ↓reduceIte, mul_one, LinearMap.zero_apply, map_zero, smul_eq_mul] at h1
    have h2 : ((m + n : ℕ) : K) = 0 := by push_cast; linear_combination h1
    exact absurd (Nat.cast_eq_zero.mp h2) (by omega)
  lie_e_f := by rw [tensorE, tensorF, tensorH, lie_diagEnd, rel_ef, rel_ef]
  lie_h_e_nsmul := by
    rw [tensorH, tensorE, lie_diagEnd, rel_he, rel_he, diagEnd_smul, two_smul, two_nsmul]
  lie_h_f_nsmul := by
    rw [tensorH, tensorF, lie_diagEnd, rel_hf, rel_hf, diagEnd_smul]
    module

/-! ## B. Highest-weight vectors

### B.1. The coefficients -/

/-- The coefficient of `v_a ⊗ v_{k-a}` in the highest-weight vector of weight `m + n - 2k`
of `V(m) ⊗ V(n)`: `(-1)^a (k choose a) (n-k+a)! (m-a)!`. -/
def cgCoeff (m n k a : ℕ) : K :=
  (-1) ^ a * ((k.choose a * (n - k + a).factorial * (m - a).factorial : ℕ) : K)

/-- The two-term recursion of the coefficients that makes the raising operator vanish. -/
lemma cgCoeff_rec {j a : ℕ} (hjm : j + 1 ≤ m) (hjn : j + 1 ≤ n) (ha : a ≤ j) :
    cgCoeff (K := K) m n (j + 1) (a + 1) * (((a : K) + 1) * ((m : K) - a)) +
      cgCoeff m n (j + 1) a * ((((j - a : ℕ) : K) + 1) * ((n : K) - ((j - a : ℕ) : K))) = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + a := ⟨j - a, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = r + a + 1 := ⟨m - (a + 1), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = s + d + a + 1 := ⟨n - (d + a + 1), by omega⟩
  have e1 : s + d + a + 1 - (d + a + 1) + (a + 1) = s + a + 1 := by omega
  have e2 : s + d + a + 1 - (d + a + 1) + a = s + a := by omega
  have e3 : r + a + 1 - (a + 1) = r := by omega
  have e4 : r + a + 1 - a = r + 1 := by omega
  have e5 : d + a - a = d := by omega
  have hC := Nat.choose_succ_right_eq (d + a + 1) a
  have e6 : d + a + 1 - a = d + 1 := by omega
  rw [e6] at hC
  have hC' : ((d + a + 1).choose (a + 1) : K) * ((a : K) + 1) =
      ((d + a + 1).choose a : K) * ((d : K) + 1) := by
    have h := congrArg (Nat.cast (R := K)) hC
    push_cast at h
    exact h
  simp only [cgCoeff, e1, e2, e3, e4, e5, Nat.factorial_succ]
  push_cast
  linear_combination
    ((-1 : K) ^ a * ((s + a).factorial : K) * (r.factorial : K) * ((r : K) + 1) *
      ((s : K) + a + 1)) * (-hC')

/-- The highest-weight vector of weight `m + n - 2k` in `V(m) ⊗ V(n)`. -/
def hwVec (m n k : ℕ) : StandardSl2Module K m ⊗[K] StandardSl2Module K n :=
  ∑ a ∈ Finset.range (k + 1), cgCoeff (K := K) m n k a • (vNat m a ⊗ₜ vNat n (k - a))

/-! ### B.2. Weight and raising operator -/

/-- `hwVec m n k` has weight `m + n - 2k`. -/
lemma tensorH_hwVec (k : ℕ) :
    tensorH (K := K) m n (hwVec m n k) = ((m : K) + n - 2 * k) • hwVec m n k := by
  rw [hwVec, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [map_smul, tensorH_tmul_vNat, smul_comm]
  congr 1
  rw [Nat.cast_sub hak]
  ring

/-- `hwVec m n k` is killed by the diagonal raising operator when `k ≤ min m n`. -/
lemma tensorE_hwVec [CharZero K] {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    tensorE (K := K) m n (hwVec m n k) = 0 := by
  rcases k with _ | j
  · simp [hwVec, tensorE, diagEnd_tmul, ρE_vNat_zero]
  · have hterm : ∀ a ∈ Finset.range (j + 1 + 1),
        tensorE (K := K) m n (cgCoeff (K := K) m n (j + 1) a •
          (vNat m a ⊗ₜ vNat n (j + 1 - a))) =
          cgCoeff (K := K) m n (j + 1) a • (ρE (vNat m a) ⊗ₜ vNat n (j + 1 - a)) +
            cgCoeff (K := K) m n (j + 1) a • (vNat m a ⊗ₜ ρE (vNat n (j + 1 - a))) := by
      intro a _
      rw [map_smul, tensorE, diagEnd_tmul, smul_add]
    rw [hwVec, map_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_range_succ' _ (j + 1), Finset.sum_range_succ _ (j + 1)]
    simp only [ρE_vNat_zero, Nat.sub_self, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      smul_zero, add_zero]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a ha => ?_
    have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [Nat.add_sub_add_right, show j + 1 - a = j - a + 1 by omega, ρE_vNat_succ, ρE_vNat_succ,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul, ← add_smul,
      cgCoeff_rec hkm hkn haj, zero_smul]

/-! ### B.3. Primitive vectors and lowering strings -/

/-- `hwVec m n k` is nonzero for `k ≤ n`: its `v_0 ⊗ v_k` coefficient is `(n-k)! m!`. -/
lemma hwVec_ne_zero [CharZero K] {k : ℕ} (hkn : k ≤ n) :
    hwVec (K := K) m n k ≠ 0 := by
  intro h0
  have h1 := congrArg (tensorCoord m n 0 ⟨k, by omega⟩) h0
  rw [hwVec, map_sum, Finset.sum_range_succ'] at h1
  simp only [map_smul, tensorCoord_tmul, vNat_apply, Fin.val_zero, smul_eq_mul, map_zero,
    Nat.sub_zero, ↓reduceIte, mul_one] at h1

  rw [Finset.sum_eq_zero (fun a _ => by simp), zero_add] at h1
  simp [cgCoeff, Nat.factorial_ne_zero] at h1

/-- `hwVec m n k` is a primitive vector of weight `m + n - 2k` for the diagonal action. -/
lemma hwVec_hasPrimitiveVectorWith [CharZero K] {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m)
    (hkn : k ≤ n) :
    (isSl2Triple_tensor (K := K) hmn).HasPrimitiveVectorWith (hwVec (K := K) m n k)
      ((m + n - 2 * k : ℕ) : K) where
  ne_zero := hwVec_ne_zero hkn
  lie_h := by
    rw [Module.End.lie_apply, tensorH_hwVec, Nat.cast_sub (by omega)]
    push_cast
    ring_nf
  lie_e := by rw [Module.End.lie_apply, tensorE_hwVec hkm hkn]

/-- The first `m + n - 2k + 1` members of the lowering string of `hwVec m n k` are nonzero. -/
lemma tensorF_pow_hwVec_ne_zero [CharZero K] {k l : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m)
    (hkn : k ≤ n) (hl : l ≤ m + n - 2 * k) :
    (tensorF (K := K) m n ^ l) (hwVec m n k) ≠ 0 :=
  prim_f_pow_ne_zero (hwVec_hasPrimitiveVectorWith hmn hkm hkn) hl

/-- The lowering string of `hwVec m n k` ends after `m + n - 2k + 1` steps. -/
lemma tensorF_pow_hwVec_eq_zero [CharZero K] {k : ℕ} (hmn : 0 < m + n) (hkm : k ≤ m)
    (hkn : k ≤ n) :
    (tensorF (K := K) m n ^ (m + n - 2 * k + 1)) (hwVec m n k) = 0 :=
  prim_f_pow_zero (hwVec_hasPrimitiveVectorWith hmn hkm hkn)

end PhyslibAlpha.Sl2
