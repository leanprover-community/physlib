/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorHighestWeight

/-!

# Schur's lemma for the standard sl₂ modules

Linear maps between standard modules that commute with the `sl₂` action.

## i. Overview

A linear map `φ : V(a) → V(b)` between standard modules is an intertwiner if it commutes with
the raising, lowering and weight operators. The image of the highest-weight vector `v_0` is then
killed by the raising operator and has weight `a`. In `V(b)` the only vectors killed by the raising
operator are the multiples of `v_0`, which have weight `b`. Hence `φ v_0 = c • v_0` with `c = 0`
unless `a = b`, and since `v_l = f^l v_0` this determines `φ` completely. This is Schur's lemma
for the standard modules: an intertwiner `V(a) → V(b)` is zero for `a ≠ b` and a scalar multiple of
the identity for `a = b`.

## ii. Key results

- `IsIntertwiner` is the predicate for linear maps commuting with `ρE`, `ρF` and `ρH`.
- `IsIntertwiner.apply_vNat` shows that an intertwiner sends `v_l` to `c • v_l` for a fixed `c`.
- `IsIntertwiner.eq_zero_of_ne` shows that an intertwiner `V(a) → V(b)` with `a ≠ b` vanishes.
- `IsIntertwiner.eq_smul_id` shows that an intertwiner `V(n) → V(n)` is a scalar multiple of the
  identity.

## iii. Table of contents

- A. Intertwiners
  - A.1. Definition and closure properties
  - A.2. Coordinate vectors and vectors killed by the raising operator
  - A.3. Schur's lemma

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Intertwiners

### A.1. Definition and closure properties

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

variable {K : Type*} [Field K] {a b n : ℕ}

/-- A linear map between standard modules is an intertwiner if it commutes with the raising,
lowering and weight operators. -/
structure IsIntertwiner (φ : StandardSl2Module K a →ₗ[K] StandardSl2Module K b) : Prop where
  comm_ρE : φ ∘ₗ ρE = ρE ∘ₗ φ
  comm_ρF : φ ∘ₗ ρF = ρF ∘ₗ φ
  comm_ρH : φ ∘ₗ ρH = ρH ∘ₗ φ

namespace IsIntertwiner

variable {φ ψ : StandardSl2Module K a →ₗ[K] StandardSl2Module K b}

lemma apply_ρE (hφ : IsIntertwiner φ) (x : StandardSl2Module K a) : φ (ρE x) = ρE (φ x) :=
  LinearMap.congr_fun hφ.comm_ρE x

lemma apply_ρF (hφ : IsIntertwiner φ) (x : StandardSl2Module K a) : φ (ρF x) = ρF (φ x) :=
  LinearMap.congr_fun hφ.comm_ρF x

lemma apply_ρH (hφ : IsIntertwiner φ) (x : StandardSl2Module K a) : φ (ρH x) = ρH (φ x) :=
  LinearMap.congr_fun hφ.comm_ρH x

lemma apply_ρF_pow (hφ : IsIntertwiner φ) (l : ℕ) (x : StandardSl2Module K a) :
    φ ((ρF ^ l) x) = (ρF ^ l) (φ x) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [pow_succ', Module.End.mul_apply, hφ.apply_ρF, ih, pow_succ',
      Module.End.mul_apply]

/-- The identity is an intertwiner. -/
lemma id : IsIntertwiner (LinearMap.id : StandardSl2Module K n →ₗ[K] StandardSl2Module K n) :=
  ⟨rfl, rfl, rfl⟩

/-- Scalar multiples of intertwiners are intertwiners. -/
lemma smul (hφ : IsIntertwiner φ) (c : K) : IsIntertwiner (c • φ) where
  comm_ρE := by rw [LinearMap.smul_comp, hφ.comm_ρE, LinearMap.comp_smul]
  comm_ρF := by rw [LinearMap.smul_comp, hφ.comm_ρF, LinearMap.comp_smul]
  comm_ρH := by rw [LinearMap.smul_comp, hφ.comm_ρH, LinearMap.comp_smul]

/-- Sums of intertwiners are intertwiners. -/
lemma add (hφ : IsIntertwiner φ) (hψ : IsIntertwiner ψ) : IsIntertwiner (φ + ψ) where
  comm_ρE := by rw [LinearMap.add_comp, hφ.comm_ρE, hψ.comm_ρE, LinearMap.comp_add]
  comm_ρF := by rw [LinearMap.add_comp, hφ.comm_ρF, hψ.comm_ρF, LinearMap.comp_add]
  comm_ρH := by rw [LinearMap.add_comp, hφ.comm_ρH, hψ.comm_ρH, LinearMap.comp_add]

end IsIntertwiner

/-!

### A.2. Coordinate vectors and vectors killed by the raising operator

-/

/-- The lowering string of `v_0` runs through the coordinate vectors: `f^l v_0 = v_l`. -/
lemma ρF_pow_vNat_zero (l : ℕ) :
    ((ρF : Module.End K (StandardSl2Module K n)) ^ l) (vNat n 0) = vNat n l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [pow_succ', Module.End.mul_apply, ih, ρF_vNat]

/-- Two linear maps out of a standard module agree if they agree on all `v_l`. -/
lemma StandardSl2Module.linearMap_ext_vNat {M : Type*} [AddCommGroup M]
    [Module K M] {α β : StandardSl2Module K a →ₗ[K] M} (h : ∀ l, α (vNat a l) = β (vNat a l)) :
    α = β := by
  refine (Pi.basisFun K (Fin (a + 1))).ext fun k => ?_
  have hk : (Pi.basisFun K (Fin (a + 1))) k = vNat a k := by
    rw [Pi.basisFun_apply, vNat_eq_v (Nat.lt_succ_iff.mp k.isLt)]
    rfl
  rw [hk]
  exact h k

/-- A vector of `V(n)` killed by the raising operator is a multiple of `v_0`. -/
lemma eq_smul_vNat_zero_of_ρE_eq_zero [CharZero K] {w : StandardSl2Module K n}
    (hw : (ρE : Module.End K (StandardSl2Module K n)) w = 0) :
    w = w ⟨0, Nat.succ_pos n⟩ • vNat n 0 := by
  funext k
  rcases k with ⟨_ | j, hk⟩
  · simp [vNat_apply]
  · have hj : j ≠ n := by omega
    have h := congrFun hw ⟨j, by omega⟩
    simp only [ρE, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hj, dite_false] at h
    have hne : (((j : ℕ) + 1) * ((n : K) - (j : ℕ)) : K) ≠ 0 := by
      have h1 : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have h2 : ((n : K) - (j : ℕ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast (by omega : n ≠ j)
      exact mul_ne_zero (by exact_mod_cast h1) h2
    have hz : w ⟨j + 1, hk⟩ = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (by exact_mod_cast h') hne
      · exact h'
    simp [hz, vNat_apply]

/-!

### A.3. Schur's lemma

-/

namespace IsIntertwiner

variable [CharZero K] {φ : StandardSl2Module K a →ₗ[K] StandardSl2Module K b}

/-- The image of `v_0` under an intertwiner is a multiple of `v_0`. -/
lemma apply_vNat_zero (hφ : IsIntertwiner φ) :
    φ (vNat a 0) = φ (vNat a 0) ⟨0, Nat.succ_pos b⟩ • vNat b 0 := by
  apply eq_smul_vNat_zero_of_ρE_eq_zero
  rw [← hφ.apply_ρE, ρE_vNat_zero, map_zero]

/-- An intertwiner sends every coordinate vector `v_l` to the same multiple `c • v_l`, where `c`
is the `v_0`-coordinate of the image of `v_0`. -/
lemma apply_vNat (hφ : IsIntertwiner φ) (l : ℕ) :
    φ (vNat a l) = φ (vNat a 0) ⟨0, Nat.succ_pos b⟩ • vNat b l := by
  rw [← ρF_pow_vNat_zero l, hφ.apply_ρF_pow]
  conv_lhs => rw [hφ.apply_vNat_zero]
  rw [map_smul, ρF_pow_vNat_zero]

/-- The scalar of an intertwiner vanishes unless the two highest weights agree. -/
lemma coeff_eq_zero_of_ne (hφ : IsIntertwiner φ) (hab : a ≠ b) :
    φ (vNat a 0) ⟨0, Nat.succ_pos b⟩ = 0 := by
  set c := φ (vNat a 0) ⟨0, Nat.succ_pos b⟩
  have h := congrFun (hφ.apply_ρH (vNat a 0)) ⟨0, Nat.succ_pos b⟩
  rw [ρH_vNat, map_smul, hφ.apply_vNat_zero, map_smul, ρH_vNat] at h
  simp only [Pi.smul_apply, smul_eq_mul, vNat_apply, CharP.cast_eq_zero, mul_zero, sub_zero,
    ite_true, mul_one] at h
  have hab' : (a : K) ≠ b := by exact_mod_cast hab
  rcases mul_eq_zero.mp (by linear_combination h : ((a : K) - b) * c = 0) with h' | h'
  · exact absurd (sub_eq_zero.mp h') hab'
  · exact h'

/-- **Schur's lemma**, first half: an intertwiner `V(a) → V(b)` with `a ≠ b` is zero. -/
lemma eq_zero_of_ne (hφ : IsIntertwiner φ) (hab : a ≠ b) : φ = 0 :=
  StandardSl2Module.linearMap_ext_vNat fun l => by
    rw [hφ.apply_vNat, hφ.coeff_eq_zero_of_ne hab, zero_smul, LinearMap.zero_apply]

/-- **Schur's lemma**, second half: an intertwiner `V(n) → V(n)` is a scalar multiple of the
identity. -/
lemma eq_smul_id {φ : StandardSl2Module K n →ₗ[K] StandardSl2Module K n} (hφ : IsIntertwiner φ) :
    φ = φ (vNat n 0) ⟨0, Nat.succ_pos n⟩ • LinearMap.id :=
  StandardSl2Module.linearMap_ext_vNat fun l => by
    rw [hφ.apply_vNat, LinearMap.smul_apply, LinearMap.id_apply]

end IsIntertwiner

end PhyslibAlpha.Sl2
