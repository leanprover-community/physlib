/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.WignerEckart

/-!

# The projection theorem for vector operators

Tensor operators are unique up to a scalar, and every vector operator on an irreducible
multiplet is a multiple of the angular momentum itself.

## i. Overview

By the Wigner–Eckart theorem the tensor operators of rank `k` from `V(m)` to `V(p)` form a space
of dimension at most one. So if one nonzero tensor operator is known, every other one is a scalar
multiple of it.

For rank `k = 2` (vector operators, `κ = 1` in physics notation) and `m = p = n` there is a
canonical nonzero tensor operator: the `sl₂` action itself, `v_0 ↦ e`, `v_1 ↦ -h`, `v_2 ↦ -2f`,
corresponding to the spherical components of the angular momentum `J`. Hence every vector
operator `T` on the multiplet `V(n)` satisfies `T = c • J` for a single scalar `c`. This is the
projection theorem behind the Landé `g`-factor; the usual formula
`c = ⟨J · V⟩ / (j(j+1))` for the scalar is not part of this file.

## ii. Key results

- `IsTensorIntertwiner.exists_eq_smul_of_ne_zero` and `IsTensorOperator.exists_eq_smul_of_ne_zero`
  give uniqueness up to a scalar.
- `sl2Operator` is the `sl₂` action as a rank-2 tensor operator, see `isTensorOperator_sl2Operator`.
- `IsTensorOperator.exists_eq_smul_sl2Operator` is the projection theorem.

## iii. Table of contents

- A. Uniqueness up to a scalar
- B. The angular momentum as a vector operator
  - B.1. Definition and values
  - B.2. Commutation relations
- C. The projection theorem

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.11.

## A. Uniqueness up to a scalar

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct

open StandardSl2Module

variable {K : Type*} [Field K] [CharZero K] {k m n p : ℕ}

/-- Two tensor intertwiners into the same `V(p)` are proportional, provided the second one is
nonzero. -/
lemma IsTensorIntertwiner.exists_eq_smul_of_ne_zero (hmn : 0 < m + n)
    {φ ψ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K p}
    (hφ : IsTensorIntertwiner φ) (hψ : IsTensorIntertwiner ψ) (hψ0 : ψ ≠ 0) :
    ∃ c : K, φ = c • ψ := by
  by_cases hp : ∃ j : Fin (min m n + 1), m + n - 2 * (j : ℕ) = p
  · obtain ⟨j, rfl⟩ := hp
    obtain ⟨a, ha⟩ := hφ.exists_eq_smul_cgProj hmn
    obtain ⟨b, hb⟩ := hψ.exists_eq_smul_cgProj hmn
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hψ0 (by rw [hb, zero_smul])
    exact ⟨a / b, by rw [ha, hb, smul_smul, div_mul_cancel₀ a hb0]⟩
  · push Not at hp
    exact absurd (hψ.eq_zero_of_forall_ne hmn hp) hψ0

/-- Two tensor operators of rank `k` from `V(m)` to `V(p)` are proportional, provided the second
one is nonzero. -/
lemma IsTensorOperator.exists_eq_smul_of_ne_zero (hkm : 0 < k + m)
    {T S : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K] StandardSl2Module K p}
    (hT : IsTensorOperator T) (hS : IsTensorOperator S) (hS0 : S ≠ 0) :
    ∃ c : K, T = c • S := by
  have hl0 : TensorProduct.lift S ≠ 0 := by
    intro h
    apply hS0
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have := LinearMap.congr_fun h (x ⊗ₜ y)
    simpa only [TensorProduct.lift.tmul, LinearMap.zero_apply] using this
  obtain ⟨c, hc⟩ := hT.lift_isTensorIntertwiner.exists_eq_smul_of_ne_zero hkm
    hS.lift_isTensorIntertwiner hl0
  refine ⟨c, LinearMap.ext fun x => LinearMap.ext fun y => ?_⟩
  have := LinearMap.congr_fun hc (x ⊗ₜ y)
  simpa only [TensorProduct.lift.tmul, LinearMap.smul_apply] using this

/-!

## B. The angular momentum as a vector operator

### B.1. Definition and values

-/

variable (n) in
/-- The `sl₂` action on `V(n)` as a tensor operator of rank 2: `v_0 ↦ e`, `v_1 ↦ -h`,
`v_2 ↦ -2f`. These are the spherical components of the angular momentum, up to normalisation. -/
def sl2Operator : StandardSl2Module K 2 →ₗ[K] Module.End K (StandardSl2Module K n) :=
  (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 0).smulRight ρE +
    (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 1).smulRight ((-1 : K) • ρH) +
    (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 2).smulRight ((-2 : K) • ρF)

omit [CharZero K] in
lemma sl2Operator_vNat_zero : sl2Operator (K := K) n (vNat 2 0) = ρE := by
  simp [sl2Operator, vNat_apply]

omit [CharZero K] in
lemma sl2Operator_vNat_one : sl2Operator (K := K) n (vNat 2 1) = (-1 : K) • ρH := by
  simp [sl2Operator, vNat_apply]

omit [CharZero K] in
lemma sl2Operator_vNat_two : sl2Operator (K := K) n (vNat 2 2) = (-2 : K) • ρF := by
  simp [sl2Operator, vNat_apply]

omit [CharZero K] in
lemma sl2Operator_vNat_of_lt {l : ℕ} (hl : 2 < l) : sl2Operator (K := K) n (vNat 2 l) = 0 := by
  rw [vNat_of_lt hl, map_zero]

/-!

### B.2. Commutation relations

-/

lemma ρE_mul_ρF' : (ρE : Module.End K (StandardSl2Module K n)) * ρF = ρF * ρE + ρH := by
  have h := rel_ef (K := K) (n := n)
  rw [LieRing.of_associative_ring_bracket] at h
  rw [← h]
  abel

omit [CharZero K] in
lemma ρH_mul_ρE' : (ρH : Module.End K (StandardSl2Module K n)) * ρE = ρE * ρH + (2 : K) • ρE := by
  have h := rel_he (K := K) (n := n)
  rw [LieRing.of_associative_ring_bracket] at h
  rw [← h]
  abel

omit [CharZero K] in
lemma ρH_mul_ρF' : (ρH : Module.End K (StandardSl2Module K n)) * ρF = ρF * ρH - (2 : K) • ρF := by
  have h := rel_hf (K := K) (n := n)
  rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add'] at h
  rw [h]
  module

lemma ρE_vNat_two_one : (ρE : Module.End K (StandardSl2Module K 2)) (vNat 2 1) =
    (2 : K) • vNat 2 0 := by
  rw [ρE_vNat_succ]
  norm_num

lemma ρE_vNat_two_two : (ρE : Module.End K (StandardSl2Module K 2)) (vNat 2 2) =
    (2 : K) • vNat 2 1 := by
  rw [ρE_vNat_succ]
  norm_num

omit [CharZero K] in
lemma ρH_vNat_two_zero : (ρH : Module.End K (StandardSl2Module K 2)) (vNat 2 0) =
    (2 : K) • vNat 2 0 := by
  rw [ρH_vNat]
  norm_num

omit [CharZero K] in
lemma ρH_vNat_two_one : (ρH : Module.End K (StandardSl2Module K 2)) (vNat 2 1) = 0 := by
  rw [ρH_vNat]
  norm_num

omit [CharZero K] in
lemma ρH_vNat_two_two : (ρH : Module.End K (StandardSl2Module K 2)) (vNat 2 2) =
    (-2 : K) • vNat 2 2 := by
  rw [ρH_vNat]
  norm_num

omit [CharZero K] in
/-- A commutation relation `[Y, A x] = A (X x)` for a linear `A` holds for all `x` once it holds
on the coordinate vectors. -/
lemma comm_of_vNat {X : Module.End K (StandardSl2Module K k)}
    {Y : Module.End K (StandardSl2Module K n)}
    {A : StandardSl2Module K k →ₗ[K] Module.End K (StandardSl2Module K n)}
    (h : ∀ l, Y * A (vNat k l) - A (vNat k l) * Y = A (X (vNat k l)))
    (x : StandardSl2Module K k) :
    Y ∘ₗ A x - A x ∘ₗ Y = A (X x) := by
  have hext : (LinearMap.mulLeft K Y - LinearMap.mulRight K Y) ∘ₗ A = A ∘ₗ X :=
    linearMap_ext_vNat fun l => by
      simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply] using h l
  have := LinearMap.congr_fun hext x
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Module.End.mul_eq_comp] using this

/-- The `sl₂` action is a tensor operator of rank 2 on every `V(n)`. -/
lemma isTensorOperator_sl2Operator : IsTensorOperator (sl2Operator (K := K) n) where
  comm_E := comm_of_vNat fun l => by
    match l with
    | 0 => rw [sl2Operator_vNat_zero, ρE_vNat_zero, map_zero, sub_self]
    | 1 =>
      rw [sl2Operator_vNat_one, ρE_vNat_two_one, map_smul, sl2Operator_vNat_zero]
      simp only [smul_mul_assoc, mul_smul_comm, ρH_mul_ρE']
      module
    | 2 =>
      rw [sl2Operator_vNat_two, ρE_vNat_two_two, map_smul, sl2Operator_vNat_one]
      simp only [smul_mul_assoc, mul_smul_comm, ρE_mul_ρF']
      module
    | l + 3 =>
      have h3 : 2 < l + 3 := by omega
      simp only [vNat_of_lt h3, map_zero, mul_zero, zero_mul, sub_self]
  comm_F := comm_of_vNat fun l => by
    match l with
    | 0 =>
      rw [sl2Operator_vNat_zero, ρF_vNat, sl2Operator_vNat_one, ρE_mul_ρF']
      module
    | 1 =>
      rw [sl2Operator_vNat_one, ρF_vNat, sl2Operator_vNat_two]
      simp only [smul_mul_assoc, mul_smul_comm, ρH_mul_ρF']
      module
    | 2 =>
      rw [sl2Operator_vNat_two, ρF_vNat, sl2Operator_vNat_of_lt (by omega)]
      simp only [smul_mul_assoc, mul_smul_comm]
      module
    | l + 3 =>
      have h3 : 2 < l + 3 := by omega
      simp only [vNat_of_lt h3, map_zero, mul_zero, zero_mul, sub_self]
  comm_H := comm_of_vNat fun l => by
    match l with
    | 0 =>
      rw [sl2Operator_vNat_zero, ρH_vNat_two_zero, map_smul, sl2Operator_vNat_zero, ρH_mul_ρE']
      module
    | 1 =>
      rw [sl2Operator_vNat_one, ρH_vNat_two_one, map_zero]
      simp only [smul_mul_assoc, mul_smul_comm]
      module
    | 2 =>
      rw [sl2Operator_vNat_two, ρH_vNat_two_two, map_smul, sl2Operator_vNat_two]
      simp only [smul_mul_assoc, mul_smul_comm, ρH_mul_ρF']
      module
    | l + 3 =>
      have h3 : 2 < l + 3 := by omega
      simp only [vNat_of_lt h3, map_zero, mul_zero, zero_mul, sub_self]

/-- On `V(n)` with `n > 0` the `sl₂` action is a nonzero tensor operator. -/
lemma sl2Operator_ne_zero (hn : 0 < n) : sl2Operator (K := K) n ≠ 0 := by
  intro h
  have h1 := congrArg (fun A => A (vNat 2 0) (vNat n 1)) h
  simp only [sl2Operator_vNat_zero, LinearMap.zero_apply] at h1
  have hE := ρE_vNat_succ (K := K) (n := n) 0
  rw [zero_add] at hE
  rw [hE] at h1
  have h0 := congrFun h1 ⟨0, Nat.succ_pos n⟩
  simp only [Pi.smul_apply, smul_eq_mul, vNat_apply, Pi.zero_apply] at h0
  norm_num at h0
  exact (Nat.cast_ne_zero.mpr hn.ne') h0

/-!

## C. The projection theorem

-/

/-- **Projection theorem.** Every vector operator (tensor operator of rank 2) on the multiplet
`V(n)` is a scalar multiple of the angular momentum `sl2Operator n`. -/
lemma IsTensorOperator.exists_eq_smul_sl2Operator
    {T : StandardSl2Module K 2 →ₗ[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K n}
    (hT : IsTensorOperator T) : ∃ c : K, T = c • sl2Operator n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    refine hT.eq_zero_of_forall_ne (by norm_num) fun j => ?_
    have := j.isLt
    omega
  · exact hT.exists_eq_smul_of_ne_zero (by omega) isTensorOperator_sl2Operator
      (sl2Operator_ne_zero hn)

end PhyslibAlpha.Sl2
