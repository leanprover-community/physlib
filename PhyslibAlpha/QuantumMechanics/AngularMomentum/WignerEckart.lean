/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorIntertwiner

/-!

# The Wigner–Eckart theorem for sl₂

Tensor operators between standard `sl₂` modules and the factorisation of their matrix elements.

## i. Overview

A tensor operator of rank `k` from `V(m)` to `V(p)` is a linear map
`T : V(k) → Hom(V(m), V(p))` with `[X, T x] = T (X x)` for the raising, lowering and weight
operators `X`. In physics notation, with `k = 2κ`, `m = 2j` and `p = 2j'`, the vectors `T v_q` are
the components `T^{(κ)}_μ` of a spherical tensor operator, and the condition is the usual
commutator definition.

The map `x ⊗ y ↦ T x y` is then a tensor intertwiner `V(k) ⊗ V(m) → V(p)`. By the results of
`Sl2.TensorIntertwiner` this gives the Wigner–Eckart theorem: if `p = k + m - 2j`, there is a
single scalar `c` (the reduced matrix element) with `T x y = c • cgProj (x ⊗ y)` for all `x, y`,
so every matrix element is `c` times a Clebsch–Gordan coefficient. If `p` is not of this form,
`T = 0` (the triangle and parity rule). Independently of this, the weight operator alone gives the
rule for the magnetic quantum numbers: a matrix element vanishes unless the weights add up.

The basis `v_l = f^l v_0` of the standard modules is not normalised, so the Clebsch–Gordan
coefficients here differ from the usual tabulated values by normalisation factors. The statements
themselves do not depend on this choice.

## ii. Key results

- `IsTensorOperator` is the predicate for tensor operators.
- `IsTensorOperator.lift_isTensorIntertwiner` turns a tensor operator into a tensor intertwiner.
- `IsTensorOperator.exists_eq_smul_cgProj` is the Wigner–Eckart theorem.
- `IsTensorOperator.eq_zero_of_forall_ne` is the triangle and parity selection rule.
- `IsTensorOperator.apply_vNat_eq_zero_of_weight_ne` is the selection rule for the weights.

## iii. Table of contents

- A. Tensor operators
  - A.1. Definition
  - A.2. Tensor operators as tensor intertwiners
- B. The Wigner–Eckart theorem
  - B.1. Factorisation and the triangle rule
  - B.2. The weight selection rule

## iv. References

- E. P. Wigner, *Group Theory and its Application to the Quantum Mechanics of Atomic Spectra*,
  Academic Press (1959), chapter 21.
- C. Eckart, *The application of group theory to the quantum dynamics of monatomic systems*,
  Rev. Mod. Phys. 2, 305 (1930).

## A. Tensor operators

### A.1. Definition

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct

open StandardSl2Module

variable {K : Type*} [Field K] {k m p : ℕ}

/-- A tensor operator of rank `k` from `V(m)` to `V(p)`: a linear map
`T : V(k) → Hom(V(m), V(p))` with `[X, T x] = T (X x)` for `X = e, f, h`. -/
structure IsTensorOperator
    (T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K] StandardSl2Module K p) :
    Prop where
  comm_E : ∀ x, ρE ∘ₗ T x - T x ∘ₗ ρE = T (ρE x)
  comm_F : ∀ x, ρF ∘ₗ T x - T x ∘ₗ ρF = T (ρF x)
  comm_H : ∀ x, ρH ∘ₗ T x - T x ∘ₗ ρH = T (ρH x)

/-!

### A.2. Tensor operators as tensor intertwiners

-/

namespace IsTensorOperator

variable {T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K] StandardSl2Module K p}

/-- Leibniz form of the commutation relation for the raising operator. -/
lemma apply_ρE (hT : IsTensorOperator T) (x : StandardSl2Module K k)
    (y : StandardSl2Module K m) : ρE (T x y) = T (ρE x) y + T x (ρE y) := by
  have h := LinearMap.congr_fun (hT.comm_E x) y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  rw [← h, sub_add_cancel]

/-- Leibniz form of the commutation relation for the lowering operator. -/
lemma apply_ρF (hT : IsTensorOperator T) (x : StandardSl2Module K k)
    (y : StandardSl2Module K m) : ρF (T x y) = T (ρF x) y + T x (ρF y) := by
  have h := LinearMap.congr_fun (hT.comm_F x) y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  rw [← h, sub_add_cancel]

/-- Leibniz form of the commutation relation for the weight operator. -/
lemma apply_ρH (hT : IsTensorOperator T) (x : StandardSl2Module K k)
    (y : StandardSl2Module K m) : ρH (T x y) = T (ρH x) y + T x (ρH y) := by
  have h := LinearMap.congr_fun (hT.comm_H x) y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  rw [← h, sub_add_cancel]

/-- The map `x ⊗ y ↦ T x y` of a tensor operator is a tensor intertwiner. -/
lemma lift_isTensorIntertwiner (hT : IsTensorOperator T) :
    IsTensorIntertwiner (TensorProduct.lift T) where
  comm_E := TensorProduct.ext' fun x y => by
    simp only [LinearMap.comp_apply, tensorE, diagEnd_tmul, map_add, TensorProduct.lift.tmul,
      hT.apply_ρE]
  comm_F := TensorProduct.ext' fun x y => by
    simp only [LinearMap.comp_apply, tensorF, diagEnd_tmul, map_add, TensorProduct.lift.tmul,
      hT.apply_ρF]
  comm_H := TensorProduct.ext' fun x y => by
    simp only [LinearMap.comp_apply, tensorH, diagEnd_tmul, map_add, TensorProduct.lift.tmul,
      hT.apply_ρH]

end IsTensorOperator

/-!

## B. The Wigner–Eckart theorem

### B.1. Factorisation and the triangle rule

-/

namespace IsTensorOperator

variable [CharZero K]

/-- **Triangle and parity rule.** If `p` is not of the form `k + m - 2j` with `j ≤ min k m`,
every tensor operator of rank `k` from `V(m)` to `V(p)` is zero. -/
lemma eq_zero_of_forall_ne (hkm : 0 < k + m)
    {T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K] StandardSl2Module K p}
    (hT : IsTensorOperator T) (hp : ∀ j : Fin (min k m + 1), k + m - 2 * (j : ℕ) ≠ p) :
    T = 0 := by
  have h := hT.lift_isTensorIntertwiner.eq_zero_of_forall_ne hkm hp
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have := LinearMap.congr_fun h (x ⊗ₜ y)
  simpa only [TensorProduct.lift.tmul, LinearMap.zero_apply] using this

/-- **Wigner–Eckart theorem.** A tensor operator of rank `k` from `V(m)` to `V(k + m - 2j)`
factorises as `T x y = c • cgProj (x ⊗ y)`: a single reduced matrix element `c` times the
Clebsch–Gordan projection. -/
lemma exists_eq_smul_cgProj (hkm : 0 < k + m) {j : Fin (min k m + 1)}
    {T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K]
      StandardSl2Module K (k + m - 2 * (j : ℕ))}
    (hT : IsTensorOperator T) :
    ∃ c : K, ∀ x y, T x y = c • cgProj hkm j (x ⊗ₜ y) := by
  obtain ⟨c, hc⟩ := hT.lift_isTensorIntertwiner.exists_eq_smul_cgProj hkm
  refine ⟨c, fun x y => ?_⟩
  have := LinearMap.congr_fun hc (x ⊗ₜ y)
  simpa only [TensorProduct.lift.tmul, LinearMap.smul_apply] using this

/-- **Wigner–Eckart theorem**, matrix-element form: every matrix element
`⟨v_s | T v_q | v_r⟩` is the reduced matrix element `c` times the Clebsch–Gordan coefficient, the
`v_s`-coordinate of `cgProj (v_q ⊗ v_r)`. -/
lemma exists_coord_eq (hkm : 0 < k + m) {j : Fin (min k m + 1)}
    {T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K]
      StandardSl2Module K (k + m - 2 * (j : ℕ))}
    (hT : IsTensorOperator T) :
    ∃ c : K, ∀ (q r : ℕ) (s : Fin (k + m - 2 * (j : ℕ) + 1)),
      T (vNat k q) (vNat m r) s = c * cgProj hkm j (vNat k q ⊗ₜ vNat m r) s := by
  obtain ⟨c, hc⟩ := hT.exists_eq_smul_cgProj hkm
  exact ⟨c, fun q r s => by rw [hc]; rfl⟩

/-!

### B.2. The weight selection rule

-/

/-- **Weight selection rule.** The matrix element `⟨v_s | T v_q | v_r⟩` vanishes unless the
weights add up, `(k - 2q) + (m - 2r) = p - 2s`. In physics notation this is `μ + m_j = m_{j'}`. -/
lemma apply_vNat_eq_zero_of_weight_ne
    {T : StandardSl2Module K k →ₗ[K] StandardSl2Module K m →ₗ[K] StandardSl2Module K p}
    (hT : IsTensorOperator T) (q r : ℕ) (s : Fin (p + 1))
    (hne : (k : ℤ) - 2 * q + ((m : ℤ) - 2 * r) ≠ (p : ℤ) - 2 * (s : ℕ)) :
    T (vNat k q) (vNat m r) s = 0 := by
  have h := congrFun (hT.apply_ρH (vNat k q) (vNat m r)) s
  rw [ρH_vNat, ρH_vNat] at h
  simp only [map_smul, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  change ((p : K) - 2 * (s : ℕ)) * T (vNat k q) (vNat m r) s = _ at h
  have hK : ((k : K) - 2 * q + ((m : K) - 2 * r)) ≠ (p : K) - 2 * (s : ℕ) := by
    intro e
    apply hne
    exact_mod_cast e
  have h' : (((p : K) - 2 * (s : ℕ)) - ((k : K) - 2 * q + ((m : K) - 2 * r))) *
      T (vNat k q) (vNat m r) s = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with e | e
  · exact absurd (sub_eq_zero.mp e).symm hK
  · exact e

end IsTensorOperator

end PhyslibAlpha.Sl2
