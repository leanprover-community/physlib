/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJ
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.MultipoleSumRule

/-!

# The Wigner–Eckart theorem with Clebsch–Gordan coefficients

The matrix elements of a tensor operator in the orthonormal bases are a reduced matrix element
times the Clebsch–Gordan coefficients, and the total rate out of a substate does not depend on
the substate.

## i. Overview

`WignerEckart` shows that a tensor operator `T` of rank `κ = k/2` from `V(m)` to
`V(k + m - 2j)` is `T x y = c • cgProj (x ⊗ y)`. Here the projection is written in the
orthonormal bases: `⟨u_s, cgProj x⟩ = ⟨w_j, w_j⟩^(-1/2) ⟨|J', J' - s⟩, x⟩` (`invForm_cgProj`),
because the component `V(k + m - 2j)` sits isometrically inside `V(k) ⊗ V(m)` (`embed`) and is
orthogonal to the other components. With `J = m/2`, `M = J - r`, `μ = κ - q`, `J' = J + κ - j`
and `M' = J' - s` this gives

`⟨J' M' | T^κ_μ | J M⟩ = R · ⟨κ μ J M | J' M'⟩`

with one reduced matrix element `R` (`IsTensorOperator.exists_normVec_eq`). The coefficient is
coupled in the order `κ ⊗ J`; `cgCoefficient_swap` relates it to the order `J ⊗ κ` by the phase
`(-1)^(J + κ - J')`.

Combined with the sum rule of `MultipoleSumRule`, the total transition strength out of
`|J M⟩`,

`Σ_{μ M'} |⟨J' M' | T^κ_μ | J M⟩|² = R² (2J' + 1) / (2J + 1)`,

does not depend on `M` (`IsTensorOperator.sum_sq_normVec`).

## ii. Key results

- `wigner3j_swap`, `cgCoefficient_swap`: exchanging the two coupled angular momenta.
- `invForm_cgProj`: the Clebsch–Gordan projection in the orthonormal bases.
- `IsTensorOperator.exists_normVec_eq`: the Wigner–Eckart theorem with Clebsch–Gordan
  coefficients.
- `IsTensorOperator.sum_sq_normVec`: the total strength out of a substate.

## iii. Table of contents

- A. Exchanging the coupled angular momenta
- B. The projections in the orthonormal bases
- C. The Wigner–Eckart theorem
- D. The total strength out of a substate

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.11.
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  section 5.4.

## A. Exchanging the coupled angular momenta

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

lemma neg_one_pow_congr_nat {p q : ℕ} (h : p % 2 = q % 2) : (-1 : ℝ) ^ p = (-1) ^ q := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

section Swap

variable {m n : ℕ}

/-- `(j₂ j₁ J; m₂ m₁ -M) = (-1)^(j₁ + j₂ + J) (j₁ j₂ J; m₁ m₂ -M)`. -/
lemma wigner3j_swap {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hl : l ≤ m + n - 2 * k)
    (hα : α ≤ m) (hβ : β ≤ n) :
    wigner3j n m k l β α = (-1) ^ (m + n - k) * wigner3j m n k l α β := by
  by_cases h : α + β = k + l
  · rw [wigner3j, wigner3j, ite_eq_left (show β + α = k + l by omega), ite_eq_left h]
    have hR := isMagic_regge hkm hkn hl hα hβ h
    have hswap := threeJR_swap_columns hR
    have hJ : regge m n k l α β 0 0 + regge m n k l α β 0 1 + regge m n k l α β 0 2 =
        m + n - k := by
      simp only [regge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      omega
    rw [hJ] at hswap
    rw [← hswap]
    congr 1
    funext i j
    fin_cases i <;> fin_cases j <;> simp [regge]
    omega
  · rw [wigner3j, wigner3j, ite_eq_right (show ¬(β + α = k + l) by omega), ite_eq_right h,
      mul_zero]

/-- **Exchange symmetry.** `⟨j₁ m₁ j₂ m₂ | J M⟩ = (-1)^(j₁ + j₂ - J) ⟨j₂ m₂ j₁ m₁ | J M⟩`. -/
lemma cgCoefficient_swap (hmn : 0 < m + n) {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) :
    cgCoefficient m n k l α β = (-1) ^ k * cgCoefficient n m k l β α := by
  rw [cgCoefficient_eq_wigner3j hmn hkm hkn hl hα hβ,
    cgCoefficient_eq_wigner3j (by omega) hkn hkm (by omega) hβ hα,
    wigner3j_swap hkm hkn hl hα hβ, show n + m - 2 * k + 1 = m + n - 2 * k + 1 by omega]
  have hp : (-1 : ℝ) ^ (m + k + l) = (-1) ^ k * (-1) ^ (n + k + l) * (-1) ^ (m + n - k) := by
    rw [← pow_add, ← pow_add]
    exact neg_one_pow_congr_nat (by omega)
  rw [hp]
  ring

end Swap

/-!

## B. The projections in the orthonormal bases

-/

section Projection

variable {m n : ℕ}

lemma stringVec_eq_smul_embed (hmn : 0 < m + n) (j : Fin (min m n + 1)) (l : ℕ) :
    stringVec m n j l = Real.sqrt (hwNormSq m n j) • embed hmn j (vNat _ l) := by
  have hjm : (j : ℕ) ≤ m := by have := j.isLt; omega
  have hjn : (j : ℕ) ≤ n := by have := j.isLt; omega
  rw [embed_vNat, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hwNormSq_pos hjm hjn)).ne',
    one_smul]

/-- `⟨u, cgProj x⟩ = ⟨w_j, w_j⟩^(-1/2) ⟨embed u, x⟩`. -/
lemma invForm_cgProj (hmn : 0 < m + n) (j : Fin (min m n + 1))
    (y : StandardSl2Module ℝ (m + n - 2 * (j : ℕ)))
    (x : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    invForm ℝ _ y (cgProj hmn j x) =
      (Real.sqrt (hwNormSq m n j))⁻¹ * tensorForm m n (embed hmn j y) x := by
  have hjm : (j : ℕ) ≤ m := by have := j.isLt; omega
  have hjn : (j : ℕ) ≤ n := by have := j.isLt; omega
  have hs := (Real.sqrt_pos.mpr (hwNormSq_pos hjm hjn)).ne'
  have h : (invForm ℝ _ y) ∘ₗ cgProj (K := ℝ) hmn j =
      (Real.sqrt (hwNormSq m n j))⁻¹ • (tensorForm m n (embed hmn j y)) :=
    (tensorStringBasis (K := ℝ) hmn).ext fun i => by
      obtain ⟨j', l'⟩ := i
      rw [tensorStringBasis_apply, LinearMap.comp_apply, LinearMap.smul_apply, cgProj_apply,
        cgEquiv_stringVec, sumVec, smul_eq_mul]
      by_cases hj : j' = j
      · subst hj
        rw [DirectSum.component.lof_self, stringVec_eq_smul_embed hmn j', map_smul, smul_eq_mul,
          tensorForm_embed, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      · simp only [DirectSum.component.of, hj, ↓reduceDIte, map_zero]
        rw [stringVec_eq_smul_embed hmn j', map_smul, smul_eq_mul,
          tensorForm_embed_of_ne hmn j (Ne.symm hj), mul_zero, mul_zero]
  exact LinearMap.congr_fun h x

end Projection

/-!

## C. The Wigner–Eckart theorem

-/

namespace IsTensorOperator

variable {k m : ℕ} (hkm : 0 < k + m) {j : Fin (min k m + 1)}
  {T : StandardSl2Module ℝ k →ₗ[ℝ] StandardSl2Module ℝ m →ₗ[ℝ]
    StandardSl2Module ℝ (k + m - 2 * (j : ℕ))}

include hkm in
/-- **Wigner–Eckart theorem with Clebsch–Gordan coefficients.** With `κ = k/2`, `μ = κ - q`,
`J = m/2`, `M = J - r`, `J' = (k + m)/2 - j` and `M' = J' - s`, there is a reduced matrix element
`R` with `⟨J' M' | T^κ_μ | J M⟩ = R · ⟨κ μ J M | J' M'⟩` for all `q, r, s`. -/
lemma exists_normVec_eq (hT : IsTensorOperator T) :
    ∃ R : ℝ, ∀ q r s : ℕ, invForm ℝ _ (normVec _ s) (T (normVec k q) (normVec m r)) =
      R * cgCoefficient k m j s q r := by
  obtain ⟨c, hc⟩ := hT.exists_eq_smul_cgProj hkm
  refine ⟨c * (Real.sqrt (hwNormSq k m j))⁻¹, fun q r s => ?_⟩
  rw [hc, map_smul, smul_eq_mul, invForm_cgProj, embed_normVec, cgCoefficient, tensorForm_comm]
  ring

/-!

## D. The total strength out of a substate

-/

include hkm in
/-- **The total strength out of a substate.** If `⟨J' M' | T^κ_μ | J M⟩ = R · ⟨κ μ J M | J' M'⟩`,
then `Σ_{μ M'} |⟨J' M' | T^κ_μ | J M⟩|² = R² (2J' + 1) / (2J + 1)` for every `M`. -/
lemma sum_sq_normVec (R : ℝ)
    (hR : ∀ q r s : ℕ, invForm ℝ _ (normVec _ s) (T (normVec k q) (normVec m r)) =
      R * cgCoefficient k m j s q r) {r : ℕ} (hr : r ≤ m) :
    ∑ q ∈ Finset.range (k + 1), ∑ s ∈ Finset.range (k + m - 2 * (j : ℕ) + 1),
      (invForm ℝ _ (normVec _ s) (T (normVec k q) (normVec m r))) ^ 2 =
        R ^ 2 * (((k + m - 2 * (j : ℕ) + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  have hjk : (j : ℕ) ≤ k := by have := j.isLt; omega
  have hjm : (j : ℕ) ≤ m := by have := j.isLt; omega
  have hsum := sum_sq_cgCoefficient_initial (m := m) (n := k) (by omega) hjm hjk hr
  rw [show m + k - 2 * (j : ℕ) = k + m - 2 * (j : ℕ) by omega] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hq' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hs' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [hR, cgCoefficient_swap hkm hjk hjm hs' hq' hr]
  have hsq : ((-1 : ℝ) ^ (j : ℕ)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination (R ^ 2 * cgCoefficient m k (j : ℕ) s r q ^ 2) * hsq

end IsTensorOperator

end PhyslibAlpha.Sl2
