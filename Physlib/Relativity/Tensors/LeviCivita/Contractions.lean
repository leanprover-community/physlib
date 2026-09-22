/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.LeviCivita.Basic
public import Physlib.Mathematics.KroneckerDelta.Contraction
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.RealTensor.Units.Basic
/-!

# Contraction identities for the Levi-Civita tensor

## i. Overview

This file proves the "epsilon-epsilon" contraction identities for the rank-four Levi-Civita
tensor `leviCivita` (notation `ε4`) in `d = 4`, stated in terms of the standard-basis
components of `ε4` itself (`realLorentzTensor.leviCivita_basis_repr_apply`).

The underlying facts about the `generalizedKroneckerDelta` alone, with no
tensor content, live in `Physlib.Mathematics.KroneckerDelta.Contraction`, next to the
definition of `generalizedKroneckerDelta`. Here we specialise those facts to the components of
`ε4`, where `(ε4)_b = (Tensor.basis _).repr ε4 b` is the standard-basis component of `ε4`, an
integer Levi-Civita symbol carried to the reals, and the sums run over the remaining
(uncontracted) component slots.

It also proves the Lorentzian tensor identities obtained by lowering all four indices of one
factor: the complete contraction is `-24`, while contracting three index pairs gives `-6` times
the unit tensor.

The Lorentzian proofs proceed through reusable component statements: lowering all four indices
contributes the orientation sign, tensor contractions become finite sums of matching components,
and the Euclidean contraction theorems evaluate those sums.

## ii. Key results

- `euclidLeviCivita_symbol_contract_zero` : full Euclidean contraction equals `24`.
- `euclidLeviCivita_symbol_contract_one` : the triple Euclidean contraction equals `6 · δ[a,b]`.
- `euclidLeviCivita_symbol_contract_two` :
  `∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])`.
- `realLorentzTensor.leviCivita_lowered_basis_repr_apply` : lowering all four indices changes
  every standard-basis component by the Lorentzian orientation sign `-1`.
- `realLorentzTensor.leviCivita_contract_three_basis_repr_apply` : the tensor triple contraction
  is the sum of matching standard-basis components.
- `leviCivita_contract_self` : `ε^{μνρσ} ε_{μνρσ} = -24`.
- `leviCivita_contract_three` : `ε^{μνρσ} ε_{μνρτ} = -6 δ^σ_τ`.

## iii. Table of contents

- A. Euclidean epsilon-epsilon contraction identities
- B. Lorentzian epsilon-epsilon contraction identities
  - B.1. The epsilon-epsilon contraction identities

## iv. References

* None.
-/

@[expose] public section

open Matrix TensorSpecies Tensor KroneckerDelta

/-!

## A. Euclidean epsilon-epsilon contraction identities

-/

TODO "The contractions done here use the relativistic Levi-Civita tensor `ε4`
  but treat it as a Euclidean tensor. We should define
  a euclidean form of the Levi-Civita tensor and prove replace the
  results here with theorems about that tensor."

/-- **Full Euclidean Levi-Civita contraction** `∑_b (ε4)_b · (ε4)_b = 24` at the symbol level:
summing the square of every standard-basis component of `ε4` over all four `Fin 4` index slots,
paired naively (no metric), counts the `4! = 24` permutations. The Lorentz contraction
`ε^{μνρσ} ε_{μνρσ}` lowers one factor with `η` and equals `-24` instead. -/
lemma euclidLeviCivita_symbol_contract_zero :
    ∑ g : (Fin 4 → Fin 4), euclidLeviCivita g * euclidLeviCivita g = 24 := by
  have hcast : ∀ g : Fin 4 → Fin 4,
      ((generalizedKroneckerDelta g id : ℝ)) * (generalizedKroneckerDelta g id : ℝ)
        = ((generalizedKroneckerDelta g id * generalizedKroneckerDelta g id : ℤ) : ℝ) :=
    fun g => by push_cast; ring
  simp only [euclidLeviCivita]
  rw [Finset.sum_congr rfl fun g _ => hcast g, ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_self]
  norm_num

/-- **Triple Euclidean Levi-Civita contraction** `∑_h (ε4)_{a,h} · (ε4)_{b,h} = 6 · δ[a,b]` at
the symbol level: contracting three of the four `Fin 4` component slots of `ε4` with the naive
Kronecker pairing leaves one free pair `a, b` and the factor `3! = 6`. The Lorentz form carries
an extra `det η = -1`. -/
lemma euclidLeviCivita_symbol_contract_one (a b : Fin 4) :
    ∑ h : Fin 3 → Fin 4, euclidLeviCivita (Fin.cons a h) * euclidLeviCivita (Fin.cons b h)
      = 6 * ((kroneckerDelta a b : ℕ) : ℝ) := by
  have hcast : ∀ h' : Fin 3 → Fin 4,
      (generalizedKroneckerDelta (Fin.cons a h') id : ℝ)
        * (generalizedKroneckerDelta (Fin.cons b h') id : ℝ)
        = ((generalizedKroneckerDelta (Fin.cons a h') id
            * generalizedKroneckerDelta (Fin.cons b h') id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  simp only [euclidLeviCivita]
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons]
  push_cast; ring

/-- **Triple Euclidean Levi-Civita contraction with the free index last.** This is the same
contraction as `euclidLeviCivita_symbol_contract_one`, in the slot order produced by the tensor
notation for `ε^{μνρσ} ε_{μνρτ}`. -/
lemma euclidLeviCivita_symbol_contract_one_last (a b : Fin 4) :
    ∑ h : Fin 3 → Fin 4, euclidLeviCivita (Fin.snoc h a) * euclidLeviCivita (Fin.snoc h b)
      = 6 * ((kroneckerDelta a b : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl fun h _ => ?_, euclidLeviCivita_symbol_contract_one a b]
  simp only [euclidLeviCivita, ← Int.cast_mul, generalizedKroneckerDelta_mul]
  rw [Fin.snoc_eq_cons_rotate, Fin.snoc_eq_cons_rotate]
  exact congrArg (fun z : ℤ => (z : ℝ))
    (generalizedKroneckerDelta_comp_perm (Fin.cons a h) (Fin.cons b h) (finRotate (3 + 1)))

/-- **Double Euclidean Levi-Civita contraction**
`∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])` at the symbol level:
contracting two of the four `Fin 4` component slots of `ε4` with the naive Kronecker pairing
leaves two free pairs and the factor `2! = 2`. The Lorentz form carries an extra `det η = -1`. -/
lemma euclidLeviCivita_symbol_contract_two (r s t w : Fin 4) :
    ∑ h : Fin 2 → Fin 4, euclidLeviCivita (Fin.cons r (Fin.cons s h))
          * euclidLeviCivita (Fin.cons t (Fin.cons w h))
      = 2 * (((kroneckerDelta r t : ℕ) : ℝ) * ((kroneckerDelta s w : ℕ) : ℝ)
          - ((kroneckerDelta r w : ℕ) : ℝ) * ((kroneckerDelta s t : ℕ) : ℝ)) := by
  have hcast : ∀ h' : Fin 2 → Fin 4,
      (generalizedKroneckerDelta
          (Fin.cons r (Fin.cons (s) h')) id : ℝ)
        * (generalizedKroneckerDelta
          (Fin.cons t (Fin.cons (w) h')) id : ℝ)
        = ((generalizedKroneckerDelta
            (Fin.cons r (Fin.cons (s) h')) id
            * generalizedKroneckerDelta
              (Fin.cons t (Fin.cons (w) h')) id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  simp only [euclidLeviCivita]
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons₂]
  push_cast; ring

/-!

## B. Lorentzian epsilon-epsilon contraction identities

-/

namespace realLorentzTensor

open TensorSpecies Tensor
open ComponentIdx.DropPairSection

/-- Lowering all four indices of the Levi-Civita tensor changes the sign of every standard-basis
component. This is the tensor-component form of the Lorentzian orientation factor
`det η = -1`. -/
lemma leviCivita_lowered_basis_repr_apply
    (b : ComponentIdx (S := realLorentzTensor 3)
      ![Color.down, Color.down, Color.down, Color.down]) :
    (Tensor.basis _).repr ({ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ) b =
      - (Tensor.basis _).repr ε4 b := by
  simp only [toDualMapAtIndex_basis_repr_apply_eq_mul]
  by_cases hb : Function.Injective b
  · have hp := minkowskiMatrix.prod_diagonal_comp_of_injective hb
    rw [Fin.prod_univ_four] at hp
    norm_num at hp
    linear_combination ((Tensor.basis _).repr ε4 b) * hp
  · have hcomp : ¬ Function.Injective (fun i => finSumFinEquiv (b i)) :=
      fun h => hb (Function.Injective.of_comp h)
    rw [leviCivita_basis_repr_eq_leviCivitaSymbol,
      leviCivitaSymbol_eq_zero_of_not_injective hcomp]
    norm_num

/-- The sum of the squared standard-basis components of the contravariant Levi-Civita tensor is
`4! = 24`. -/
lemma leviCivita_basis_contract_self :
    ∑ b : ComponentIdx (S := realLorentzTensor 3)
        ![Color.up, Color.up, Color.up, Color.up],
      (Tensor.basis _).repr ε4 b * (Tensor.basis _).repr ε4 b = 24 := by
  calc
    _ = ∑ g : Fin 4 → Fin 4, euclidLeviCivita g * euclidLeviCivita g :=
      Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 4))
        (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ fun b => by
          rw [leviCivita_basis_repr_apply]
          rfl
    _ = 24 := euclidLeviCivita_symbol_contract_zero

/-- Contracting the first three standard-basis components of two contravariant Levi-Civita tensors
gives `3! = 6` times the Kronecker delta on the remaining components. -/
lemma leviCivita_basis_contract_three (a b : Fin 1 ⊕ Fin 3) :
    ∑ h : Fin 3 → Fin 1 ⊕ Fin 3,
      (Tensor.basis _).repr ε4 (Fin.snoc h a) *
      (Tensor.basis _).repr ε4 (Fin.snoc h b) =
      6 * (if a = b then 1 else 0) := by
  simp only [leviCivita_basis_repr_apply]
  have hs (y : Fin 1 ⊕ Fin 3) (h : Fin 3 → Fin 1 ⊕ Fin 3) :
      (fun i => finSumFinEquiv ((Fin.snoc h y : Fin 4 → Fin 1 ⊕ Fin 3) i)) =
        Fin.snoc (fun i => finSumFinEquiv (h i)) (finSumFinEquiv y) := by
    funext i
    fin_cases i <;> rfl
  rw [Finset.sum_congr rfl fun h _ => by rw [hs a h, hs b h]]
  calc
    _ = ∑ g : Fin 3 → Fin 4,
        (generalizedKroneckerDelta (Fin.snoc g (finSumFinEquiv a)) id : ℝ) *
          (generalizedKroneckerDelta (Fin.snoc g (finSumFinEquiv b)) id : ℝ) :=
      Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 3))
        (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ fun _ => rfl
    _ = 6 * ((kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) : ℕ) : ℝ) :=
      euclidLeviCivita_symbol_contract_one_last _ _
    _ = 6 * (if a = b then 1 else 0) := by
      by_cases hab : a = b
      · subst hab
        simp [KroneckerDelta.eq_one_of_same]
      · rw [ite_eq_right hab,
          KroneckerDelta.eq_zero_of_ne (fun h => hab (finSumFinEquiv.injective h))]
        norm_num

/-- The standard-basis component formula for the tensor contraction
`ε^{μνρσ} ε_{μνρτ}`. -/
lemma leviCivita_contract_three_basis_repr_apply
    (b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.down]) :
    (Tensor.basis _).repr
        {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(τ)}ᵀ b =
      ∑ h : Fin 3 → Fin 1 ⊕ Fin 3,
        (Tensor.basis _).repr ε4 (Fin.snoc h (b 0)) *
          (Tensor.basis _).repr ({ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ) (Fin.snoc h (b 1)) := by
  have route {cA cB : Fin 4 → Color}
      (h1 : (0 : Fin 4) ≠ 2) (h2 : (1 : Fin 6) ≠ 4) (h3 : (2 : Fin 8) ≠ 6)
      (b : Fin 2 → Fin 1 ⊕ Fin 3) (x0 x1 x2 : Fin 1 ⊕ Fin 3) :
      let v := (ofFinEquiv (S := realLorentzTensor 3) (c := Fin.append cA cB) h3
        ((ofFinEquiv h2 ((ofFinEquiv h1 b (x0, x0)).1) (x1, x1)).1) (x2, x2)).1
      (ComponentIdx.prod (S := realLorentzTensor 3) (c := cA) (c1 := cB)) v =
        (![x0, x1, x2, b 0], ![x0, x1, x2, b 1]) := by
    dsimp only
    apply Prod.ext <;> funext m <;> fin_cases m <;> rfl
  simp only [contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    route]
  let F (h : Fin 3 → Fin 1 ⊕ Fin 3) :=
    (Tensor.basis _).repr ε4 ![h 0, h 1, h 2, b 0] *
      (Tensor.basis _).repr ({ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ) ![h 0, h 1, h 2, b 1]
  change (∑ x0, ∑ x1, ∑ x2, F ![x0, x1, x2]) = _
  let e : ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≃
      (Fin 3 → Fin 1 ⊕ Fin 3) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun v => (v 0, v 1, v 2)
      left_inv := fun _ => rfl
      right_inv := fun v => by funext m; fin_cases m <;> rfl }
  calc
    _ = ∑ h, F h := by
      rw [← Equiv.sum_comp e F]
      simp only [Fintype.sum_prod_type]
      rfl
    _ = _ := by
      refine Finset.sum_congr rfl fun h _ => ?_
      dsimp only [F]
      have hs (y : Fin 1 ⊕ Fin 3) :
          (![h 0, h 1, h 2, y] : Fin 4 → Fin 1 ⊕ Fin 3) = Fin.snoc h y := by
        funext i
        fin_cases i <;> rfl
      rw [hs (b 0), hs (b 1)]

/-!

### B.1. The epsilon-epsilon contraction identities

-/

/-- Contracting three indices of the Lorentzian Levi-Civita tensor with a fully lowered copy gives
`-6` times the mixed-index unit tensor. -/
lemma leviCivita_contract_three : {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(τ) =
    (-6) • unitTensor (S := realLorentzTensor) Color.down | σ τ }ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [map_zsmul, Finsupp.coe_smul, Pi.smul_apply, zsmul_eq_mul,
    permT_basis_repr_symm_apply, basisIdxCongr_eq_refl, Equiv.refl_apply,
    unitTensor_repr_apply Color.down]
  rw [IsReindexing.inv_eq_self_of_pointwise_eq _ (by decide),
    IsReindexing.inv_eq_self_of_pointwise_eq _ (by decide)]
  norm_num
  rw [leviCivita_contract_three_basis_repr_apply]
  calc
    _ = - ∑ h : Fin 3 → Fin 1 ⊕ Fin 3,
          (Tensor.basis _).repr ε4 (Fin.snoc h (b 0)) *
          (Tensor.basis _).repr ε4 (Fin.snoc h (b 1)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [leviCivita_lowered_basis_repr_apply]
      ring
    _ = - (6 * (if b 0 = b 1 then 1 else 0)) := by
      rw [leviCivita_basis_contract_three]
    _ = (if b 0 = b 1 then -6 else 0) := by
      split_ifs <;> norm_num

-- `checkType` linter: whnf on these full-contraction tensor-notation statements exceeds the
-- linter's 200k-heartbeat budget (since the v4.32.0 bump; still the case on v4.33.0). The proofs
-- themselves elaborate within the default budget.
/-- Fully contracting the tensor product of `ε4` and its fully lowered form is the sum of the
products of their matching standard-basis components. -/
@[nolint checkType]
lemma leviCivita_contract_self_eq_sum :
    {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ.toScalar =
      ∑ b : ComponentIdx (S := realLorentzTensor 3)
          ![Color.up, Color.up, Color.up, Color.up],
        (Tensor.basis _).repr ε4 b *
          (Tensor.basis _).repr ({ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ) b := by
  have route {cA cB : Fin 4 → Color}
      (h1 : (0 : Fin 2) ≠ 1) (h2 : (1 : Fin 4) ≠ 3)
      (h3 : (2 : Fin 6) ≠ 5) (h4 : (3 : Fin 8) ≠ 7)
      (x0 x1 x2 x3 : Fin 1 ⊕ Fin 3) :
      let v := (ofFinEquiv (S := realLorentzTensor 3) (c := Fin.append cA cB) h4
        ((ofFinEquiv h3
          ((ofFinEquiv h2
            ((ofFinEquiv h1 (fun j => j.elim0) (x0, x0)).1) (x1, x1)).1) (x2, x2)).1)
          (x3, x3)).1
      (ComponentIdx.prod (S := realLorentzTensor 3) (c := cA) (c1 := cB)) v =
        (![x0, x1, x2, x3], ![x0, x1, x2, x3]) := by
    dsimp only
    apply Prod.ext <;> funext m <;> fin_cases m <;> rfl
  rw [Tensor.toScalar_eq_repr]
  simp only [contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    route]
  let F (b : Fin 4 → Fin 1 ⊕ Fin 3) := (Tensor.basis _).repr ε4 b *
    (Tensor.basis _).repr ({ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ) b
  change (∑ x0, ∑ x1, ∑ x2, ∑ x3, F ![x0, x1, x2, x3]) = ∑ b, F b
  let e : ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≃
      (Fin 4 → Fin 1 ⊕ Fin 3) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      invFun := fun v => (v 0, v 1, v 2, v 3)
      left_inv := fun _ => rfl
      right_inv := fun v => by funext m; fin_cases m <;> rfl }
  rw [← Equiv.sum_comp e F]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Fully contracting the Lorentzian Levi-Civita tensor with a lowered copy gives `-24`. -/
@[nolint checkType]
lemma leviCivita_contract_self :
    {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ.toScalar = - 24 := by
  rw [leviCivita_contract_self_eq_sum]
  calc
    _ = - ∑ b : ComponentIdx (S := realLorentzTensor 3)
        ![Color.up, Color.up, Color.up, Color.up],
      (Tensor.basis _).repr ε4 b * (Tensor.basis _).repr ε4 b := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [leviCivita_lowered_basis_repr_apply]
        ring
    _ = -24 := by rw [leviCivita_basis_contract_self]

end realLorentzTensor
