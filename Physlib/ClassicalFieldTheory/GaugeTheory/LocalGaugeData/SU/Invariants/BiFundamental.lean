/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
/-!
# Invariants of two fundamental or two anti-fundamental indices of `SU(N)`

## i. Overview

The tensors with `n` fundamental indices, or with `n` anti-fundamental indices, have the tuples
`Fin n → Fin N` as component indices, and `g` moves the components by one factor of `g`, or of
its complex conjugate, per index (A).

For `SU(2)` the invariant tensors with two fundamental indices, and those with two
anti-fundamental indices, are the multiples of the antisymmetric symbol `ε` (B). The phase
`diag (i, -i)` negates the two diagonal components, and the quarter turn sends the component
`(0, 1)` to minus the component `(1, 0)`. For `N ≥ 3` there are none at all (C): the centre element
`ω 1`, with `ω` a primitive `N`-th root of unity, scales every component by `ω² ≠ 1`, or by its
conjugate.

Families indexed by `Fin n → Fin N` are turned into maps by `fundMap` and `antiFundMap`, and for
`SU(2)` the invariants of the span of such a family with two indices reduce to the epsilon
contraction `T ![0, 1] - T ![1, 0]` (D).

## ii. Key results

- `suTensor.epsilonFund`, `suTensor.epsilonAntiFund` : the antisymmetric symbols of `SU(2)`.
- `suTensor.exists_eq_smul_epsilonFund_of_invariant` : the invariant tensors with two fundamental
  indices of `SU(2)`, and its anti-fundamental twin.
- `suTensor.eq_zero_of_invariant_fundPair` : for `N ≥ 3` there are none, and its
  anti-fundamental twin.
- `suTensor.invariantReductionToEpsilonFund` : the reduction of the invariants of the span of a
  family to the epsilon contraction, and its anti-fundamental twin.

## iii. Table of contents

- A. Tensors with fundamental or with anti-fundamental indices
- B. Two indices of `SU(2)`: the antisymmetric symbol
- C. Two indices of `SU(N)` for `N ≥ 3`: no invariants
- D. Maps from components

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies Tensor SU

variable {N : ℕ}

/-!

## A. Tensors with fundamental or with anti-fundamental indices

-/

/-- The components of `g • t` for a tensor with `n` fundamental indices: one factor of `g` per
  index. -/
lemma basis_repr_smul_fund {n : ℕ} (g : SU N) (t : (suTensor N).Tensor fun _ : Fin n => .fund)
    (φ : Fin n → Fin N) :
    (Tensor.basis _).repr (g • t) φ
      = ∑ ψ : Fin n → Fin N, (∏ i, g.1 (φ i) (ψ i)) * (Tensor.basis _).repr t ψ := by
  rw [basis_repr_smul]
  refine Finset.sum_congr rfl fun ψ _ => congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)
  change LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N)) (fundRep N g) _ _ = _
  rw [toMatrix_fundRep]

/-- The components of `g • t` for a tensor with `n` anti-fundamental indices: one factor of the
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

/-- A sum over pairs of labels is a double sum. -/
lemma sum_fin_two_arrow {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin N) → M) :
    ∑ ψ : Fin 2 → Fin N, F ψ = ∑ x, ∑ y, F ![x, y] := by
  rw [← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-!

## B. Two indices of `SU(2)`: the antisymmetric symbol

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

/-- A function of two labels fixed by a diagonal matrix with entries squaring to `-1` and by
  the quarter turn, acting by one factor of `M g` per label, is a multiple of the antisymmetric
  symbol. -/
lemma eq_smul_epsilon_of_fixed (M : SU 2 → Matrix (Fin 2) (Fin 2) ℂ) {u v : ℂ}
    (hu : u * u = -1) (hv : v * v = -1)
    (hD : M (diagPhase Complex.I (by simp)) = diagonal ![u, v])
    (hR : M (rotation 0 1 (by norm_num)) = !![0, -1; 1, 0]) {c : (Fin 2 → Fin 2) → ℂ}
    (hc : ∀ (g : SU 2) (φ : Fin 2 → Fin 2),
      c φ = ∑ ψ : Fin 2 → Fin 2, (∏ i, M g (φ i) (ψ i)) * c ψ) (φ : Fin 2 → Fin 2) :
    c φ = c ![0, 1] * ((if φ = ![0, 1] then 1 else 0) - (if φ = ![1, 0] then 1 else 0)) := by
  have h1 := hc (diagPhase Complex.I (by simp)) ![0, 0]
  have h2 := hc (diagPhase Complex.I (by simp)) ![1, 1]
  have h3 := hc (rotation 0 1 (by norm_num)) ![0, 1]
  rw [hD] at h1 h2
  rw [hR] at h3
  simp only [sum_fin_two_arrow, Fin.sum_univ_two, Fin.prod_univ_two, diagonal_apply, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, empty_val', Fin.isValue] at h1 h2 h3
  simp [hu, hv] at h1 h2 h3
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, φ = ![a, b] := ⟨φ 0, φ 1, by
    funext i
    fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> simp
  · linear_combination h1 / 2
  · linear_combination h3
  · linear_combination h2 / 2

/-- An invariant tensor with two fundamental indices of `SU(2)` is a multiple of the
  antisymmetric symbol. -/
lemma exists_eq_smul_epsilonFund_of_invariant (t : (suTensor 2).Tensor fun _ : Fin 2 => .fund)
    (ht : ∀ g : SU 2, g • t = t) : ∃ a : ℂ, t = a • epsilonFund := by
  refine ⟨(Tensor.basis _).repr t ![0, 1],
    (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)⟩
  rw [map_smul, Finsupp.smul_apply, basis_repr_epsilonFund, smul_eq_mul]
  refine eq_smul_epsilon_of_fixed (fun g => g.1) Complex.I_mul_I
    (by rw [neg_mul_neg, Complex.I_mul_I]) ?_ ?_ (fun g φ => ?_) φ
  · rw [diagPhase_val]
    congr 1
    funext i
    fin_cases i <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [← basis_repr_smul_fund, ht]

/-- An invariant tensor with two anti-fundamental indices of `SU(2)` is a multiple of the
  antisymmetric symbol. -/
lemma exists_eq_smul_epsilonAntiFund_of_invariant
    (t : (suTensor 2).Tensor fun _ : Fin 2 => .antiFund) (ht : ∀ g : SU 2, g • t = t) :
    ∃ a : ℂ, t = a • epsilonAntiFund := by
  refine ⟨(Tensor.basis _).repr t ![0, 1],
    (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)⟩
  rw [map_smul, Finsupp.smul_apply, basis_repr_epsilonAntiFund, smul_eq_mul]
  refine eq_smul_epsilon_of_fixed (fun g => g.1.map (starRingEnd ℂ))
    (by rw [neg_mul_neg, Complex.I_mul_I]) Complex.I_mul_I ?_ ?_ (fun g φ => ?_) φ
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp only [Matrix.map_apply]
    rw [← basis_repr_smul_antiFund, ht]

/-- The determinant of an element of `SU(2)`, written out. -/
lemma det_fin_two_eq_one (g : SU 2) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  rw [← det_fin_two]
  exact (mem_specialUnitaryGroup_iff.mp g.2).2

/-- The antisymmetric symbol with two fundamental indices is invariant: `g ⊗ g` scales it by
  `det g = 1`. -/
lemma epsilonFund_invariant (g : SU 2) : g • epsilonFund = epsilonFund := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)
  rw [basis_repr_smul_fund]
  simp only [basis_repr_epsilonFund, sum_fin_two_arrow, Fin.sum_univ_two, Fin.prod_univ_two]
  have hdet := det_fin_two_eq_one g
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, φ = ![a, b] := ⟨φ 0, φ 1, by
    funext i
    fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : ℂ) * hdet

/-- The antisymmetric symbol with two anti-fundamental indices is invariant: `ḡ ⊗ ḡ` scales it
  by the conjugate of `det g = 1`. -/
lemma epsilonAntiFund_invariant (g : SU 2) : g • epsilonAntiFund = epsilonAntiFund := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)
  rw [basis_repr_smul_antiFund]
  simp only [basis_repr_epsilonAntiFund, sum_fin_two_arrow, Fin.sum_univ_two, Fin.prod_univ_two]
  have hdet := congrArg (starRingEnd ℂ) (det_fin_two_eq_one g)
  simp only [map_sub, map_mul, map_one] at hdet
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin 2, φ = ![a, b] := ⟨φ 0, φ 1, by
    funext i
    fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : ℂ) * hdet

/-!

## C. Two indices of `SU(N)` for `N ≥ 3`: no invariants

-/

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def rootOfUnity (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma rootOfUnity_isPrimitiveRoot (hN : N ≠ 0) : IsPrimitiveRoot (rootOfUnity N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma rootOfUnity_mul_star : rootOfUnity N * star (rootOfUnity N) = 1 := by
  have h : starRingEnd ℂ (2 * Real.pi * Complex.I / N) = -(2 * Real.pi * Complex.I / N) := by
    simp [map_div₀, Complex.conj_ofReal, Complex.conj_I, neg_div, map_ofNat]
  rw [rootOfUnity, Complex.star_def, ← Complex.exp_conj, h, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero]

/-- The centre element `ω 1` of `SU(N)`, for `ω` the primitive `N`-th root of unity. -/
noncomputable def centre (N : ℕ) (hN : N ≠ 0) : SU N :=
  ⟨rootOfUnity N • 1, by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul,
      Matrix.one_mul, rootOfUnity_mul_star, one_smul, det_smul, det_one, mul_one,
      Fintype.card_fin]
    exact ⟨rfl, (rootOfUnity_isPrimitiveRoot hN).pow_eq_one⟩⟩

/-- The centre element scales the components of a tensor with two fundamental indices by `ω²`. -/
lemma basis_repr_centre_smul_fund (hN : N ≠ 0) (t : (suTensor N).Tensor fun _ : Fin 2 => .fund)
    (φ : Fin 2 → Fin N) :
    (Tensor.basis _).repr (centre N hN • t) φ
      = rootOfUnity N ^ 2 * (Tensor.basis _).repr t φ := by
  rw [basis_repr_smul_fund, Finset.sum_eq_single φ]
  · simp [centre, pow_two]
  · intro ψ _ hψ
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (Ne.symm hψ)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [centre, hi]),
      zero_mul]
  · simp

/-- The centre element scales the components of a tensor with two anti-fundamental indices by
  `ω̄²`. -/
lemma basis_repr_centre_smul_antiFund (hN : N ≠ 0)
    (t : (suTensor N).Tensor fun _ : Fin 2 => .antiFund) (φ : Fin 2 → Fin N) :
    (Tensor.basis _).repr (centre N hN • t) φ
      = starRingEnd ℂ (rootOfUnity N) ^ 2 * (Tensor.basis _).repr t φ := by
  rw [basis_repr_smul_antiFund, Finset.sum_eq_single φ]
  · simp [centre, pow_two]
  · intro ψ _ hψ
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (Ne.symm hψ)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [centre, hi]),
      zero_mul]
  · simp

/-- For `N ≥ 3`, `ω² ≠ 1`. -/
lemma rootOfUnity_sq_ne_one (hN : 3 ≤ N) : rootOfUnity N ^ 2 ≠ 1 :=
  (rootOfUnity_isPrimitiveRoot (by omega)).pow_ne_one_of_pos_of_lt two_ne_zero (by omega)

/-- For `N ≥ 3` the only invariant tensor with two fundamental indices is zero: the centre
  element scales it by `ω² ≠ 1`. -/
lemma eq_zero_of_invariant_fundPair (hN : 3 ≤ N) (t : (suTensor N).Tensor fun _ : Fin 2 => .fund)
    (ht : ∀ g : SU N, g • t = t) : t = 0 := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)
  have h := basis_repr_centre_smul_fund (by omega) t φ
  rw [ht] at h
  rw [map_zero, Finsupp.zero_apply]
  have h' : (1 - rootOfUnity N ^ 2) * (Tensor.basis _).repr t φ = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 (rootOfUnity_sq_ne_one hN).symm)

/-- For `N ≥ 3` the only invariant tensor with two anti-fundamental indices is zero: the centre
  element scales it by `ω̄² ≠ 1`. -/
lemma eq_zero_of_invariant_antiFundPair (hN : 3 ≤ N)
    (t : (suTensor N).Tensor fun _ : Fin 2 => .antiFund) (ht : ∀ g : SU N, g • t = t) :
    t = 0 := by
  refine (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)
  have h := basis_repr_centre_smul_antiFund (by omega) t φ
  rw [ht] at h
  rw [map_zero, Finsupp.zero_apply]
  have hne : starRingEnd ℂ (rootOfUnity N) ^ 2 ≠ 1 := by
    rw [← map_pow, Ne, map_eq_one_iff _ (RingHom.injective _)]
    exact rootOfUnity_sq_ne_one hN
  have h' : (1 - starRingEnd ℂ (rootOfUnity N) ^ 2) * (Tensor.basis _).repr t φ = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hne.symm)

/-!

## D. Maps from components

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}

/-- The linear map out of the tensors with `n` fundamental indices sending the basis tensor with
  labels `l` to `T l`. -/
noncomputable def fundMap {n : ℕ} (T : (Fin n → Fin N) → B) :
    (suTensor N).Tensor (fun _ : Fin n => .fund) →ₗ[ℂ] B :=
  familyMap (Equiv.refl _) T

/-- The linear map out of the tensors with `n` anti-fundamental indices sending the basis tensor
  with labels `l` to `T l`. -/
noncomputable def antiFundMap {n : ℕ} (T : (Fin n → Fin N) → B) :
    (suTensor N).Tensor (fun _ : Fin n => .antiFund) →ₗ[ℂ] B :=
  familyMap (Equiv.refl _) T

@[simp]
lemma fundMap_basis {n : ℕ} (T : (Fin n → Fin N) → B) (l : Fin n → Fin N) :
    fundMap T (Tensor.basis (S := suTensor N) (fun _ : Fin n => Color.fund) l) = T l :=
  familyMap_basis (S := suTensor N) (c := fun _ : Fin n => Color.fund) (Equiv.refl _) T l

@[simp]
lemma antiFundMap_basis {n : ℕ} (T : (Fin n → Fin N) → B) (l : Fin n → Fin N) :
    antiFundMap T (Tensor.basis (S := suTensor N) (fun _ : Fin n => Color.antiFund) l) = T l :=
  familyMap_basis (S := suTensor N) (c := fun _ : Fin n => Color.antiFund) (Equiv.refl _) T l

/-- A linear map moving a family with `n` fundamental labels by one factor of `g` per label
  intertwines the map of the family with the action of `g`. -/
lemma fundMap_smul_of_law {n : ℕ} (T : (Fin n → Fin N) → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ l : Fin n → Fin N, σ (T l) = ∑ a : Fin n → Fin N, (∏ i, g.1 (a i) (l i)) • T a)
    (t : (suTensor N).Tensor fun _ : Fin n => .fund) :
    σ (fundMap T t) = fundMap T (g • t) :=
  familyMap_smul_of_law _ T g (fun l => (hσ l).trans <|
    Finset.sum_congr rfl fun a _ => congrArg (· • T a) <| Finset.prod_congr rfl fun i _ => by
      change _ = LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
        (fundRep N g) _ _
      rw [toMatrix_fundRep]
      rfl) t

/-- A linear map moving a family with `n` anti-fundamental labels by one factor of the complex
  conjugate of `g` per label intertwines the map of the family with the action of `g`. -/
lemma antiFundMap_smul_of_law {n : ℕ} (T : (Fin n → Fin N) → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ l : Fin n → Fin N, σ (T l)
      = ∑ a : Fin n → Fin N, (∏ i, starRingEnd ℂ (g.1 (a i) (l i))) • T a)
    (t : (suTensor N).Tensor fun _ : Fin n => .antiFund) :
    σ (antiFundMap T t) = antiFundMap T (g • t) :=
  familyMap_smul_of_law _ T g (fun l => (hσ l).trans <|
    Finset.sum_congr rfl fun a _ => congrArg (· • T a) <| Finset.prod_congr rfl fun i _ => by
      change _ = LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
        (antiFundRep N g) _ _
      rw [toMatrix_antiFundRep, val_inv]
      rfl) t

/-- The map of a family with `n` fundamental labels is equivariant when the family moves by one
  factor of `g` per label, the summed label first. -/
lemma isEquivariant_fundMap {n : ℕ} (T : (Fin n → Fin N) → B)
    (hT : ∀ (g : SU N) (l : Fin n → Fin N), ρ g (T l)
      = ∑ a : Fin n → Fin N, (∏ i, g.1 (a i) (l i)) • T a) :
    (suTensor N).IsEquivariant (fun _ => .fund) ρ (fundMap T) :=
  ⟨fun g t => (fundMap_smul_of_law T g (hT g) t).symm⟩

/-- The map of a family with `n` anti-fundamental labels is equivariant when the family moves by
  one factor of the complex conjugate of `g` per label, the summed label first. -/
lemma isEquivariant_antiFundMap {n : ℕ} (T : (Fin n → Fin N) → B)
    (hT : ∀ (g : SU N) (l : Fin n → Fin N), ρ g (T l)
      = ∑ a : Fin n → Fin N, (∏ i, starRingEnd ℂ (g.1 (a i) (l i))) • T a) :
    (suTensor N).IsEquivariant (fun _ => .antiFund) ρ (antiFundMap T) :=
  ⟨fun g t => (antiFundMap_smul_of_law T g (hT g) t).symm⟩

/-- The map of a family with two fundamental labels sends the antisymmetric symbol to the
  epsilon contraction. -/
lemma fundMap_epsilonFund (T : (Fin 2 → Fin 2) → B) :
    fundMap T epsilonFund = T ![0, 1] - T ![1, 0] := by
  simp [fundMap, epsilonFund, familyMap, sub_smul, Finset.sum_sub_distrib, Finsupp.single_apply]

/-- The map of a family with two anti-fundamental labels sends the antisymmetric symbol to the
  epsilon contraction. -/
lemma antiFundMap_epsilonAntiFund (T : (Fin 2 → Fin 2) → B) :
    antiFundMap T epsilonAntiFund = T ![0, 1] - T ![1, 0] := by
  simp [antiFundMap, epsilonAntiFund, familyMap, sub_smul, Finset.sum_sub_distrib,
    Finsupp.single_apply]

/-- For a family with two fundamental labels of `SU(2)` whose map is equivariant, the invariants
  of the span reduce to the span of the epsilon contraction `T ![0, 1] - T ![1, 0]`. -/
noncomputable def invariantReductionToEpsilonFund {ρ : Representation ℂ (SU 2) B}
    {T : (Fin 2 → Fin 2) → B} (hT : (suTensor 2).IsEquivariant (fun _ => .fund) ρ (fundMap T)) :
    InvariantReductionToSpan (fun g : SU 2 => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (isAdjointClosed 2 _) epsilonFund epsilonFund_invariant
    exists_eq_smul_epsilonFund_of_invariant (range_familyMap _ T) _ (fundMap_epsilonFund T)

/-- For a family with two anti-fundamental labels of `SU(2)` whose map is equivariant, the
  invariants of the span reduce to the span of the epsilon contraction
  `T ![0, 1] - T ![1, 0]`. -/
noncomputable def invariantReductionToEpsilonAntiFund {ρ : Representation ℂ (SU 2) B}
    {T : (Fin 2 → Fin 2) → B}
    (hT : (suTensor 2).IsEquivariant (fun _ => .antiFund) ρ (antiFundMap T)) :
    InvariantReductionToSpan (fun g : SU 2 => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (isAdjointClosed 2 _) epsilonAntiFund
    epsilonAntiFund_invariant exists_eq_smul_epsilonAntiFund_of_invariant
    (range_familyMap _ T) _ (antiFundMap_epsilonAntiFund T)

/-- For `N ≥ 3` and a family with two fundamental labels whose map is equivariant, the
  invariants of the span reduce to `⊥`. -/
lemma reducesInvariantsTo_bot_span_of_fundMap (hN : 3 ≤ N) {T : (Fin 2 → Fin N) → B}
    (hT : (suTensor N).IsEquivariant (fun _ => .fund) ρ (fundMap T)) :
    ReducesInvariantsTo (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) ⊥ := by
  rw [← range_familyMap (S := suTensor N) (c := fun _ : Fin 2 => Color.fund) (Equiv.refl _) T]
  exact hT.reducesInvariantsTo_bot (isAdjointClosed N _) (eq_zero_of_invariant_fundPair hN)

/-- For `N ≥ 3` and a family with two anti-fundamental labels whose map is equivariant, the
  invariants of the span reduce to `⊥`. -/
lemma reducesInvariantsTo_bot_span_of_antiFundMap (hN : 3 ≤ N) {T : (Fin 2 → Fin N) → B}
    (hT : (suTensor N).IsEquivariant (fun _ => .antiFund) ρ (antiFundMap T)) :
    ReducesInvariantsTo (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) ⊥ := by
  rw [← range_familyMap (S := suTensor N) (c := fun _ : Fin 2 => Color.antiFund)
    (Equiv.refl _) T]
  exact hT.reducesInvariantsTo_bot (isAdjointClosed N _) (eq_zero_of_invariant_antiFundPair hN)

end suTensor
