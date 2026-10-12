/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Adjoint
/-!

# Schur's lemma for the adjoint representation of `SU(n)`

Every endomorphism commuting with the complex adjoint representation of `SU(n)` is a scalar.

## i. Overview

We show that an endomorphism `T` of the complexification of `su(n)` commuting with the adjoint
action of `SU(n)` is a multiple of the identity (A). Working with the underlying matrices:

- the adjoint action of a diagonal element of `SU(n)`, with phases powers of a primitive fifth root
  of unity, separates the entry `(p, q)` from all others, so `T` acts by a scalar on the elements
  `c E_pq` supported at an off-diagonal entry (A.1);
- the adjoint action of a permutation matrix shows this scalar is the same for all off-diagonal
  entries, so `T` acts by a single scalar `μ` on the elements with zero diagonal (A.2);
- a rotation in the `(p, q)`-plane conjugates `E_pp - E_qq` to `E_pq + E_qp`, so `T` acts by `μ`
  on `E_pp - E_qq`, and hence on all of the complexification (A.3).

As a consequence, every `SU(n)`-invariant bilinear form on the complexification is a multiple of
the contraction `adjointℂContr` (B).

## ii. Key results

- `SULieAlgebra.end_eq_smul_id_of_commute_adjointℂ` : Schur's lemma for the complex adjoint
  representation.
- `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr` : every intertwiner `adj ⊗ adj → ℂ` is a
  multiple of the complex contraction.

## iii. Table of contents

- A. Schur's lemma
  - A.1. Elements supported at an off-diagonal entry
  - A.2. Elements with zero diagonal
  - A.3. All elements
- B. Invariant bilinear forms

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct

namespace SULieAlgebra

/-!

## A. Schur's lemma

### A.1. Elements supported at an off-diagonal entry

An endomorphism commuting with the adjoint action preserves the line spanned by `E_pq` for
`p ≠ q`, so acts on it by a scalar `μ_pq`.

-/

/-- An endomorphism commuting with the adjoint action keeps an element supported at an
  off-diagonal entry `(p, q)` supported there. -/
lemma toMatrixℂ_end_eq_single_of_toMatrixℂ_eq_single {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {p q : Fin n} (hpq : p ≠ q)
    {A : Complexification n} {c : ℂ} (hA : toMatrixℂ A = single p q c) :
    toMatrixℂ (T A) = single p q (toMatrixℂ (T A) p q) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hinv : ζ⁻¹ = starRingEnd ℂ ζ := Complex.inv_eq_conj (hζ.norm'_eq_one (by norm_num))
  -- the diagonal element of `SU(n)` with phase `ζ` at `p`, `ζ⁻¹` at `q` and `1` elsewhere
  set e : Fin n → ℤ := fun x => if x = p then 1 else if x = q then -1 else 0 with he
  have hphase (x y : Fin n) : ζ ^ e x * star (ζ ^ e y) = ζ ^ (e x - e y) := by
    simp [← hinv, zpow_sub₀ hζ0, div_eq_mul_inv]
  have hmem : diagonal (fun x => ζ ^ e x) ∈ specialUnitaryGroup (Fin n) ℂ := by
    refine mem_specialUnitaryGroup_iff.2 ⟨?_, ?_⟩
    · simp [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, ← hinv,
        zpow_ne_zero _ hζ0]
    · simp [he, apply_ite (ζ ^ · : ℤ → ℂ), Finset.prod_ite, Finset.filter_eq', hζ0, hpq.symm]
  -- `T A` is an eigenvector of its adjoint action, with the eigenvalue of the entry `(p, q)`
  have hTA : adjointℂ ⟨_, hmem⟩ (T A) = ζ ^ (e p - e q) • T A := by
    rw [← LinearMap.comp_apply (adjointℂ _), ← hT, LinearMap.comp_apply,
      adjointℂ_eq_smul_of_toMatrixℂ_apply_eq_zero rfl
        fun x y h => hA ▸ single_apply_of_ne (c := _) (h := mt (And.imp Eq.symm Eq.symm) h),
      map_smul, hphase]
  refine Matrix.ext fun x y => ?_
  by_cases h : x = p ∧ y = q
  · obtain ⟨rfl, rfl⟩ := h
    exact (single_apply_same ..).symm
  refine (toMatrixℂ_apply_eq_zero_of_adjointℂ_eq_smul rfl hTA ?_).trans
    (single_apply_of_ne (c := _) (h := mt (And.imp Eq.symm Eq.symm) h)).symm
  rw [hphase, Ne, ← div_eq_one_iff_eq (zpow_ne_zero _ hζ0), ← zpow_sub₀ hζ0,
    hζ.zpow_eq_one_iff_dvd]
  simp only [he]
  split_ifs <;> omega

/-- An endomorphism commuting with the adjoint action acts by a scalar on the elements supported
  at an off-diagonal entry `(p, q)`. -/
lemma exists_end_eq_smul_of_toMatrixℂ_eq_single {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {p q : Fin n} (hpq : p ≠ q) :
    ∃ μ : ℂ, ∀ (A : Complexification n) (c : ℂ), toMatrixℂ A = single p q c → T A = μ • A := by
  set E := ofTracelessℂ (single p q 1) (trace_single_eq_of_ne _ _ _ hpq) with hE
  have hsmul (B : Complexification n) (c : ℂ) (hB : toMatrixℂ B = single p q c) : B = c • E :=
    toMatrixℂ_injective (by simp [hB, hE])
  obtain ⟨μ, hμ⟩ : ∃ μ, T E = μ • E :=
    ⟨_, hsmul _ _ (toMatrixℂ_end_eq_single_of_toMatrixℂ_eq_single hT hpq
      (toMatrixℂ_ofTracelessℂ _ _))⟩
  exact ⟨μ, fun A c hA => by rw [hsmul A c hA, map_smul, hμ, smul_comm]⟩

/-!

### A.2. Elements with zero diagonal

The scalars `μ_pq` are all equal to a single `μ`, so the endomorphism acts by `μ` on every
element with zero diagonal.

-/

/-- If an endomorphism commuting with the adjoint action acts by `μ` on the elements supported
  at `(i, j)`, it acts by `μ` on the elements supported at `(σ i, σ j)` for any permutation `σ`. -/
lemma end_eq_smul_of_toMatrixℂ_eq_single_perm {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {i j : Fin n} {μ : ℂ}
    (hμ : ∀ (A : Complexification n) (c : ℂ), toMatrixℂ A = single i j c → T A = μ • A)
    (σ : Equiv.Perm (Fin n)) (A : Complexification n) (c : ℂ)
    (hA : toMatrixℂ A = single (σ i) (σ j) c) : T A = μ • A := by
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_apply_perm σ
  rw [← Representation.self_inv_apply adjointℂ g A, ← LinearMap.comp_apply T, hT,
    LinearMap.comp_apply, hμ _ c (Matrix.ext fun x y => ?_), map_smul]
  rw [← hg, Representation.self_inv_apply, hA]
  simp only [single_apply, Equiv.apply_eq_iff_eq]

/-- An endomorphism commuting with the adjoint action acts by a single scalar on the elements
  supported at any off-diagonal entry. -/
lemma exists_end_eq_smul_of_toMatrixℂ_eq_single_of_ne {n : ℕ}
    {T : Module.End ℂ (Complexification n)} (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) :
    ∃ μ : ℂ, ∀ p q : Fin n, p ≠ q →
      ∀ (A : Complexification n) (c : ℂ), toMatrixℂ A = single p q c → T A = μ • A := by
  rcases subsingleton_or_nontrivial (Fin n) with hn | hn
  · exact ⟨0, fun p q hpq => (hpq (Subsingleton.elim p q)).elim⟩
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  obtain ⟨μ, hμ⟩ := exists_end_eq_smul_of_toMatrixℂ_eq_single hT hij
  refine ⟨μ, fun p q hpq => ?_⟩
  -- move `(i, j)` to `(p, q)` by two transpositions
  have h₁ := end_eq_smul_of_toMatrixℂ_eq_single_perm hT hμ (Equiv.swap i p)
  rw [Equiv.swap_apply_left] at h₁
  have h₂ := end_eq_smul_of_toMatrixℂ_eq_single_perm hT h₁ (Equiv.swap (Equiv.swap i p j) q)
  rwa [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
    (fun h => hij ((Equiv.swap i p).injective ((Equiv.swap_apply_left i p).trans h))) hpq] at h₂

/-- An endomorphism commuting with the adjoint action acts by a scalar on the elements with zero
  diagonal. -/
lemma exists_end_eq_smul_of_toMatrixℂ_diag_eq_zero {n : ℕ}
    {T : Module.End ℂ (Complexification n)} (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) :
    ∃ μ : ℂ, ∀ A : Complexification n, (toMatrixℂ A).diag = 0 → T A = μ • A := by
  obtain ⟨μ, hμ⟩ := exists_end_eq_smul_of_toMatrixℂ_eq_single_of_ne hT
  refine ⟨μ, fun A hA => ?_⟩
  have hd : ∀ p, toMatrixℂ A p p = 0 := congr_fun hA
  -- an element with zero diagonal is the sum of its off-diagonal entries
  have htr (p q : Fin n) : (single p q (toMatrixℂ A p q)).trace = 0 := by
    rcases eq_or_ne p q with rfl | h <;> simp [*]
  rw [show A = ∑ p, ∑ q, ofTracelessℂ _ (htr p q) from
    toMatrixℂ_injective (by simp [← matrix_eq_sum_single])]
  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain rfl | h := eq_or_ne p q
  · rw [show ofTracelessℂ _ (htr p p) = 0 from toMatrixℂ_injective (by simp [hd]), map_zero,
      smul_zero]
  · exact hμ p q h _ _ (toMatrixℂ_ofTracelessℂ _ _)

/-!

### A.3. All elements

The endomorphism also acts by `μ` on the diagonal elements `E_pp - E_qq`, and hence on every
element: it is `μ` times the identity.

-/

/-- An endomorphism commuting with the adjoint action, acting by `μ` on the elements with zero
  diagonal, also acts by `μ` on the element `E_pp - E_qq`. -/
lemma end_eq_smul_of_toMatrixℂ_eq_single_sub_single {n : ℕ}
    {T : Module.End ℂ (Complexification n)} (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {μ : ℂ}
    (hμ : ∀ A : Complexification n, (toMatrixℂ A).diag = 0 → T A = μ • A) {p q : Fin n}
    {A : Complexification n} (hA : toMatrixℂ A = single p p 1 - single q q 1) : T A = μ • A := by
  obtain rfl | hpq := eq_or_ne p q
  · rw [show A = 0 from toMatrixℂ_injective (by simp [hA]), map_zero, smul_zero]
  -- the rotation by `π / 4` in the `(p, q)`-plane, conjugating `E_pp - E_qq` to `E_pq + E_qp`
  set s : ℂ := (((√2)⁻¹ : ℝ) : ℂ)
  have hs : s ^ 2 = 1 / 2 := by simp [s, ← Complex.ofReal_pow]
  set U : Matrix (Fin n) (Fin n) ℂ := 1 - single p p 1 - single q q 1 +
    s • (single p p 1 + single p q 1 + single q p 1 - single q q 1) with hU
  have hUs : star U = U := by
    simp [hU, s, star_eq_conjTranspose]
    module
  have hUU : U * U = 1 ∧ U * (single p p 1 - single q q 1) * U = single p q 1 + single q p 1 := by
    constructor <;>
    simp only [hU, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.zero_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hpq,
      single_mul_single_of_ne _ _ _ _ (Ne.symm hpq), mul_one] <;>
    match_scalars <;> first | ring1 | linear_combination 2 * hs
  obtain ⟨g, hg⟩ := exists_toMatrixℂ_adjointℂ_eq_unitary
    ⟨U, mem_unitaryGroup_iff.2 (by rw [hUs, hUU.1])⟩
  have hgA : (toMatrixℂ (adjointℂ g A)).diag = 0 := by
    rw [hg]
    change (U * toMatrixℂ A * star U).diag = 0
    rw [hA, hUs, hUU.2, diag_add, diag_single_of_ne _ _ _ hpq, diag_single_of_ne _ _ _ hpq.symm,
      add_zero]
  rw [← Representation.inv_self_apply adjointℂ g A, ← LinearMap.comp_apply T, hT,
    LinearMap.comp_apply, hμ _ hgA, map_smul, Representation.inv_self_apply]

/-- An endomorphism of the complexification commuting with the adjoint action is a scalar: the
  complex adjoint representation satisfies Schur's lemma. -/
lemma end_eq_smul_id_of_commute_adjointℂ {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  obtain ⟨μ, hμ⟩ := exists_end_eq_smul_of_toMatrixℂ_diag_eq_zero hT
  refine ⟨μ, LinearMap.ext fun A => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  obtain hn | ⟨⟨i⟩⟩ := isEmpty_or_nonempty (Fin n)
  · exact toMatrixℂ_injective (Subsingleton.elim _ _)
  -- `A` is an element with zero diagonal plus a combination of the elements `E_pp - E_ii`
  have htr (p : Fin n) : (single p p (1 : ℂ) - single i i 1).trace = 0 := by simp
  have hdiag : (toMatrixℂ (A - ∑ p, toMatrixℂ A p p • ofTracelessℂ _ (htr p))).diag = 0 := by
    have h0 : ∑ p, toMatrixℂ A p p = 0 := trace_toMatrixℂ A
    funext x
    simp [Matrix.sum_apply, single_apply, mul_sub, Finset.sum_sub_distrib, h0]
  rw [← sub_add_cancel A (∑ p, toMatrixℂ A p p • ofTracelessℂ _ (htr p)), map_add, hμ _ hdiag,
    map_sum, smul_add, Finset.smul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
  rw [map_smul, end_eq_smul_of_toMatrixℂ_eq_single_sub_single hT hμ (toMatrixℂ_ofTracelessℂ _ _),
    smul_comm]

/-!

## B. Invariant bilinear forms

-/

/-- Every bilinear form on the complexification is the contraction against an endomorphism,
  the contraction being nondegenerate. -/
lemma exists_eq_adjointℂContr_tmul {n : ℕ}
    (B : Complexification n ⊗[ℂ] Complexification n →ₗ[ℂ] ℂ) :
    ∃ T : Module.End ℂ (Complexification n), ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C) :=
  ⟨(LinearMap.BilinForm.toDual _ adjointℂContr_nondegenerate).symm.toLinearMap ∘ₗ curry B,
    fun A C => (LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := adjointℂContr_nondegenerate) (curry B A) C).symm⟩

/-- The endomorphism representing an invariant bilinear form commutes with the adjoint
  action. -/
lemma adjointℂ_comp_eq_of_adjointℂContr_tmul {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ))
    {T : Module.End ℂ (Complexification n)} (hT : ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C))
    (g : specialUnitaryGroup (Fin n) ℂ) :
    T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T := by
  have hB (A C : Complexification n) : B (adjointℂ g A ⊗ₜ adjointℂ g C) = B (A ⊗ₜ C) := by
    simpa only [Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply] using Representation.IntertwiningMap.isIntertwining _ _ B g
        (A ⊗ₜ C)
  refine LinearMap.ext fun A => sub_eq_zero.1 (adjointℂContr_separating_left _ fun C => ?_)
  rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
    ← Representation.self_inv_apply adjointℂ g C, hB, hT, adjointℂContr_adjointℂ]

/-- Every intertwiner `adj ⊗ adj → ℂ` is a multiple of the contraction: up to scale, the
  contraction is the unique `SU(n)`-invariant bilinear form on the complexification. -/
lemma intertwiningMap_eq_smul_adjointℂContr {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ)) :
    ∃ z : ℂ, B = z • adjointℂContr := by
  obtain ⟨T, hT⟩ := exists_eq_adjointℂContr_tmul B.toLinearMap
  obtain ⟨μ, hμ⟩ :=
    end_eq_smul_id_of_commute_adjointℂ (adjointℂ_comp_eq_of_adjointℂContr_tmul B hT)
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun A C => ?_)⟩
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]
  rfl

end SULieAlgebra
