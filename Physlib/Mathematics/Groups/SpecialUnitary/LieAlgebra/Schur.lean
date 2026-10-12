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

- the adjoint action of a diagonal element of `SU(n)` with phases given by a primitive fifth root of
  unity separates the entry `(p, q)` from all others, so `T` acts by a scalar on the elements
  supported at an off-diagonal entry (A.1);
- the adjoint action of a permutation matrix shows this scalar is the same for all off-diagonal
  entries, so `T` acts by a single scalar on the elements with zero diagonal (A.2);
- the adjoint action of a unitary rotating `E_pp - E_qq` to `E_pq + E_qp` extends this to the
  diagonal elements, and hence to all of the complexification (A.3).

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

-/

/-- An endomorphism commuting with the adjoint action keeps an element supported at an
  off-diagonal entry `(p, q)` supported there. -/
lemma toMatrixℂ_apply_eq_zero_of_comp_eq {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {p q : Fin n} (hpq : p ≠ q)
    {A : Complexification n} (hA : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ A x y = 0)
    (x y : Fin n) (hxy : ¬(x = p ∧ y = q)) : toMatrixℂ (T A) x y = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  set e : Fin n → ℤ := fun x => if x = p then 1 else if x = q then -1 else 0 with he
  have hphase (x y : Fin n) : ζ ^ e x * star (ζ ^ e y) = ζ ^ (e x - e y) := by
    rw [star_zpow₀, Complex.star_def, ← Complex.inv_eq_conj (hζ.norm'_eq_one (by norm_num)),
      _root_.inv_zpow, ← _root_.zpow_neg, ← zpow_add₀ hζ0, sub_eq_add_neg]
  have hkey : ζ ^ (e x - e y) ≠ ζ ^ (e p - e q) := by
    rw [Ne, ← div_eq_one_iff_eq (zpow_ne_zero _ hζ0), ← zpow_sub₀ hζ0, hζ.zpow_eq_one_iff_dvd]
    simp only [he]
    split_ifs <;> omega
  have hmem : diagonal (fun x => ζ ^ e x) ∈ specialUnitaryGroup (Fin n) ℂ := by
    rw [mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext x
      rw [Pi.star_apply, hphase, sub_self, zpow_zero]
    · rw [det_diagonal,
        Finset.prod_congr rfl fun x _ => (show ζ ^ e x = (if x = p then ζ else 1) *
          (if x = q then ζ⁻¹ else 1) by simp only [he]; split_ifs <;> simp_all),
        Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq',
        ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), mul_inv_cancel₀ hζ0]
  have hTA : adjointℂ ⟨_, hmem⟩ (T A) = ζ ^ (e p - e q) • T A := by
    rw [← LinearMap.comp_apply (adjointℂ _), ← hT, LinearMap.comp_apply,
      adjointℂ_eq_smul_of_toMatrixℂ_apply_eq_zero rfl hA, map_smul, hphase]
  exact toMatrixℂ_apply_eq_zero_of_adjointℂ_eq_smul rfl hTA (by rwa [hphase])

/-- An endomorphism commuting with the adjoint action acts by a scalar on the elements supported
  at an off-diagonal entry `(p, q)`. -/
lemma end_eq_smul_of_toMatrixℂ_apply_eq_zero {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {p q : Fin n} (hpq : p ≠ q) :
    ∃ μ : ℂ, ∀ A : Complexification n, (∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ A x y = 0) →
      T A = μ • A := by
  obtain ⟨E, hE⟩ : ∃ E : Complexification n, toMatrixℂ E = single p q 1 :=
    ⟨_, toMatrixℂ_ofTracelessℂ _ (trace_single_eq_of_ne _ _ _ hpq)⟩
  have hsupp (B : Complexification n) (hB : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ B x y = 0) :
      B = toMatrixℂ B p q • E := by
    refine toMatrixℂ_injective (Matrix.ext fun x y => ?_)
    rw [map_smul, hE, Matrix.smul_apply, single_apply]
    by_cases h : x = p ∧ y = q
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [hB x y h, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.symm⟩, smul_zero]
  have hEs (x y : Fin n) (h : ¬(x = p ∧ y = q)) : toMatrixℂ E x y = 0 := by
    rw [hE, single_apply, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.symm⟩]
  have hTE := hsupp (T E) (toMatrixℂ_apply_eq_zero_of_comp_eq hT hpq hEs)
  refine ⟨toMatrixℂ (T E) p q, fun A hA => ?_⟩
  rw [hsupp A hA, map_smul, smul_comm, ← hTE]

/-!

### A.2. Elements with zero diagonal

-/

/-- An endomorphism commuting with the adjoint action acts by a scalar on the elements with zero
  diagonal. -/
lemma end_eq_smul_of_toMatrixℂ_diag_eq_zero {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) :
    ∃ μ : ℂ, ∀ A : Complexification n, (toMatrixℂ A).diag = 0 → T A = μ • A := by
  rcases lt_or_ge n 2 with hn | hn
  · -- with at most one coordinate, a matrix with zero diagonal vanishes
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
    refine ⟨0, fun A hA => ?_⟩
    rw [show A = 0 from toMatrixℂ_injective (Matrix.ext fun x y => by
      rw [Subsingleton.elim x y, map_zero]; exact congr_fun hA y), map_zero, smul_zero]
  -- the scalar `μ` at an off-diagonal entry `(i, j)` is moved to any `(p, q)` by a permutation
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨μ, hμ⟩ := end_eq_smul_of_toMatrixℂ_apply_eq_zero hT hij
  have hμ' (p q : Fin n) (hpq : p ≠ q) (B : Complexification n)
      (hB : ∀ x y, ¬(x = p ∧ y = q) → toMatrixℂ B x y = 0) : T B = μ • B := by
    have hr := (Equiv.swap i p).injective.ne hij
    rw [Equiv.swap_apply_left] at hr
    obtain ⟨g, hg⟩ :=
      exists_toMatrixℂ_adjointℂ_apply_perm (Equiv.swap (Equiv.swap i p j) q * Equiv.swap i p)
    have hsupp (x y : Fin n) (h : ¬(x = i ∧ y = j)) :
        toMatrixℂ (adjointℂ g⁻¹ B) x y = 0 := by
      rw [← hg, Representation.self_inv_apply]
      refine hB _ _ fun h' => h ⟨(Equiv.injective _) (h'.1.trans ?_),
        (Equiv.injective _) (h'.2.trans ?_)⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hr hpq]
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [← Representation.self_inv_apply adjointℂ g B, ← LinearMap.comp_apply T, hT,
      LinearMap.comp_apply, hμ _ hsupp, map_smul]
  -- an element with zero diagonal is a sum of elements supported at off-diagonal entries
  refine ⟨μ, fun A hA => ?_⟩
  have htr (p q : Fin n) : (single p q (toMatrixℂ A p q)).trace = 0 := by
    by_cases h : p = q
    · rw [h, show toMatrixℂ A q q = 0 from congr_fun hA q, single_zero, trace_zero]
    · exact trace_single_eq_of_ne _ _ _ h
  have hsum : A = ∑ p, ∑ q, ofTracelessℂ _ (htr p q) := toMatrixℂ_injective (by
    simp only [map_sum, toMatrixℂ_ofTracelessℂ]
    exact matrix_eq_sum_single _)
  rw [hsum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : p = q
  · subst h
    rw [show ofTracelessℂ _ (htr p p) = 0 from toMatrixℂ_injective (by
      rw [toMatrixℂ_ofTracelessℂ, map_zero, show toMatrixℂ A p p = 0 from congr_fun hA p,
        single_zero]), map_zero, smul_zero]
  · exact hμ' p q h _ fun x y hxy => by
      rw [toMatrixℂ_ofTracelessℂ, single_apply, ite_eq_right fun h' => hxy ⟨h'.1.symm, h'.2.symm⟩]

/-!

### A.3. All elements

-/

/-- An endomorphism commuting with the adjoint action, acting by `μ` on the elements with zero
  diagonal, also acts by `μ` on the element `E_pp - E_qq`. -/
lemma end_eq_smul_of_toMatrixℂ_eq_single_sub_single {n : ℕ}
    {T : Module.End ℂ (Complexification n)} (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) {μ : ℂ}
    (hμ : ∀ A : Complexification n, (toMatrixℂ A).diag = 0 → T A = μ • A) {p q : Fin n}
    {A : Complexification n} (hA : toMatrixℂ A = single p p 1 - single q q 1) : T A = μ • A := by
  by_cases hpq : p = q
  · subst hpq
    rw [show A = 0 from toMatrixℂ_injective (by rw [hA, sub_self, map_zero]), map_zero, smul_zero]
  set s : ℂ := (((√2)⁻¹ : ℝ) : ℂ)
  have hs : s ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt zero_le_two]
    push_cast
    ring
  set U : Matrix (Fin n) (Fin n) ℂ := 1 - single p p 1 - single q q 1 +
    s • (single p p 1 + single p q 1 + single q p 1 - single q q 1) with hU
  have hUs : star U = U := by
    simp only [hU, star_eq_conjTranspose, conjTranspose_add, conjTranspose_sub,
      conjTranspose_smul, conjTranspose_one, conjTranspose_single, star_one, s,
      Complex.star_def, Complex.conj_ofReal]
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
    rw [hA, hUs, hUU.2]
    funext x
    simp only [diag_apply, Matrix.add_apply, single_apply, Pi.zero_apply]
    split_ifs <;> simp_all
  rw [← Representation.inv_self_apply adjointℂ g A, ← LinearMap.comp_apply T, hT,
    LinearMap.comp_apply, hμ _ hgA, map_smul, Representation.inv_self_apply]

/-- An endomorphism of the complexification commuting with the adjoint action is a scalar: the
  complex adjoint representation satisfies Schur's lemma. -/
lemma end_eq_smul_id_of_commute_adjointℂ {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  obtain ⟨μ, hμ⟩ := end_eq_smul_of_toMatrixℂ_diag_eq_zero hT
  refine ⟨μ, LinearMap.ext fun A => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact toMatrixℂ_injective (Matrix.ext fun x => x.elim0)
  -- `A` is an element with zero diagonal plus a combination of the elements `E_pp - E_ii`
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htr (p : Fin n) : (single p p (1 : ℂ) - single i i 1).trace = 0 := by
    rw [trace_sub, trace_single_eq_same, trace_single_eq_same, sub_self]
  have hdiag : (toMatrixℂ (A - ∑ p, toMatrixℂ A p p • ofTracelessℂ _ (htr p))).diag = 0 := by
    funext x
    simp only [map_sub, map_sum, map_smul, toMatrixℂ_ofTracelessℂ, diag_apply, Matrix.sub_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    rw [show ∑ p, toMatrixℂ A p p = (toMatrixℂ A).trace from rfl, trace_toMatrixℂ]
    simp [single_apply]
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
