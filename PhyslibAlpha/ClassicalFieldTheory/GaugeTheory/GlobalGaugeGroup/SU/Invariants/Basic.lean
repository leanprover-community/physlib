/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.TensorSpecies
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import PhyslibAlpha.Mathematics.ForMathlib.DataStructures.Matrix.PlaneMatrix
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization.Conditions
/-!
# What commutes with the adjoint action of `SU(N)`, and the Reynolds element of its tensors

Schur's lemma for the adjoint representation, and the Haar average over the tensors.

## i. Overview

The elements `SU.planeEmbed p q U` of `SU(N)`, an element `U` of `SU(2)` acting on the plane of two
coordinates (`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Adjoint`), do all
the work. A diagonal phase `diag (u, ū)`, the rotation by a quarter turn, and the rotation by an
eighth of a turn, embedded in every plane, force a linear endomorphism of the complexified Lie
algebra `ℂ ⊗[ℝ] su(N)` commuting with the adjoint action to be scalar (A); this is computed on the
matrices `adjMat A`, which identify the complexified Lie algebra with the traceless complex
matrices. With Schur's lemma for the fundamental representation, `SU.eq_smul_one_of_commute`,
these are the facts behind the classification of the invariant tensors of `SU(N)` with a
fundamental and an anti-fundamental index, and with one or two adjoint indices.

The tensors of `SU(N)` have a Reynolds element, the Haar average over the compact group, so the
invariants in the range of an equivariant map out of them come from invariant tensors (B).

## ii. Key results

- `suTensor.eq_smul_id_of_commute_adjRep` : an endomorphism of the complexified Lie algebra
  commuting with the adjoint action is scalar.
- `suTensor.hasReynolds` : the tensors of `SU(N)` have a Reynolds element.

## iii. Table of contents

- A. Endomorphisms of the complexified Lie algebra commuting with `SU(N)`
- B. Reynolds elements for the tensors

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups

/-!

## A. Endomorphisms of the complexified Lie algebra commuting with `SU(N)`

-/

namespace suTensor

open SU TensorProduct

variable {N : ℕ}

/-- The matrix unit at `(x, y)` off the diagonal, as an element of the complexified Lie algebra,
  and zero on the diagonal. -/
noncomputable def offDiag (x y : Fin N) : SUAlgebraComplexified N :=
  ofTraceless (if x = y then 0 else single x y 1)

/-- The difference of the diagonal matrix units at `x` and at `y`, as an element of the
  complexified Lie algebra. -/
noncomputable def diagDiff (x y : Fin N) : SUAlgebraComplexified N :=
  ofTraceless (single x x 1 - single y y 1)

lemma adjMat_offDiag (x y : Fin N) :
    adjMat N (offDiag x y) = if x = y then 0 else single x y 1 := by
  refine adjMat_ofTraceless ?_
  split_ifs with h
  · exact trace_zero _ _
  · exact trace_single_eq_of_ne _ _ _ h

lemma adjMat_offDiag_of_ne {x y : Fin N} (h : x ≠ y) : adjMat N (offDiag x y) = single x y 1 := by
  simp [adjMat_offDiag, h]

@[simp]
lemma offDiag_self (x : Fin N) : offDiag x x = 0 :=
  adjMat_injective (by simp [adjMat_offDiag])

@[simp]
lemma adjMat_diagDiff (x y : Fin N) : adjMat N (diagDiff x y) = single x x 1 - single y y 1 :=
  adjMat_ofTraceless (by rw [trace_sub, trace_single_eq_same, trace_single_eq_same, sub_self])

@[simp]
lemma diagDiff_self (x : Fin N) : diagDiff x x = 0 :=
  adjMat_injective (by simp)

/-- The adjoint action of an element of `SU(2)` embedded in a plane of two coordinates on a
  matrix supported on that plane is the conjugation of the matrix on the plane. -/
lemma adjMat_adjRep_planeEmbed {p q : Fin N} (hpq : p ≠ q) (U : SU 2)
    (A : SUAlgebraComplexified N) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : adjMat N A = planeInclusion p q * M * (planeInclusion p q)ᵀ) :
    adjMat N (adjRep N (planeEmbed p q hpq U) A)
      = planeInclusion p q * (U.1 * M * U.1ᴴ) * (planeInclusion p q)ᵀ := by
  rw [adjMat_adjRep, val_inv, hA, planeEmbed_val, star_eq_conjTranspose,
    planeMatrix_conj hpq]

/-- The phase `(1 + i) / √2`, a square root of `i` of modulus one. -/
noncomputable def sqrtI : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)

lemma star_sqrtI : star sqrtI = (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
  simp [sqrtI, Complex.conj_ofReal, sub_eq_add_neg]

lemma sqrtI_mul_star : sqrtI * star sqrtI = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [star_sqrtI, sqrtI, div_mul_div_comm, h2, div_eq_one_iff_eq two_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma sqrtI_mul_self : sqrtI * sqrtI = Complex.I := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [sqrtI, div_mul_div_comm, h2, div_eq_iff two_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma star_sqrtI_mul_self : star sqrtI * star sqrtI = -Complex.I := by
  rw [← star_mul, sqrtI_mul_self, Complex.star_def, Complex.conj_I]

lemma sqrtI_ne_I : sqrtI ≠ Complex.I := fun h => by
  have h' := congrArg Complex.re h
  rw [sqrtI, Complex.div_ofReal_re] at h'
  simp only [Complex.add_re, Complex.one_re, Complex.I_re, add_zero] at h'
  exact (div_ne_zero one_ne_zero (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') h'

lemma star_sqrtI_ne_I : star sqrtI ≠ Complex.I := fun h => by
  have h' := congrArg Complex.re h
  rw [star_sqrtI, Complex.div_ofReal_re] at h'
  simp only [Complex.sub_re, Complex.one_re, Complex.I_re, sub_zero] at h'
  exact (div_ne_zero one_ne_zero (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') h'

/-- The adjoint action of a diagonal matrix of `SU(N)` scales the entry at `(x, y)` by
  `d x * star (d y)`. -/
lemma adjMat_adjRep_apply_of_diagonal {g : SU N} {d : Fin N → ℂ} (hg : g.1 = diagonal d)
    (A : SUAlgebraComplexified N) (x y : Fin N) :
    adjMat N (adjRep N g A) x y = d x * adjMat N A x y * star (d y) := by
  rw [adjMat_adjRep, val_inv, hg, star_eq_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

variable {L : SUAlgebraComplexified N →ₗ[ℂ] SUAlgebraComplexified N}

/-- For two distinct coordinates `p` and `q`, an endomorphism commuting with the adjoint action
  sends the matrix unit at `(p, q)` to a multiple of itself. The phase `diag (ω, ω̄)` in the
  plane of `p` and `q`, with `ω² = i`, multiplies that matrix unit by `i` and no other entry
  by `i`. -/
lemma map_offDiag_eq_smul (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
    L (adjRep N g A) = adjRep N g (L A)) {p q : Fin N} (hpq : p ≠ q) :
    L (offDiag p q) = adjMat N (L (offDiag p q)) p q • offDiag p q := by
  set d : Fin N → ℂ := fun x => if x = p then sqrtI else if x = q then star sqrtI else 1
  set g := planeEmbed p q hpq (diagPhase sqrtI sqrtI_mul_star)
  have hg : g.1 = diagonal d := by
    rw [planeEmbed_val, diagPhase_val, planeMatrix_diagonal hpq]
  have h1 : sqrtI * (starRingEnd ℂ) sqrtI = 1 := sqrtI_mul_star
  have h2 : (starRingEnd ℂ) sqrtI * sqrtI = 1 := by rw [mul_comm]; exact sqrtI_mul_star
  have h3 : (starRingEnd ℂ) sqrtI * (starRingEnd ℂ) sqrtI = -Complex.I := star_sqrtI_mul_self
  have h4 : (starRingEnd ℂ) sqrtI ≠ Complex.I := star_sqrtI_ne_I
  have h5 : (1 : ℂ) ≠ Complex.I := fun h => by simp [Complex.ext_iff] at h
  have h6 : -Complex.I ≠ Complex.I := fun h => by
    have := congrArg Complex.im h
    norm_num at this
  have hmul : ∀ x y, d x * star (d y) = Complex.I ↔ x = p ∧ y = q := fun x y => by
    by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hyp : y = p <;>
      by_cases hyq : y = q <;>
      simp_all [d, Ne.symm hpq, sqrtI_mul_self, sqrtI_ne_I]
  have hY : adjRep N g (L (offDiag p q)) = Complex.I • L (offDiag p q) := by
    rw [← hL, ← map_smul]
    congr 1
    refine adjMat_injective (Matrix.ext fun x y => ?_)
    rw [adjMat_adjRep_apply_of_diagonal hg, map_smul, Matrix.smul_apply,
      adjMat_offDiag_of_ne hpq, single_apply, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [mul_one, mul_one]
      exact (hmul _ _).2 ⟨rfl, rfl⟩
    · simp
  refine adjMat_injective (Matrix.ext fun x y => ?_)
  rw [map_smul, Matrix.smul_apply, adjMat_offDiag_of_ne hpq, single_apply, smul_eq_mul]
  have hxy := congrArg (fun A => adjMat N A x y) hY
  simp only [adjMat_adjRep_apply_of_diagonal hg, map_smul, Matrix.smul_apply,
    smul_eq_mul] at hxy
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [mul_one]
  · have hne : d x * star (d y) ≠ Complex.I := fun he =>
      h ⟨((hmul x y).1 he).1.symm, ((hmul x y).1 he).2.symm⟩
    rw [mul_zero]
    have h' : (d x * star (d y) - Complex.I) * adjMat N (L (offDiag p q)) x y = 0 := by
      linear_combination hxy
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hne)

/-- The quarter turn in the plane of `p` and `q` sends the matrix unit at `(p, q)` to minus the
  one at `(q, p)`. -/
lemma adjRep_quarterTurn_offDiag {p q : Fin N} (hpq : p ≠ q) :
    adjRep N (planeEmbed p q hpq (rotation 0 1 (by norm_num))) (offDiag p q) = -offDiag q p := by
  refine adjMat_injective ?_
  rw [adjMat_adjRep_planeEmbed hpq _ _ (single 0 1 1)
    (by rw [adjMat_offDiag_of_ne hpq, planeInclusion_single]; rfl)]
  rw [show (rotation 0 1 (by norm_num)).1 * single 0 1 1 * (rotation 0 1 (by norm_num)).1ᴴ
      = -single 1 0 (1 : ℂ) by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, single_apply, Matrix.vecMul, dotProduct]]
  rw [Matrix.mul_neg, Matrix.neg_mul, planeInclusion_single, map_neg,
    adjMat_offDiag_of_ne (Ne.symm hpq)]
  rfl

/-- The coefficients of the matrix units at `(p, q)` and at `(q, p)` agree. -/
lemma coeff_offDiag_swap (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
    L (adjRep N g A) = adjRep N g (L A)) {p q : Fin N} (hpq : p ≠ q) :
    adjMat N (L (offDiag q p)) q p = adjMat N (L (offDiag p q)) p q := by
  have h := hL (planeEmbed p q hpq (rotation 0 1 (by norm_num))) (offDiag p q)
  rw [adjRep_quarterTurn_offDiag, map_neg, map_offDiag_eq_smul hL (Ne.symm hpq),
    map_offDiag_eq_smul hL hpq, map_smul, adjRep_quarterTurn_offDiag] at h
  have h' := congrArg (fun A => adjMat N A q p) h
  simpa [adjMat_offDiag_of_ne (Ne.symm hpq)] using h'

/-- The cosine and sine of an eighth of a turn, the real number `1 / √2`. -/
noncomputable def invSqrtTwo : ℝ := (Real.sqrt 2)⁻¹

lemma invSqrtTwo_sq_add : invSqrtTwo ^ 2 + invSqrtTwo ^ 2 = 1 := by
  rw [invSqrtTwo, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma invSqrtTwo_mul_self : (invSqrtTwo : ℂ) * invSqrtTwo = 1 / 2 := by
  have h := invSqrtTwo_sq_add
  have h' : (invSqrtTwo : ℂ) ^ 2 + (invSqrtTwo : ℂ) ^ 2 = 1 := by exact_mod_cast h
  linear_combination h' / 2

/-- The eighth turn in the plane of `p` and `q` sends the sum of the matrix units at `(p, q)`
  and at `(q, p)` to minus the difference of the diagonal matrix units at `p` and at `q`. -/
lemma adjRep_eighthTurn_offDiag {p q : Fin N} (hpq : p ≠ q) :
    adjRep N (planeEmbed p q hpq (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add))
      (offDiag p q + offDiag q p) = -diagDiff p q := by
  refine adjMat_injective ?_
  rw [adjMat_adjRep_planeEmbed hpq _ _ (single 0 1 1 + single 1 0 1)
    (by rw [map_add, adjMat_offDiag_of_ne hpq, adjMat_offDiag_of_ne (Ne.symm hpq),
      Matrix.mul_add, Matrix.add_mul, planeInclusion_single, planeInclusion_single]; rfl)]
  rw [show (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add).1 * (single 0 1 1 + single 1 0 1)
      * (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add).1ᴴ
      = -(single 0 0 (1 : ℂ) - single 1 1 1) by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, single_apply, Matrix.vecMul, dotProduct] <;>
      first
        | linear_combination (2 : ℂ) * invSqrtTwo_mul_self
        | linear_combination (-2 : ℂ) * invSqrtTwo_mul_self]
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, planeInclusion_single,
    planeInclusion_single, map_neg, adjMat_diagDiff]
  rfl

/-- For two distinct coordinates `p` and `q`, an endomorphism commuting with the adjoint action
  scales the difference of the diagonal matrix units at `p` and at `q` by the coefficient of the
  matrix unit at `(p, q)`. -/
lemma map_diagDiff_eq_smul (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
    L (adjRep N g A) = adjRep N g (L A)) {p q : Fin N} (hpq : p ≠ q) :
    L (diagDiff p q) = adjMat N (L (offDiag p q)) p q • diagDiff p q := by
  have h := hL (planeEmbed p q hpq (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add))
    (offDiag p q + offDiag q p)
  rw [adjRep_eighthTurn_offDiag, map_neg, map_add, map_offDiag_eq_smul hL (Ne.symm hpq),
    map_offDiag_eq_smul hL hpq, coeff_offDiag_swap hL hpq, ← smul_add, map_smul,
    adjRep_eighthTurn_offDiag, smul_neg] at h
  exact neg_injective h

/-- For three distinct coordinates `p`, `q` and `r`, the coefficients of the matrix units at
  `(p, q)` and at `(p, r)` agree. The difference of the diagonal units at `p` and `r` is the sum
  of those at `p` and `q` and at `q` and `r`. -/
lemma coeff_offDiag_eq (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
    L (adjRep N g A) = adjRep N g (L A)) {p q r : Fin N} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) : adjMat N (L (offDiag p r)) p r = adjMat N (L (offDiag p q)) p q := by
  have hsum : diagDiff p r = diagDiff p q + diagDiff q r :=
    adjMat_injective (by simp)
  have h := congrArg L hsum
  rw [map_add, map_diagDiff_eq_smul hL hpr, map_diagDiff_eq_smul hL hpq,
    map_diagDiff_eq_smul hL hqr] at h
  have h' := congrArg (fun A => adjMat N A p p) h
  simpa [single_apply, hpq, hpr, Ne.symm hpq, Ne.symm hpr] using h'

/-- All the matrix units off the diagonal have the same coefficient under an endomorphism
  commuting with the adjoint action. -/
lemma exists_coeff_offDiag_eq (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
    L (adjRep N g A) = adjRep N g (L A)) :
    ∃ μ : ℂ, ∀ x y : Fin N, x ≠ y → adjMat N (L (offDiag x y)) x y = μ := by
  by_cases hN : 2 ≤ N
  · set a : Fin N := ⟨0, by omega⟩
    set b : Fin N := ⟨1, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have ha : ∀ y, a ≠ y → adjMat N (L (offDiag a y)) a y = adjMat N (L (offDiag a b)) a b :=
      fun y hy => by
        by_cases hyb : y = b
        · rw [hyb]
        · exact coeff_offDiag_eq hL hab hy (Ne.symm hyb)
    refine ⟨adjMat N (L (offDiag a b)) a b, fun x y hxy => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      exact ha y hxy
    · by_cases hya : y = a
      · subst hya
        rw [coeff_offDiag_swap hL (Ne.symm hxy)]
        exact ha x (Ne.symm hxa)
      · rw [coeff_offDiag_eq hL hxa hxy (Ne.symm hya), coeff_offDiag_swap hL (Ne.symm hxa)]
        exact ha x (Ne.symm hxa)
  · refine ⟨0, fun x y hxy => absurd ?_ hxy⟩
    ext
    omega

/-- An element of the complexified Lie algebra is the combination of the entries of its matrix off
  the diagonal against the matrix units, and of its diagonal entries against the differences of
  the diagonal matrix units at a fixed coordinate. -/
lemma eq_sum_offDiag_add_sum_diagDiff (A : SUAlgebraComplexified N) (x₀ : Fin N) :
    A = ∑ x, ∑ y, adjMat N A x y • offDiag x y + ∑ x, adjMat N A x x • diagDiff x x₀ := by
  have htr : ∑ x, adjMat N A x x = 0 := trace_adjMat A
  refine adjMat_injective (Matrix.ext fun i j => ?_)
  have hoff : ∀ x y, adjMat N (offDiag x y) i j = if x = i ∧ y = j ∧ i ≠ j then 1 else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [adjMat_offDiag, ite_true, Matrix.zero_apply]
      split_ifs with h
      · exact absurd (h.1.symm.trans h.2.1) h.2.2
      · rfl
    · rw [adjMat_offDiag_of_ne hxy, single_apply]
      by_cases h : x = i ∧ y = j
      · obtain ⟨rfl, rfl⟩ := h
        simp [hxy]
      · rw [ite_eq_right_iff.mpr fun h' => absurd h' h,
          ite_eq_right_iff.mpr fun h' => absurd ⟨h'.1, h'.2.1⟩ h]
  simp only [map_add, map_sum, map_smul, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, adjMat_diagDiff, Matrix.sub_apply, hoff,
    single_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  by_cases hij : i = j
  · subst hij
    have hx₀ : (∑ x, if x₀ = i then adjMat N A x x else 0) = 0 := by
      split_ifs <;> simp [htr]
    simp only [ne_eq, not_true_eq_false, and_false, ite_false, Finset.sum_const_zero, and_self,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hx₀, sub_zero, zero_add]
  · have h2 : ∀ x : Fin N, ¬(x = i ∧ x = j) := fun x h => hij (h.1.symm.trans h.2)
    simp only [h2, ite_false, Finset.sum_const_zero, sub_zero, add_zero]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single j (fun y _ hy => by simp [hy]) (by simp)]
    simp [hij]

/-- An endomorphism of the complexified Lie algebra commuting with the adjoint action of every
  element of `SU(N)` is scalar, a form of Schur's lemma for the adjoint representation. -/
lemma eq_smul_id_of_commute_adjRep (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
    L (adjRep N g A) = adjRep N g (L A)) :
    ∃ z : ℂ, L = z • LinearMap.id := by
  obtain ⟨μ, hμ⟩ := exists_coeff_offDiag_eq hL
  refine ⟨μ, LinearMap.ext fun A => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (SUAlgebraComplexified 0) :=
      ⟨fun A B => adjMat_injective (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  have hoff : ∀ x y, L (offDiag x y) = μ • offDiag x y := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [map_offDiag_eq_smul hL hxy, hμ x y hxy]
  have hdiag : ∀ x y, L (diagDiff x y) = μ • diagDiff x y := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [map_diagDiff_eq_smul hL hxy, hμ x y hxy]
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  conv_lhs => rw [eq_sum_offDiag_add_sum_diagDiff A ⟨0, hN⟩]
  conv_rhs => rw [eq_sum_offDiag_add_sum_diagDiff A ⟨0, hN⟩]
  simp only [map_add, map_sum, map_smul, hoff, hdiag, smul_add, Finset.smul_sum, smul_comm μ]

/-!

## B. Reynolds elements for the tensors

`SU(N)` is identified with the global gauge group `GlobalGaugeGroup.SU N`, a compact topological
group, by `GlobalGaugeGroup.SU.groupEquiv`. On it the matrix entries of every color are continuous,
being those of `g`, of `g⁻¹ = g†` and the traces `tr (λ_a g λ_b g⁻¹) / 2` of the adjoint action, so
the Haar average gives a Reynolds element, which is pushed forward to `SU(N)`.

-/

/-- The matrix entries of every color depend continuously on the element of the global gauge group
  `SU(N)`. -/
lemma continuous_toMatrix_rep (k : Color) (x y : basisIdx N k) :
    Continuous fun h : (GlobalGaugeGroup.SU N).group => LinearMap.toMatrix (basis N k)
      (basis N k) (rep N k ((GlobalGaugeGroup.SU.groupEquiv N).symm h)) x y := by
  have hg : Continuous fun h : (GlobalGaugeGroup.SU N).group =>
      (((GlobalGaugeGroup.SU.groupEquiv N).symm h : SU N) : Matrix (Fin N) (Fin N) ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun h : (GlobalGaugeGroup.SU N).group =>
      ((((GlobalGaugeGroup.SU.groupEquiv N).symm h)⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
    simp_rw [← map_inv]
    exact hg.comp continuous_inv
  cases k
  · change Continuous fun h => LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
      (fundRep N ((GlobalGaugeGroup.SU.groupEquiv N).symm h)) x y
    simp_rw [toMatrix_fundRep]
    exact hg.matrix_elem x y
  · change Continuous fun h => LinearMap.toMatrix (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))
      (antiFundRep N ((GlobalGaugeGroup.SU.groupEquiv N).symm h)) x y
    simp_rw [toMatrix_antiFundRep, transpose_apply]
    exact hi.matrix_elem y x
  · change Continuous fun h => adjMatrix ((GlobalGaugeGroup.SU.groupEquiv N).symm h) x y
    simp_rw [adjMatrix_apply]
    exact ((continuous_const.matrix_mul ((hg.matrix_mul continuous_const).matrix_mul
      hi)).matrix_trace).div_const 2

variable (N) in
/-- The tensors of `SU(N)` with any list of colors have a Reynolds element, the Haar average over
  the compact group `SU(N)`. -/
lemma hasReynolds {n : ℕ} (c : Fin n → Color) : (suTensor N).HasReynolds c := by
  have := Module.Finite.of_basis (TensorSpecies.Tensor.basis (S := suTensor N) c)
  exact TensorSpecies.HasReynolds.of_comp
    (φ := (GlobalGaugeGroup.SU.groupEquiv N).symm.toMonoidHom)
    (GlobalGaugeGroup.SU.groupEquiv N).symm.surjective
    (Representation.exists_isReynolds_of_compactSpace ⊤
      (TensorSpecies.continuousMatrixCoeff_top_comp _ continuous_toMatrix_rep))

end suTensor
