/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinatewise conjugation in an orthonormal basis

There is no canonical conjugation on an abstract inner product space, so this file attaches one to
an orthonormal basis `e` by conjugating the coordinates in it:
`conjugation e x = ∑ i, conj ⟪e i, x⟫ • e i`. It is a conjugate-linear isometric involution of `V`
(`TauCeti.conjugation_conjugation`, `TauCeti.inner_conjugation_conjugation`), and conjugating an
operator by it, `A ↦ J ∘ A ∘ J` (`TauCeti.conjCLM`), is the coordinate-free description of
conjugating the matrix of `A` entrywise.

## Main definitions

* `TauCeti.conjugation`: the conjugate-linear isometric involution attached to an orthonormal basis.
* `TauCeti.conjCLM`: conjugation of a continuous linear operator, `A ↦ J ∘ A ∘ J`.

## Main statements

* `TauCeti.conjugation_conjugation` and `TauCeti.inner_conjugation_conjugation`: conjugation is an
  involution, and reverses the inner product.
* `TauCeti.conjugation_basis`: the basis it is attached to is fixed vector by vector, which is what
  makes it *the* conjugation of that basis.
* `TauCeti.inner_conjugation_left_basis`: pairing a conjugate against a basis vector swaps the two
  arguments of the inner product.
* `TauCeti.conjCLM_one`, `TauCeti.conjCLM_mul` and `TauCeti.conjCLM_conjCLM`: conjugation of
  operators is a multiplicative involution fixing the identity.
* `TauCeti.conjCLM_add` and `TauCeti.conjCLM_smul`: it is additive and conjugate-linear, so with
  the two preceding it is a conjugate-linear ring involution of the operators.
* `TauCeti.norm_conjCLM`: conjugation of operators preserves the operator norm.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

section Conjugation

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Coordinatewise conjugation in an orthonormal basis.** A conjugate-linear isometric involution
of `V`, which on coordinates is `x i ↦ conj (x i)`. -/
noncomputable def conjugation (e : OrthonormalBasis ι 𝕜 V) (x : V) : V :=
  ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i

variable (e : OrthonormalBasis ι 𝕜 V)

/-- Conjugation, expanded as the coordinate sum defining it. -/
theorem conjugation_apply (x : V) :
    conjugation e x = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i :=
  (rfl)

/-- The coordinates of a conjugate are the conjugated coordinates. -/
@[simp]
theorem inner_conjugation (x : V) (j : ι) :
    ⟪e j, conjugation e x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 := by
  classical
  have h : ∀ i, ⟪e j, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i⟫_𝕜 =
      if i = j then (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 else 0 := fun i ↦ by
    rw [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [conjugation_apply, inner_sum]
  simp only [h]
  simp

/-- Conjugation fixes the zero vector. -/
@[simp]
theorem conjugation_zero : conjugation e (0 : V) = 0 := by
  simp [conjugation_apply]

/-- Conjugation is additive. -/
@[simp]
theorem conjugation_add (x y : V) :
    conjugation e (x + y) = conjugation e x + conjugation e y := by
  simp [conjugation_apply, inner_add_right, add_smul, Finset.sum_add_distrib]

/-- Conjugation is conjugate-linear: a scalar comes out conjugated. -/
@[simp]
theorem conjugation_smul (c : 𝕜) (x : V) :
    conjugation e (c • x) = (starRingEnd 𝕜) c • conjugation e x := by
  simp [conjugation_apply, inner_smul_right, Finset.smul_sum, smul_smul]

/-- Conjugation commutes with negation. -/
@[simp]
theorem conjugation_neg (x : V) : conjugation e (-x) = -conjugation e x := by
  simp [conjugation_apply, inner_neg_right, neg_smul, Finset.sum_neg_distrib]

/-- Conjugation commutes with subtraction. -/
@[simp]
theorem conjugation_sub (x y : V) :
    conjugation e (x - y) = conjugation e x - conjugation e y := by
  simp [conjugation_apply, inner_sub_right, sub_smul, Finset.sum_sub_distrib]

/-- Conjugation is an involution. -/
@[simp]
theorem conjugation_conjugation (x : V) : conjugation e (conjugation e x) = x := by
  have h : ∀ i, (starRingEnd 𝕜) ⟪e i, conjugation e x⟫_𝕜 = ⟪e i, x⟫_𝕜 := fun i ↦ by
    rw [inner_conjugation]; simp
  rw [conjugation_apply (x := conjugation e x)]
  simp only [h]
  exact e.sum_repr' x

/-- **Conjugation fixes the basis it is attached to.** Coordinatewise conjugation is the identity
on the vectors whose coordinates are `0` and `1`. -/
@[simp]
theorem conjugation_basis (j : ι) : conjugation e (e j) = e j := by
  classical
  have h : ∀ i, (starRingEnd 𝕜) ⟪e i, e j⟫_𝕜 = ⟪e i, e j⟫_𝕜 := fun i ↦ by
    rw [orthonormal_iff_ite.mp e.orthonormal]
    split <;> simp
  rw [conjugation_apply]
  simp only [h]
  exact e.sum_repr' (e j)

/-- Conjugation reverses the inner product: it is conjugate-linear and isometric. -/
@[simp]
theorem inner_conjugation_conjugation (x y : V) :
    ⟪conjugation e x, conjugation e y⟫_𝕜 = (starRingEnd 𝕜) ⟪x, y⟫_𝕜 := by
  have hxy : ⟪x, y⟫_𝕜 = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 * ⟪e i, y⟫_𝕜 := by
    conv_lhs => rw [← e.sum_repr' x]
    rw [sum_inner]
    simp [inner_smul_left]
  rw [conjugation_apply e x, sum_inner, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, inner_conjugation]
  simp [mul_comm]

/-- **Pairing a conjugate against a basis vector swaps the arguments.** Conjugation fixes `e j`, so
the reversal of the inner product turns `⟪J x, e j⟫` into `⟪e j, x⟫`. This is the form in which the
conjugation is contracted against a coordinate. -/
@[simp]
theorem inner_conjugation_left_basis (x : V) (j : ι) :
    ⟪conjugation e x, e j⟫_𝕜 = ⟪e j, x⟫_𝕜 := by
  conv_lhs => rw [← conjugation_basis e j]
  rw [inner_conjugation_conjugation, inner_conj_symm]

/-- Conjugation is isometric, as the reversal of the inner product shows on the diagonal. -/
@[simp]
theorem norm_conjugation (x : V) : ‖conjugation e x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) (conjugation e x), norm_eq_sqrt_re_inner (𝕜 := 𝕜) x,
    inner_conjugation_conjugation]
  simp

end Conjugation

section ConjugateOperator

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- **Conjugation of a continuous linear operator**, `A ↦ J ∘ A ∘ J` for `J` the conjugation of `e`.
The two conjugate-linearities of `J` cancel, so the result is `𝕜`-linear, and it is bounded because
`J` is isometric. -/
noncomputable def conjCLM (A : V →L[𝕜] V) : V →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun x := conjugation e (A (conjugation e x))
      map_add' x y := by simp
      map_smul' c x := by simp } ‖A‖ fun x ↦ by
    simpa using A.le_opNorm (conjugation e x)

/-- Evaluation of a conjugated operator. -/
@[simp]
theorem conjCLM_apply (A : V →L[𝕜] V) (x : V) :
    conjCLM e A x = conjugation e (A (conjugation e x)) :=
  (rfl)

/-- Conjugation fixes the identity, because `J` is an involution. -/
@[simp]
theorem conjCLM_one : conjCLM e 1 = 1 := by
  ext x
  simp

/-- Conjugation is multiplicative, again because `J` is an involution: the two inner copies of `J`
cancel. -/
@[simp]
theorem conjCLM_mul (A B : V →L[𝕜] V) : conjCLM e (A * B) = conjCLM e A * conjCLM e B := by
  ext x
  simp

/-- Conjugation of operators is an involution, because `J` is. -/
@[simp]
theorem conjCLM_conjCLM (A : V →L[𝕜] V) : conjCLM e (conjCLM e A) = A := by
  ext x
  simp

/-- Conjugation kills the zero operator. -/
@[simp]
theorem conjCLM_zero : conjCLM e (0 : V →L[𝕜] V) = 0 := by
  ext x
  simp

/-- Conjugation of operators is additive. -/
@[simp]
theorem conjCLM_add (A B : V →L[𝕜] V) : conjCLM e (A + B) = conjCLM e A + conjCLM e B := by
  ext x
  simp

/-- Conjugation of operators commutes with negation. -/
@[simp]
theorem conjCLM_neg (A : V →L[𝕜] V) : conjCLM e (-A) = -conjCLM e A := by
  ext x
  simp

/-- Conjugation commutes with subtraction of operators. -/
@[simp]
theorem conjCLM_sub (A B : V →L[𝕜] V) : conjCLM e (A - B) = conjCLM e A - conjCLM e B := by
  ext x
  simp

/-- Conjugation of operators is conjugate-linear: a scalar of the operator passes through the
outer `J` only, so it comes out conjugated. -/
@[simp]
theorem conjCLM_smul (c : 𝕜) (A : V →L[𝕜] V) : conjCLM e (c • A) = star c • conjCLM e A := by
  ext x
  simp [RCLike.star_def]

/-- Conjugation does not increase the operator norm. -/
theorem norm_conjCLM_le (A : V →L[𝕜] V) : ‖conjCLM e A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Conjugation preserves the operator norm: it does not increase it, and it is an involution. -/
@[simp]
theorem norm_conjCLM (A : V →L[𝕜] V) : ‖conjCLM e A‖ = ‖A‖ :=
  le_antisymm (norm_conjCLM_le e A) <| by
    simpa using norm_conjCLM_le e (conjCLM e A)

/-- Conjugation of operators is a contraction, hence continuous. -/
theorem lipschitzWith_one_conjCLM : LipschitzWith 1 (conjCLM e) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← conjCLM_sub, norm_conjCLM]
    simp

end ConjugateOperator

end TauCeti
