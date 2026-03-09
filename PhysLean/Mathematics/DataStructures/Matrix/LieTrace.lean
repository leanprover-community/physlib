/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import PhysLean.Mathematics.SchurTriangulation

/-!
# Lie's Trace Formula

This file proves the formula `det (exp A) = exp (tr A)` for matrices, also known as Lie's trace
formula.

The proof proceeds by first showing the formula for upper-triangular matrices and then
leveraging Schur triangulation to generalize to any matrix. An upper-triangular matrix `A`
is defined in `mathlib` as `Matrix.BlockTriangular A id`.

## Main results

- `Matrix.det_exp`: The determinant of the exponential of a matrix is the exponential of its trace.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators Topology

variable {𝕂 m n : Type*}

instance [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance

/-- If every term of a series is zero, then its sum is zero. -/
lemma tsum_eq_zero
    {β : Type*} [TopologicalSpace β] [AddCommMonoid β]
    {f : ℕ → β} (h : ∀ n, f n = 0) :
    (∑' n, f n) = 0 := by
  simp_all only [tsum_zero]

/-!
  ### The determinant of the matrix exponential
-/
section DetExp

variable [RCLike 𝕂]

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

/-- Apply a matrix `tsum` to a given entry. -/
lemma matrix_tsum_apply
    {f : ℕ → Matrix m m 𝕂} (hf : Summable f) (i j : m) :
    (∑' n, f n) i j = ∑' n, (f n) i j := by
  have h_row_summable : Summable (fun n ↦ (f n) i) := by
    have h := Pi.summable.1 hf
    exact h i
  have h₁ : ((∑' n, f n) : Matrix m m 𝕂) i = (∑' n, (f n) i) := by
    exact tsum_apply hf
  have h₂ : ((∑' n, (f n) i) : m → 𝕂) j = (∑' n, (f n) i j) := by
    exact tsum_apply h_row_summable
  rw [h₁, h₂]

variable [Fintype m] [LinearOrder m]

/-- For upper-triangular matrices, the diagonal of a product is the product of the diagonals.
This is a specific case of a more general property for block-triangular matrices. -/
lemma diag_mul_of_blockTriangular_id {A B : Matrix m m 𝕂}
    (hA : BlockTriangular A id) (hB : BlockTriangular B id) : (A * B).diag = A.diag * B.diag := by
  ext i
  simp only [diag_apply, mul_apply, Pi.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ j_ne_i
    cases lt_or_gt_of_ne j_ne_i with
    | inl h => rw [hA h, zero_mul] -- j < i
    | inr h => rw [hB h, mul_zero] -- i < j
  · intro; simp_all only [Finset.mem_univ, not_true_eq_false]

/-- Powers of block triangular matrices are block triangular. -/
lemma blockTriangular.pow {A : Matrix m m 𝕂} (hA : BlockTriangular A id) (k : ℕ) :
    BlockTriangular (A ^ k) id := by
  induction k with
  | zero => rw [pow_zero]; exact blockTriangular_one
  | succ k ihk => rw [pow_succ]; exact ihk.mul hA

/-- For an upper-triangular matrix, the diagonal of a power is the power of the diagonal. -/
lemma diag_pow_of_blockTriangular_id {A : Matrix m m 𝕂}
    (hA : BlockTriangular A id) (k : ℕ) : (A ^ k).diag = A.diag ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; simp [diag_one]
  | succ k ih =>
    have h_pow_k : BlockTriangular (A ^ k) id := blockTriangular.pow hA k
    rw [pow_succ, pow_succ, diag_mul_of_blockTriangular_id h_pow_k hA, ih]

/-- The exponential of an upper-triangular matrix is upper-triangular. -/
lemma blockTriangular_exp_of_blockTriangular_id
    {A : Matrix m m 𝕂} (hA : BlockTriangular A id) :
    (NormedSpace.exp A).BlockTriangular id := by
  intro i j hij
  rw [NormedSpace.exp_eq_tsum 𝕂]
  let exp_series := fun n => ((n.factorial : 𝕂)⁻¹) • (A ^ n)
  change (∑' n, exp_series n) i j = 0
  rw [matrix_tsum_apply (NormedSpace.expSeries_summable' A) i j]
  apply tsum_eq_zero
  intro n
  have h_pow : BlockTriangular (A ^ n) id := by
    induction n with
    | zero => rw [pow_zero]; exact blockTriangular_one
    | succ k ihk => rw [pow_succ]; exact ihk.mul hA
  simp only [smul_apply]
  rw [h_pow hij, smul_zero]

/--
For an upper–triangular matrix `A`, the `(i,i)` entry of the power `A ^ n`
is simply the `n`-th power of the original diagonal entry.
-/
lemma diag_pow_entry_eq_pow_diag_entry {A : Matrix m m 𝕂}
    (hA : BlockTriangular A id) (n : ℕ) (i : m) :
    (A ^ n) i i = (A i i) ^ n := by
  have h := diag_pow_of_blockTriangular_id hA n
  simpa [diag_apply, Pi.pow_apply] using congr_arg (fun d => d i) h

/-- Each term in the matrix exponential series equals the corresponding scalar term on the
diagonal -/
lemma exp_series_diag_term_eq {A : Matrix m m 𝕂} (hA : BlockTriangular A id)
    (n : ℕ) (i : m) :
    ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i = (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  simp [smul_apply, diag_pow_entry_eq_pow_diag_entry hA]

/-- The diagonal of the matrix exponential series equals the scalar exponential series -/
lemma matrix_exp_series_diag_eq_scalar_series {A : Matrix m m 𝕂} (hA : BlockTriangular A id)
    (i : m) :
    (∑' n, ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i) = ∑' n, (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  exact tsum_congr (exp_series_diag_term_eq hA · i)

/-- The diagonal of the exponential of an upper-triangular matrix `A` consists of the
exponentials of the diagonal entries of `A`. -/
theorem diag_exp_of_blockTriangular_id
    {A : Matrix m m 𝕂} (hA : BlockTriangular A id) :
    (NormedSpace.exp A).diag = fun i => NormedSpace.exp (A i i) := by
  funext i
  rw [NormedSpace.exp_eq_tsum 𝕂, diag_apply]
  simp_rw [matrix_tsum_apply (NormedSpace.expSeries_summable' A) i i]
  rw [matrix_exp_series_diag_eq_scalar_series hA i]
  rw [NormedSpace.exp_eq_tsum 𝕂]

/-- Lie's trace formula for upper triangular matrices. -/
lemma det_exp_of_blockTriangular_id {A : Matrix m m 𝕂} (hA : BlockTriangular A id) :
    (NormedSpace.exp A).det = NormedSpace.exp A.trace := by
  have h_exp_upper : BlockTriangular (NormedSpace.exp A) id :=
    blockTriangular_exp_of_blockTriangular_id hA
  rw [det_of_upperTriangular h_exp_upper]
  have h_diag_exp : (NormedSpace.exp A).diag = fun i => NormedSpace.exp (A i i) :=
    diag_exp_of_blockTriangular_id hA
  simp_rw [← diag_apply]
  simp_rw [h_diag_exp]
  erw [← NormedSpace.exp_sum Finset.univ]
  congr 1

/-- The trace is invariant under unitary conjugation. -/
lemma trace_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    trace ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = trace A := by
  have h_unitary : star (U : Matrix m m 𝕂) * (U : Matrix m m 𝕂) = 1 :=
    UnitaryGroup.star_mul_self U
  simpa [Matrix.mul_assoc, h_unitary, Matrix.one_mul] using
    (Matrix.trace_mul_cycle (U : Matrix m m 𝕂) A (star (U : Matrix m m 𝕂)))

/-- The determinant is invariant under unitary conjugation. -/
lemma det_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    det ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = det A := by
  rw [det_mul_right_comm]
  simp_all only [SetLike.coe_mem, Unitary.mul_star_self_of_mem, one_mul]

/-- The exponential of a matrix commutes with unitary conjugation. -/
lemma exp_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    NormedSpace.exp ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) =
      (U : Matrix m m 𝕂) * NormedSpace.exp A * star (U : Matrix m m 𝕂) := by
  let Uu : (Matrix m m 𝕂)ˣ :=
    { val := (U : Matrix m m 𝕂)
      inv := star (U : Matrix m m 𝕂)
      val_inv := by simp
      inv_val := by simp}
  have h_units := Matrix.exp_units_conj Uu A
  simpa [Uu] using h_units

lemma det_exp_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    (NormedSpace.exp ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂))).det =
    (NormedSpace.exp A).det := by
  rw [exp_unitary_conj, det_unitary_conj]

/-- The determinant of the exponential of a matrix is the exponential of its trace.
This is also known as **Lie's trace formula**. -/
theorem det_exp {𝕂 m : Type*} [RCLike 𝕂] [IsAlgClosed 𝕂] [Fintype m] [LinearOrder m]
    (A : Matrix m m 𝕂) :
    (NormedSpace.exp A).det = NormedSpace.exp A.trace := by
  let U := A.schurTriangulationUnitary
  let T := A.schurTriangulation
  have h_prop : T.val.IsUpperTriangular := T.property
  have h_conj : A = U * T * star U := schur_triangulation A
  have h_trace_invariant : A.trace = T.val.trace := by
    erw [h_conj, trace_unitary_conj]
  have h_det_invariant : (NormedSpace.exp A).det = (NormedSpace.exp T.val).det := by
    erw [h_conj, det_exp_unitary_conj]
  have h_triangular_case : (NormedSpace.exp T.val).det = NormedSpace.exp T.val.trace :=
    det_exp_of_blockTriangular_id h_prop
  rw [h_det_invariant, h_triangular_case, h_trace_invariant]

end DetExp

-- `Matrix.map` commutes with an absolutely convergent series.
lemma map_tsum {α β m n : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β]
    (f : α →+ β) (hf : Continuous f) {s : ℕ → Matrix m n α} (hs : Summable s) :
    (∑' k, s k).map f = ∑' k, (s k).map f := by
  let F : Matrix m n α →+ Matrix m n β := AddMonoidHom.mapMatrix f
  have hF : Continuous F := Continuous.matrix_map continuous_id hf
  exact (hs.hasSum.map F hF).tsum_eq.symm

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

end Matrix

namespace NormedSpace

lemma exp_map_algebraMap {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (exp A).map (algebraMap ℝ ℂ) = exp (A.map (algebraMap ℝ ℂ)) := by
  letI : SeminormedRing (Matrix n n ℝ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix n n ℝ) := inferInstance
  letI : SeminormedRing (Matrix n n ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix n n ℂ) := inferInstance
  simp only [exp_eq_tsum ℝ]
  have hs : Summable (fun k => (k.factorial : ℝ)⁻¹ • A ^ k) := by
    exact NormedSpace.expSeries_summable' A
  erw [Matrix.map_tsum (algebraMap ℝ ℂ).toAddMonoidHom RCLike.continuous_ofReal hs]
  apply tsum_congr
  intro k
  erw [Matrix.map_smul, Matrix.map_pow]
  simp

end NormedSpace

section DetExp
namespace Matrix
/--
Lie's trace formula over ℝ: det(exp(A)) = exp(tr(A)) for any real matrix A.
This is proved by transferring the result from ℂ using the naturality of polynomial identities.
-/
theorem det_exp_real {n : Type*} [Fintype n] [LinearOrder n]
    (A : Matrix n n ℝ) : (NormedSpace.exp A).det = Real.exp A.trace := by
  let A_ℂ := A.map (algebraMap ℝ ℂ)
  have h_complex : (NormedSpace.exp A_ℂ).det = Complex.exp A_ℂ.trace := by
    haveI : IsAlgClosed ℂ := Complex.isAlgClosed
    rw [Complex.exp_eq_exp_ℂ, ← Matrix.det_exp]
  have h_trace_comm : A_ℂ.trace = (algebraMap ℝ ℂ) A.trace := by
    simp only [A_ℂ, trace, diag_map, map_sum];rfl
  have h_det_comm : (algebraMap ℝ ℂ) ((NormedSpace.exp A).det) = (NormedSpace.exp A_ℂ).det := by
    rw [@RingHom.map_det]
    rw [← NormedSpace.exp_map_algebraMap]; rfl
  rw [← h_det_comm] at h_complex
  rw [h_trace_comm] at h_complex
  have h_exp_comm : Complex.exp ((algebraMap ℝ ℂ) A.trace) =
      (algebraMap ℝ ℂ) (Real.exp A.trace) := by
    erw [← Complex.ofReal_exp]
    simp_all only [Complex.coe_algebraMap, Algebra.algebraMap_self, RingHom.id_apply,
      Complex.ofReal_exp, A_ℂ]
  rw [h_exp_comm] at h_complex
  exact Complex.ofReal_injective h_complex

end Matrix
