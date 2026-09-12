/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.LogExp
public import QuantumInfo.ForMathlib.HermitianMat.Trace

/-! # Block-diagonal Hermitian matrices

A Hermitian matrix on `d × ι` that is *block diagonal* with respect to the second factor can be
written as `∑ i, X i ⊗ₖ basisProj 𝕜 i`, where `basisProj 𝕜 i` is the rank-one projector onto the
`i`-th standard basis vector of `ι`. Such a matrix behaves blockwise under all of the operations
we care about: its continuous functional calculus (and hence its logarithm) is applied to each
block separately, its kernel is the product of the blockwise kernels, and inner products of two
such matrices decompose as the sum of the blockwise inner products.
-/

@[expose] public section

noncomputable section

open scoped Kronecker Matrix RealInnerProductSpace

namespace HermitianMat

variable {d ι 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

variable (𝕜) in
/-- The rank-one projector onto the `i`-th standard basis vector. -/
def basisProj (i : ι) : HermitianMat ι 𝕜 :=
  diagonal 𝕜 (fun j ↦ if j = i then 1 else 0)

variable (𝕜) in
private def P (i : ι) : Matrix ι ι 𝕜 :=
  Matrix.diagonal (fun j ↦ if j = i then 1 else 0)

omit [Fintype ι] in
private theorem basisProj_mat_P (i : ι) : (basisProj 𝕜 i).mat = P 𝕜 i := by
  simp only [basisProj, diagonal_mat, P]
  congr 1
  funext j
  split_ifs <;> simp

omit [Fintype ι] in
@[simp]
theorem basisProj_mat (i : ι) :
    (basisProj 𝕜 i).mat = Matrix.diagonal (fun j ↦ if j = i then (1 : 𝕜) else 0) :=
  basisProj_mat_P i

private theorem P_mul_P (i j : ι) : P 𝕜 i * P 𝕜 j = if i = j then P 𝕜 i else 0 := by
  by_cases h : i = j
  · subst h
    simp only [P, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk]
  · simp only [P, Matrix.diagonal_mul_diagonal, if_neg h, ← Matrix.diagonal_zero]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk, h]

omit [Fintype ι] in
private theorem P_conjTranspose (i : ι) : (P 𝕜 i)ᴴ = P 𝕜 i := by
  simp only [P, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

omit [DecidableEq d] in
private theorem block_mul (A B : ι → Matrix d d 𝕜) :
    (∑ i, A i ⊗ₖ P 𝕜 i) * (∑ j, B j ⊗ₖ P 𝕜 j) = ∑ i, (A i * B i) ⊗ₖ P 𝕜 i := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [← Matrix.mul_kronecker_mul, P_mul_P, if_pos rfl]
  · intro j _ hj
    rw [← Matrix.mul_kronecker_mul, P_mul_P, if_neg (Ne.symm hj)]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [DecidableEq d] [Fintype d] in
private theorem block_conjTranspose (A : ι → Matrix d d 𝕜) :
    (∑ i, A i ⊗ₖ P 𝕜 i)ᴴ = ∑ i, (A i)ᴴ ⊗ₖ P 𝕜 i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Matrix.kroneckerMap_conjTranspose, P_conjTranspose]

omit [Fintype d] in
private theorem sum_one_kron_P : ∑ i : ι, (1 : Matrix d d 𝕜) ⊗ₖ P 𝕜 i = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.sum_apply]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, P, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hab : a = b <;> by_cases hij : i = j <;> simp [hab, hij]

private theorem block_unitary (U : ι → Matrix.unitaryGroup d 𝕜) :
    (∑ i, (U i).val ⊗ₖ P 𝕜 i) ∈ Matrix.unitaryGroup (d × ι) 𝕜 := by
  have h1 : ∀ i, (U i).val * ((U i).val)ᴴ = 1 := fun i ↦ by
    have := Matrix.mem_unitaryGroup_iff.mp (U i).2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, block_conjTranspose, block_mul]
  simp only [h1]
  exact sum_one_kron_P

omit [Fintype d] in
private theorem diagonal_block (E : ι → d → ℝ) :
    (diagonal 𝕜 (fun x : d × ι ↦ E x.2 x.1)).mat = ∑ i, (diagonal 𝕜 (E i)).mat ⊗ₖ P 𝕜 i := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.sum_apply]
  simp only [diagonal_mat, Matrix.diagonal_apply, Matrix.kroneckerMap_apply, P, Prod.mk.injEq]
  by_cases hab : a = b <;> by_cases hij : i = j <;> simp [hab, hij]

private theorem conj_block (E : ι → d → ℝ) (U : ι → Matrix.unitaryGroup d 𝕜) :
    ∑ i, ((diagonal 𝕜 (E i)).conj (U i).val) ⊗ₖ basisProj 𝕜 i
      = (diagonal 𝕜 (fun x : d × ι ↦ E x.2 x.1)).conj (∑ i, (U i).val ⊗ₖ P 𝕜 i) := by
  ext1
  rw [mat_finset_sum, conj_apply_mat, diagonal_block, block_conjTranspose, block_mul, block_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [kronecker_mat, conj_apply_mat, basisProj_mat_P]

theorem mulVec_sum_kron_basisProj (X : ι → HermitianMat d 𝕜) (v : d × ι → 𝕜) (a : d) (i : ι) :
    ((∑ j, X j ⊗ₖ basisProj 𝕜 j).mat *ᵥ v) (a, i) = ((X i).mat *ᵥ (fun b ↦ v (b, i))) a := by
  simp only [mat_finset_sum, kronecker_mat, basisProj_mat, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Finset.sum_mul, mul_ite, mul_zero, ite_mul, zero_mul]
  simp

theorem ker_sum_kron_basisProj_le {X Y : ι → HermitianMat d 𝕜}
    (h : ∀ i, (X i).ker ≤ (Y i).ker) :
    (∑ i, X i ⊗ₖ basisProj 𝕜 i).ker ≤ (∑ i, Y i ⊗ₖ basisProj 𝕜 i).ker := by
  intro v hv
  rw [mem_ker_iff_mulVec_zero] at hv ⊢
  funext p
  obtain ⟨a, i⟩ := p
  have hvi : (WithLp.toLp 2 (fun b ↦ v (b, i)) : EuclideanSpace 𝕜 d) ∈ (X i).ker := by
    rw [mem_ker_iff_mulVec_zero]
    funext b
    rw [← mulVec_sum_kron_basisProj X v b i, hv]
    rfl
  have hY := (mem_ker_iff_mulVec_zero _ _).mp (h i hvi)
  rw [mulVec_sum_kron_basisProj Y v a i]
  exact congrFun hY a

/-- The continuous functional calculus acts blockwise on a block-diagonal matrix. -/
theorem cfc_sum_kron_basisProj (X : ι → HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (∑ i, X i ⊗ₖ basisProj 𝕜 i).cfc f = ∑ i, (X i).cfc f ⊗ₖ basisProj 𝕜 i := by
  set U : ι → Matrix.unitaryGroup d 𝕜 := fun i ↦ (X i).H.eigenvectorUnitary with hU
  set E : ι → d → ℝ := fun i ↦ (X i).H.eigenvalues with hE
  have hX : ∀ i, X i = (diagonal 𝕜 (E i)).conj (U i).val := fun i ↦ eq_conj_diagonal (X i)
  set V : Matrix.unitaryGroup (d × ι) 𝕜 := ⟨_, block_unitary U⟩ with hV
  have key : ∀ E' : ι → d → ℝ, ∑ i, ((diagonal 𝕜 (E' i)).conj (U i).val) ⊗ₖ basisProj 𝕜 i
      = (diagonal 𝕜 (fun x : d × ι ↦ E' x.2 x.1)).conj V.val := fun E' ↦ conj_block E' U
  have h1 : ∑ i, X i ⊗ₖ basisProj 𝕜 i
      = (diagonal 𝕜 (fun x : d × ι ↦ E x.2 x.1)).conj V.val := by
    rw [← key E]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← hX i]
  have h2 : ∀ i, (X i).cfc f = (diagonal 𝕜 (f ∘ E i)).conj (U i).val := by
    intro i
    rw [hX i, cfc_conj_unitary, cfc_diagonal]
  rw [h1, cfc_conj_unitary, cfc_diagonal,
    show (f ∘ fun x : d × ι ↦ E x.2 x.1) = (fun x : d × ι ↦ (f ∘ E x.2) x.1) from rfl,
    ← key (fun i ↦ f ∘ E i)]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h2 i]

/-- The matrix logarithm acts blockwise on a block-diagonal matrix. -/
theorem log_sum_kron_basisProj (X : ι → HermitianMat d 𝕜) :
    (∑ i, X i ⊗ₖ basisProj 𝕜 i).log = ∑ i, (X i).log ⊗ₖ basisProj 𝕜 i := by
  simp only [HermitianMat.log]
  exact cfc_sum_kron_basisProj X Real.log

omit [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] in
theorem smul_kronecker (r : ℝ) (A : HermitianMat d 𝕜) (B : HermitianMat ι 𝕜) :
    (r • A) ⊗ₖ B = r • (A ⊗ₖ B) := by
  ext1
  rw [kronecker_mat, mat_smul, mat_smul, kronecker_mat, Matrix.smul_kronecker]

@[simp]
theorem trace_basisProj (i : ι) : (basisProj 𝕜 i).trace = 1 := by
  rw [basisProj, trace_diagonal]
  simp

theorem inner_basisProj (i j : ι) :
    ⟪basisProj 𝕜 i, basisProj 𝕜 j⟫ = if i = j then 1 else 0 := by
  rw [inner_eq_re_trace, basisProj_mat_P, basisProj_mat_P, P_mul_P]
  split_ifs with h
  · simp [P, Matrix.trace_diagonal]
  · simp

end HermitianMat

end
