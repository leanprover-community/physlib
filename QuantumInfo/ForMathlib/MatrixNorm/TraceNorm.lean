/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Majorization
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import QuantumInfo.ForMathlib.Isometry

@[expose] public section

open BigOperators
open Classical

namespace Matrix
noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R]

/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace

@[simp]
theorem traceNorm_zero : traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]

/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem traceNorm_neg (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _


open MatrixOrder Isometry

/-- The trace norm is invariant under left multiplication by an isometry. -/
theorem traceNorm_isometry_left [Fintype k] {A : Matrix n m R} {u : Matrix k n R}
  (hu₁ : u.Isometry) : traceNorm (u * A) = traceNorm A := by
  unfold traceNorm
  congr 1
  simp [Matrix.mul_assoc]
  nth_rw 2 [← Matrix.mul_assoc]
  simp [show uᴴ * u = 1 from hu₁]

/-- The trace norm is invariant under right multiplication by the adjoint of an isometry. -/
theorem traceNorm_isometry_right [Fintype k] {A : Matrix n m R} {u : Matrix k m R}
  (hu₁ : u.Isometry) : traceNorm (A * uᴴ) = traceNorm A := by
  unfold traceNorm
  congr 1
  simp [← Matrix.mul_assoc]
  nth_rw 2 [Matrix.mul_assoc]
  have hA := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hsqrt : CFC.sqrt (u * (Aᴴ * A) * uᴴ) = u * CFC.sqrt (Aᴴ * A) * uᴴ := by
    have h_conj (B : Matrix m m R) (hB : 0 ≤ B) : 0 ≤ u * B * uᴴ := by
      rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
      exact hB.mul_mul_conjTranspose_same u
    apply (CFC.sqrt_eq_iff _ _ (h_conj _ hA) (h_conj _ (CFC.sqrt_nonneg _))).mpr
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, ← Matrix.mul_assoc uᴴ]
    simp [show uᴴ * u = 1 from hu₁]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc u, CFC.sqrt_mul_sqrt_self _ hA]
  rw [hsqrt, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp [show uᴴ * u = 1 by exact hu₁]

private theorem traceNorm_isometry_conj {A : Matrix n n R} {u : Matrix m n R}
  (hu : u.Isometry) {v : Matrix m n R} (hv : v.Isometry) :
    traceNorm (u * A * vᴴ) = traceNorm A := by
    rw [traceNorm_isometry_right hv, traceNorm_isometry_left hu]

/-- The trace norm is invariant under unitary conjugation. -/
@[simp]
theorem traceNorm_unitary_conj {A : Matrix n n R} {U : Matrix.unitaryGroup n R} :
  traceNorm (U.val * A * U.valᴴ) = traceNorm A := by
  have hu := (Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.2
  exact traceNorm_isometry_conj hu.1 hu.1

/-- For Hermitian matrices, the trace norm is the sum of absolute eigenvalues.

This is Proposition 9.1.1 in Wilde. -/
theorem traceNorm_Hermitian_eq_sum_abs_eigenvalues {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, abs (hA.eigenvalues i) := by
  obtain ⟨U, D, hD, hA_eq, h_eig⟩ : ∃ U : Matrix.unitaryGroup n R, ∃ D : Matrix n n R, D.IsDiag ∧ A = U.val * D * U.valᴴ ∧ ∀ i, D i i = hA.eigenvalues i := by
    refine' ⟨hA.eigenvectorUnitary, _, isDiag_diagonal _, hA.spectral_theorem, _⟩
    simp [diagonal]
  nth_rw 1 [hA_eq, traceNorm_unitary_conj]
  unfold traceNorm
  rw [← Matrix.IsDiag.diagonal_diag hD]
  simp [Matrix.diagonal_mul_diagonal, h_eig]
  simp_rw [← sq, ← Real.sqrt_sq_eq_abs, ← Matrix.trace_diagonal]
  set B := ((diagonal fun i => (hA.eigenvalues i : R) ^ 2)) with bD
  rw [CFC.sqrt_eq_real_sqrt B _, bD]
  . rw [cfcₙ_eq_cfc (by fun_prop) (by simp)]
    rw_mod_cast [cfc_diagonal (g := fun i => (hA.eigenvalues i) ^2)]
    simp
  . apply Matrix.PosSemidef.nonneg
    rw [Matrix.posSemidef_diagonal_iff]
    exact_mod_cast fun i => sq_nonneg (hA.eigenvalues i)

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde. -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm :=
  open MatrixOrder in
  And.left $ RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg

/-- The trace norm is zero iff the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  open MatrixOrder in
  set B := CFC.sqrt (Aᴴ * A) with hB_de
  have hB_posSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hB_hermitian : B.IsHermitian := hB_posSemidef.1
  have hB_pos : B.PosSemidef := ⟨hB_hermitian, hB_posSemidef.2⟩
  constructor
  · intro h
    have h₂ : ∀ i, hB_hermitian.eigenvalues i = 0 := by
      have h_sum : (↑(∑ j, hB_hermitian.eigenvalues j) : R) = 0 := by
        rw [hB_hermitian.sum_eigenvalues_eq_trace, ← hB_hermitian.re_trace_eq_trace]
        unfold traceNorm at h
        norm_cast
      have : ∑ j, hB_hermitian.eigenvalues j = 0 := by exact_mod_cast h_sum
      intro i
      exact Finset.sum_eq_zero_iff_of_nonneg (λ j _ => hB_pos.eigenvalues_nonneg j)
        |>.mp this i (Finset.mem_univ i)
    have h₃ : CFC.sqrt (Aᴴ * A) = 0 := hB_hermitian.eigenvalues_zero_eq_zero h₂
    have h₄ : Aᴴ * A = 0 := by
      simpa [h₃] using (
        CFC.nnrpow_sqrt_two (Aᴴ * A)
        (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self)
      ).symm
    rw [Matrix.conjTranspose_mul_self_eq_zero] at h₄
    exact h₄
  · rintro rfl
    simp

/-- The trace norm is homogeneous under scalar multiplication. Property 9.1.2 in Wilde. -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = (‖c‖^2:R) • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, Matrix.mul_smul, smul_mul, smul_smul]
    rw [RCLike.mul_conj c]
  rw [traceNorm, h]
  open MatrixOrder in
  have : RCLike.re (trace (‖c‖ • CFC.sqrt (Aᴴ * A))) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re]
    apply Or.inl
    rfl
  convert this using 3
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases h : c = 0
  · subst c
    simp
  · have hM_pd : (Aᴴ * A).PosSemidef := by apply posSemidef_conjTranspose_mul_self
    set M := (Aᴴ * A)
    rw [sq]
    simp [SemigroupAction.mul_smul]
    apply CFC.sqrt_unique;
    · simp; rw [CFC.sqrt_mul_sqrt_self M hM_pd.nonneg]
    · exact le_trans ( by norm_num ) (
        smul_le_smul_of_nonneg_left ( show 0 ≤ CFC.sqrt M from by exact (CFC.sqrt_nonneg M) ) ( norm_nonneg c ) );

section complexTraceNorm

variable [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
private lemma inner_A_mulVec_eq (A : Matrix n n ℂ) (v w : n → ℂ) :
    inner ℂ (WithLp.toLp 2 (A.mulVec v)) (WithLp.toLp 2 (A.mulVec w)) =
      star v ⬝ᵥ ((Aᴴ * A).mulVec w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

/-- Singular value decomposition for square complex matrices, with singular values expressed as
square roots of the eigenvalues of `Aᴴ * A`. -/
theorem exists_svd_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    ∃ V W : Matrix.unitaryGroup n ℂ,
      A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  let s : n → ℂ := fun i => Real.sqrt (hH.eigenvalues i)
  have hs_ne {i : n} (hi : hH.eigenvalues i ≠ 0) : s i ≠ 0 := by
    dsimp [s]
    exact_mod_cast Real.sqrt_ne_zero'.2
      (lt_of_le_of_ne (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) (Ne.symm hi))
  let u : n → EuclideanSpace ℂ n := fun i =>
    if hi : hH.eigenvalues i ≠ 0 then
      ((s i)⁻¹ • WithLp.toLp 2 (A.mulVec (hH.eigenvectorBasis i).ofLp))
    else 0
  have hu : Orthonormal ℂ ({i | hH.eigenvalues i ≠ 0}.domRestrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [u, s, Set.domRestrict]
    have hi' : hH.eigenvalues i.1 ≠ 0 := i.2
    have hj' : hH.eigenvalues j.1 ≠ 0 := j.2
    simp only [hi', hj', not_false_eq_true, ite_true]
    rw [inner_smul_left, inner_smul_right, inner_A_mulVec_eq, hH.mulVec_eigenvectorBasis j.1]
    by_cases hij : i.1 = j.1
    · cases Subtype.ext hij
      simp [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      field_simp [show (Real.sqrt (hH.eigenvalues i.1) : ℂ) ≠ 0 by simpa [s] using hs_ne i.2]
      exact_mod_cast (Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i.1)).symm
    · simpa [hij, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal, mul_comm]
        using (show i ≠ j from fun h => hij (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ n) (ι := n)
      (by simp [finrank_euclideanSpace]) (v := u)
      (s := {i | hH.eigenvalues i ≠ 0}) hu
  let V : Matrix.unitaryGroup n ℂ := ⟨Matrix.of (fun i j ↦ b j i), by
    simp only [Matrix.mem_unitaryGroup_iff]
    ext i j
    have h1 := b.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp_all [inner]
    exact h1⟩
  let W : Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary
  have hAW : A * W.val = V.val * Matrix.diagonal s := by
    ext i j
    have hleft : (A * W.val) i j = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.IsHermitian.eigenvectorUnitary_apply]
    by_cases hj : hH.eigenvalues j = 0
    · have hzero : A.mulVec (hH.eigenvectorBasis j).ofLp = 0 := by
        apply (WithLp.toLp_injective (p := 2))
        exact inner_self_eq_zero.mp (by
          rw [inner_A_mulVec_eq]
          rw [hH.mulVec_eigenvectorBasis j, hj]
          simp)
      rw [hleft, congrFun hzero i]
      simp [Matrix.mul_apply, Matrix.diagonal, V, s, hj]
    · have hbji : b j i = (s j)⁻¹ * A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        simpa [u, hj] using congrArg (fun x : EuclideanSpace ℂ n => x.ofLp i) (hb j hj)
      have hs_mul : s j * b j i = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        rw [hbji]; field_simp [hs_ne hj]
      rw [hleft, ← hs_mul]; simp [Matrix.mul_apply, Matrix.diagonal, V, s, mul_comm]
  refine ⟨V, W, ?_⟩
  simpa [W, Matrix.IsHermitian.eigenvectorUnitary, Matrix.mul_assoc] using
    congrArg (fun X => X * W.valᴴ) hAW

open scoped MatrixOrder in
private lemma traceNorm_eq_sum_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    A.traceNorm = ∑ i, Real.sqrt (hH.eigenvalues i) := by
  intro hH
  unfold Matrix.traceNorm
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hH, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The trace norm of a square complex matrix is the sum of its singular values. -/
theorem traceNorm_eq_sum_singularValues [DecidableEq n] (A : Matrix n n ℂ) :
    A.traceNorm = ∑ i, singularValues A i := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  rw [traceNorm_eq_sum_sqrt_eigenvalues A]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [singularValues]

omit [DecidableEq n] in
/-- The trace norm of a square complex matrix is the sum of its sorted singular values. -/
theorem traceNorm_eq_sum_singularValuesSorted [DecidableEq n] (A : Matrix n n ℂ) :
    A.traceNorm = ∑ i : Fin (Fintype.card n), singularValuesSorted A i := by
  rw [traceNorm_eq_sum_singularValues]
  simpa using (sum_singularValues_rpow_eq_sum_sorted A (1 : ℝ))

section
open scoped Matrix.Norms.L2Operator

omit [DecidableEq n] in
/-- Every singular value is bounded by the operator norm. -/
theorem singularValues_le_opNorm [DecidableEq n] (A : Matrix n n ℂ) (i : n) :
    singularValues A i ≤ ‖A‖ := by
  let : Nonempty n := ⟨i⟩
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  have hmem : hH.eigenvalues i ∈ spectrum ℝ (Aᴴ * A) := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    exact ⟨i, rfl⟩
  have hsq : singularValues A i * singularValues A i ≤ ‖A‖ * ‖A‖ := by
    have hsv_sq : singularValues A i * singularValues A i = hH.eigenvalues i := by
      dsimp [singularValues]
      simpa [pow_two] using (Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i))
    rw [hsv_sq]
    calc
      hH.eigenvalues i ≤ ‖Aᴴ * A‖ := by
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)] using
          spectrum.norm_le_norm_of_mem hmem
      _ = ‖A‖ * ‖A‖ := Matrix.l2_opNorm_conjTranspose_mul_self A
  exact (sq_le_sq₀ (singularValues_nonneg A i) (norm_nonneg A)).mp (by simpa [sq] using hsq)

omit [DecidableEq n] in
/-- The trace norm is bounded by the operator norm on the left times the trace norm on the right. -/
theorem traceNorm_mul_le_opNorm_traceNorm [DecidableEq n] (A B : Matrix n n ℂ) :
    (A * B).traceNorm ≤ ‖A‖ * B.traceNorm := by
  classical
  by_cases h : IsEmpty n
  · let := h
    simp [Subsingleton.elim A 0, Subsingleton.elim B 0]
  · let : Nonempty n := not_isEmpty_iff.mp h
    have hcard : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ‹Nonempty n›
    have htop : singularValuesSorted A ⟨0, hcard⟩ ≤ ‖A‖ := by
      rw [singularValuesSorted_zero_eq_sup A hcard]
      rw [Finset.sup'_le_iff]
      exact fun i _ => singularValues_le_opNorm A i
    have hA_bound : ∀ i : Fin (Fintype.card n), singularValuesSorted A i ≤ ‖A‖ := by
      intro i
      exact ((singularValuesSorted_antitone A) (Fin.zero_le i)).trans htop
    calc
      (A * B).traceNorm = ∑ i : Fin (Fintype.card n), singularValuesSorted (A * B) i := by
        rw [traceNorm_eq_sum_singularValuesSorted]
      _ ≤ ∑ i : Fin (Fintype.card n), singularValuesSorted A i * singularValuesSorted B i := by
        simpa using (sum_rpow_singularValues_mul_le A B (by positivity : 0 < (1 : ℝ)))
      _ ≤ ∑ i : Fin (Fintype.card n), ‖A‖ * singularValuesSorted B i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_right (hA_bound i) (singularValuesSorted_nonneg B i)
      _ = ‖A‖ * ∑ i : Fin (Fintype.card n), singularValuesSorted B i := by
        rw [Finset.mul_sum]
      _ = ‖A‖ * B.traceNorm := by
        rw [traceNorm_eq_sum_singularValuesSorted]

omit [DecidableEq n] in
/-- The trace norm is invariant under conjugate transpose. -/
theorem traceNorm_conjTranspose (A : Matrix n n ℂ) :
    Aᴴ.traceNorm = A.traceNorm := by
  classical
  let : DecidableEq n := Classical.decEq n
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨V, W, hA⟩ := Matrix.exists_svd_sqrt_eigenvalues A
  set D : Matrix n n ℂ :=
    Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hDH : Dᴴ = D := by simp [D, Matrix.diagonal_conjTranspose]
  calc
    Aᴴ.traceNorm = (W.val * D * V.valᴴ).traceNorm := by
      rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hDH, ← Matrix.mul_assoc]
    _ = D.traceNorm := traceNorm_isometry_conj
        ((Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.prop).1
        ((Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.prop).1
    _ = (V.val * D * W.valᴴ).traceNorm := (traceNorm_isometry_conj
        ((Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.prop).1
        ((Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.prop).1).symm
    _ = A.traceNorm := by rw [hA]

omit [Fintype m] [RCLike R] [DecidableEq n] in
/-- The trace norm is bounded by trace norm on the left times operator norm on the right. -/
theorem traceNorm_mul_le_traceNorm_opNorm [DecidableEq n] (A B : Matrix n n ℂ) :
    (A * B).traceNorm ≤ A.traceNorm * ‖B‖ := by
  calc
    (A * B).traceNorm = ((A * B)ᴴ).traceNorm := by rw [traceNorm_conjTranspose]
    _ ≤ A.traceNorm * ‖B‖ := by
      simpa [Matrix.conjTranspose_mul, Matrix.l2_opNorm_conjTranspose,
        traceNorm_conjTranspose, mul_comm] using
        Matrix.traceNorm_mul_le_opNorm_traceNorm Bᴴ Aᴴ

omit [Fintype m] [RCLike R] [DecidableEq n] in
/-- Multiplication on both sides by contractions does not increase trace norm. -/
theorem traceNorm_sandwich_le [DecidableEq n] {S M T : Matrix n n ℂ} (hS : ‖S‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) : (S * M * T).traceNorm ≤ M.traceNorm :=
  calc (S * M * T).traceNorm
      ≤ (M * T).traceNorm := by
        exact le_trans
          (by simpa [Matrix.mul_assoc] using Matrix.traceNorm_mul_le_opNorm_traceNorm S (M * T))
          (by simpa using mul_le_mul_of_nonneg_right hS (Matrix.traceNorm_nonneg (M * T)))
    _ ≤ M.traceNorm := by
        exact le_trans (traceNorm_mul_le_traceNorm_opNorm M T)
          (by simpa using mul_le_mul_of_nonneg_left hT (Matrix.traceNorm_nonneg M))

end

/-- The absolute value of the trace is bounded by the trace norm. -/
theorem abs_trace_le_traceNorm (A : Matrix n n ℂ) :
    ‖A.trace‖ ≤ A.traceNorm := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ := exists_svd_sqrt_eigenvalues A
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  set C : Matrix.unitaryGroup n ℂ := star W * V
  calc
    ‖A.trace‖ = ‖(C.val * D).trace‖ := by
      congr 1
      rw [hA]
      change (V.val * D * W.valᴴ).trace = (W.valᴴ * V.val * D).trace
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ ≤ ∑ i, ‖(C.val * D) i i‖ := by
      simpa [Matrix.trace] using norm_sum_le (s := Finset.univ) (f := fun i => (C.val * D) i i)
    _ = ∑ i, ‖C.val i i‖ * Real.sqrt (hH.eigenvalues i) := by
      simp [D, Matrix.mul_apply, Matrix.diagonal, Real.norm_eq_abs, abs_of_nonneg]
    _ ≤ ∑ i, Real.sqrt (hH.eigenvalues i) := by
      exact Finset.sum_le_sum (fun i _ => by
        simpa using mul_le_mul_of_nonneg_right
          (entry_norm_bound_of_unitary C.property i i)
          (Real.sqrt_nonneg _))
    _ = A.traceNorm := by
      simpa [hH] using (traceNorm_eq_sum_sqrt_eigenvalues A).symm

end complexTraceNorm

/-- For square complex matrices, the trace norm is the maximum of `re (Tr[U * A])`
over unitaries `U`. -/
theorem traceNorm_eq_max_re_tr_U (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U : unitaryGroup n ℂ, Complex.re ((U.val * A).trace) = x} A.traceNorm := by
  classical
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ :
      ∃ V W : Matrix.unitaryGroup n ℂ,
        A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
    simpa [hH] using exists_svd_sqrt_eigenvalues A
  have htraceNorm : A.traceNorm = ∑ i, Real.sqrt (hH.eigenvalues i) := by
    simpa [hH] using traceNorm_eq_sum_sqrt_eigenvalues A
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hVu : V.valᴴ * V.val = 1 := (Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.prop |>.1
  have hWu : W.valᴴ * W.val = 1 := (Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.prop |>.1
  refine ⟨⟨W * star V, ?_⟩, ?_⟩
  · calc Complex.re (((W * star V).val * A).trace)
        = Complex.re (D.trace) := by
          rw [hA]; congr 1
          change (W.val * V.valᴴ * (V.val * D * W.valᴴ)).trace = D.trace
          simp [Matrix.mul_assoc, hVu, Matrix.trace_mul_comm, hWu]
      _ = A.traceNorm := by simp [D, Matrix.trace, htraceNorm]
  · rintro _ ⟨U, rfl⟩
    set C : Matrix.unitaryGroup n ℂ := star W * U * V
    rw [show Complex.re ((U.val * A).trace) =
        ∑ i, Real.sqrt (hH.eigenvalues i) * Complex.re (C.val i i) by
      conv_lhs => rw [hA]
      have h1 : (U.val * (V.val * D * W.valᴴ)).trace = (C.val * D).trace := by
        change _ = (W.valᴴ * U.val * V.val * D).trace
        rw [show (U.val * (V.val * D * W.valᴴ)).trace =
            (((U.val * V.val) * D) * W.valᴴ).trace by simp [Matrix.mul_assoc],
          Matrix.trace_mul_comm _ W.valᴴ]
        simp [Matrix.mul_assoc]
      rw [h1]
      simp [D, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Complex.mul_re, mul_comm],
      htraceNorm]
    have hdiag_le : ∀ i, Complex.re (C.val i i) ≤ 1 := fun i =>
      (Complex.re_le_norm _).trans (by
        have hsq : ‖C.val i i‖ ^ 2 ≤ 1 := by
          linarith [(Finset.single_le_sum (f := fun j => ‖C.val i j‖ ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)).trans_eq
            (Matrix.unitary_row_sum_norm_sq C.val (Matrix.mem_unitaryGroup_iff.mp C.prop) i)]
        nlinarith [norm_nonneg (C.val i i), hsq])
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [hdiag_le i, Real.sqrt_nonneg (hH.eigenvalues i)]

/-- The trace norm satisfies the triangle inequality for square complex matrices. -/
theorem traceNorm_add_le (A B : Matrix n n ℂ) : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_re_tr_U (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h₁
  obtain h₂ := (traceNorm_eq_max_re_tr_U A).right
  obtain h₃ := (traceNorm_eq_max_re_tr_U B).right
  simp only [upperBounds, Set.mem_ofPred_eq] at h₂ h₃
  calc _
    _ = RCLike.re ((Uab.1 * A).trace) + RCLike.re ((Uab.1 * B).trace) := h₁.symm
    _ ≤ traceNorm A + RCLike.re ((Uab.1 * B).trace) := by
      simpa [add_comm] using add_le_add_right
        (h₂ (a := RCLike.re ((Uab.1 * A).trace)) ⟨Uab, rfl⟩)
        (RCLike.re ((Uab.1 * B).trace))
    _ ≤ _ := by
      simpa [add_comm] using add_le_add_left
        (h₃ (a := RCLike.re ((Uab.1 * B).trace)) ⟨Uab, rfl⟩) (traceNorm A)

/-- A positive semidefinite matrix has trace norm equal to its trace. -/
theorem PosSemidef.traceNorm_eq_trace {A : Matrix m m R} (hA : A.PosSemidef) :
    A.traceNorm = A.trace := by
  have : Aᴴ * A = A^2 := by rw [hA.1, pow_two]
  open MatrixOrder in
  rw [traceNorm, this, CFC.sqrt_sq A, hA.1.re_trace_eq_trace]

/-- The trace norm is convex. Property 9.1.5 in Wilde. -/
theorem traceNorm_convex (M N : Matrix n n ℂ) (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
  ((l:ℂ) • M + ((1 - l) : ℂ) • N).traceNorm ≤ l * M.traceNorm + (1-l) * N.traceNorm := by
  refine (traceNorm_add_le _ _).trans ?_
  simp_rw [traceNorm_smul]
  nth_rw 1 [← Complex.ofReal_one]
  simp_rw [← Complex.ofReal_sub, Complex.norm_real]
  simp [Real.norm_eq_abs, abs_of_nonneg (hl.1), abs_of_nonneg (sub_nonneg.mpr (hl.2))]

end traceNorm

end Matrix
