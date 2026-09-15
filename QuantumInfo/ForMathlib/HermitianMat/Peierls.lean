/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.HermitianMat.LiebConcavity

@[expose] public section

noncomputable section

variable {d : Type*}
variable [Fintype d] [DecidableEq d]
variable {𝕜 : Type*} [RCLike 𝕜]

open HermitianMat
open scoped InnerProductSpace RealInnerProductSpace Topology

namespace HermitianMat

/--
The trace of cfc(g, A) is invariant under unitary conjugation of A.
Follows from `cfc_conj_unitary` and `trace_conj_unitary`.
-/
lemma trace_cfc_conj_unitary (A : HermitianMat d ℂ) (g : ℝ → ℝ) (U : 𝐔[d]) :
    ((A.conj U.val).cfc g).trace = (A.cfc g).trace := by
  rw [cfc_conj_unitary, trace_conj_unitary]

/--
Peierls inequality: for a convex function g, the sum of g applied to the
diagonal entries of a Hermitian matrix is at most the trace of g(A).
This follows from Jensen's inequality applied to the spectral decomposition.
-/
theorem peierls_inequality (A : HermitianMat d ℂ) (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) :
    ∑ i, g ((A.mat i i).re) ≤ (A.cfc g).trace := by
  -- By the properties of the trace and the convexity of $g$, we have:
  have h_trace_le : ∑ i, g ((A.mat i i).re) ≤ ∑ j, g (A.H.eigenvalues j) *
      ∑ i, ‖(A.H.eigenvectorUnitary.val i j)‖^2 := by
    -- By the spectral theorem, we can write A as ∑_i λ_i u_i u_i^*,
    -- where λ_i are the eigenvalues and u_i are the corresponding eigenvectors.
    have h_spectral : ∀ i, (A.mat i i).re = ∑ j, A.H.eigenvalues j *
        ‖(A.H.eigenvectorUnitary.val i j)‖^2 := by
      intro i
      have h_sum : (A.mat i i).re = ∑ j, (A.H.eigenvectorBasis j i) *
          star (A.H.eigenvectorBasis j i) * A.H.eigenvalues j := by
        have this := congr_fun (congr_fun A.H.spectral_theorem i) i
        simp_all [Matrix.mul_apply, Matrix.diagonal]
        simp [Complex.ext_iff, mul_comm, mul_left_comm]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all [Complex.ext_iff, mul_comm]
      simp [Complex.normSq, Complex.sq_norm]
    have h_jensen : ∀ i, g ((A.mat i i).re) ≤ ∑ j, ‖(A.H.eigenvectorUnitary.val i j)‖^2 *
        g (A.H.eigenvalues j) := by
      intro i
      have h_convex_comb : ∑ j, ‖(A.H.eigenvectorUnitary.val i j)‖^2 = 1 := by
        have := congr_fun (congr_fun A.H.eigenvectorUnitary.2.2 i) i
        simp_all [Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        exact_mod_cast this
      convert! hg.map_sum_le _ _ _ <;> simp_all [mul_comm]
    convert! Finset.sum_le_sum fun i _ => h_jensen i using 1
    rw [Finset.sum_comm, Finset.sum_congr rfl]; intros; rw [Finset.mul_sum]; ac_rfl
  have h_unitary : ∀ (j : d), ∑ i, ‖(A.H.eigenvectorUnitary.val i j)‖^2 = 1 := by
    exact fun j => Matrix.unitaryGroup_row_norm (H A).eigenvectorUnitary j
  simp_all [trace_cfc_eq]

theorem peierls_inequality_ici (A : HermitianMat d ℂ) (g : ℝ → ℝ) (hg : ConvexOn ℝ (Set.Ici 0) g)
  (hA : 0 ≤ A) :
    ∑ i, g ((A.mat i i).re) ≤ (A.cfc g).trace := by
  -- By the properties of the trace and the convexity of $g$, we have:
  have h_trace_le : ∑ i, g ((A.mat i i).re) ≤ ∑ j, g (A.H.eigenvalues j) *
      ∑ i, ‖(A.H.eigenvectorUnitary.val i j)‖^2 := by
    -- By the spectral theorem, we can write A as ∑_i λ_i u_i u_i^*,
    -- where λ_i are the eigenvalues and u_i are the corresponding eigenvectors.
    have h_spectral : ∀ i, (A.mat i i).re = ∑ j, A.H.eigenvalues j *
        ‖(A.H.eigenvectorUnitary.val i j)‖^2 := by
      intro i
      have h_sum : (A.mat i i).re = ∑ j, (A.H.eigenvectorBasis j i) *
          star (A.H.eigenvectorBasis j i) * A.H.eigenvalues j := by
        have := A.H.spectral_theorem
        replace this := congr_fun (congr_fun this i) i; simp_all [Matrix.mul_apply, Matrix.diagonal]
        simp [Complex.ext_iff, mul_comm, mul_left_comm]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all [Complex.ext_iff, mul_comm]
      simp [Complex.normSq, Complex.sq_norm]
    have h_jensen : ∀ i, g ((A.mat i i).re) ≤ ∑ j, ‖(A.H.eigenvectorUnitary.val i j)‖^2 *
        g (A.H.eigenvalues j) := by
      intro i
      have h_convex_comb : ∑ j, ‖(A.H.eigenvectorUnitary.val i j)‖^2 = 1 := by
        replace this := congr_fun (congr_fun A.H.eigenvectorUnitary.2.2 i) i
        simp_all [Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        exact_mod_cast this
      convert! hg.map_sum_le _ _ _
      · simp_all [mul_comm]
      · simp
      · simpa
      · simp
        intro i
        exact A.eigenvalues_nonneg hA i
    convert! Finset.sum_le_sum fun i _ => h_jensen i using 1
    rw [Finset.sum_comm, Finset.sum_congr rfl]; intros; rw [Finset.mul_sum]; ac_rfl
  have h_unitary : ∀ (j : d), ∑ i, ‖(A.H.eigenvectorUnitary.val i j)‖^2 = 1 := by
    exact fun j => Matrix.unitaryGroup_row_norm (H A).eigenvectorUnitary j
  simp_all [trace_cfc_eq]

set_option backward.isDefEq.respectTransparency false in
/--
Joint convexity of the trace functional: for a convex function g,
the map A ↦ tr(g(A)) is convex on the space of Hermitian matrices.
-/
theorem trace_function_convex_univ (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (fun A : HermitianMat d ℂ => (A.cfc g).trace) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  -- Let $C = aA + bB$.
  set C : HermitianMat d ℂ := a • A + b • B
  -- By the properties of the trace and the convexity of $g$, we have:
  have h_trace : (C.cfc g).trace = ∑ i, g (C.H.eigenvalues i) := by
    exact trace_cfc_eq C g
  have h_sum : ∑ i, g (C.H.eigenvalues i) ≤
      a * ∑ i, g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re +
      b * ∑ i, g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i |> Complex.re) := by
    have h_sum : ∀ i, g (C.H.eigenvalues i) ≤
        a * g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re +
        b * g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re := by
      intro i
      have h_eigenvalue : C.H.eigenvalues i =
          a * ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re +
          b * ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re := by
        have h_add : (C.conj (star C.H.eigenvectorUnitary.val)).mat i i =
            a * (A.conj (star C.H.eigenvectorUnitary.val)).mat i i +
            b * (B.conj (star C.H.eigenvectorUnitary.val)).mat i i := by
          simp +zetaDelta only [mat_add, mat_smul, map_add, mat_apply]
          simp only [conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mat_smul, Algebra.mul_smul_comm,
            Algebra.smul_mul_assoc]
          rfl
        have h_eig2 : (C.conj (star C.H.eigenvectorUnitary.val)) =
            (diagonal ℂ C.H.eigenvalues).conj 1 := by
          convert congr_arg (conj (star C.H.eigenvectorUnitary.val) ·) (eq_conj_diagonal C) using 1
          simp [conj_conj]
        -- In the eigenbasis of `C`, the `i`-th diagonal entry is exactly the `i`-th eigenvalue.
        have h_diag : (C.conj (star C.H.eigenvectorUnitary.val)).mat i i =
            (C.H.eigenvalues i : ℂ) := by
          rw [h_eig2, conj_one, mat_apply, diagonal_apply, if_pos rfl]
          rfl
        simpa using congr_arg Complex.re (h_diag.symm.trans h_add)
      rw [h_eigenvalue]
      exact hg.2 trivial trivial ha hb hab
    simpa only [Finset.mul_sum, Finset.sum_add_distrib] using Finset.sum_le_sum fun i _ => h_sum i
  have hAtr : ∑ i, g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re ≤ (A.cfc g).trace := by
    convert peierls_inequality _ _ hg using 1
    convert trace_cfc_conj_unitary _ _ _ using 1
    rotate_right
    exact C.H.eigenvectorUnitary
    simp [conj_conj]
  have hBtr : ∑ i, g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re ≤ (B.cfc g).trace := by
    convert peierls_inequality _ _ hg using 1
    convert trace_cfc_conj_unitary _ _ _
    rotate_right
    exact C.H.eigenvectorUnitary
    simp [conj_conj]
  have h1 := h_sum.trans
    (add_le_add (mul_le_mul_of_nonneg_left hAtr ha) (mul_le_mul_of_nonneg_left hBtr hb))
  simp_all only
  exact h1

set_option backward.isDefEq.respectTransparency false in
open ComplexOrder in
/--
Convexity of trace functions: if `g` is convex on `ℝ₊`, then `A ↦ Tr[g(A)]` is
convex on PSD matrices. -/
theorem trace_function_convex_ici {g : ℝ → ℝ} (hg : ConvexOn ℝ (Set.Ici 0) g) :
    ConvexOn ℝ {A : HermitianMat d ℂ | 0 ≤ A} (fun A => (A.cfc g).trace) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro A hA B hB a b ha hb hab
  -- Let $C = aA + bB$.
  set C : HermitianMat d ℂ := a • A + b • B
  -- By the properties of the trace and the convexity of $g$, we have:
  have h_trace : (C.cfc g).trace = ∑ i, g (C.H.eigenvalues i) := by
    exact trace_cfc_eq C g
  have h_sum : ∑ i, g (C.H.eigenvalues i) ≤
      a * ∑ i, g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re +
      b * ∑ i, g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re := by
    have h_sum : ∀ i, g (C.H.eigenvalues i) ≤
        a * g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re +
        b * g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re := by
      intro i
      have h_eigenvalue : C.H.eigenvalues i =
          a * ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re +
          b * ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re := by
        have h_eigenvalue : (C.conj (star C.H.eigenvectorUnitary.val)).mat i i =
            a * (A.conj (star C.H.eigenvectorUnitary.val)).mat i i +
            b * (B.conj (star C.H.eigenvectorUnitary.val)).mat i i := by
          simp +zetaDelta only [mat_add, mat_smul, map_add, mat_apply]
          simp only [conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mat_smul, Algebra.mul_smul_comm,
            Algebra.smul_mul_assoc]
          rfl
        have h_eig2 : (C.conj (star C.H.eigenvectorUnitary.val)) =
            (diagonal ℂ C.H.eigenvalues).conj 1 := by
          convert congr_arg (conj (star C.H.eigenvectorUnitary.val) ·) (eq_conj_diagonal C) using 1
          simp [conj_conj]
        -- In the eigenbasis of `C`, the `i`-th diagonal entry is exactly the `i`-th eigenvalue.
        have h_diag : (C.conj (star C.H.eigenvectorUnitary.val)).mat i i =
            (C.H.eigenvalues i : ℂ) := by
          rw [h_eig2, conj_one, mat_apply, diagonal_apply, if_pos rfl]
          rfl
        simpa using congr_arg Complex.re (h_diag.symm.trans h_eigenvalue)
      rw [h_eigenvalue]
      refine hg.2 ?_ ?_ ha hb hab
      · simp
        exact (Complex.le_def.mp (((zero_le_iff.mp (conj_nonneg _ hA)).diag_nonneg (i := i)))).1
      · simp
        exact (Complex.le_def.mp (((zero_le_iff.mp (conj_nonneg _ hB)).diag_nonneg (i := i)))).1
    simpa only [Finset.mul_sum, Finset.sum_add_distrib] using Finset.sum_le_sum fun i _ => h_sum i
  -- With convexity of g, we have ∑_i g(A_ii) ≤ Tr(g(A)) and ∑_i g(B_ii) ≤ Tr(g(B))
  have hAtr : ∑ i, g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i).re ≤ (A.cfc g).trace := by
    have hA' : 0 ≤ A.conj (star C.H.eigenvectorUnitary.val) := A.conj_nonneg _ hA
    calc ∑ i, g ((A.conj (star C.H.eigenvectorUnitary.val)).mat i i |> Complex.re)
        ≤ ((A.conj (star C.H.eigenvectorUnitary.val)).cfc g).trace :=
          peierls_inequality_ici _ _ hg hA'
      _ = (A.cfc g).trace :=
          trace_cfc_conj_unitary A g ⟨star C.H.eigenvectorUnitary.val, by
            rw [Matrix.mem_unitaryGroup_iff, star_star]; exact C.H.eigenvectorUnitary.prop.1⟩
  have hBtr : ∑ i, g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i).re ≤ (B.cfc g).trace := by
    have hB' : 0 ≤ B.conj (star C.H.eigenvectorUnitary.val) := B.conj_nonneg _ hB
    calc ∑ i, g ((B.conj (star C.H.eigenvectorUnitary.val)).mat i i |> Complex.re)
        ≤ ((B.conj (star C.H.eigenvectorUnitary.val)).cfc g).trace :=
          peierls_inequality_ici _ _ hg hB'
      _ = (B.cfc g).trace :=
          trace_cfc_conj_unitary B g ⟨star C.H.eigenvectorUnitary.val, by
            rw [Matrix.mem_unitaryGroup_iff, star_star]; exact C.H.eigenvectorUnitary.prop.1⟩
  have h1 := h_sum.trans
    (add_le_add (mul_le_mul_of_nonneg_left hAtr ha) (mul_le_mul_of_nonneg_left hBtr hb))
  simp_all only
  exact h1

-- /-- Strict convexity of trace functions: if `g` is strictly convex on `ℝ₊`, then
-- `A ↦ Tr[g(A)]` is strictly convex on PSD matrices. -/
-- theorem trace_function_strictConvex {g : ℝ → ℝ} (hg : StrictConvexOn ℝ (Set.Ici 0) g)
--     (hg_cont : Continuous g) :
--     StrictConvexOn ℝ {A : HermitianMat d ℂ | 0 ≤ A}
--       (fun A => (A.cfc g).trace) := by
--   not needed right now
