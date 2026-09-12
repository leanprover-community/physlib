/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib
public import QuantumInfo.ForMathlib.Matrix

/-! # Majorization and weak log-majorization

This file develops the theory of majorization for finite sequences, leading to
the key singular value inequality needed for the Schatten–Hölder inequality.

## Main results

* `sum_rpow_singularValues_mul_le`: for `r > 0`, the singular values of `A * B`
  satisfy `∑ σᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r`.
* `holder_step_for_singularValues`: the Hölder step giving
  `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σᵢ(A)^p)^{r/p} · (∑ σᵢ(B)^q)^{r/q}`.
-/

@[expose] public section

open Finset BigOperators Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

/-! ## Sorted singular values -/

/-- The singular values of a square complex matrix `A`, defined as the square
roots of the eigenvalues of `A†A`. These are indexed by `d` without a
particular ordering.

Note: We use `A.conjTranspose` as the argument to `isHermitian_mul_conjTranspose_self`
so that the underlying Hermitian matrix is `A† * A` (matching the convention in `schattenNorm`). -/
def singularValues (A : Matrix d d ℂ) : d → ℝ :=
  fun i => Real.sqrt ((isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i)

/-- Singular values are nonneg. -/
lemma singularValues_nonneg (A : Matrix d d ℂ) (i : d) :
    0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

/-- The sorted singular values of a square complex matrix, in decreasing order,
indexed by `Fin (Fintype.card d)`.

We define them by sorting the multiset of singular values. -/
noncomputable def singularValuesSorted (A : Matrix d d ℂ) :
    Fin (Fintype.card d) → ℝ :=
  fun i =>
    let vals : Multiset ℝ := Finset.univ.val.map (singularValues A)
    let sorted := vals.sort (· ≥ ·)
    sorted.get ⟨i.val, by rw [Multiset.length_sort]; show i.val < (Multiset.map (singularValues A) univ.val).card; rw [Multiset.card_map]; simp [Finset.card_univ]⟩

/-- Sorted singular values are nonneg. -/
lemma singularValuesSorted_nonneg (A : Matrix d d ℂ) (i : Fin (Fintype.card d)) :
    0 ≤ singularValuesSorted A i := by
  have h_nonneg : ∀ i, 0 ≤ (singularValues A i) := by
    exact singularValues_nonneg A
  have h_sorted_nonneg : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → ∀ i < l.length, 0 ≤ l[i]! := by
    aesop
  contrapose! h_sorted_nonneg
  use Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·)
  refine' ⟨_, i, _, _⟩
  · aesop
  · simp [Finset.card_univ]
  · convert h_sorted_nonneg using 1
    unfold singularValuesSorted; aesop

/-- The sum `∑ singularValues A i ^ p` equals the sum over sorted singular values. -/
lemma sum_singularValues_rpow_eq_sum_sorted (A : Matrix d d ℂ) (p : ℝ) :
    ∑ i : d, singularValues A i ^ p =
    ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
  have h_perm : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val := by
    have h_multiset : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.sort (Multiset.map (fun i => singularValues A i) Finset.univ.val) (· ≥ ·) := by
      aesop
    convert h_multiset using 1
    refine' congr_arg _ (List.ext_get _ _) <;> simp [singularValuesSorted]
  have h_sum_eq : Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValues A i) Finset.univ.val)) = Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val)) := by
    rw [h_perm]
  convert h_sum_eq using 1
  · erw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  · simp [Finset.sum]
    rfl

/-! ## Weak log-majorization and its consequences -/

/-- Sorted singular values are antitone (decreasing). -/
lemma singularValuesSorted_antitone (A : Matrix d d ℂ) :
    Antitone (singularValuesSorted A) := by
  intro i j hij
  have h_sorted : List.Pairwise (· ≥ ·) (Finset.univ.val.map (singularValues A) |>.sort (· ≥ ·)) := by
    exact Multiset.pairwise_sort _ _
  exact h_sorted.rel_get_of_le hij

/-- The product of nonneg antitone sequences is antitone. -/
lemma antitone_mul_of_antitone_nonneg {n : ℕ}
    {f g : Fin n → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) :
    Antitone (fun i => f i * g i) := by
  exact fun i j hij => mul_le_mul (hf hij) (hg hij) (hg_nn _) (hf_nn _)

/-! ### Compound matrices and auxiliary lemmas for Horn's inequality

The proof of Horn's inequality uses the *compound matrix* (or *k-th exterior power*
of a matrix).  For a `d × d` matrix `M` and `k ≤ card d`, the `k`-th compound matrix
`C_k(M)` is indexed by `k`-element subsets of the index type, with entry `(S, T)` being
the minor `det M[S, T]`.

The key properties are:
1. **Cauchy–Binet**: `C_k(M N) = C_k(M) · C_k(N)`.
2. **Spectral characterisation**: the largest singular value of `C_k(M)` is
   `∏_{i=1}^k σ↓ᵢ(M)`.
3. **Operator-norm submultiplicativity**: `σ₁(A B) ≤ σ₁(A) · σ₁(B)`.

Combining these gives Horn's inequality:
  `∏ σ↓(AB) = σ₁(C_k(AB)) = σ₁(C_k(A) C_k(B)) ≤ σ₁(C_k(A)) σ₁(C_k(B))
            = (∏ σ↓(A))(∏ σ↓(B))`.
-/

namespace AllOrdered

/-- A `LinearOrder` on any `Fintype`, obtained classically via well-ordering. -/
scoped instance fintypeLinearOrderClassical (α : Type*) [Fintype α] [DecidableEq α] :
    LinearOrder α := by
  classical
  exact linearOrderOfSTO (WellOrderingRel)

end AllOrdered

open scoped AllOrdered

/-- The `k`-th compound (exterior-power) matrix of `M`. -/
noncomputable def compoundMatrix (M : Matrix d d ℂ) (k : ℕ) :
    Matrix {S : Finset d // S.card = k} {S : Finset d // S.card = k} ℂ :=
  fun S T =>
    @Matrix.det (Fin k) _ _ ℂ _
      (M.submatrix (fun i => S.1.orderEmbOfFin S.2 i) (fun j => T.1.orderEmbOfFin T.2 j))

/-- **Cauchy–Binet formula** for rectangular matrices: if `A` is `m × n` and `B` is
`n × m`, then `det(A * B) = ∑_S det(A[:,S]) * det(B[S,:])` where the sum is
over `m`-element subsets `S` of the column/row index. -/
lemma cauchyBinet {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {R : Type*} [CommRing R]
    (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset n // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
      (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  have h_cauchy_binet : ∀ (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R), Matrix.det (A * B) = ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) := by
    simp [Matrix.det_apply']
    simp [Matrix.mul_apply, Finset.mul_sum]
    intro A B; rw [← Finset.sum_comm]; congr; ext x; simp [mul_comm]
    simp only [prod_sum, sum_mul]
    refine' Finset.sum_bij (fun f _ => fun i => f (x.symm i) (Finset.mem_univ _)) _ _ _ _
    · simp
    · simp only [univ_pi_univ, mem_univ, funext_iff, forall_true_left, forall_const]
      exact fun a₁ a₂ h i => by simpa using h (x i)
    · simp only [mem_univ, univ_pi_univ, exists_const, forall_const]
      exact fun b => ⟨fun i _ => b (x i), by ext i; simp⟩
    · simp only [univ_pi_univ, mem_univ, prod_mul_distrib, prod_attach_univ,
      Equiv.symm_apply_apply, forall_const]
      intro a
      rw [← Equiv.prod_comp x.symm]
      ring_nf
      rw [← Equiv.prod_comp x.symm]
      simp only [mul_comm, mul_assoc]
      conv_rhs => rw [← Equiv.prod_comp x]
      simp [Equiv.symm_apply_apply]
  -- Split the sum into injective and non-injective functions.
  have h_split : ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) = ∑ σ : Fin m → n, if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs with hσ <;> simp_all [Function.Injective]
    obtain ⟨i, j, hij, hne⟩ := hσ
    exact mul_eq_zero_of_right _ (Matrix.det_zero_of_row_eq hne (by ext1; simp only [of_apply, hij]))
  -- Group the sum by the image of the injective functions.
  have h_group : ∑ σ : Fin m → n, (if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) := by
    rw [← Finset.sum_comm, Finset.sum_congr rfl]
    intro σ _
    by_cases hσ : Function.Injective σ
    · simp [hσ]
      rw [Finset.sum_eq_single ⟨Finset.image σ Finset.univ, by simp [Finset.card_image_of_injective _ hσ]⟩]
      · simp
      · grind
      · simp
    · simp [hσ]
  -- For each subset $S$ of size $m$, the inner sum is equal to the product of the determinants of the submatrices of $A$ and $B$ corresponding to $S$.
  have h_inner : ∀ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = Matrix.det (Matrix.submatrix A id (S.val.orderEmbOfFin S.property)) * Matrix.det (Matrix.submatrix B (S.val.orderEmbOfFin S.property) id) := by
    intro S
    have h_inner_sum : ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ τ : Equiv.Perm (Fin m), (∏ i, A i (S.val.orderEmbOfFin S.property (τ i))) * Matrix.det (Matrix.of (fun i j ↦ B (S.val.orderEmbOfFin S.property (τ i)) j)) := by
      have h_inner_sum : Finset.filter (fun σ : Fin m → n => Function.Injective σ ∧ Finset.image σ Finset.univ = S.val) Finset.univ = Finset.image (fun τ : Equiv.Perm (Fin m) => fun i => S.val.orderEmbOfFin S.property (τ i)) Finset.univ := by
        ext σ
        simp [Finset.mem_image]
        constructor
        · intro hσ
          obtain ⟨a, ha⟩ : ∃ a : Fin m → Fin m, ∀ i, σ i = S.val.orderEmbOfFin S.property (a i) := by
            have h_exists_a : ∀ i, ∃ a : Fin m, σ i = S.val.orderEmbOfFin S.property a := by
              intro i
              have h_exists_a : σ i ∈ S.val := by
                exact hσ.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
              have h_exists_a : Finset.image (fun a : Fin m => S.val.orderEmbOfFin S.property a) Finset.univ = S.val := by
                refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun a _ => Finset.orderEmbOfFin_mem _ _ _) _
                rw [Finset.card_image_of_injective _ fun a b h => by simpa [Fin.ext_iff] using h]; simp [S.2]
              grind
            exact ⟨fun i => Classical.choose (h_exists_a i), fun i => Classical.choose_spec (h_exists_a i)⟩
          have ha_inj : Function.Injective a := by
            exact fun i j hij => hσ.1 <| by simp [ha, hij]
          exact ⟨Equiv.ofBijective a ⟨ha_inj, Finite.injective_iff_surjective.mp ha_inj⟩, funext fun i => ha i ▸ rfl⟩
        · rintro ⟨a, rfl⟩
          constructor
          · exact fun i j hij => a.injective <| by simpa using hij
          · refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _) ?_
            rw [Finset.card_image_of_injective _ fun i j hij => by simpa [Fin.ext_iff] using hij]; simp [S.2]
      rw [← Finset.sum_filter, h_inner_sum, Finset.sum_image]
      exact fun τ _ τ' _ h => Equiv.Perm.ext fun i => by simpa using congr_fun h i
    rw [h_inner_sum, Matrix.det_apply', Matrix.det_apply']
    simp [Matrix.det_apply', Finset.sum_mul]
    refine' Finset.sum_bij (fun σ _ => σ⁻¹) _ _ _ _ <;> simp [Equiv.Perm.sign_inv]
    · exact fun b => ⟨b⁻¹, inv_inv b⟩
    · intro σ
      rw [← Equiv.prod_comp σ⁻¹]
      simp [mul_assoc, mul_left_comm, Finset.mul_sum]
      refine' Finset.sum_bij (fun τ _ => σ * τ) _ _ _ _ <;> simp [Equiv.Perm.sign_mul]
      · exact fun b => ⟨σ⁻¹ * b, by simp⟩
      · cases' Int.units_eq_one_or (Equiv.Perm.sign σ) with h h <;> simp [h]
  rw [h_cauchy_binet, h_split, h_group, Finset.sum_congr rfl fun S hS => h_inner S]

/--
The `compoundMatrix` of a product is the product of the `compoundMatrix`s.
-/
lemma compoundMatrix_mul (M N : Matrix d d ℂ) (k : ℕ) :
    compoundMatrix (M * N) k = compoundMatrix M k * compoundMatrix N k := by
  ext1
  apply cauchyBinet

set_option backward.isDefEq.respectTransparency false in
/-- `compoundMatrix` commutes with `conjTranspose`. -/
lemma compoundMatrix_conjTranspose (M : Matrix d d ℂ) (k : ℕ) :
    compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
  ext1
  unfold compoundMatrix
  rw [Matrix.conjTranspose_apply, ← Matrix.det_conjTranspose]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The compound matrix of a diagonal matrix is diagonal, with entries being
products of eigenvalues over k-subsets. -/
lemma compoundMatrix_diagonal (f : d → ℂ) (k : ℕ) :
    compoundMatrix (Matrix.diagonal f) k =
    Matrix.diagonal (fun S : {S : Finset d // S.card = k} =>
      ∏ i : Fin k, f (S.1.orderEmbOfFin S.2 i)) := by
  ext S T; by_cases h : S = T <;> simp_all [Matrix.diagonal]
  · refine' Matrix.det_of_isUpperTriangular _ |> fun h => h.trans _
    · intro i j hij; aesop
    · aesop
  · -- Since $S \neq T$, there exists some $i \in S$ such that $i \notin T$.
    obtain ⟨i, hiS, hiT⟩ : ∃ i ∈ S.val, i ∉ T.val := by
      contrapose! h
      exact Subtype.ext (Finset.eq_of_subset_of_card_le h (by simp [S.2, T.2]))
    obtain ⟨j, hj⟩ : ∃ j : Fin k, (S.val.orderEmbOfFin S.2) j = i := by
      have h_row_zero : Finset.image (fun j : Fin k => S.val.orderEmbOfFin S.2 j) Finset.univ = S.val := by
        refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun j _ => Finset.orderEmbOfFin_mem _ _ _) _
        simp [Finset.card_image_of_injective, Function.Injective, *]
      exact Exists.elim (Finset.mem_image.mp (h_row_zero.symm ▸ hiS)) fun j hj => ⟨j, hj.2⟩
    -- Since the row corresponding to $i$ in the submatrix is all zeros, the determinant of this submatrix is zero.
    have h_det_zero : Matrix.det (Matrix.of (fun i j => if (S.val.orderEmbOfFin S.2 i) = (T.val.orderEmbOfFin T.2 j) then f (T.val.orderEmbOfFin T.2 j) else 0) : Matrix (Fin k) (Fin k) ℂ) = 0 := by
      rw [Matrix.det_eq_zero_of_row_eq_zero j]; aesop
    exact h_det_zero

/-- The compound matrix of a unitary matrix is unitary. -/
lemma compoundMatrix_unitary (U : Matrix d d ℂ)
    (hU : U ∈ Matrix.unitaryGroup d ℂ) (k : ℕ) :
    compoundMatrix U k ∈ Matrix.unitaryGroup {S : Finset d // S.card = k} ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ← compoundMatrix_conjTranspose, ← compoundMatrix_mul,
    show Uᴴ * U = 1 by exact Matrix.mem_unitaryGroup_iff'.mp hU]
  simpa using compoundMatrix_diagonal (1 : d → ℂ) k

/-- The `k`-th compound matrix bundled as a unitary. -/
noncomputable def compoundUnitary (U : Matrix.unitaryGroup d ℂ) (k : ℕ) :
    Matrix.unitaryGroup {S : Finset d // S.card = k} ℂ :=
  ⟨compoundMatrix U.val k, compoundMatrix_unitary U.val U.property k⟩

omit [DecidableEq d] in
/-- The index set of the `k`-th compound matrix is nonempty when `k ≤ card d`. -/
lemma compound_card_pos (k : ℕ) (hk : k ≤ Fintype.card d) :
    0 < Fintype.card {S : Finset d // S.card = k} := by
  classical
  obtain ⟨S, _, hScard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset d)) hk
  exact Fintype.card_pos_iff.mpr ⟨⟨S, hScard⟩⟩

/-- The canonical zero index in `Fin (Fintype.card {S : Finset d // S.card = k})`,
witnessed by `compound_card_pos`. -/
def compoundZero (k : ℕ) (hk : k ≤ Fintype.card d) :
    Fin (Fintype.card {S : Finset d // S.card = k}) :=
  ⟨0, compound_card_pos k hk⟩

/--
The eigenvalues of the compound matrix of a Hermitian matrix are the products
of eigenvalues over k-subsets. More precisely, the singular values of
`compoundMatrix M k` are the square roots of products of eigenvalues of M†M
over k-subsets.
-/
lemma singularValues_compoundMatrix_eq (M : Matrix d d ℂ) (k : ℕ) :
    ∀ (S : {S : Finset d // S.card = k}),
    ∃ (j : {S : Finset d // S.card = k}),
    singularValues (compoundMatrix M k) j =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  unfold singularValues
  intro S
  have h_eigenvalues : ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k}, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self (compoundMatrix M k).conjTranspose) ∘ σ) = fun S => ∏ i : Fin k, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self M.conjTranspose)) (S.1.orderEmbOfFin S.2 i) := by
    apply IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    rotate_right
    exact compoundMatrix (Matrix.IsHermitian.eigenvectorUnitary (isHermitian_mul_conjTranspose_self M.conjTranspose)) k
    · exact compoundMatrix_unitary _ (by simp [Matrix.unitaryGroup]) _
    · have h_compoundMatrix_mul : compoundMatrix (M.conjTranspose * M) k = compoundMatrix M.conjTranspose k * compoundMatrix M k := by
        exact compoundMatrix_mul _ _ _
      have h_compoundMatrix_conjTranspose : compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
        exact compoundMatrix_conjTranspose M k
      have := Matrix.IsHermitian.spectral_theorem (isHermitian_mul_conjTranspose_self M.conjTranspose)
      convert congr_arg (fun x => compoundMatrix x k) this using 1 <;> simp [h_compoundMatrix_mul, h_compoundMatrix_conjTranspose]
      rw [compoundMatrix_mul, compoundMatrix_mul]
      rw [← compoundMatrix_conjTranspose]
      rw [compoundMatrix_diagonal]; simp [Matrix.mul_assoc]
      congr! 3
  obtain ⟨σ, hσ⟩ := h_eigenvalues
  use σ S; simp_all [funext_iff]
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num [Finset.prod_nonneg, Real.sqrt_nonneg]
  · rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => Real.mul_self_sqrt (_)]
    intro i hi; exact (by
    apply Matrix.eigenvalues_conjTranspose_mul_self_nonneg)
  · refine' Finset.prod_nonneg fun i _ => _
    exact eigenvalues_conjTranspose_mul_self_nonneg M _

/-- The product of nonneg values over a k-subset is at most the product of the
    k largest values. -/
lemma prod_le_prod_sorted {n : ℕ} {f : Fin n → ℝ}
    (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    (k : ℕ) (hk : k ≤ n)
    (g : Fin k → Fin n) (hg : Function.Injective g) :
    ∏ i : Fin k, f (g i) ≤ ∏ i : Fin k, f ⟨i.val, by omega⟩ := by
  -- The sorted values at positions g(i) are bounded by the sorted values at positions i,
  -- because g is injective so g(i) ≥ i (in the sorted sense), and f is antitone.
  -- We use the fact that for injective g : Fin k → Fin n, sorting g gives values ≥ identity.
  -- First sort g to get g' with g'(0) < g'(1) < ... < g'(k-1)
  -- Then g'(i) ≥ i since we're choosing k distinct values from Fin n
  -- So f(g'(i)) ≤ f(i) by antitonicity
  -- And the product is preserved under sorting (it's the same set of values)
  have h_exists_sorted : ∃ (g' : Fin k → Fin n),
      Function.Injective g' ∧ StrictMono g' ∧
      Finset.image g Finset.univ = Finset.image g' Finset.univ := by
    exact ⟨Finset.orderEmbOfFin (Finset.image g Finset.univ) (by simp [Finset.card_image_of_injective _ hg]),
      fun a b h => by simpa using h,
      fun a b h => by simpa using h,
      by ext x; simp⟩
  obtain ⟨g', hg'_inj, hg'_mono, hg'_eq⟩ := h_exists_sorted
  have h_prod_eq : ∏ i : Fin k, f (g i) = ∏ i : Fin k, f (g' i) := by
    rw [← Finset.prod_image (f := f) (fun a _ b _ h => hg (by simpa using h)),
        ← Finset.prod_image (f := f) (fun a _ b _ h => hg'_inj (by simpa using h))]
    exact Finset.prod_congr hg'_eq (fun _ _ => rfl)
  rw [h_prod_eq]
  apply Finset.prod_le_prod (fun i _ => hf_nn _) (fun i _ => ?_)
  apply hf
  -- Need: i.val ≤ (g' i).val for strictly monotone g'
  -- By induction: g'(0) ≥ 0, and g'(j+1) > g'(j) ≥ j implies g'(j+1) ≥ j+1
  suffices h : ∀ (m : ℕ) (hm : m < k), m ≤ (g' ⟨m, hm⟩).val from h i.val i.isLt
  intro m hm
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have ihm := ih (by omega)
    have := hg'_mono (show (⟨m, by omega⟩ : Fin k) < ⟨m + 1, hm⟩ by simp [Fin.lt_def])
    omega

/-- The 0th sorted singular value is the maximum of the singular values. -/
lemma singularValuesSorted_zero_eq_sup {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted A ⟨0, h⟩ = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp h))
      (singularValues A) := by
  refine' le_antisymm _ _
  · -- Since the list is sorted in decreasing order, every element in the list is less than or equal to the supremum of the original set.
    have h_le_sup : ∀ x ∈ Multiset.sort (Multiset.map (singularValues A) Finset.univ.val) (· ≥ ·), x ≤ Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨Classical.choose (Finset.card_pos.mp h)⟩) (singularValues A) := by
      aesop
    exact h_le_sup _ (by simp [singularValuesSorted])
  · have h_max_le_ge : ∀ i, singularValues A i ≤ singularValuesSorted A ⟨0, h⟩ := by
      intro i
      have h_max_le_ge : ∀ j, singularValuesSorted A j ≤ singularValuesSorted A ⟨0, h⟩ := by
        exact fun j => singularValuesSorted_antitone A (Nat.zero_le _)
      exact (by
      have h_max_le_ge : ∃ j, singularValues A i = singularValuesSorted A j := by
        have h_exists_j : singularValues A i ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
          simp [Multiset.mem_sort]
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp h_exists_j
        exact ⟨⟨j, by simpa using j.2⟩, hj.symm⟩
      aesop)
    exact Finset.sup'_le _ _ fun i _ => h_max_le_ge i

/-- Each singular value appears in the sorted list. -/
lemma singularValues_mem_sorted {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (i : e) :
    ∃ j : Fin (Fintype.card e), singularValues A i = singularValuesSorted A j := by
  have h_mem : singularValues A i ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
    simp [Multiset.mem_sort]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h_mem
  exact ⟨⟨j, by simpa using j.2⟩, hj.symm⟩

/-- Each sorted singular value appears among the original singular values. -/
lemma singularValuesSorted_mem_values {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (j : Fin (Fintype.card e)) :
    ∃ i : e, singularValuesSorted A j = singularValues A i := by
  have h_mem : singularValuesSorted A j ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
    simp [singularValuesSorted]
  rw [Multiset.mem_sort] at h_mem
  simp at h_mem
  obtain ⟨i, hi⟩ := h_mem
  exact ⟨i, hi.symm⟩

/-- Stronger version of `singularValues_compoundMatrix_eq` that exposes the permutation. -/
lemma singularValues_compoundMatrix_perm (M : Matrix d d ℂ) (k : ℕ) :
    ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k},
    ∀ S, singularValues (compoundMatrix M k) (σ S) =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  unfold singularValues
  have h_eigenvalues : ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k}, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self (compoundMatrix M k).conjTranspose) ∘ σ) = fun S => ∏ i : Fin k, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self M.conjTranspose)) (S.1.orderEmbOfFin S.2 i) := by
    apply IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    rotate_right
    exact compoundMatrix (Matrix.IsHermitian.eigenvectorUnitary (isHermitian_mul_conjTranspose_self M.conjTranspose)) k
    · exact compoundMatrix_unitary _ (by simp [Matrix.unitaryGroup]) _
    · have h_compoundMatrix_mul : compoundMatrix (M.conjTranspose * M) k = compoundMatrix M.conjTranspose k * compoundMatrix M k := by
        exact compoundMatrix_mul _ _ _
      have h_compoundMatrix_conjTranspose : compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
        exact compoundMatrix_conjTranspose M k
      have := Matrix.IsHermitian.spectral_theorem (isHermitian_mul_conjTranspose_self M.conjTranspose)
      convert congr_arg (fun x => compoundMatrix x k) this using 1 <;> simp [h_compoundMatrix_mul, h_compoundMatrix_conjTranspose]
      rw [compoundMatrix_mul, compoundMatrix_mul]
      rw [← compoundMatrix_conjTranspose]
      rw [compoundMatrix_diagonal]; simp [Matrix.mul_assoc]
      congr! 3
  obtain ⟨σ, hσ⟩ := h_eigenvalues
  use σ
  intro S
  simp_all [funext_iff]
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num [Finset.prod_nonneg, Real.sqrt_nonneg]
  · rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => Real.mul_self_sqrt (_)]
    intro i hi; exact (by apply Matrix.eigenvalues_conjTranspose_mul_self_nonneg)
  · refine Finset.prod_nonneg fun i _ => ?_
    exact eigenvalues_conjTranspose_mul_self_nonneg M _

/-- Converse of `singularValues_compoundMatrix_eq`: every singular value of the
    compound matrix is a product of singular values of M over some k-subset. -/
lemma singularValues_compoundMatrix_rev (M : Matrix d d ℂ) (k : ℕ)
    (j : {S : Finset d // S.card = k}) :
    ∃ (S : {S : Finset d // S.card = k}),
    singularValues (compoundMatrix M k) j =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  obtain ⟨σ, hσ⟩ := singularValues_compoundMatrix_perm M k
  exact ⟨σ.symm j, by rw [← hσ]; simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- There exists a bijection `σ : Fin (card d) ≃ d` such that
    `singularValues M (σ i) = singularValuesSorted M i` for all `i`. -/
lemma exists_sorting_equiv (M : Matrix d d ℂ) :
    ∃ σ : Fin (Fintype.card d) ≃ d,
    ∀ i, singularValues M (σ i) = singularValuesSorted M i := by
  -- Apply the lemma `exists_subset_prod_eq_sorted_prod` to obtain the bijection `σ`.
  have h_bij : ∃ σ : Fin (Fintype.card d) ≃ d, ∀ i, singularValues M (σ i) = singularValuesSorted M i := by
    have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      have h_multiset : Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) = Finset.univ.val.map (singularValues M) := by
        have h_multiset : Finset.univ.val = Multiset.map (fun i => (Fintype.equivFin d).symm i) (Finset.univ.val) := by
          exact Eq.symm (Multiset.map_univ_val_equiv (Fintype.equivFin d |> Equiv.symm))
        rw [h_multiset, Multiset.map_map]
        aesop
      have h_multiset_sorted : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.map (singularValues M) Finset.univ.val := by
        have h_multiset_sorted_eq : List.ofFn (singularValuesSorted M) = Multiset.sort (Multiset.map (singularValues M) Finset.univ.val) (· ≥ ·) := by
          refine' List.ext_get _ _ <;> simp [List.ofFn_eq_map] at *; aesop (simp_config := { singlePass := true })
        exact h_multiset_sorted_eq ▸ by simp
      rw [h_multiset, h_multiset_sorted]
    have h_perm : List.Perm (List.ofFn (singularValuesSorted M)) (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      exact Multiset.coe_eq_coe.mp h_perm
    have h_perm : ∃ σ : Fin (Fintype.card d) ≃ Fin (Fintype.card d), ∀ i, singularValuesSorted M i = singularValues M (Fintype.equivFin d |>.symm (σ i)) := by
      have h_perm : ∀ {l1 l2 : List ℝ}, l1.Perm l2 → ∃ σ : Fin l1.length ≃ Fin l2.length, ∀ i, l1.get i = l2.get (σ i) := by
        intros l1 l2 h_perm; induction' h_perm with l1 l2 h_perm ih <;> simp_all
        · obtain ⟨σ, hσ⟩ := ‹∃ σ : Fin l2.length ≃ Fin h_perm.length, ∀ i : Fin l2.length, l2[i] = h_perm[σ i]›; use Equiv.ofBijective (fun i => Fin.cases 0 (fun i => Fin.succ (σ i)) i) ⟨fun i j hij => ?_, fun i => ?_⟩
          simp_all [Fin.forall_fin_succ]
          · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> simp_all [Fin.ext_iff]
            simpa [Fin.ext_iff] using σ.injective (Fin.ext hij)
          · refine i.cases ?_ ?_
            · simp [Fin.exists_fin_succ]
            · simp only [Fin.exists_fin_succ, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj]
              exact fun i => Or.inr ⟨σ.symm i, by simp⟩
        · refine' ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, _⟩; simp [Fin.forall_fin_succ]; aesop
        · rename_i h₁ h₂ h₃ h₄
          obtain ⟨σ₁, hσ₁⟩ := h₃
          obtain ⟨σ₂, hσ₂⟩ := h₄
          use σ₁.trans σ₂
          simp [hσ₁, hσ₂]
      obtain ⟨σ, hσ⟩ := h_perm ‹_›
      refine ⟨Equiv.ofBijective (fun i => ⟨σ ⟨i, ?_⟩, ?_⟩) ⟨?_, ?_⟩, ?_⟩
      · simp
      · exact lt_of_lt_of_le (Fin.is_lt _) (by simp)
      · norm_num [Function.Injective, Function.Surjective]
        exact fun i j hij => Fin.ext <| by simpa [Fin.ext_iff] using σ.injective <| Fin.ext hij
      · intro b
        obtain ⟨a, ha⟩ : ∃ a : Fin (List.ofFn (singularValuesSorted M)).length, σ a = ⟨b, by simp⟩ := by
          exact σ.surjective _
        use ⟨a, lt_of_lt_of_le a.2 (by simp)⟩
        exact Fin.ext (by simp [ha])
      · intro i
        specialize hσ ⟨i, by simp⟩
        simp_all
    exact ⟨Equiv.trans h_perm.choose (Fintype.equivFin d |> Equiv.symm), fun i => h_perm.choose_spec i ▸ rfl⟩
  exact ⟨h_bij.choose, fun i => by simpa only [Equiv.symm_apply_eq] using h_bij.choose_spec i⟩

/-- For any k-subset S of d, the product of singular values over S is ≤ the
    product of the top k sorted singular values. -/
lemma prod_singularValues_subset_le_sorted_prod (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) (S : {S : Finset d // S.card = k}) :
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) ≤
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ := by
  obtain ⟨σ, hσ⟩ := exists_sorting_equiv M
  -- Define g : Fin k → Fin (card d) as σ⁻¹ ∘ (S.orderEmbOfFin)
  set g : Fin k → Fin (Fintype.card d) := fun i => σ.symm (S.1.orderEmbOfFin S.2 i)
  have hg_eq : ∀ i, singularValues M (S.1.orderEmbOfFin S.2 i) = singularValuesSorted M (g i) := by
    intro i
    simp [g]
    rw [← hσ]
    simp
  simp_rw [hg_eq]
  apply prod_le_prod_sorted (singularValuesSorted_antitone M) (singularValuesSorted_nonneg M) k hk g
  intro i j hij
  simpa [g] using congr_arg σ hij

set_option backward.isDefEq.respectTransparency false in
lemma exists_subset_prod_eq_sorted_prod (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∃ S : {S : Finset d // S.card = k},
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) =
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ := by
  by_contra h_contra
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (Fintype.card d) ≃ d, ∀ i : Fin (Fintype.card d), singularValues M (σ i) = singularValuesSorted M i := by
    have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
        have h_sorted : List.ofFn (singularValuesSorted M) = Multiset.sort (Multiset.map (singularValues M) Finset.univ.val) (· ≥ ·) := by
          refine' List.ext_get _ _ <;> simp
          exact fun n i => rfl
        simp [h_sorted, List.ofFn_eq_map]
        refine' Multiset.eq_of_le_of_card_le _ _ <;> simp [Multiset.le_iff_count]
        intro a; rw [Multiset.count_map]; simp [List.count]
        rw [← Multiset.toFinset_card_of_nodup] <;> norm_num [Finset.card_image_of_injective, Function.Injective]
        · rw [List.countP_eq_length_filter]
          simp [Finset.card]
          rw [← List.toFinset_card_of_nodup] <;> norm_num [List.nodup_finRange]
          · rw [Finset.card_filter]; simp [eq_comm, Fintype.equivFin]
            rw [← Multiset.toFinset_card_of_nodup] <;> norm_num [Finset.card_image_of_injective, Function.Injective]
            · refine' le_of_eq _; rw [Finset.card_filter, Finset.card_filter]; rw [← Finset.sum_bij (fun x _ => (Fintype.equivFin d) x)]; aesop
              · exact fun x _ y _ h => Fintype.equivFin d |>.injective h ▸ rfl
              · exact fun b _ => ⟨(Fintype.equivFin d).symm b, Finset.mem_univ _, by simp⟩
              · simp [Fintype.equivFin]
            · exact Multiset.Nodup.filter _ (Finset.nodup _)
          · exact List.Nodup.filter _ (List.nodup_finRange _)
        · exact Multiset.Nodup.filter _ (Finset.nodup _)
      exact h_perm.trans (by simp)
    have h_perm : List.Perm (List.ofFn (singularValuesSorted M)) (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      exact Multiset.coe_eq_coe.mp h_perm
    have h_perm : ∃ σ : Fin (Fintype.card d) ≃ Fin (Fintype.card d), List.ofFn (singularValuesSorted M) = List.map (fun i => singularValues M ((Fintype.equivFin d).symm (σ i))) (List.finRange (Fintype.card d)) := by
      have := h_perm
      have h_perm : ∀ {l₁ l₂ : List ℝ}, List.Perm l₁ l₂ → ∃ σ : Fin l₁.length ≃ Fin l₂.length, l₁ = List.map (fun i => l₂.get (σ i)) (List.finRange l₁.length) := by
        intro l₁ l₂ h_perm
        induction' h_perm with l₁ l₂ h_perm ih
        · aesop
        · rename_i a_ih
          obtain ⟨σ, hσ⟩ := a_ih
          use Equiv.ofBijective (fun i => Fin.cases ⟨0, by simp⟩ (fun i => Fin.succ (σ i)) i) ⟨fun i j hij => ?_, fun i => ?_⟩
          · simp [List.finRange_succ] at *
            exact hσ
          · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> simp [Fin.ext_iff] at hij ⊢
            simpa [Fin.ext_iff] using σ.injective (Fin.ext hij) |> fun h => by simpa [Fin.ext_iff] using h;
          · rcases i with ⟨_ | i, hi⟩
            · exact ⟨⟨0, by simp⟩, rfl⟩
            · exact ⟨Fin.succ (σ.symm ⟨i, by simpa using hi⟩), by simp⟩
        · use Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩; simp [List.finRange_succ]
          refine' List.ext_get _ _ <;> simp [Function.comp]
          intro n hn; rcases n with (_ | _ | n) <;> trivial
        · rename_i h₁ h₂ h₃ h₄
          obtain ⟨σ₁, hσ₁⟩ := h₃
          obtain ⟨σ₂, hσ₂⟩ := h₄
          use σ₁.trans σ₂
          simp [hσ₁, hσ₂]
      obtain ⟨σ, hσ⟩ := h_perm ‹_›
      simp [List.ofFn_eq_map] at hσ ⊢
      generalize_proofs at *; (
      exact ⟨Equiv.ofBijective (fun i => ⟨σ ⟨i, by simp⟩, by solve_by_elim⟩) ⟨fun i j hij => by simpa [Fin.ext_iff] using σ.injective (Fin.ext <| by simpa [Fin.ext_iff] using hij), fun i => by
        obtain ⟨a, ha⟩ := σ.surjective ⟨i, by simp⟩
        exact ⟨⟨a, by simpa using a.2⟩, Fin.ext <| by simpa [Fin.ext_iff] using congr_arg Fin.val ha⟩⟩, fun i => by simpa [Fin.ext_iff] using congr_arg (fun l => l[i]!) hσ⟩)
    obtain ⟨σ, hσ⟩ := h_perm
    use Equiv.ofBijective (fun i => (Fintype.equivFin d).symm (σ i)) ⟨fun i j hij => by simpa [Fin.ext_iff] using σ.injective (by simpa [Fin.ext_iff] using hij), fun i => by
      exact ⟨σ.symm (Fintype.equivFin d i), by simp⟩;⟩
    intro i
    replace hσ := congr_arg (fun l => l[i]!) hσ
    simp_all
  refine' h_contra ⟨⟨Finset.image σ (Finset.univ.filter fun i => i.val < k), _⟩, _⟩ <;> simp_all
  rw [Finset.card_image_of_injective _ σ.injective, Finset.card_eq_of_bijective]
  use fun i hi => ⟨i, by linarith⟩
  all_goals norm_num [Fin.ext_iff] at *
  have h_prod_eq : ∏ x ∈ Finset.image σ (Finset.univ.filter fun i : Fin (Fintype.card d) => i.val < k), singularValues M x = ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ := by
    rw [Finset.prod_image] <;> simp [hσ]
    refine' Finset.prod_bij (fun i hi => ⟨i, by linarith [Fin.is_lt i, Finset.mem_filter.mp hi]⟩) _ _ _ _ <;> simp [Fin.ext_iff]
    exact fun b => ⟨⟨b, by linarith [Fin.is_lt b]⟩, by simp, rfl⟩
  convert h_prod_eq using 1
  rw [← Finset.prod_image]
  · congr! 1
    refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ => _) _ <;> simp [Finset.card_image_of_injective, Function.Injective]
    rw [Finset.card_eq_of_bijective]
    use fun i hi => ⟨i, by linarith⟩
    · exact fun a ha => ⟨a, Finset.mem_filter.mp ha |>.2, rfl⟩
    · grind
    · simp +contextual [Fin.ext_iff]
  · exact fun x _ y _ hxy => by simpa [Fin.ext_iff] using hxy

lemma prod_singularValuesSorted_eq_compoundSV (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ =
    singularValuesSorted (compoundMatrix M k) ⟨0, by
      have : Fintype.card {S : Finset d // S.card = k} = (Fintype.card d).choose k := by
        simp [Fintype.card_subtype]
      rw [this]; exact Nat.choose_pos hk⟩ := by
  set hcard : 0 < Fintype.card {S : Finset d // S.card = k} := by
    simp [Fintype.card_subtype]; exact Nat.choose_pos hk
  apply le_antisymm
  · obtain ⟨S₀, hS₀⟩ := exists_subset_prod_eq_sorted_prod M k hk
    obtain ⟨j₀, hj₀⟩ := singularValues_compoundMatrix_eq M k S₀
    obtain ⟨idx, hidx⟩ := singularValues_mem_sorted (compoundMatrix M k) j₀
    rw [← hS₀, ← hj₀, hidx]
    have : NeZero (Fintype.card {S : Finset d // S.card = k}) := ⟨by omega⟩
    exact singularValuesSorted_antitone (compoundMatrix M k) (Fin.zero_le idx)
  · obtain ⟨j, hj⟩ := singularValuesSorted_mem_values (compoundMatrix M k) ⟨0, hcard⟩
    obtain ⟨S, hS⟩ := singularValues_compoundMatrix_rev M k j
    rw [hj, hS]
    exact prod_singularValues_subset_le_sorted_prod M k hk S

/--
The **Rayleigh quotient bound**:
For a Hermitian matrix H with eigenvalues λ, we have
`v† H v ≤ (max λ) · v† v` for all v. -/
lemma IsHermitian.inner_le_sup_eigenvalue_mul_inner
    {e : Type*} [Fintype e] [DecidableEq e]
    (H : Matrix e e ℂ) (hH : H.IsHermitian)
    (he : 0 < Fintype.card e)
    (v : e → ℂ) :
    Complex.re (star v ⬝ᵥ H.mulVec v) ≤
    Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp he))
      hH.eigenvalues * Complex.re (star v ⬝ᵥ v) := by
  have := hH.spectral_theorem
  -- Let $w = U^* v$, then $v^* H v = w^* D w$.
  set w : e → ℂ := star (hH.eigenvectorUnitary : Matrix e e ℂ) |> Matrix.mulVec <| v
  have h_eq : (star v ⬝ᵥ H *ᵥ v).re = (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re := by
    replace this := congr_arg (fun m => star v ⬝ᵥ m *ᵥ v) this; simp_all [Matrix.mul_assoc]
    simp +zetaDelta at *
    simp [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    congr! 3
    ext i j; simp [Matrix.mul_apply, Matrix.diagonal]
  -- Since $D$ is diagonal with eigenvalues $\lambda_i$, we have $w^* D w = \sum_{i} \lambda_i |w_i|^2$.
  have h_diag : (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re = ∑ i, (hH.eigenvalues i) * ‖w i‖ ^ 2 := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm,]
    simp [Complex.normSq, Complex.sq_norm, diagonal]
    rw [← Finset.sum_sub_distrib]; refine' Finset.sum_congr rfl fun i hi => _; rw [Finset.sum_eq_single i, Finset.sum_eq_single i] <;> simp +contextual; ring_nf
    · exact fun j hj => Or.inl (by rw [if_neg (Ne.symm hj)]; norm_num)
    · exact fun j hj => Or.inl (by rw [if_neg (Ne.symm hj)]; norm_num)
  -- Since $U$ is unitary, we have $\|w\|^2 = \|v\|^2$.
  have h_unitary : ∑ i, ‖w i‖ ^ 2 = (star v ⬝ᵥ v).re := by
    have h_unitary : ∀ (U : Matrix e e ℂ), U.conjTranspose * U = 1 → ∀ (v : e → ℂ), ∑ i, ‖(U.mulVec v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      intro U hU v
      have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ v) := by
        have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ (Uᴴ * U).mulVec v) := by
          simp [Matrix.mulVec, dotProduct]
          simp [Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
          exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) |> Eq.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h_unitary, hU, Matrix.one_mulVec]
      convert congr_arg Complex.re h_unitary using 1 <;> simp [sq]; ring_nf!
      · simp [dotProduct, sq]; ring_nf!
        simp [Complex.normSq, Complex.sq_norm]; ring_nf!
      · simp [dotProduct]
        simp [← sq, Complex.normSq_apply, Complex.sq_norm]
    convert h_unitary (star (hH.eigenvectorUnitary : Matrix e e ℂ)) _ v using 1 <;> norm_num [Matrix.mulVec, dotProduct]
    · norm_num [Complex.normSq, Complex.sq_norm]
    · simp [Matrix.star_eq_conjTranspose]
      simp [Matrix.IsHermitian.eigenvectorUnitary]
  rw [h_eq, h_diag, ← h_unitary, Finset.mul_sum _ _ _]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Finset.le_sup' (fun i => hH.eigenvalues i) (Finset.mem_univ i)) (sq_nonneg _)

/- All eigenvalues of `A† A` are bounded by (max singular value)². -/
lemma eigenvalue_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (i : e) :
  (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 := by
  -- By definition of singular values, we know that $\sigma_i(A)^2 = \lambda_i(A^*A)$.
  have h_singular_value_squared : ∀ i, (singularValues A i) ^ 2 = (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i := by
    intro i
    simp [singularValues]
    rw [Real.sq_sqrt (_)]
    convert Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i using 1
  rw [← h_singular_value_squared i]
  gcongr
  · exact Real.sqrt_nonneg _
  · convert singularValuesSorted_zero_eq_sup A h |> fun h => h.ge.trans' _
    exact Finset.le_sup' (fun i => singularValues A i) (Finset.mem_univ i)

/-- The quadratic form of `A† A` is bounded by (max singular value)² * ‖v‖². -/
lemma quadratic_form_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (v : e → ℂ) :
  Complex.re (star v ⬝ᵥ (A.conjTranspose * A).mulVec v) ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
  apply le_trans (IsHermitian.inner_le_sup_eigenvalue_mul_inner (Aᴴ * A) (by
    simp [Matrix.IsHermitian]) h v)
  apply_rules [mul_le_mul_of_nonneg_right, Finset.sup'_le]
  · intro i _
    convert! eigenvalue_le_singularValuesSorted_sq A h i using 1
    simp [Matrix.conjTranspose_conjTranspose]
  · simp [dotProduct]
    exact Finset.sum_nonneg fun _ _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- The largest singular value of a matrix product is at most the product of the
largest singular values: `σ₁(M * N) ≤ σ₁(M) * σ₁(N)`.
This is operator-norm submultiplicativity. -/
lemma singularValuesSorted_mul_le {e : Type*} [Fintype e] [DecidableEq e]
    (M N : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted (M * N) ⟨0, h⟩ ≤
    singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
  rw [singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup]
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN).
  have h_eigenvalue_le : ∀ i, (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := by
    intro i
    have h_eigenvalue_le : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 := by
      -- By the properties of singular values and eigenvalues, we know that the eigenvalues of $(MN)^* (MN)$ are bounded by the product of the squares of the singular values of $M$ and $N$.
      have h_eigenvalue_bound : ∀ (v : e → ℂ), Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
        intro v
        have h_quadratic_form : Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) := by
          have := quadratic_form_le_singularValuesSorted_sq M h (N.mulVec v)
          convert this using 1 <;> simp [Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
        have h_quadratic_form_N : Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) ≤ (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
          convert quadratic_form_le_singularValuesSorted_sq N h v using 1
        simpa only [mul_assoc] using h_quadratic_form.trans (mul_le_mul_of_nonneg_left h_quadratic_form_N (sq_nonneg _))
      convert h_eigenvalue_bound ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvectorBasis i) using 1
      · have := (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues_eq i; aesop
      · simp [dotProduct]
        have := (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvectorBasis.orthonormal
        rw [orthonormal_iff_ite] at this
        simp_all [Complex.ext_iff, inner]
    linarith
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN) and take the square root.
  have h_sqrt_eigenvalue_le : ∀ i, singularValues (M * N) i ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
    intro i
    have h_sqrt_eigenvalue_le_i : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := h_eigenvalue_le i
    have h_sqrt_eigenvalue_le_i' : Real.sqrt ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i) ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (singularValuesSorted_nonneg M ⟨0, h⟩) (singularValuesSorted_nonneg N ⟨0, h⟩), h_sqrt_eigenvalue_le_i⟩
    exact h_sqrt_eigenvalue_le_i' |> le_trans (by
    exact le_rfl)
  simp_all [Finset.sup'_le_iff]
  convert h_sqrt_eigenvalue_le using 1
  rw [singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup]

/-- Horn's inequality (weak log-majorization of singular values):
For all `k`, `∏_{i<k} σ↓ᵢ(AB) ≤ ∏_{i<k} σ↓ᵢ(A) · σ↓ᵢ(B)`.
This follows from submultiplicativity of the operator norm applied to
exterior powers of the matrices. -/
lemma horn_weak_log_majorization (A B : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩ ≤
    ∏ i : Fin k, (singularValuesSorted A ⟨i.val, by omega⟩ *
                   singularValuesSorted B ⟨i.val, by omega⟩) := by
  -- Rewrite the RHS as (prod of σ↓(A)) * (prod of σ↓(B))
  rw [Finset.prod_mul_distrib]
  -- Use the compound matrix characterisation and submultiplicativity
  have hcard : 0 < Fintype.card {S : Finset d // S.card = k} := by
    have : Fintype.card {S : Finset d // S.card = k} = (Fintype.card d).choose k := by
      simp [Fintype.card_subtype]
    rw [this]; exact Nat.choose_pos hk
  calc ∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩
      = singularValuesSorted (compoundMatrix (A * B) k) ⟨0, hcard⟩ :=
        prod_singularValuesSorted_eq_compoundSV (A * B) k hk
    _ = singularValuesSorted (compoundMatrix A k * compoundMatrix B k) ⟨0, hcard⟩ := by
        rw [compoundMatrix_mul]
    _ ≤ singularValuesSorted (compoundMatrix A k) ⟨0, hcard⟩ *
        singularValuesSorted (compoundMatrix B k) ⟨0, hcard⟩ :=
        singularValuesSorted_mul_le _ _ hcard
    _ = (∏ i : Fin k, singularValuesSorted A ⟨i.val, by omega⟩) *
        (∏ i : Fin k, singularValuesSorted B ⟨i.val, by omega⟩) := by
        rw [← prod_singularValuesSorted_eq_compoundSV A k hk,
            ← prod_singularValuesSorted_eq_compoundSV B k hk]

/-! ### Weak log-majorization implies sum of powers inequality -/

/-- Raising nonneg antitone sequences to a positive power preserves antitonicity. -/
lemma rpow_antitone_of_nonneg_antitone {n : ℕ}
    {f : Fin n → ℝ} (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    {r : ℝ} (hr : 0 < r) :
    Antitone (fun i => f i ^ r) := by
  exact fun i j hij => Real.rpow_le_rpow (hf_nn _) (hf hij) hr.le

/-- Weak log-majorization is preserved under positive powers. -/
lemma rpow_preserves_weak_log_maj {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩)
    {r : ℝ} (hr : 0 < r) :
    ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, (fun j => x j ^ r) ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, (fun j => y j ^ r) ⟨i.val, by omega⟩ := by
  intro k hk
  convert Real.rpow_le_rpow _ (h_log_maj k hk) hr.le using 1 <;>
    norm_num [Real.finsetProd_rpow _ _ fun i _ => hx_nn _,
              Real.finsetProd_rpow _ _ fun i _ => hy_nn _]
  exact Finset.prod_nonneg fun _ _ => hx_nn _

/-
The Abel summation identity (a rewriting of the sum) gives:
∑_{i=0}^{n-1} x_i * d_i = x_{n-1} * D_{n-1} + ∑_{i=0}^{n-2} (x_i - x_{i+1}) * D_i
(This is essentially Finset.sum_range_by_parts with f = x and g = d.)
Each term is nonneg because:
- x_{n-1} ≥ 0 (positive) and D_{n-1} ≥ 0 (see below)
- x_i - x_{i+1} ≥ 0 (x is antitone) and D_i ≥ 0 (see below)
D_k = ∑_{j=0}^k log(y_j/x_j) = log(∏_{j=0}^k y_j/x_j) = log(∏ y_j / ∏ x_j) ≥ log(1) = 0
because ∏ y_j ≥ ∏ x_j (weak log-majorization) and both products are positive.
So ∑ x_i * d_i is a sum of nonneg terms, hence ≥ 0.
Use Finset.sum_range_by_parts from Mathlib. The key Mathlib lemma is:
Finset.sum_range_by_parts f g n = f (n-1) • ∑_{i<n} g i - ∑_{i<n-1} (f(i+1) - f(i)) • ∑_{j<i+1} g j
Here f i = x ⟨i, ...⟩ (antitone) and g i = log(y ⟨i,...⟩ / x ⟨i,...⟩).
Actually, it may be easier to prove this directly by induction on n, without using Finset.sum_range_by_parts. The induction step would split off the last term and use the IH.
For the direct induction approach on n:
- n = 0: sum is empty, 0 ≥ 0.
- n = 1: x_0 * log(y_0/x_0) ≥ 0 since x_0 > 0 and log(y_0/x_0) ≥ 0 (from ∏_{i<1} x_i ≤ ∏_{i<1} y_i, i.e., x_0 ≤ y_0, so y_0/x_0 ≥ 1, so log(y_0/x_0) ≥ 0).
- n+1 → n+2: Split ∑_{i=0}^{n+1} x_i * log(y_i/x_i) = ∑_{i=0}^{n} x_i * log(y_i/x_i) + x_{n+1} * log(y_{n+1}/x_{n+1}).
  Now ∑_{i=0}^{n} x_i * log(y_i/x_i) ≥ ∑_{i=0}^{n} x_{n+1} * log(y_i/x_i) (since x_i ≥ x_{n+1} and log(y_i/x_i) could be negative, but x_i * log(y_i/x_i) ≥ x_{n+1} * log(y_i/x_i) when log(y_i/x_i) ≥ 0).
Hmm, this doesn't work cleanly because log(y_i/x_i) can be negative for some i.
Better approach: prove it directly using the Abel summation identity and nonnegativity of each term.
-/
lemma sum_mul_log_nonneg_of_weak_log_maj {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_pos : ∀ i, 0 < x i) (hy_pos : ∀ i, 0 < y i)
    (hx_anti : Antitone x)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩) :
    0 ≤ ∑ i, x i * Real.log (y i / x i) := by
  by_contra h_neg
  -- Let $d_i = \log(y_i / x_i)$ and $D_k = \sum_{j=0}^{k} d_j$.
  set d : Fin n → ℝ := fun i => Real.log (y i / x i)
  set D : Fin n → ℝ := fun k => ∑ i ∈ Finset.Iic k, d i
  -- By Abel's summation formula, we have $\sum_{i=0}^{n-1} x_i d_i = x_{n-1} D_{n-1} + \sum_{i=0}^{n-2} (x_i - x_{i+1}) D_i$.
  have hn : n ≠ 0 := by rintro rfl; simp at h_neg
  have h_abel : ∑ i, x i * d i = x ⟨n - 1, by omega⟩ * D ⟨n - 1, by omega⟩ + ∑ i : Fin (n - 1),
      (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) * D ⟨i.val, by omega⟩ := by
    rcases n with ⟨⟩ <;> norm_num at *
    rename_i n
    have h_abel : ∀ m : Fin (n + 1), ∑ i ∈ Finset.Iic m, x i * d i = x m * D m + ∑ i ∈ Finset.Iio m, (x i - x (i + 1)) * D i := by
      intro m
      induction' m using Fin.inductionOn with m ih
      · simp +zetaDelta at *
        rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0] <;> aesop
      · rw [show (Finset.Iic (Fin.succ m) : Finset (Fin (n + 1))) = Finset.Iic (Fin.castSucc m) ∪ { Fin.succ m } from ?_, Finset.sum_union] <;> norm_num [Finset.sum_singleton, Finset.sum_union, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
        · rw [show (Finset.Iio (Fin.succ m) : Finset (Fin (n + 1))) = Finset.Iio (Fin.castSucc m) ∪ { Fin.castSucc m } from ?_, Finset.sum_union] <;> norm_num [Finset.sum_singleton, Finset.sum_union, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
          · rw [ih]
            ring_nf!
            rw [show (Finset.Iic (Fin.succ m) : Finset (Fin (n + 1))) = Finset.Iic (Fin.castSucc m) ∪ { Fin.succ m } from ?_, Finset.sum_union] <;> norm_num; ring!
            ext i; simp [Finset.mem_Iic, Finset.mem_insert]
            exact ⟨fun hi => or_iff_not_imp_left.mpr fun hi' => Nat.le_of_lt_succ <| hi.lt_of_ne hi', fun hi => hi.elim (fun hi => hi.symm ▸ le_rfl) fun hi => Nat.le_trans hi (Nat.le_succ _)⟩
          · ext i; simp [Fin.lt_def, Fin.le_iff_val_le_val]
        · ext i; simp [Finset.mem_Iic, Finset.mem_insert]
          exact ⟨fun hi => or_iff_not_imp_left.mpr fun hi' => Nat.le_of_lt_succ <| hi.lt_of_ne hi', fun hi => hi.elim (fun hi => hi.symm ▸ le_rfl) fun hi => Nat.le_trans hi (Nat.le_succ _)⟩
    convert h_abel ⟨n, Nat.lt_succ_self _⟩ using 1
    · rw [show (Iic ⟨n, Nat.lt_succ_self _⟩ : Finset (Fin (n + 1))) = Finset.univ from Finset.eq_univ_of_forall fun i => Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)]
    · refine' congr rfl (Finset.sum_bij (fun i hi => ⟨i, by omega⟩) _ _ _ _) <;> simp [Fin.add_def, Nat.mod_eq_of_lt]
      · exact fun i j h => Fin.ext h
      · exact fun i hi => ⟨⟨i, by linarith [Fin.is_lt i, show (i : ℕ) < n from hi]⟩, rfl⟩
  -- Since $D_k \geq 0$ for all $k$, we have $x_{n-1} D_{n-1} \geq 0$ and $(x_i - x_{i+1}) D_i \geq 0$ for all $i$.
  have h_nonneg : ∀ k : Fin n, 0 ≤ D k := by
    intro k
    have h_prod : ∏ i ∈ Finset.Iic k, y i ≥ ∏ i ∈ Finset.Iic k, x i := by
      specialize h_log_maj (k + 1) (by linarith [Fin.is_lt k])
      rw [show (Finset.Iic k : Finset (Fin n)) = Finset.image (fun i : Fin (k + 1) => ⟨i, by linarith [Fin.is_lt k, Fin.is_lt i]⟩) Finset.univ from ?_, Finset.prod_image] <;> norm_num
      · rwa [Finset.prod_image <| by intros i hi j hj hij; simpa [Fin.ext_iff] using hij]
      · intro i j hij
        exact Fin.ext <| by simpa using congr_arg Fin.val hij
      · ext ⟨i, hi⟩; simp [Fin.ext_iff, Fin.le_iff_val_le_val]
        exact ⟨fun hi' => ⟨⟨i, by linarith [Fin.is_lt k]⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ Nat.le_trans (Nat.le_of_lt_succ (by linarith [Fin.is_lt a, Fin.is_lt k])) (Nat.le_refl _)⟩
    simp +zetaDelta at *
    rw [← Real.log_prod fun i hi => ne_of_gt (div_pos (hy_pos i) (hx_pos i))]; exact Real.log_nonneg (by rw [Finset.prod_div_distrib]; exact by rw [le_div_iff₀ (Finset.prod_pos fun i hi => hx_pos i)]; linarith)
  exact h_neg <| h_abel.symm ▸ add_nonneg (mul_nonneg (le_of_lt (hx_pos _)) (h_nonneg _)) (Finset.sum_nonneg fun i hi => mul_nonneg (sub_nonneg.mpr (hx_anti <| Nat.le_succ _)) (h_nonneg _))

/-
PROBLEM
For positive reals a, b: b - a ≥ a · log(b/a).
Equivalently: t - 1 ≥ log(t) for t = b/a.
PROVIDED SOLUTION
We need b - a ≥ a * log(b/a) for a, b > 0. Equivalently, dividing by a > 0: b/a - 1 ≥ log(b/a). Let t = b/a > 0. Then we need t - 1 ≥ log(t), which is equivalent to log(t) ≤ t - 1. This is Real.log_le_sub_one_of_le or follows from Real.add_one_le_exp: for any x, 1 + x ≤ exp(x). Taking x = log(t): 1 + log(t) ≤ exp(log(t)) = t, so log(t) ≤ t - 1. Multiply by a > 0 to get a * log(b/a) ≤ a * (b/a - 1) = b - a.
-/
lemma sub_ge_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b - a ≥ a * Real.log (b / a) := by
  nlinarith [Real.log_le_sub_one_of_pos (div_pos hb ha), mul_div_cancel₀ b ha.ne']

/- Weak log-majorization of nonneg antitone sequences implies the sum inequality ∑ x_i ≤ ∑ y_i. -/
lemma weak_log_maj_sum_le {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (hx_anti : Antitone x) (hy_anti : Antitone y)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩) :
    ∑ i, x i ≤ ∑ i, y i := by
  induction' n with n ih
  · norm_num +zetaDelta at *
  · by_cases h_last : x (Fin.last n) = 0
    · simp [Fin.sum_univ_castSucc, h_last]
      refine le_add_of_le_of_nonneg (ih (fun i => hx_nn _) (fun i => hy_nn _) (fun i j hij => hx_anti hij) (fun i j hij => hy_anti hij) ?_) (hy_nn _)
      intro k hk
      simp
      exact h_log_maj k (by linarith)
    · -- Since $x_{\text{last}} > 0$, we have $x_i > 0$ for all $i$.
      have hx_pos : ∀ i, 0 < x i := by
        exact fun i => lt_of_lt_of_le (lt_of_le_of_ne (hx_nn _) (Ne.symm h_last)) (hx_anti (Fin.le_last _))
      have hy_pos : ∀ i, 0 < y i := by
        intro i; specialize h_log_maj (n + 1) le_rfl; contrapose! h_log_maj; simp_all [Fin.prod_univ_castSucc]
        exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (Finset.prod_nonneg fun _ _ => hy_nn _) (by linarith [hy_anti (show i ≤ Fin.last n from Fin.le_last i)])) (mul_pos (Finset.prod_pos fun _ _ => hx_pos _) (hx_pos _))
      have h_sum_mul_log_nonneg : 0 ≤ ∑ i, x i * Real.log (y i / x i) := by
        apply sum_mul_log_nonneg_of_weak_log_maj (fun i => hx_pos i) (fun i => hy_pos i) hx_anti (fun k hk => h_log_maj k hk)
      have h_sum_mul_log_nonneg : ∑ i, (y i - x i) ≥ ∑ i, x i * Real.log (y i / x i) := by
        exact Finset.sum_le_sum fun i _ => by have := sub_ge_mul_log_div (hx_pos i) (hy_pos i); ring_nf at *; linarith
      norm_num at *; linarith

/-- Weak log-majorization of nonneg antitone sequences implies the sum of
powers inequality. -/
lemma weak_log_maj_sum_rpow_le {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (hx_anti : Antitone x) (hy_anti : Antitone y)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩)
    {r : ℝ} (hr : 0 < r) :
    ∑ i, x i ^ r ≤ ∑ i, y i ^ r := by
  apply weak_log_maj_sum_le
  · exact fun i => Real.rpow_nonneg (hx_nn i) r
  · exact fun i => Real.rpow_nonneg (hy_nn i) r
  · exact rpow_antitone_of_nonneg_antitone hx_anti hx_nn hr
  · exact rpow_antitone_of_nonneg_antitone hy_anti hy_nn hr
  · exact rpow_preserves_weak_log_maj hx_nn hy_nn h_log_maj hr

/-! ## Key singular value inequality for products -/

lemma sum_rpow_singularValues_mul_le (A B : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ r ≤
    ∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r) := by
  have h_rw : ∀ i : Fin (Fintype.card d),
      singularValuesSorted A i ^ r * singularValuesSorted B i ^ r =
      (singularValuesSorted A i * singularValuesSorted B i) ^ r := by
    intro i
    rw [Real.mul_rpow (singularValuesSorted_nonneg A i) (singularValuesSorted_nonneg B i)]
  simp_rw [h_rw]
  apply weak_log_maj_sum_rpow_le
  · exact fun i => singularValuesSorted_nonneg (A * B) i
  · exact fun i => mul_nonneg (singularValuesSorted_nonneg A i) (singularValuesSorted_nonneg B i)
  · exact singularValuesSorted_antitone (A * B)
  · exact antitone_mul_of_antitone_nonneg
      (singularValuesSorted_antitone A) (singularValuesSorted_antitone B)
      (singularValuesSorted_nonneg A) (singularValuesSorted_nonneg B)
  · exact horn_weak_log_majorization A B
  · exact hr

/-! ## Hölder inequality for singular values -/

/--
The finite-sum Hölder inequality applied to sequences of r-th powers of
sorted singular values.

With conjugate exponents `p' = p/r > 1` and `q' = q/r > 1` (which satisfy
`1/p' + 1/q' = 1` when `1/r = 1/p + 1/q`), this gives:
  `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}`

Note: The sums on the RHS don't depend on the ordering, so we can replace
sorted singular values with unsorted ones.
-/
lemma holder_step_for_singularValues (A B : Matrix d d ℂ)
    {r p q : ℝ} (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    (∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r)) ≤
    (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) ^ (r / p) *
    (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ q) ^ (r / q) := by
  have h_holder : (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) * (singularValuesSorted B i ^ r)) ≤ (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) ^ (p / r)) ^ (r / p) * (∑ i : Fin (Fintype.card d), (singularValuesSorted B i ^ r) ^ (q / r)) ^ (r / q) := by
    have := @Real.inner_le_Lp_mul_Lq
    convert @this (Fin (Fintype.card d)) Finset.univ (fun i => singularValuesSorted A i ^ r) (fun i => singularValuesSorted B i ^ r) (p / r) (q / r) _ using 1 <;> norm_num [hr.ne', hp.ne', hq.ne', div_eq_mul_inv]
    · simp only [abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg A _) _),
              abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg B _) _)]
    · constructor <;> norm_num [hr.ne', hp.ne', hq.ne'] at hpqr ⊢ <;> ring_nf at hpqr ⊢ <;> nlinarith [inv_pos.2 hr, inv_pos.2 hp, inv_pos.2 hq, mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hp.ne', mul_inv_cancel₀ hq.ne']
  convert h_holder using 3 <;> push_cast [← Real.rpow_mul (singularValuesSorted_nonneg _ _), mul_div_cancel₀ _ hr.ne'] <;> ring_nf

end
