/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa, Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.CFC

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!

# Projectors associated to Hermitian matrices

 * `projector`: The `HermitianMat` that projects onto a given submodule
 * `supportProj`: The `HermitianMat` that projects onto the range (nonzero eigenvalues)
 * `kerProj`: The `HermitianMat` that projects onto the kernel
 * `projLE`: With notation `{A ≤ₚ B}`, `projLE A B` is the projector onto the nonnegative
   eigenspace of `B - A`.
 * `projLT`: With notation `{A <ₚ B}`, `projLT A B` is the projector onto the positive
   eigenspace of `B - A`.
 * Positive and negative part, written `A⁺` and `A⁻`, give the restriction of a HermitianMat
   onto its positive (resp. negative) eigenvalues; equivalently, it's nonnegative (resp.
   nonpositive) eigenvalues.
-/

@[expose] public section

noncomputable section
namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] (S : Submodule 𝕜 (EuclideanSpace 𝕜 n))

variable (A B : HermitianMat n 𝕜)

open scoped InnerProductSpace

/--
Given a Submodule (EuclideanSpace ...) to HermitianMat, this gives the projector onto that subspace,
i.e. a matrix that squares to itself, preserves vectors in the submodule, and zeroes out anything
in the orthogonal complement of that submodule.
-/
noncomputable def projector (S : Submodule 𝕜 (EuclideanSpace 𝕜 n)) : HermitianMat n 𝕜 :=
  let P := S.subtypeL.comp S.orthogonalProjectionOnto
  ⟨P.toMatrix (EuclideanSpace.basisFun n 𝕜).toBasis (EuclideanSpace.basisFun n 𝕜).toBasis, by
    ext i j
    have h1 := S.inner_starProjection_left_eq_right (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp_all [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left]
    exact h1⟩

theorem projector_add_orthogonal : projector S + projector Sᗮ = 1 := by
  unfold projector;
  erw [ Subtype.mk_eq_mk ];
  ext i j; simp [ LinearMap.toMatrix_apply, Matrix.one_apply ] ;

theorem projector_nonneg : 0 ≤ projector S := by
  rw [zero_le_iff]
  unfold projector
  let P := S.subtypeL.comp S.orthogonalProjectionOnto
  have hP : P.toLinearMap.IsSymmetricProjection := by
    simpa [Submodule.starProjection, P] using
      (Submodule.isSymmetricProjection_starProjection (U := S))
  exact LinearMap.posSemidef_toMatrix_iff _ |>.2
    ((LinearMap.IsIdempotentElem.isPositive_iff_isSymmetric hP.1).2 hP.2)

@[simp]
theorem projector_ker : (projector S).ker = Sᗮ := by
  ext v
  change (Matrix.toEuclideanLin
      (LinearMap.toMatrix (PiLp.basisFun 2 𝕜 n) (PiLp.basisFun 2 𝕜 n)
        (S.subtypeL.comp S.orthogonalProjectionOnto)) v = 0 ↔ v ∈ Sᗮ)
  rw [show Matrix.toEuclideanLin = Matrix.toLpLin (2 : ENNReal) (2 : ENNReal) from rfl,
    Matrix.toLpLin_eq_toLin, Matrix.toLin_toMatrix]
  exact Submodule.starProjection_apply_eq_zero_iff (K := S)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem trace_projector : (projector S).trace = (Module.finrank 𝕜 S : ℝ) := by
  suffices h_trace : ((S.subtype ∘ₗ S.orthogonalProjectionOnto).toMatrix (EuclideanSpace.basisFun n 𝕜).toBasis (EuclideanSpace.basisFun n 𝕜).toBasis).trace = Module.finrank 𝕜 S by
    simp [projector, trace_eq_re_trace, h_trace]
  suffices h_trace : ((S.subtype ∘ₗ S.orthogonalProjectionOnto).toMatrix (EuclideanSpace.basisFun n 𝕜).toBasis (EuclideanSpace.basisFun n 𝕜).toBasis).trace = (LinearMap.id.toMatrix (Module.finBasis 𝕜 S) (Module.finBasis 𝕜 S)).trace by
    simp [h_trace]
  rw [LinearMap.toMatrix_comp _ (Module.finBasis 𝕜 ↥S), Matrix.trace_mul_comm, ← LinearMap.toMatrix_comp]
  congr 2
  ext1
  simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/--
The `HermitianMat.projector` for the `HermitianMat.support` submodule.
-/
noncomputable def supportProj (A : HermitianMat n 𝕜) : HermitianMat n 𝕜 := projector A.support

/--
The `HermitianMat.projector` for the `HermitianMat.ker` submodule.
-/
noncomputable def kerProj (A : HermitianMat n 𝕜) : HermitianMat n 𝕜 := projector A.ker

@[simp]
theorem supportProj_ker : A.supportProj.ker = A.ker := by
  rw [supportProj, projector_ker, support_orthogonal_eq_range]

@[simp]
theorem kerProj_ker : A.kerProj.ker = A.support := by
  rw [kerProj, projector_ker, ker_orthogonal_eq_support]

@[simp]
theorem kerProj_add_supportProj : A.kerProj + A.supportProj = 1 := by
  rw [← projector_add_orthogonal A.ker, ker_orthogonal_eq_support, kerProj, supportProj]

@[simp]
theorem kerProj_of_nonSingular [NonSingular A] : A.kerProj = 0 := by
  simp only [kerProj, nonSingular_ker_bot, HermitianMat.ext_iff]
  simp [projector]

@[simp]
theorem supportProj_of_nonSingular [NonSingular A] : A.supportProj = 1 := by
  simpa using A.kerProj_add_supportProj

/--
The projector onto a submodule S is the sum of the outer products of the vectors in an orthonormal basis of S.
-/
theorem projector_eq_sum_rankOne (b : OrthonormalBasis ι 𝕜 S) :
    (projector S).mat = ∑ i, Matrix.vecMulVec (S.subtype (b i)) (star (S.subtype (b i))) := by
  unfold projector;
  ext i j;
  field_simp;
  simp [Matrix.vecMulVec]
  -- By definition of orthogonal projection, we can write the projection of $e_j$ onto $S$ as $\sum_{k} \langle e_j, b_k \rangle b_k$.
  have h_proj : ∀ j : n, S.orthogonalProjectionOnto (EuclideanSpace.single j 1) = ∑ k, (star (b k |>.1 j)) • (b k |>.1) := by
    intro j
    have h_proj : S.orthogonalProjectionOnto (EuclideanSpace.single j 1) = ∑ k, (inner 𝕜 (b k |>.1) (EuclideanSpace.single j 1)) • (b k |>.1) := by
      convert b.sum_repr ( S.orthogonalProjectionOnto ( EuclideanSpace.single j 1 ) ) using 1;
      constructor <;> intro h <;> simp_all [ Subtype.ext_iff, b.repr_apply_apply ];
    convert! h_proj using 3
    simp [ inner];
  convert! congr_arg ( fun x : EuclideanSpace ( _ ) n => x i ) ( h_proj j ) using 1
  simp [ Matrix.sum_apply, mul_comm ]

/--
The projector onto the support of A is the sum of the projections onto the eigenvectors with non-zero eigenvalues.
-/
lemma projector_support_eq_sum : A.supportProj.mat =
    ∑ i, (if A.H.eigenvalues i = 0 then 0 else 1) •
      Matrix.vecMulVec (A.H.eigenvectorBasis i) (star (A.H.eigenvectorBasis i)) := by
  have h_support : A.support = Submodule.span (𝕜) (Set.image (fun i => A.H.eigenvectorBasis i) { i | A.H.eigenvalues i ≠ 0 }) := by
    refine' le_antisymm _ _;
    · intro x hx;
      -- By definition of $A.support$, we know that $x$ is in the orthogonal complement of the kernel of $A$.
      have h_orthogonal_complement : x ∈ (A.ker : Submodule (𝕜) (EuclideanSpace (𝕜) n))ᗮ := by
        convert hx using 1;
        exact ker_orthogonal_eq_support A;
      -- By definition of $A.ker$, we know that $x$ is orthogonal to all eigenvectors with zero eigenvalues.
      have h_orthogonal_zero_eigenvalues : ∀ i, A.H.eigenvalues i = 0 → inner (𝕜) (A.H.eigenvectorBasis i) x = 0 := by
        intro i hi
        have h_eigenvector_zero : A.mat.mulVec (A.H.eigenvectorBasis i) = 0 := by
          have := A.H.mulVec_eigenvectorBasis i; aesop;
        convert h_orthogonal_complement ( A.H.eigenvectorBasis i ) _ using 1;
        exact (mem_ker_iff_mulVec_zero A ((H A).eigenvectorBasis i)).mpr h_eigenvector_zero;
      -- By definition of $A.ker$, we know that $x$ can be written as a linear combination of eigenvectors with non-zero eigenvalues.
      have h_decomp : x = ∑ i, (inner (𝕜) (A.H.eigenvectorBasis i) x) • A.H.eigenvectorBasis i := by
        exact Eq.symm (OrthonormalBasis.sum_repr' (H A).eigenvectorBasis x);
      rw [ h_decomp ];
      exact Submodule.sum_mem _ fun i _ => if hi : A.H.eigenvalues i = 0 then by simp [h_orthogonal_zero_eigenvalues i hi ] else Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ i, hi, rfl ⟩ );
    · rw [ Submodule.span_le, Set.image_subset_iff ];
      intro i hi;
      simp_all [ HermitianMat.support ];
      use (1 / A.H.eigenvalues i) • A.H.eigenvectorBasis i;
      convert congr_arg ( fun x => ( 1 / A.H.eigenvalues i ) • x ) ( A.H.mulVec_eigenvectorBasis i ) using 1
      simp [hi]
      simp [ funext_iff, Matrix.mulVec, dotProduct ];
      exact PiLp.ext_iff;
  have h_orthonormal_basis : ∃ b : OrthonormalBasis {i : n | A.H.eigenvalues i ≠ 0} (𝕜) (Submodule.span (𝕜) (Set.image (fun i => A.H.eigenvectorBasis i) {i | A.H.eigenvalues i ≠ 0})), ∀ i, b i = A.H.eigenvectorBasis i := by
    refine' ⟨ _, _ ⟩;
    refine' OrthonormalBasis.mk _ _;
    use fun i => ⟨ A.H.eigenvectorBasis i, Submodule.subset_span ( Set.mem_image_of_mem _ i.2 ) ⟩;
    all_goals simp [ Orthonormal ];
    · intro i j hij; have := A.H.eigenvectorBasis.orthonormal; simp_all [ orthonormal_iff_ite ] ;
      exact fun h => hij <| Subtype.ext h;
    · rw [ Submodule.eq_top_iff' ];
      rintro ⟨ x, hx ⟩;
      rw [ Submodule.mem_span ] at hx ⊢;
      intro p hp; specialize hx ( Submodule.map ( Submodule.subtype _ ) p ) ; simp_all [ Set.range_subset_iff ] ;
      exact hx fun i hi => ⟨ _, hp i hi, rfl ⟩;
  obtain ⟨ b, hb ⟩ := h_orthonormal_basis
  have h_sum_rankOne : (projector A.support).mat = ∑ i, Matrix.vecMulVec (b i) (star (b i)) := by
    convert! projector_eq_sum_rankOne _ b using 1
    simp [h_support] at *
  simp_all [ Finset.sum_ite ];
  convert h_sum_rankOne using 1;
  · exact h_support ▸ rfl;
  · refine' Finset.sum_bij ( fun i hi => ⟨ i, by simpa using hi ⟩ ) _ _ _ _ <;> simp [ Finset.mem_filter, hb ]

/-
`HermitianMat.supportProj` as a cfc.
-/
theorem supportProj_eq_cfc : A.supportProj = A.cfc (if · = 0 then 0 else 1) := by
  apply HermitianMat.ext;
  rw [HermitianMat.cfc_toMat_eq_sum_smul_proj];
  convert projector_support_eq_sum A using 1;
  refine' Finset.sum_congr rfl fun i _ => _;
  ext x y
  simp [ Matrix.vecMulVec, Matrix.mul_apply ] ;
  simp [ Matrix.single ];
  simp [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
  rw [ Finset.sum_eq_single i ] <;> aesop

/-
`HermitianMat.kerProj` as a cfc.
-/
theorem kerProj_eq_cfc : A.kerProj = A.cfc (if · = 0 then 1 else 0) := by
  have h : A.cfc (fun x ↦ (1 : ℝ) - (if x = 0 then 0 else 1)) = A.cfc (if · = 0 then 1 else 0) := by
    congr 1
    funext x
    split_ifs <;> norm_num
  rw [← h, cfc_sub_apply, cfc_const, one_smul, ← supportProj_eq_cfc, eq_sub_iff_add_eq,
    kerProj_add_supportProj]

/-- `HermitianMat.kerProj` is idempotent. -/
theorem kerProj_sq : A.kerProj.mat * A.kerProj.mat = A.kerProj.mat := by
  have hf : (fun x : ℝ ↦ (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0))
      = (if · = 0 then 1 else 0) := by
    funext x
    split_ifs <;> norm_num
  rw [kerProj_eq_cfc, ← mat_cfc_mul_apply, hf]

/-- Projector onto the non-negative eigenspace of `B - A`. Accessible by the notation
`{A ≤ₚ B}`, which is scoped to `HermitianMat`. This is the unique maximum operator `P`
such that `P^2 = P` and `P * A * P ≤ P * B * P` in the Loewner order. -/
def projLE (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 ≤ x then 1 else 0)

/-- Projector onto the positive eigenspace of `B - A`. Accessible by the notation
`{A <ₚ B}`, which is scoped to `HermitianMat`. Compare with `proj_le`. -/
noncomputable def projLT (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 < x then 1 else 0)

-- Note this is in the opposite direction as in the Stein's Lemma paper, which uses `≥ₚ`
-- as the default ordering. We offer the `≥ₚ` notation which is the same with the arguments
-- flipped, similar to how `GT.gt` is defeq to `LT.lt` with arguments flipped.
-- We put the ≥ₚ first, since both can delaborate and we want to show the ≤ₚ one.
scoped notation "{" A " ≥ₚ " B "}" => projLE B A
scoped notation "{" A " ≤ₚ " B "}" => projLE A B

scoped notation "{" A " >ₚ " B "}" => projLT B A
scoped notation "{" A " <ₚ " B "}" => projLT A B

theorem projLE_def : {A ≤ₚ B} = (B - A).cfc (fun x ↦ if 0 ≤ x then 1 else 0) := by
  rfl

theorem projLT_def : {A <ₚ B} = (B - A).cfc (fun x ↦ if 0 < x then 1 else 0) := by
  rfl

theorem projLE_sq : {A ≤ₚ B}^2 = {A ≤ₚ B} := by
  rw [projLE_def, ← cfc_pow, ← cfc_comp]
  congr! 2 with x
  simp

theorem projLT_sq : {A <ₚ B}^2 = {A <ₚ B} := by
  rw [projLT_def, ← cfc_pow, ← cfc_comp]
  congr! 2 with x
  simp

theorem projLE_zero_cfc : {0 ≤ₚ A} = A.cfc (fun x ↦ if 0 ≤ x then 1 else 0) := by
  simp only [projLE_def, sub_zero]

theorem projLT_zero_cfc : {0 <ₚ A} = A.cfc (fun x ↦ if 0 < x then 1 else 0) := by
  simp only [projLT_def, sub_zero]

theorem projLE_zero_cfc' : {A ≤ₚ 0} = A.cfc (fun x ↦ if x ≤ 0 then 1 else 0) := by
  simp only [projLE_def, zero_sub]
  --TODO: Should do a `HermitianMat.cfc_comp_neg`?
  nth_rw 1 [← cfc_id A]
  rw [← cfc_neg, ← cfc_comp]
  congr! 2 with x
  simp

theorem projLT_zero_cfc' : {A <ₚ 0} = A.cfc (fun x ↦ if x < 0 then 1 else 0) := by
  simp only [projLT_def, zero_sub]
  --TODO: Should do a `HermitianMat.cfc_comp_neg`?
  nth_rw 1 [← cfc_id A]
  rw [← cfc_neg, ← cfc_comp]
  congr! 2 with x
  simp

theorem projLE_nonneg : 0 ≤ {A ≤ₚ B} := by
  rw [projLE_def, cfc_nonneg_iff]
  intro i
  apply ite_nonneg <;> norm_num

theorem projLT_nonneg : 0 ≤ {A <ₚ B} := by
  rw [projLT_def, cfc_nonneg_iff]
  intro i
  apply ite_nonneg <;> norm_num

set_option backward.isDefEq.respectTransparency false in
theorem projLE_le_one : {A ≤ₚ B} ≤ 1 := by
  --The whole `rw` line is a defeq, i.e. `change _root_.cfc _ (B - A).mat ≤ 1` works too.
  --TODO better API.
  open MatrixOrder in
  rw [← Subtype.coe_le_coe, val_eq_coe, selfAdjoint.val_one]
  apply cfc_le_one (f := fun x ↦ if 0 ≤ x then 1 else 0)
  intros; split <;> norm_num

open MatrixOrder in
theorem projLE_mul_nonneg : 0 ≤ {A ≤ₚ B}.mat * (B - A).mat := by
  rw [projLE_def]
  nth_rewrite 2 [← cfc_id (B - A)]
  rw [← mat_cfc_mul]
  apply cfc_nonneg
  aesop

open MatrixOrder in
theorem projLE_mul_le : {A ≤ₚ B}.mat * A.mat ≤ {A ≤ₚ B}.mat * B.mat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  exact projLE_mul_nonneg A B

@[simp]
theorem proj_le_add_lt : {A <ₚ B} + {B ≤ₚ A} = 1 := by
  rw [projLE_def, projLT_def]
  rw [← neg_sub A B]
  nth_rw 1 [← cfc_id (A - B)]
  rw[← cfc_neg, ← cfc_comp, ← cfc_add]
  convert cfc_const (A - B) 1 with x
  · simp; grind
  · simp

theorem conj_lt_add_conj_le : A.conj {A <ₚ 0} + A.conj {0 ≤ₚ A} = A := by
  rw (occs := [2, 4, 5]) [← cfc_id A]
  rw [projLT_zero_cfc', projLE_zero_cfc, cfc_conj, cfc_conj, ← cfc_add]
  congr; ext
  simp; grind

/-
The projection onto the support can be split into the projection onto positive
and negative eigenvalues.
-/
theorem supportProj_eq_proj_lt_add_proj_lt (A : HermitianMat n 𝕜) :
    A.supportProj = {A <ₚ 0} + {0 <ₚ A} := by
  rw [supportProj_eq_cfc, projLT_zero_cfc, projLT_zero_cfc', ← cfc_add A]
  congr 1
  grind only [Pi.add_apply]

/-- The positive part of a Hermitian matrix: the projection onto its positive eigenvalues. -/
instance : PosPart (HermitianMat n 𝕜) where
  posPart A := A.cfc (fun x ↦ x ⊔ 0)

/-- The negative part of a Hermitian matrix: the projection onto its negative eigenvalues. -/
instance : NegPart (HermitianMat n 𝕜) where
  negPart A := A.cfc (fun x ↦ -x ⊔ 0)

theorem posPart_eq_cfc_max : A⁺ = A.cfc (fun x ↦ x ⊔ 0) := by
  rfl

theorem negPart_eq_cfc_min : A⁻ = A.cfc (fun x ↦ -x ⊔ 0) := by
  rfl

theorem posPart_eq_cfc_ite : A⁺ = A.cfc (fun x ↦ if 0 ≤ x then x else 0) := by
  simp only [← max_def', posPart_eq_cfc_max]

theorem negPart_eq_cfc_ite : A⁻ = A.cfc (fun x ↦ if x ≤ 0 then -x else 0) := by
  simp only [negPart_eq_cfc_min, max_def]
  congr; ext
  split <;> split <;> grind

/-- There is an existing (very slow) `PosPart` instance on `Matrix n n 𝕜`, this shows
that this is equal. -/
theorem posPart_eq_posPart_toMat : A⁺ = A.mat⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rfl

/-- There is an existing (very slow) `PosPart` instance on `Matrix n n 𝕜`, this shows
that this is equal. -/
theorem negPart_eq_negPart_toMat : A⁻ = A.mat⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  rfl

/-- The positive part can be equivalently described as the nonnegative part. -/
theorem posPart_eq_cfc_lt : A⁺ = A.cfc (fun x ↦ if 0 < x then x else 0) := by
  rw [posPart_eq_cfc_ite]
  congr with x
  rcases lt_trichotomy x 0 <;> grind

/-- The negative part can be equivalently described as the nonpositive part. -/
theorem negPart_eq_cfc_lt : A⁻ = A.cfc (fun x ↦ if x < 0 then -x else 0) := by
  rw [negPart_eq_cfc_ite]
  congr with x
  rcases lt_trichotomy x 0 <;> grind

theorem posPart_add_negPart : A⁺ - A⁻ = A := by
  rw [posPart_eq_cfc_ite, negPart_eq_cfc_lt, ← cfc_sub]
  convert cfc_id A
  ext; dsimp; grind

theorem posPart_eq_self {A : HermitianMat n 𝕜} (hA : 0 ≤ A) :
    A⁺ = A := by
  nth_rw 2 [← cfc_id A]
  apply cfc_congr_of_nonneg hA
  grind [Set.EqOn]

theorem posPart_nonneg : 0 ≤ A⁺ := by
  rw [posPart_eq_cfc_ite, cfc_nonneg_iff]
  intro; split <;> order

theorem negPart_nonneg : 0 ≤ A⁻ := by
  rw [negPart_eq_cfc_ite, cfc_nonneg_iff]
  intro; split <;> grind

theorem posPart_le : A ≤ A⁺ := by
  nth_rw 1 [← cfc_id A]
  rw [posPart_eq_cfc_ite, ← sub_nonneg, ← cfc_sub, cfc_nonneg_iff]
  intro; simp; split <;> order

theorem posPart_mul_negPart : A⁺.mat * A⁻.mat = 0 := by
  rw [posPart_eq_cfc_ite, negPart_eq_cfc_ite, ← mat_cfc_mul]
  convert congrArg mat (cfc_const A 0)
  · grind [Pi.mul_apply, mul_eq_zero]
  · simp

open RealInnerProductSpace

theorem projLE_inner_nonneg  : 0 ≤ ⟪{A ≤ₚ B}, (B - A)⟫ :=
  --This inner is equal to `(B - A)⁺.trace`, could be better way to describe it
  inner_mul_nonneg (projLE_mul_nonneg A B)

theorem projLE_inner_le : ⟪{A ≤ₚ B}, A⟫ ≤ ⟪{A ≤ₚ B}, B⟫ := by
  rw [← sub_nonneg, ← inner_sub_right]
  exact projLE_inner_nonneg A B

open RealInnerProductSpace in
theorem inner_projLE_nonneg : 0 ≤ ⟪{A ≤ₚ B}, (B - A)⟫ :=
  projLE_inner_nonneg A B

open RealInnerProductSpace in
theorem inner_projLE_le : ⟪{A ≤ₚ B}, A⟫ ≤ ⟪{A ≤ₚ B}, B⟫ :=
  projLE_inner_le A B

--TODO: When we upgrade `cfc_continuous` from 𝕜 to ℂ, we upgrade these too.
@[fun_prop]
theorem posPart_Continuous : Continuous (·⁺ : HermitianMat n ℂ → _) := by
  simp_rw [posPart_eq_cfc_max]
  fun_prop

@[fun_prop]
theorem negPart_Continuous : Continuous (·⁻ : HermitianMat n ℂ → _) := by
  simp_rw [negPart_eq_cfc_min]
  fun_prop

--Many missing lemmas: see `Mathlib.Algebra.Order.Group.PosPart` for examples
-- (They don't apply here since it's not a Lattice, and there's no well-defined `max` in
--   the Loewner order.)
-- PosPart is Monotone (so `A ≤ B` implies `A⁺ ≤ B⁺`), as is NegPart
-- PosPart and NegPart commute with nonnegative scalar muliptlication
-- `A⁺ ≤ 0 ↔ A⁺ = 0 ↔ A = 0`
-- `0 ≤ A → A⁺ = A`
-- `0 < A → 0 < A⁺` (this is not the PosDef version, this is `≤ && ≠`)
-- `A.PosDef → A⁺.PosDef`
-- versions of those ^^ for negPart
-- simp: 0⁺ = 0, 0⁻ = 0, 1⁺ = 1, 1⁻ = 0
--   (-A)⁺ = A⁻, (-A)⁻ = A⁺
--  A⁺⁺ = A⁺, A⁺⁻ = 0

-- variable {d : Type*} [Fintype d] [DecidableEq d] (A B : HermitianMat d ℂ)

theorem one_sub_projLT : 1 - {B ≤ₚ A} = {A <ₚ B} := by
  rw [sub_eq_iff_eq_add, proj_le_add_lt]

open MatrixOrder ComplexOrder in
theorem projLT_mul_nonneg : 0 ≤ {A <ₚ B}.mat * (B - A).mat := by
  rw [projLT_def]
  nth_rewrite 2 [← cfc_id (B - A)]
  rw [← mat_cfc_mul]
  apply cfc_nonneg
  intros
  simp only [Pi.mul_apply, id_eq, ite_mul, one_mul, zero_mul]
  split <;> order

open MatrixOrder ComplexOrder in
theorem proj_lt_mul_lt : {A <ₚ B}.mat * A.mat ≤ {A <ₚ B}.mat * B.mat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  exact A.projLT_mul_nonneg B

theorem inner_negPart_nonpos : ⟪A, A⁻⟫ ≤ 0 := by
  rw [← neg_le_neg_iff, neg_zero, ← inner_neg_right]
  apply inner_mul_nonneg
  nth_rw 1 [← A.cfc_id]
  rw [negPart_eq_cfc_ite]
  rw [← cfc_neg]
  rw [← mat_cfc_mul]
  change 0 ≤ A.cfc _
  rw [cfc_nonneg_iff]
  intro i
  dsimp
  split_ifs with h
  · rw [neg_neg]
    exact mul_self_nonneg _
  · simp

@[simp]
theorem posPart_inner_negPart_zero : ⟪A⁺, A⁻⟫ = 0 := by
  have hi := inner_eq_trace_rc A⁺ A⁻
  rw [posPart_mul_negPart, Matrix.trace_zero] at hi
  simpa only [map_eq_zero] using hi

theorem inner_negPart_zero_iff : ⟪A, A⁻⟫ = 0 ↔ 0 ≤ A := by
  constructor
  · intro h
    nth_rw 1 [← posPart_add_negPart A] at h
    rw [inner_sub_left, sub_eq_zero, posPart_inner_negPart_zero, eq_comm, inner_self_eq_zero] at h
    rw [← zero_smul ℝ 1, ← cfc_const A, negPart_eq_cfc_ite] at h --TODO cfc_zero
    rw [cfc_eq_cfc_iff_eqOn, A.H.spectrum_real_eq_range_eigenvalues, Set.eqOn_range] at h
    replace h (i) := congrFun h i
    simp only [Function.comp_apply, ite_eq_right_iff, neg_eq_zero] at h
    rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg]
    intro i
    contrapose! h
    use i, h.le, h.ne
  · intro h
    apply le_antisymm
    · exact inner_negPart_nonpos A
    · exact inner_ge_zero h (negPart_nonneg A)

theorem posPart_eq_zero_iff : A⁺ = 0 ↔ A ≤ 0 := by
  refine ⟨fun h => by simpa [h] using posPart_le (A := A), fun hA => ?_⟩
  have hnegPart : (-A)⁻ = A⁺ := by
    rw [negPart_eq_cfc_ite, posPart_eq_cfc_ite]
    nth_rw 1 [← cfc_id A]
    rw [← cfc_neg, ← cfc_comp]
    congr! 2 with x; simp
  have h0 : ⟪-A, A⁺⟫ = 0 := by
    simpa [hnegPart] using (inner_negPart_zero_iff (A := -A)).2 (by simpa using hA)
  have hA_eq : -A = A⁻ - A⁺ := by
    conv_lhs => rw [show A = A⁺ - A⁻ from (posPart_add_negPart A).symm]
    abel
  have hself : ⟪A⁺, A⁺⟫ = 0 := by
    rw [hA_eq, HermitianMat.inner_sub_right, HermitianMat.inner_comm A⁻ A⁺,
      posPart_inner_negPart_zero, zero_sub, neg_eq_zero] at h0
    exact h0
  exact inner_self_eq_zero.mp hself

theorem inner_negPart_neg_iff : ⟪A, A⁻⟫ < 0 ↔ ¬0 ≤ A := by
  simp [← inner_negPart_zero_iff, lt_iff_le_and_ne, inner_negPart_nonpos A]

/-- The self-duality of the PSD cone: a matrix is PSD iff its inner product with all
nonnegative matrices is non-negative. -/
theorem nonneg_iff_inner_nonneg (A : HermitianMat n 𝕜) :
    0 ≤ A ↔ ∀ B, 0 ≤ B → 0 ≤ ⟪A, B⟫ := by
  use fun h _ ↦ inner_ge_zero h
  intro h
  contrapose! h
  classical
  use A⁻, negPart_nonneg A
  rwa [inner_negPart_neg_iff]

section kronecker

open Kronecker

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem ker_le_ker_supportProj (A : HermitianMat n ℂ) : A.ker ≤ A.supportProj.ker := by
  rw [supportProj_eq_cfc]
  exact ker_le_ker_cfc (fun i hi ↦ by simp [hi])

lemma supportProj_kron_diagonal (f : n → ℝ) (g : m → ℝ) :
    (diagonal 𝕜 f ⊗ₖ diagonal 𝕜 g).supportProj =
      (diagonal 𝕜 f).supportProj ⊗ₖ (diagonal 𝕜 g).supportProj := by
  rw [supportProj_eq_cfc, supportProj_eq_cfc, supportProj_eq_cfc, kronecker_diagonal,
    cfc_diagonal, cfc_diagonal, cfc_diagonal, kronecker_diagonal]
  congr 1
  funext i
  by_cases h1 : f i.1 = 0 <;> by_cases h2 : g i.2 = 0 <;> simp [h1, h2]

/-- The support projector of a Kronecker product is the Kronecker product of the support
projectors. -/
theorem supportProj_kron (A : HermitianMat n 𝕜) (B : HermitianMat m 𝕜) :
    (A ⊗ₖ B).supportProj = A.supportProj ⊗ₖ B.supportProj := by
  obtain ⟨UA, DA, rfl⟩ : ∃ UA : Matrix.unitaryGroup n 𝕜, ∃ DA, A = (diagonal 𝕜 DA).conj UA.val :=
    ⟨_, _, eq_conj_diagonal A⟩
  obtain ⟨UB, DB, rfl⟩ : ∃ UB : Matrix.unitaryGroup m 𝕜, ∃ DB, B = (diagonal 𝕜 DB).conj UB.val :=
    ⟨_, _, eq_conj_diagonal B⟩
  rw [← kronecker_conj, supportProj_eq_cfc,
    cfc_conj_unitary _ _ ⟨_, Matrix.kronecker_mem_unitary UA.2 UB.2⟩, ← supportProj_eq_cfc,
    supportProj_kron_diagonal, kronecker_conj]
  congr 1 <;> rw [supportProj_eq_cfc, supportProj_eq_cfc, cfc_conj_unitary]

end kronecker
