/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Bundled
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open ComplexOrder
open scoped Matrix

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable [DecidableEq dIn] [DecidableEq dOut] {M : MatrixMap dIn dOut 𝕜}

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[M(A) B] = Tr[A (dual M)(B)]`. Sometimes
called the adjoint of the map instead. The entries are read off by pairing against the standard
basis, which is what the definition below says. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R where
  toFun B := Matrix.of fun i j ↦ (M (Matrix.single j i 1) * B).trace
  map_add' B C := by
    ext i j
    simp [Matrix.mul_add]
  map_smul' r B := by
    ext i j
    simp

omit [Fintype dIn] in
theorem dual_apply (M : MatrixMap dIn dOut R) (B : Matrix dOut dOut R) (i j : dIn) :
    M.dual B i j = (M (Matrix.single j i 1) * B).trace := by
  rw [dual]
  rfl

/-- The defining property of a dual map: traces are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  have hsingle : ∀ i j : dIn, Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : R) := by
    intro i j
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hR : (A * M.dual B).trace = ∑ i, ∑ j, A i j * (M (Matrix.single i j 1) * B).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, dual_apply]
  rw [hR]
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [hsingle, map_sum, map_smul, Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]

--all properties below should provable just from `Dual.trace_eq`, since the definition of `dual`
-- itself is not very usable directly.

variable {Mℂ : MatrixMap dIn dOut ℂ}

omit [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] in
/-- A Hermitian-preserving map commutes with the conjugate transpose. This uses that the field is
`ℂ`: over `ℝ` a map is constrained only on the symmetric matrices, and says nothing about how the
antisymmetric part is transformed. -/
theorem IsHermitianPreserving.conjTranspose_map (h : Mℂ.IsHermitianPreserving)
    (X : Matrix dIn dIn ℂ) : Mℂ Xᴴ = (Mℂ X)ᴴ := by
  set P : Matrix dIn dIn ℂ := (2 : ℂ)⁻¹ • (X + Xᴴ) with hP
  set Q : Matrix dIn dIn ℂ := (2 * Complex.I)⁻¹ • (X - Xᴴ) with hQ
  have hPH : P.IsHermitian := by
    ext a b
    simp only [hP, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    simp [add_comm]
  have hQH : Q.IsHermitian := by
    ext a b
    simp only [hQ, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    rw [star_mul', star_sub]
    simp [Complex.inv_I, mul_comm]
    ring
  have hX : X = P + Complex.I • Q := by
    ext a b
    simp only [hP, hQ, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply, smul_eq_mul]
    field_simp
    ring
  have hXH : Xᴴ = P - Complex.I • Q := by
    ext a b
    simp only [hP, hQ, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply, smul_eq_mul]
    field_simp
    ring
  rw [hXH, hX]
  simp only [map_sub, map_add, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    (h hPH).eq, (h hQH).eq, RCLike.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]

omit [Fintype dIn] in
/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual (h : Mℂ.IsHermitianPreserving) :
    Mℂ.dual.IsHermitianPreserving := by
  intro B hB
  ext i j
  rw [Matrix.conjTranspose_apply, dual_apply, dual_apply, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, ← h.conjTranspose_map, Matrix.conjTranspose_single, star_one,
    hB.eq, Matrix.trace_mul_comm]

open MatrixOrder
--TODO Cleanup, find home, abstract out to HermitianMats...?
theorem _root_.Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  open scoped Matrix in
  obtain ⟨sqrtB, rfl⟩ : ∃ sqrtB : Matrix n n 𝕜, B = sqrtBᴴ * sqrtB := by
    classical
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    exact Matrix.nonneg_iff_posSemidef.mpr hB
  simp only [← Matrix.mul_assoc, ← Matrix.trace_mul_comm sqrtB]
  have h : (sqrtB * A * sqrtBᴴ).PosSemidef := by
    convert hA.conjTranspose_mul_mul_same sqrtBᴴ using 1
    simp [Matrix.mul_assoc]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.trace, Pi.single_apply] using
    Finset.sum_nonneg fun i _ ↦ h.2 (Pi.single i 1)

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem IsPositive.dual (h : Mℂ.IsPositive) : Mℂ.dual.IsPositive := by
  intro x hx
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hx ⊢
  refine ⟨IsHermitianPreserving.dual h.IsHermitianPreserving hx.1, fun v => ?_⟩
  --TODO Cleanup. Should be all in terms of HermitianMat
  have h_dual_pos : 0 ≤ (Mℂ (Matrix.vecMulVec v (star v)) * x).trace :=
    Matrix.PosSemidef.trace_mul_nonneg (h (Matrix.posSemidef_vecMulVec_self_star v))
      (Matrix.posSemidef_iff_dotProduct_mulVec.mpr hx)
  rw [Dual.trace_eq] at h_dual_pos
  convert h_dual_pos using 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem dual_Unital (h : M.IsTracePreserving) : M.dual.Unital := by
  -- By definition of dual, we know that for any matrix A, Tr(M(A) * I) = Tr(A * M*(I)).
  have h_dual_trace : ∀ A : Matrix dIn dIn 𝕜, (M A * 1).trace = (A * M.dual 1).trace := by
    exact fun A => Dual.trace_eq M A 1;
  ext i j
  specialize h_dual_trace ( Matrix.of ( fun k l => if k = j then if l = i then 1 else 0 else 0 ) )
  simp_all [ Matrix.trace, Matrix.mul_apply ] ;
  specialize h ( Matrix.of ( fun k l => if k = j then if l = i then 1 else 0 else 0 ) )
  simp_all [ Matrix.trace ]
  simp [ Matrix.one_apply, eq_comm ]

alias IsTracePreserving.dual := dual_Unital

/--
If two matrix maps satisfy the trace duality property, they are equal.
-/
lemma dual_unique
    (M : MatrixMap dIn dOut 𝕜) (M' : MatrixMap dOut dIn 𝕜)
    (h : ∀ A B, (M A * B).trace = (A * M' B).trace) : M.dual = M' := by
  -- By definition of dual, we know that for any A and B, the trace of (M A) * B equals the trace of A * (M.dual B).
  have h_dual : ∀ A : Matrix dIn dIn 𝕜, ∀ B : Matrix dOut dOut 𝕜, (M A * B).trace = (A * M.dual B).trace := by
    exact fun A B => Dual.trace_eq M A B;
  -- Since these two linear maps agree on all bases, they must be equal.
  have h_eq : ∀ A : Matrix dIn dIn 𝕜, ∀ B : Matrix dOut dOut 𝕜, (A * M.dual B).trace = (A * M' B).trace := by
    exact fun A B => h_dual A B ▸ h A B;
  refine' LinearMap.ext fun B => _;
  exact Matrix.ext_iff_trace_mul_left.mpr fun x => h_eq x B

/--
The Choi matrix of the dual map is the transpose of the reindexed Choi matrix of the original map.
-/
lemma dual_choi_matrix (M : MatrixMap dIn dOut 𝕜) :
    M.dual.choi_matrix = (M.choi_matrix.transpose).reindex (Equiv.prodComm dOut dIn) (Equiv.prodComm dOut dIn) := by
  -- By definition of dual, we know that $(M.dual (single j₁ j₂ 1)) i₁ i₂ = (M (single i₂ i₁ 1)) j₂ j₁$.
  have h_dual_def : ∀ (i₁ : dIn) (j₁ : dOut) (i₂ : dIn) (j₂ : dOut), (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = (M (Matrix.single i₂ i₁ 1)) j₂ j₁ := by
    intro i₁ j₁ i₂ j₂
    have h_dual_def : (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = Matrix.trace (Matrix.single i₂ i₁ 1 * M.dual (Matrix.single j₁ j₂ 1)) := by
      simp [ Matrix.trace, Matrix.mul_apply ];
      simp [ Matrix.single];
      rw [ Finset.sum_eq_single i₂ ]
      · aesop
      · intro b a a_1
        simp [a_1.symm]
      · aesop
    rw [ h_dual_def, ← Dual.trace_eq ];
    rw [ Matrix.trace ];
    rw [ Finset.sum_eq_single j₂ ] <;> aesop;
  aesop

/--
If the Choi matrix of a map is positive semidefinite, then the Choi matrix of its dual is also positive semidefinite.
-/
lemma dual_choi_matrix_posSemidef_of_posSemidef (M : MatrixMap dIn dOut 𝕜) (h : M.choi_matrix.PosSemidef) :
    M.dual.choi_matrix.PosSemidef := by
  rw [ dual_choi_matrix ];
  simp +zetaDelta at *;
  apply_rules [ Matrix.PosSemidef.submatrix ];
  convert h.transpose using 1

/--
The dual of the identity map is the identity map.
-/
lemma dual_id : (MatrixMap.id dIn 𝕜).dual = MatrixMap.id dIn 𝕜 := by
  exact dual_unique (id dIn 𝕜) (id dIn 𝕜) fun A_1 => congrFun rfl

set_option maxHeartbeats 600000 in
/--
The dual of a Kronecker product of maps is the Kronecker product of their duals.
-/
lemma dual_kron {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : MatrixMap A B 𝕜) (N : MatrixMap C D 𝕜) :
    (M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual := by
  have h_trace : ∀ (X : Matrix (A × C) (A × C) 𝕜) (Y : Matrix (B × D) (B × D) 𝕜), ( (M ⊗ₖₘ N) X * Y ).trace = ( X * (M.dual ⊗ₖₘ N.dual) Y ).trace := by
    -- By definition of dual, we know that $(M x1 * y1).trace = (x1 * M.dual y1).trace$ and $(N x2 * y2).trace = (x2 * N.dual y2).trace$.
    have h_dual : ∀ (x1 : Matrix A A 𝕜) (y1 : Matrix B B 𝕜), (M x1 * y1).trace = (x1 * M.dual y1).trace := by
      intro x1 y1
      convert MatrixMap.Dual.trace_eq M x1 y1 using 1
    have h_dual_N : ∀ (x2 : Matrix C C 𝕜) (y2 : Matrix D D 𝕜), (N x2 * y2).trace = (x2 * N.dual y2).trace := by
      exact fun x2 y2 => MatrixMap.Dual.trace_eq N x2 y2;
    intro X Y;
    -- By definition of Kronecker product, we can write X and Y as sums of Kronecker products.
    obtain ⟨X_sum, hX_sum⟩ : ∃ X_sum : Finset (Matrix A A 𝕜 × Matrix C C 𝕜), X = ∑ p ∈ X_sum, (Matrix.kroneckerMap (fun a b => a * b) p.1 p.2) := by
      refine' ⟨ Finset.univ.image fun p : A × A × C × C => ( Matrix.of fun i j => if i = p.1 ∧ j = p.2.1 then X ( p.1, p.2.2.1 ) ( p.2.1, p.2.2.2 ) else 0, Matrix.of fun i j => if i = p.2.2.1 ∧ j = p.2.2.2 then 1 else 0 ), _ ⟩;
      ext ⟨a, c⟩ ⟨a', c'⟩;
      rw [ Finset.sum_apply, Finset.sum_apply ];
      rw [ Finset.sum_eq_single ( ( Matrix.of fun i j => if i = a ∧ j = a' then X ( a, c ) ( a', c' ) else 0, Matrix.of fun i j => if i = c ∧ j = c' then 1 else 0 ) ) ] <;> simp;
      · intro a_1 b x x_1 x_2 x_3 a_2 a_3 a_4
        subst a_3 a_2
        contrapose! a_4; aesop;
      · exact fun h => False.elim ( h a a' c c' ( by ext i j; aesop ) ( by ext i j; aesop ) )
    obtain ⟨Y_sum, hY_sum⟩ : ∃ Y_sum : Finset (Matrix B B 𝕜 × Matrix D D 𝕜), Y = ∑ p ∈ Y_sum, (Matrix.kroneckerMap (fun a b => a * b) p.1 p.2) := by
      use Finset.image (fun p => (Matrix.of (fun i j => Y (i, p.1) (j, p.2)), Matrix.of (fun i j => if i = p.1 ∧ j = p.2 then 1 else 0))) (Finset.univ : Finset (D × D));
      ext ⟨i, j⟩ ⟨k, l⟩; simp [ Matrix.kroneckerMap ] ;
      rw [ Finset.sum_image ] <;> simp [ Matrix.sum_apply ];
      · rw [ Finset.sum_eq_single ( j, l ) ] <;> aesop;
      · intro p q h
        subst hX_sum
        simp_all only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
        obtain ⟨fst, snd⟩ := p
        obtain ⟨fst_1, snd_1⟩ := q
        obtain ⟨left, right⟩ := h
        simp_all only [Prod.mk.injEq]
        apply And.intro
        · have := congr_fun ( congr_fun right fst ) snd; aesop;
        · replace right := congr_fun ( congr_fun right fst ) snd; aesop;
    -- By linearity of the trace and the properties of the Kronecker product, we can expand both sides of the equation.
    have h_expand : ∀ (x1 y1 : Matrix A A 𝕜) (x2 y2 : Matrix C C 𝕜) (x3 y3 : Matrix B B 𝕜) (x4 y4 : Matrix D D 𝕜), ( (M ⊗ₖₘ N) (Matrix.kroneckerMap (fun a b => a * b) x1 x2) * Matrix.kroneckerMap (fun a b => a * b) x3 x4 ).trace = ( Matrix.kroneckerMap (fun a b => a * b) x1 x2 * (M.dual ⊗ₖₘ N.dual) (Matrix.kroneckerMap (fun a b => a * b) x3 x4) ).trace := by
      intro x1 y1 x2 y2 x3 y3 x4 y4
      simp [MatrixMap.kron_map_of_kron_state]
      convert congr_arg₂ ( · * · ) ( h_dual x1 x3 ) ( h_dual_N x2 x4 ) using 1 <;> simp [ Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply ]
      · simp only [Finset.sum_sigma', Finset.sum_mul _ _ _, Finset.mul_sum];
        refine' Finset.sum_bij ( fun x _ => ⟨ ⟨ x.fst.1, x.snd.1 ⟩, ⟨ x.fst.2, x.snd.2 ⟩ ⟩ ) _ _ _ _ <;> simp [ mul_assoc, mul_comm, mul_left_comm ];
        · bound;
        · exact fun b => ⟨ _, _, _, _, rfl ⟩;
      · simp only [mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul];
        simp only [← Finset.sum_product', mul_left_comm];
        refine' Finset.sum_bij ( fun x _ => ( x.1.2, x.2.2, x.1.1, x.2.1 ) ) _ _ _ _ <;> simp;
    simp_all [ Matrix.trace_sum, Finset.sum_mul _ _ _ ];
    simp [Matrix.mul_sum, h_expand]
  apply dual_unique; assumption;

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem IsCompletelyPositive.dual (h : Mℂ.IsCompletelyPositive) :
    Mℂ.dual.IsCompletelyPositive := by
  intro n
  have h_dual_pos : (MatrixMap.dual (Mℂ ⊗ₖₘ MatrixMap.id (Fin n) ℂ)).IsPositive := by
    exact IsPositive.dual (h n);
  -- By definition of complete positivity, we know that $(M ⊗ₖₘ id) dually map = M.dual ⊗ₖₘ id.dual$.
  have h_dual_kron : (MatrixMap.dual (Mℂ ⊗ₖₘ MatrixMap.id (Fin n) ℂ)) =
      (MatrixMap.dual Mℂ) ⊗ₖₘ (MatrixMap.dual (MatrixMap.id (Fin n) ℂ)) := by
    convert dual_kron Mℂ ( MatrixMap.id ( Fin n ) ℂ ) using 1;
  convert h_dual_pos using 1;
  rw [ h_dual_kron, dual_id ]

@[simp]
theorem dual_dual : M.dual.dual = M :=
  dual_unique M.dual M fun A B => by
    rw [Matrix.trace_mul_comm, ← Dual.trace_eq, Matrix.trace_mul_comm]

end MatrixMap

namespace CPTPOp

variable [DecidableEq dIn] [DecidableEq dOut]

/-- The dual (adjoint) of a channel, as a completely positive unital map. -/
def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn :=
  CPUOp.ofMat M.map.dual (.dual M.map_cp) (M.map_TP.dual)

/-- **Matrix analogue of the dual channel**: its matrix is the dual of the matrix. -/
@[simp]
theorem dual_map (M : CPTPMap dIn dOut) : M.dual.map = M.map.dual :=
  CPUOp.map_ofMat _ _ _

theorem dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.dual T := by
  exact M.dual.pos_Hermitian hT

/-- The dual of a CPTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem dual.PTP_POVM (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.dual T ∧ M.dual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.dual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.dual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_Dual (ℰ : CPTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    MState.exp_val (ℰ ρ) T = ρ.exp_val (ℰ.dual T) := by
  have hm : (ℰ ρ : MState dOut).m = ℰ.map ρ.m :=
    congrArg HermitianMat.mat (PTPOp.M_apply_MState ℰ.toPTPOp ρ)
  have hT : (ℰ.dual T : HermitianMat dIn ℂ).mat = ℰ.map.dual T.mat := by
    rw [show (ℰ.dual T : HermitianMat dIn ℂ).mat = ℰ.dual.map T.mat from rfl, dual_map]
  simp only [MState.exp_val, HermitianMat.inner_eq_re_trace, RCLike.re_to_complex,
    DensityOp.mat_M, hm, hT]
  congr 1
  apply MatrixMap.Dual.trace_eq

end CPTPOp

section hermDual

variable [DecidableEq dIn] [DecidableEq dOut]

--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
/-- The `ℂ`-linear extension of an `ℝ`-linear map of Hermitian matrices, obtained by splitting
the input into its real and imaginary parts. -/
def MatrixMap.ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    MatrixMap dIn dOut ℂ where
  toFun x := f (realPart x) + Complex.I • f (imaginaryPart x)
  map_add' x y := by
    simp only [map_add, HermitianMat.mat_add, smul_add]
    abel
  map_smul' c m := by
    have h_expand : realPart (c • m) = c.re • realPart m - c.im • imaginaryPart m ∧
      imaginaryPart (c • m) = c.re • imaginaryPart m + c.im • realPart m := by
      simp only [Subtype.ext_iff, AddSubgroupClass.coe_sub, selfAdjoint.val_smul,
        AddSubgroup.coe_add, realPart, selfAdjointPart_apply_coe, invOf_eq_inv, star_smul, RCLike.star_def,
        smul_add, imaginaryPart, LinearMap.coe_comp, Function.comp_apply,
        skewAdjoint.negISMul_apply_coe, skewAdjointPart_apply_coe,
        ← Matrix.ext_iff, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Matrix.star_apply, RCLike.star_def,
        Matrix.sub_apply, Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.inv_re,
        Complex.normSq_ofNat, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.neg_re, Complex.neg_im]
      ring_nf
      simp
    ext
    simp only [h_expand, map_sub, map_smul, map_add, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, RingHom.id_apply, Complex.ext_iff, Complex.add_re, Complex.mul_re,
      Complex.I, Complex.mul_im, Complex.add_im]
    simp only [HermitianMat.mat_sub, HermitianMat.mat_smul, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, HermitianMat.mat_add, Matrix.add_apply, Complex.add_re, Complex.add_im,
      Complex.mul_im, add_zero, one_mul, zero_sub, neg_add_rev, zero_add, Complex.sub_im]
    ring_nf
    simp

omit [Fintype dIn] [Fintype dOut] in
/-- The `ℂ`-linear extension of a map of Hermitian matrices is Hermitian-preserving. -/
theorem MatrixMap.isHermitianPreserving_ofHermitianMat
    (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    (MatrixMap.ofHermitianMat f).IsHermitianPreserving := fun _ h ↦ by
  apply Matrix.IsHermitian.add
  · apply HermitianMat.H
  · simp [IsSelfAdjoint.imaginaryPart h]

/-- The Hermitian-preserving map extending an `ℝ`-linear map of Hermitian matrices. -/
def HPOp.ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut :=
  HPOp.ofMat (MatrixMap.ofHermitianMat f) (MatrixMap.isHermitianPreserving_ofHermitianMat f)

/-- **Matrix analogue of `HPOp.ofHermitianMat`**. -/
@[simp]
theorem HPOp.map_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    (HPOp.ofHermitianMat f).map = MatrixMap.ofHermitianMat f :=
  HPOp.map_ofMat _ _

--PULLOUT
@[simp]
theorem HPOp.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMapClass.linearMap (HPOp.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  simp only [LinearMap.coe_coe, HPOp.mat_apply, HPOp.map_ofHermitianMat,
    MatrixMap.ofHermitianMat, HermitianMat.mat_mk, LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [2, 1, 2, 1]; rw [← realPart_add_I_smul_imaginaryPart x]
  suffices imaginaryPart x = 0 by simp [this]
  simp [imaginaryPart, skewAdjoint.negISMul, show star x = x from hx]

--PULLOUT
@[simp]
theorem HPOp.ofHermitianMat_linearMap (f : HPMap dIn dOut) :
    ofHermitianMat (LinearMapClass.linearMap f) = f := by
  apply HPOp.ext_map (ι := dIn) (κ := dOut)
  ext x i j
  simp only [map_ofHermitianMat, MatrixMap.ofHermitianMat, instFunLike, LinearMap.coe_coe,
    HermitianMat.val_eq_coe, HermitianMat.mat_mk, LinearMap.coe_mk, AddHom.coe_mk,
    ← map_smul, ← map_add]
  simp only [map_add, map_smul, realPart, imaginaryPart, LinearMap.coe_comp, Function.comp_apply]
  simp only [selfAdjointPart,  LinearMap.coe_mk, AddHom.coe_mk,
    HermitianMat.mat_mk,LinearMap.map_smul_of_tower, skewAdjoint.negISMul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp
  ring


variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product structure,
--doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear maps of HermitianMats
--and ℂ-linear maps of matrices.
def HPOp.hermDual : HPMap dOut dIn :=
  HPOp.ofHermitianMat (LinearMapClass.linearMap f).adjoint

@[simp]
theorem HPOp.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPOp.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMapClass.linearMap f) A, B⟫ = ⟪A, (LinearMapClass.linearMap f.hermDual) B⟫
  rw [hermDual, ← LinearMap.adjoint_inner_right, HPOp.linearMap_ofHermitianMat]

/-- Version of `HPOp.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
theorem HPOp.inner_hermDual' (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ :=
  HPOp.inner_hermDual f A B

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem MatrixMap.IsPositive.hermDual (h : MatrixMap.IsPositive f.map) : f.hermDual.map.IsPositive := by
  unfold IsPositive at h ⊢
  intro x hx
  set xH : HermitianMat dOut ℂ := ⟨x, hx.left⟩ with hxH
  have hx' : x = xH := rfl; clear_value xH; subst x; clear hxH
  change Matrix.PosSemidef (f.hermDual xH).mat
  rw [← HermitianMat.zero_le_iff] at hx ⊢
  classical
  rw [HermitianMat.nonneg_iff_inner_nonneg]
  intro y hy
  rw [HermitianMat.zero_le_iff] at hy
  specialize h hy
  change Matrix.PosSemidef (f y).mat at h
  rw [← HermitianMat.zero_le_iff] at h
  rw [HPOp.inner_hermDual, HPOp.hermDual_hermDual]
  apply HermitianMat.inner_ge_zero hx h

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem HPOp.hermDual_Unital (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual.map.Unital := by
  suffices f.hermDual 1 = 1 by --todo: make this is an accessible 'constructor' for Unital
    rw [HermitianMat.ext_iff] at this
    exact this
  open RealInnerProductSpace in
  apply ext_inner_left ℝ
  intro v
  rw [← HPOp.inner_hermDual]
  rw [HermitianMat.inner_one, HermitianMat.inner_one] --TODO change to Inner.inner
  exact congr(Complex.re $(h v)) --TODO: HPMap with IsTracePreserving give the HermitianMat.trace version

alias MatrixMap.IsTracePreserving.hermDual := HPOp.hermDual_Unital

namespace PTPOp

/-- The dual (adjoint) of a positive trace-preserving map, as a positive unital map. -/
def hermDual (M : PTPMap dIn dOut) : PUMap dOut dIn where
  toHPOp := M.toHPOp.hermDual
  pos := (OpMap.isPositive_toMat_iff (ι := dOut) (κ := dIn) _).mp M.map_pos.hermDual
  unital := (OpMap.unital_toMat_iff (ι := dOut) (κ := dIn) _).mp M.map_TP.hermDual

theorem hermDual_pos (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.hermDual T := by
  exact M.hermDual.pos_Hermitian hT

/-- The dual of a PTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem hermDual.PTP_POVM (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.hermDual T ∧ M.hermDual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.hermDual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.hermDual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_hermDual (ℰ : PTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    MState.exp_val (ℰ ρ) T = ρ.exp_val (ℰ.hermDual T) := by
  simp only [MState.exp_val]
  rw [PTPOp.M_apply_MState]
  apply HPOp.inner_hermDual'

end PTPOp

end hermDual
