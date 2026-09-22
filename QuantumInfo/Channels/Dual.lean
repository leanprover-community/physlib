/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Dennj Osele
-/
module

public import QuantumInfo.Channels.Bundled
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

@[expose] public section

noncomputable section
open ComplexOrder
open scoped Kronecker

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable [DecidableEq dIn] [DecidableEq dOut] {M : MatrixMap dIn dOut 𝕜}

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let coordDual :=
    let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
    let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
    iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2
  (Matrix.transposeLinearEquiv dIn dIn R R).toLinearMap ∘ₗ coordDual ∘ₗ
    (Matrix.transposeLinearEquiv dOut dOut R R).toLinearMap

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  have hDualIn (X Y : Matrix dIn dIn R) :
      ((Matrix.stdBasis R dIn dIn).toDualEquiv Y) X = (X * Y.transpose).trace := by
    simp [Module.Basis.toDualEquiv_apply, Module.Basis.toDual, Matrix.trace, Matrix.mul_apply,
      Matrix.stdBasis, Fintype.sum_prod_type, mul_comm]
  have hDualOut (X Y : Matrix dOut dOut R) :
      ((Matrix.stdBasis R dOut dOut).toDualEquiv Y) X = (X * Y.transpose).trace := by
    simp [Module.Basis.toDualEquiv_apply, Module.Basis.toDual, Matrix.trace, Matrix.mul_apply,
      Matrix.stdBasis, Fintype.sum_prod_type, mul_comm]
  let coordDual : MatrixMap dOut dIn R :=
    let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
    let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
    iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2
  rw [show (M A * B).trace =
      ((Matrix.stdBasis R dOut dOut).toDualEquiv B.transpose) (M A) by
    simpa using (hDualOut (M A) B.transpose).symm]
  rw [show
      ((Matrix.stdBasis R dOut dOut).toDualEquiv B.transpose) (M A) =
        ((Matrix.stdBasis R dIn dIn).toDualEquiv (coordDual B.transpose)) A by
    simp [coordDual]]
  simpa [dual, coordDual] using hDualIn A (coordDual B.transpose)

--all properties below should provable just from `inner_eq`, since the definition of `dual` itself
-- is pretty hairy (and maybe could be improved...)

set_option backward.isDefEq.respectTransparency false in
/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsHermitianPreserving) :
    M.dual.IsHermitianPreserving := by
  have map_conjTranspose (x : Matrix dIn dIn ℂ) :
      M (Matrix.conjTranspose x) = Matrix.conjTranspose (M x) := by
    have hxstar : (realPart x : Matrix dIn dIn ℂ) - Complex.I • (imaginaryPart x : Matrix dIn dIn ℂ) =
        Matrix.conjTranspose x := by
      rw [← Matrix.star_eq_conjTranspose]
      have hreal_star : (realPart (star x) : Matrix dIn dIn ℂ) = realPart x := by
        rw [realPart_apply_coe, realPart_apply_coe, star_star, add_comm]
      have himag_star : (imaginaryPart (star x) : Matrix dIn dIn ℂ) = -imaginaryPart x := by
        rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star]
        module
      have h := realPart_add_I_smul_imaginaryPart (star x : Matrix dIn dIn ℂ)
      rw [hreal_star, himag_star, smul_neg] at h
      simpa [sub_eq_add_neg] using h
    calc
      M (Matrix.conjTranspose x) = M (realPart x - Complex.I • imaginaryPart x) := by
        rw [← hxstar]
      _ = M (realPart x) - Complex.I • M (imaginaryPart x) := by
        simp [sub_eq_add_neg, map_add, map_smul]
      _ = Matrix.conjTranspose (M (realPart x) + Complex.I • M (imaginaryPart x)) := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
        rw [show Matrix.conjTranspose (M (realPart x)) = M (realPart x) by
          simpa [Matrix.IsHermitian] using h (HermitianMat.H _)]
        rw [show Matrix.conjTranspose (M (imaginaryPart x)) = M (imaginaryPart x) by
          simpa [Matrix.IsHermitian] using h (HermitianMat.H _)]
        simp [sub_eq_add_neg]
      _ = Matrix.conjTranspose (M x) := by
        congr 1
        simpa [map_add, map_smul] using congrArg M (realPart_add_I_smul_imaginaryPart x)
  intro x hx
  simpa [Matrix.IsHermitian] using show Matrix.conjTranspose (M.dual x) = M.dual x by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro A
    have htrace2 := congrArg star (Dual.trace_eq M (Matrix.conjTranspose A) (Matrix.conjTranspose x))
    rw [← Matrix.trace_conjTranspose, ← Matrix.trace_conjTranspose] at htrace2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      map_conjTranspose, hx, Matrix.conjTranspose_conjTranspose,
      Matrix.trace_mul_comm x (M A),
      Matrix.trace_mul_comm (Matrix.conjTranspose (M.dual x)) A] at htrace2
    exact htrace2.symm.trans (Dual.trace_eq M A x)

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
theorem IsPositive.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsPositive) : M.dual.IsPositive := by
  intro x hx
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hx ⊢
  use IsHermitianPreserving.dual h.IsHermitianPreserving hx.1
  intro v
  have h_dual_pos : 0 ≤ (M (Matrix.vecMulVec v (star v)) * x).trace := by
    --TODO Cleanup. Should be all in terms of HermitianMat
    apply Matrix.PosSemidef.trace_mul_nonneg;
    · apply h;
      exact Matrix.posSemidef_vecMulVec_self_star v;
    · rw [← Matrix.posSemidef_iff_dotProduct_mulVec] at hx
      exact hx;
  convert h_dual_pos using 1;
  rw [ MatrixMap.Dual.trace_eq ];
  simp [ Matrix.vecMulVec, Matrix.mul_apply, Matrix.trace ];
  simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

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
  -- By definition of dual, we know that for any A and B, the trace of (M A) * B equals the trace of
  -- A * (M.dual B).
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
  -- By definition of dual, we know that
  -- $(M.dual (single j₁ j₂ 1)) i₁ i₂ = (M (single i₂ i₁ 1)) j₂ j₁$.
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
If the Choi matrix of a map is positive semidefinite, then the Choi matrix of its dual is also
positive semidefinite.
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

private theorem matrix_mem_span_kronecker {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (X : Matrix (A × C) (A × C) 𝕜) :
    X ∈ Submodule.span 𝕜
      (Set.range (fun p : (Matrix A A 𝕜 × Matrix C C 𝕜) => p.1 ⊗ₖ p.2)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun ⟨a₁, c₁⟩ _ =>
    Submodule.sum_mem _ fun ⟨a₂, c₂⟩ _ => ?_
  rw [show Matrix.single (a₁, c₁) (a₂, c₂) (X (a₁, c₁) (a₂, c₂)) =
      X (a₁, c₁) (a₂, c₂) •
        ((Matrix.single a₁ a₂ 1 : Matrix A A 𝕜) ⊗ₖ
          (Matrix.single c₁ c₂ 1 : Matrix C C 𝕜)) by
    ext ⟨a, c⟩ ⟨a', c'⟩
    by_cases ha₁ : a₁ = a <;> by_cases hc₁ : c₁ = c <;>
      by_cases ha₂ : a₂ = a' <;> by_cases hc₂ : c₂ = c' <;>
      simp [Matrix.single, Matrix.kroneckerMap_apply, ha₁, hc₁, ha₂, hc₂]]
  exact Submodule.smul_mem _ (X (a₁, c₁) (a₂, c₂)) <|
    Submodule.subset_span ⟨
      ((Matrix.single a₁ a₂ 1 : Matrix A A 𝕜),
        (Matrix.single c₁ c₂ 1 : Matrix C C 𝕜)), rfl⟩

/--
The dual of a Kronecker product of maps is the Kronecker product of their duals.
-/
lemma dual_kron {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : MatrixMap A B 𝕜) (N : MatrixMap C D 𝕜) :
    (M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual := by
  refine dual_unique _ _ ?_
  intro X Y
  induction matrix_mem_span_kronecker X using Submodule.span_induction with
  | mem X hX =>
      rcases hX with ⟨⟨x₁, x₂⟩, rfl⟩
      induction matrix_mem_span_kronecker Y using Submodule.span_induction with
      | mem Y hY =>
          rcases hY with ⟨⟨y₁, y₂⟩, rfl⟩
          simp [MatrixMap.kron_map_of_kron_state, ← Matrix.mul_kronecker_mul,
            Matrix.trace_kronecker, Dual.trace_eq M x₁ y₁, Dual.trace_eq N x₂ y₂]
      | zero => simp
      | add Y₁ Y₂ _ _ hY₁ hY₂ =>
          simpa [map_add, Matrix.mul_add] using congrArg₂ (· + ·) hY₁ hY₂
      | smul a Y _ hY => simpa [map_smul, Matrix.mul_smul] using congrArg (a • ·) hY
  | zero => simp
  | add X₁ X₂ _ _ hX₁ hX₂ =>
      simpa [map_add, Matrix.add_mul] using congrArg₂ (· + ·) hX₁ hX₂
  | smul a X _ hX => simpa [map_smul, smul_mul_assoc] using congrArg (a • ·) hX

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem IsCompletelyPositive.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsCompletelyPositive) : M.dual.IsCompletelyPositive := by
  intro n
  have h_dual_pos : (MatrixMap.dual (M ⊗ₖₘ MatrixMap.id (Fin n) ℂ)).IsPositive := by
    exact IsPositive.dual (h n);
  -- By definition of complete positivity, we know that $(M ⊗ₖₘ id) dually map = M.dual ⊗ₖₘ id.dual$.
  have h_dual_kron : (MatrixMap.dual (M ⊗ₖₘ MatrixMap.id (Fin n) ℂ)) = (MatrixMap.dual M) ⊗ₖₘ (MatrixMap.dual (MatrixMap.id (Fin n) ℂ)) := by
    convert dual_kron M ( MatrixMap.id ( Fin n ) ℂ ) using 1;
  convert h_dual_pos using 1;
  rw [ h_dual_kron, dual_id ]

/--
The composition of the dual of the inverse of the dual basis isomorphism with the dual basis
isomorphism is the evaluation map.
-/
lemma Module.Basis.dualMap_toDualEquiv_symm_comp_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap.dualMap ∘ₗ b.toDualEquiv.toLinearMap = (Module.evalEquiv R M).toLinearMap := by
  ext x f;
  -- Since $b.toDual$ and $b.toDualEquiv.symm$ are inverses, we have $b.toDual (b.toDualEquiv.symm f) = f$.
  have h_inv : b.toDual (b.toDualEquiv.symm f) = f := by
    convert! LinearEquiv.apply_symm_apply b.toDualEquiv f;
  convert! congr_arg ( fun g => g x ) h_inv using 1;
  -- By definition of the dual basis, we know that $(b.toDual x) (b.toDualEquiv.symm f) = f x$.
  simp [Module.Basis.toDual];
  ac_rfl

/--
The composition of the inverse of the dual basis isomorphism with the dual of the dual basis
isomorphism is the inverse of the evaluation map.
-/
lemma Module.Basis.toDualEquiv_symm_comp_dualMap_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap ∘ₗ b.toDualEquiv.toLinearMap.dualMap = (Module.evalEquiv R M).symm.toLinearMap := by
  simp [ LinearMap.ext_iff ];
  intro x
  obtain ⟨y, hy⟩ : ∃ y, x = (Module.evalEquiv R M).toLinearMap y := by
    exact ⟨ _, Eq.symm <| LinearEquiv.apply_symm_apply ( Module.evalEquiv R M ) x ⟩;
  rw [ hy ];
  simp [ Module.evalEquiv, LinearEquiv.symm_apply_eq ];
  ext; simp [ Module.Dual.eval ] ;
  simp [ Module.Basis.toDual ];
  ac_rfl

@[simp]
theorem dual_dual : M.dual.dual = M := by
  refine dual_unique (M := M.dual) (M' := M) ?_
  intro A B
  calc
    (M.dual A * B).trace = (B * M.dual A).trace := by rw [Matrix.trace_mul_comm]
    _ = (M B * A).trace := by rw [Dual.trace_eq]
    _ = (A * M B).trace := by rw [Matrix.trace_mul_comm]

end MatrixMap

namespace CPTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.dual
  unital := M.TP.dual
  cp := .dual M.cp

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
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.dual T) := by
  simp only [MState.exp_val, HermitianMat.inner_eq_re_trace, RCLike.re_to_complex]
  congr 1
  apply MatrixMap.Dual.trace_eq

end CPTPMap

section hermDual

set_option backward.isDefEq.respectTransparency false in
--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
def HPMap.ofHermitianMat {dOut : Type*} (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut where
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
  HP _ h := by
    apply Matrix.IsHermitian.add
    · apply HermitianMat.H
    · simp [IsSelfAdjoint.imaginaryPart h]

set_option backward.isDefEq.respectTransparency false in
omit [Fintype dOut] in
--PULLOUT
@[simp]
theorem HPMap.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMap.ofClass (HPMap.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  simp only [ofHermitianMat, LinearMap.coe_ofClass]
  simp only [HPMap.apply_hermitianMat_eq, HPMap.map, HermitianMat.mat_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [2, 1, 2, 1]; rw [← realPart_add_I_smul_imaginaryPart x]
  suffices imaginaryPart x = 0 by simp [this]
  simp [imaginaryPart, skewAdjoint.negISMul, show star x = x from hx]

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.ofHermitianMat_linearMap (f : HPMap dIn dOut ℂ) :
    ofHermitianMat (LinearMap.ofClass f) = f := by
  ext : 3
  simp only [map, ofHermitianMat, instFunLike, LinearMap.coe_ofClass, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [realPart, imaginaryPart, LinearMap.coe_comp, Function.comp_apply]
  simp only [selfAdjointPart,  LinearMap.coe_mk, AddHom.coe_mk,
    HermitianMat.mat_mk,LinearMap.map_smul_of_tower, skewAdjoint.negISMul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp
  ring


variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product
--structure, doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear
--maps of HermitianMats and ℂ-linear maps of matrices.
def HPMap.hermDual : HPMap dOut dIn :=
  HPMap.ofHermitianMat (LinearMap.ofClass f).adjoint

@[simp]
theorem HPMap.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPMap.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMap.ofClass f) A, B⟫ = ⟪A, (LinearMap.ofClass f.hermDual) B⟫
  rw [hermDual, ← LinearMap.adjoint_inner_right, HPMap.linearMap_ofHermitianMat]

/-- Version of `HPMap.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
theorem HPMap.inner_hermDual' (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ :=
  HPMap.inner_hermDual f A B

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
  rw [HPMap.inner_hermDual, HPMap.hermDual_hermDual]
  apply HermitianMat.inner_ge_zero hx h

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem HPMap.hermDual_Unital [DecidableEq dIn] [DecidableEq dOut] (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual.map.Unital := by
  suffices f.hermDual 1 = 1 by --todo: make this is an accessible 'constructor' for Unital
    rw [HermitianMat.ext_iff] at this
    exact this
  open RealInnerProductSpace in
  apply ext_inner_left ℝ
  intro v
  rw [← HPMap.inner_hermDual]
  rw [HermitianMat.inner_one, HermitianMat.inner_one] --TODO change to Inner.inner
  exact congr(Complex.re $(h v)) --TODO: HPMap with IsTracePreserving give the HermitianMat.trace version

alias MatrixMap.IsTracePreserving.hermDual := HPMap.hermDual_Unital

namespace PTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def hermDual (M : PTPMap dIn dOut) : PUMap dOut dIn where
  toHPMap := M.toHPMap.hermDual
  pos := M.pos.hermDual
  unital := M.TP.hermDual

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
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.hermDual T) := by
  simp only [MState.exp_val]
  apply HPMap.inner_hermDual'

end PTPMap

end hermDual
