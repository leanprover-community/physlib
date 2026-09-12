/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Order
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Inner product of Hermitian Matrices

For general matrices there are multiple reasonable notions of "inner product" (Hilbert–Schmidt inner product,
Frobenius inner product), and so Mathlib avoids giving a canonical `InnerProductSpace` instance. But for the
particular case of Hermitian matrices, these all coincide, so we can put a canonical `InnerProductSpace`
instance.

This _does_ however induce a `Norm` on `HermitianMat` as well, the Frobenius norm, and this is less obviously
a uniquely correct choice. It is something that one essentially has to live with, with the way that Mathlib
currently structures the instances. (Thankfully, all norms induce the same _topology and bornology_ on
finite-dimensional matrices.)

Some care to be taken so that the topology induced by the InnerProductSpace is defeq with the Subtype
topology that HermitianMat inherits from the topology on Matrix. This can be done via
`InnerProductSpace.ofCoreOfTopology`.

-/

@[expose] public section

namespace HermitianMat

variable {R n α : Type*} [Star R] [TrivialStar R] [Fintype n]
open scoped InnerProductSpace RealInnerProductSpace
open IsMaximalSelfAdjoint

section defs

variable [Ring α] [StarAddMonoid α] [CommSemiring R] [Algebra R α] [IsMaximalSelfAdjoint R α]

/-- The Hermitian inner product, `Tr[AB]`. This is equal to `Matrix.trace (A * B)`, but gives real
  values when the matrices are complex, using `IsMaximalSelfAdjoint`. -/
instance : Inner R (HermitianMat n α) where
  inner A B := selfadjMap (A.mat * B.mat).trace

theorem inner_def (A B : HermitianMat n α) :
    ⟪A, B⟫_R = selfadjMap (A.mat * B.mat).trace := by
  rfl

end defs
section semiring

--We necessarily re-state and re-prove many of the theorems from InnerProductSpace/Basic.lean,
--because our inner product happens outside of just an `InnerProductSpace` instance.

variable [CommSemiring R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B C : HermitianMat n α)

protected theorem inner_add_right : ⟪A, B + C⟫_R = ⟪A, B⟫_R + ⟪A, C⟫_R := by
  simp [inner_def, left_distrib]

protected theorem inner_add_left : ⟪A + B, C⟫_R = ⟪A, C⟫_R + ⟪B, C⟫_R := by
  simp [inner_def, right_distrib]

@[simp]
protected theorem inner_zero_right : ⟪A, 0⟫_R = 0 := by
  simp [inner_def]

@[simp]
protected theorem inner_zero_left : ⟪0, A⟫_R = 0 := by
  simp [inner_def]

end semiring
section ring

variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B C : HermitianMat n α)

@[simp]
protected theorem inner_neg_left : ⟪-A, B⟫_R = -⟪A, B⟫_R := by
  simp [inner_def]

@[simp]
protected theorem inner_neg_right : ⟪A, -B⟫_R = -⟪A, B⟫_R := by
  simp [inner_def]

protected theorem inner_sub_left : ⟪A, B - C⟫_R = ⟪A, B⟫_R - ⟪A, C⟫_R := by
  simp [inner_def, mul_sub]

protected theorem inner_sub_right : ⟪A - B, C⟫_R = ⟪A, C⟫_R - ⟪B, C⟫_R := by
  simp [inner_def, sub_mul]

variable [StarModule R α]

@[simp]
protected theorem inner_smul_left (r : R) : ⟪r • A, B⟫_R = r * ⟪A, B⟫_R := by
  simp [inner_def, selfadj_smul]

@[simp]
protected theorem inner_smul_right (r : R) : ⟪A, r • B⟫_R = r * ⟪A, B⟫_R := by
  simp [inner_def, selfadj_smul]

/-- The Hermitian inner product as bilinear form. Compare with `innerₗ` (in the root namespace)
which requires an `InnerProductSpace` instance. -/
protected def innerₗ : LinearMap.BilinForm R (HermitianMat n α) where
  toFun A := {
    toFun := (⟪A, ·⟫_R)
    map_add' := A.inner_add_right
    map_smul' r B := by simp
  }
  map_add' A B := by ext1; apply A.inner_add_left B
  map_smul' A B := by ext1; simp

end ring
section starring

variable [CommSemiring R] [Ring α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α] [DecidableEq n]
variable (A B : HermitianMat n α)

@[simp]
theorem inner_one : ⟪A, 1⟫_R = A.trace := by
  simp only [inner_def, mat_one,  mul_one, trace]

@[simp]
theorem one_inner : ⟪1, A⟫_R = A.trace := by
  simp only [inner_def, one_mul, mat_one, trace]

end starring
section commring

variable [CommSemiring R] [CommRing α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B : HermitianMat n α)

/-- The inner product for Hermtian matrices is equal to the trace of the product. -/
theorem inner_eq_trace_mul : algebraMap R α ⟪A, B⟫_R = (A.mat * B.mat).trace := by
  apply IsMaximalSelfAdjoint.selfadj_algebra
  rw [IsSelfAdjoint, Matrix.trace]
  simp_rw [star_sum, Matrix.diag_apply, Matrix.mul_apply, star_sum, star_mul, mul_comm]
  rw [Finset.sum_comm]
  congr! <;> apply congrFun₂ (H _)

theorem inner_comm : ⟪A, B⟫_R = ⟪B, A⟫_R := by
  rw [inner_def, inner_def, Matrix.trace_mul_comm]

end commring

section trivialstar
variable [CommRing α] [StarRing α] [TrivialStar α]
variable (A B : HermitianMat n α)

/-- `HermitianMat.inner` reduces to `Matrix.trace (A * B)` when the elements are a `TrivialStar`. -/
theorem inner_eq_trace_trivial : ⟪A, B⟫_α = (A.mat * B.mat).trace := by
  rw [← inner_eq_trace_mul]
  rfl

end trivialstar

section RCLike

open ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] (A B C : HermitianMat n 𝕜)

theorem inner_eq_re_trace : ⟪A, B⟫ = RCLike.re (A.mat * B.mat).trace := by
  rfl

theorem inner_eq_trace_rc : ⟪A, B⟫ = (A.mat * B.mat).trace := by
  rw [inner_eq_re_trace, ← RCLike.conj_eq_iff_re]
  convert! (Matrix.trace_conjTranspose (A.mat * B.mat)).symm using 1
  rw [Matrix.conjTranspose_mul, A.H, B.H, Matrix.trace_mul_comm]

theorem inner_self_nonneg: 0 ≤ ⟪A, A⟫ := by
  simp_rw [inner_eq_re_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
  rw [← congrFun₂ A.H, Matrix.conjTranspose_apply]
  refine And.left <| RCLike.nonneg_iff.mp ?_
  open ComplexOrder in
  exact star_mul_self_nonneg (A.mat j i)

variable {A B C}

open MatrixOrder in
theorem inner_mul_nonneg (h : 0 ≤ A.mat * B.mat) : 0 ≤ ⟪A, B⟫ := by
  rw [Matrix.nonneg_iff_posSemidef] at h
  exact (RCLike.nonneg_iff.mp h.trace_nonneg).left

/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ ⟪A, B⟫ := by
  rw [zero_le_iff] at hB
  open MatrixOrder in
  open Classical in
  rw [inner_eq_re_trace, ← CFC.sqrt_mul_sqrt_self A.mat hA, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.mat)).left]
  exact (RCLike.nonneg_iff.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).left

theorem inner_mono (hA : 0 ≤ A) : B ≤ C → ⟪A, B⟫ ≤ ⟪A, C⟫ := by
  intro hBC
  classical have hTr : 0 ≤ ⟪A, C - B⟫ := inner_ge_zero hA (zero_le_iff.mpr hBC)
  simpa [inner_def, mul_sub] using hTr

theorem inner_mono' (hA : 0 ≤ A) : B ≤ C → ⟪B, A⟫ ≤ ⟪C, A⟫ := by
  intro hBC
  rw [inner_comm B A, inner_comm C A]
  exact inner_mono hA hBC

/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem inner_le_mul_trace (hA : 0 ≤ A) (hB : 0 ≤ B) : ⟪A, B⟫ ≤ A.trace * B.trace := by
  classical convert inner_mono hA (le_trace_smul_one hB)
  simp [mul_comm]

--TODO cleanup
private theorem inner_zero_iff_aux_lemma [DecidableEq n] (hA₁ : A.mat.PosSemidef) (hB₁ : B.mat.PosSemidef) :
  RCLike.re (A.val * B.val).trace = 0 ↔
    LinearMap.range (Matrix.toEuclideanLin A.val) ≤
      LinearMap.ker (Matrix.toEuclideanLin B.val) := by
  -- The kernel inclusion `range ≤ ker` says `(toEuclideanLin B) ∘ (toEuclideanLin A) = 0`, i.e.
  -- `B * A = 0`, which by Hermitianness of `A` and `B` is `A * B = 0`.
  rw [LinearMap.range_le_ker_iff,
    show Matrix.toEuclideanLin B.val ∘ₗ Matrix.toEuclideanLin A.val
        = Matrix.toEuclideanLin (B.val * A.val) from by
      ext v; simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.toEuclideanLin],
    LinearEquiv.map_eq_zero_iff,
    show B.val * A.val = (A.val * B.val).conjTranspose from by simp [Matrix.conjTranspose_mul],
    Matrix.conjTranspose_eq_zero]
  -- Factoring `A = Cᴴ C` and `B = Dᴴ D`, a cyclic trace identity gives `tr (A * B) = tr (Eᴴ E)`
  -- where `E = D Cᴴ`, so `re (tr (A * B)) = 0` forces `E = 0` and hence `A * B = 0`.
  open MatrixOrder in
  obtain ⟨C, hC⟩ : ∃ C : Matrix n n 𝕜, A.val = C.conjTranspose * C :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hA₁)
  open MatrixOrder in
  obtain ⟨D, hD⟩ : ∃ D : Matrix n n 𝕜, B.val = D.conjTranspose * D :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hB₁)
  have htr : (A.val * B.val).trace
      = ((D * C.conjTranspose).conjTranspose * (D * C.conjTranspose)).trace := by
    rw [hC, hD, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show C.conjTranspose * C * (D.conjTranspose * D)
          = C.conjTranspose * (C * D.conjTranspose * D) from by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show C * D.conjTranspose * D * C.conjTranspose
          = C * D.conjTranspose * (D * C.conjTranspose) from by simp [Matrix.mul_assoc]]
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  have hE0 : D * C.conjTranspose = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp <| RCLike.ext
      (by rw [← htr]; simpa using h)
      (by simpa using (RCLike.nonneg_iff.mp
        (Matrix.posSemidef_conjTranspose_mul_self (D * C.conjTranspose)).trace_nonneg).2)
  have hE0' : C * D.conjTranspose = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hE0
  rw [hC, hD, show C.conjTranspose * C * (D.conjTranspose * D)
      = C.conjTranspose * (C * D.conjTranspose) * D from by simp [Matrix.mul_assoc], hE0']
  simp

/-- The inner product of two PSD matrices is zero iff they have disjoint support, i.e., each lives entirely
in the other's kernel. -/
theorem inner_zero_iff [DecidableEq n] (hA₁ : 0 ≤ A) (hB₁ : 0 ≤ B)
    : ⟪A, B⟫ = 0 ↔ A.support ≤ B.ker := by
  rw [zero_le_iff] at hA₁ hB₁
  rw [inner_eq_re_trace]
  exact inner_zero_iff_aux_lemma hA₁ hB₁

variable {d d₂ : Type*} (A B : HermitianMat d 𝕜) [Fintype d₂] [Fintype d]

@[simp]
theorem reindex_inner (e : d ≃ d₂) (B : HermitianMat d₂ 𝕜) :
    ⟪A.reindex e, B⟫ = ⟪A, B.reindex e.symm⟫ := by
  simp only [inner_def, mat_reindex, Matrix.reindex_apply, Equiv.symm_symm]
  congr
  rw (occs := [3,4]) [← e.symm_symm]
  rw [← Matrix.submatrix_id_mul_right]
  rw (occs := [2]) [Matrix.trace_mul_comm]
  rw [Matrix.submatrix_id_mul_right, Matrix.trace_mul_comm, Equiv.symm_symm]

end RCLike

section topology
/-!
Theorems about `HermitianMat`s that have to do with the topological structure. Pretty much everything here will
assume these are matrices over ℂ, but changes to upgrade this to other types are welcome.
-/
open ComplexOrder

variable {d : Type*} [Fintype d] {𝕜 : Type*} [RCLike 𝕜]

--Check that it synthesizes ok
#guard_msgs(drop info) in
#synth ContractibleSpace (HermitianMat d ℂ)

@[fun_prop]
theorem inner_continuous : Continuous (Inner.inner ℝ (E := HermitianMat d 𝕜)) := by
  rw [funext₂ inner_eq_re_trace]
  fun_prop

@[fun_prop] --fun_prop can actually prove this, should I leave this on or not?
theorem inner_bilinForm_Continuous (A : HermitianMat d 𝕜) : Continuous ⇑(HermitianMat.innerₗ A) :=
  LinearMap.continuous_of_finiteDimensional _

end topology

section innerproductspace

variable {d d₂ : Type*} [Fintype d] [Fintype d₂] {𝕜 : Type*} [RCLike 𝕜]

/-- We define the Hermitian inner product as our "canonical" inner product, which does induce a norm.
This disagrees slightly with Mathlib convention on the `Matrix` type, which avoids asserting one norm
as there are several reasonable ones; for Hermitian matrices, though, this seem to be the right choice. -/
@[reducible]
noncomputable def InnerProductCore : InnerProductSpace.Core ℝ (HermitianMat d 𝕜) :=
   {
    inner A B := ⟪A, B⟫
    conj_inner_symm := fun x y ↦ by
      simpa using inner_comm y x
    re_inner_nonneg := inner_self_nonneg
    add_left := by simp [inner, add_mul]
    smul_left x y r := by simp
    definite x h := by
      replace h : ∑ j, ∑ i, (RCLike.re (x i j) ^ 2 + RCLike.im (x i j) ^ 2) = 0 := by
        convert h
        simp only [inner_eq_re_trace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum,
          RCLike.mul_re, sub_eq_add_neg]
        congr! 2 with i _ j
        simp only [Matrix.conjTranspose_apply, ← congrFun₂ x.H i j]
        simp [pow_two]
      ext i j
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
      replace h := congrFun h j
      rw [Pi.zero_apply, Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
      replace h := congrFun h i
      rw [Pi.zero_apply] at h
      rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity), sq_eq_zero_iff, sq_eq_zero_iff] at h
      apply RCLike.ext (h.left.trans RCLike.zero_re.symm) (h.right.trans (map_zero _).symm)
  }

open Matrix.Norms.Frobenius in
/-- The `HermitianMat` type inherits the Frobenius necessarily, since it's going to need the
Hermitian inner product, and in Mathlib an `InnerProductSpace` always carries the corresponding
norm. -/
noncomputable instance instNormedGroup : NormedAddCommGroup (HermitianMat d 𝕜) :=
  AddSubgroupClass.normedAddCommGroup _

theorem norm_eq_frobenius (A : HermitianMat d 𝕜) :
    ‖A‖ = (∑ i : d, ∑ j : d, ‖A i j‖ ^ 2) ^ (1 / 2 : ℝ) := by
  convert! ← Matrix.frobenius_norm_def A.mat
  exact Real.rpow_ofNat _ 2

theorem norm_eq_sqrt_inner_self (A : HermitianMat d 𝕜) : ‖A‖ = √(⟪A, A⟫) := by
  rw [norm_eq_frobenius, ← Real.sqrt_eq_rpow]
  congr
  simp_rw [inner_eq_re_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [map_sum]
  congr! with i _ j _
  simp only [RCLike.norm_sq_eq_def, RCLike.mul_re, sub_eq_add_neg,
    neg_mul_eq_mul_neg]
  congr 2 <;> (rw [← A.H]; simp)

noncomputable instance instNormedSpace : NormedSpace ℝ (HermitianMat d 𝕜) where
  norm_smul_le r x := by
    simp [norm_eq_sqrt_inner_self, ← mul_assoc, Real.sqrt_mul',
      inner_self_nonneg, Real.sqrt_mul_self_eq_abs]

noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (HermitianMat d 𝕜) :=
   letI : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
   letI : NormedSpace ℝ (HermitianMat d 𝕜) := instNormedSpace;
  { InnerProductCore with
    norm_sq_eq_re_inner := fun x => by
      rw [norm_eq_sqrt_inner_self, Real.sq_sqrt (inner_self_nonneg x), RCLike.re_to_real]
  }

instance : CompleteSpace (HermitianMat d 𝕜) :=
  inferInstance

--Shortcut instances
noncomputable instance : NormedAddCommGroup (HermitianMat d ℝ) :=
  inferInstance

noncomputable instance : NormedAddCommGroup (HermitianMat d ℂ) :=
  inferInstance

--PR'ed in #35056
open ComplexOrder in
lemma _root_.RCLike.instOrderClosed : OrderClosedTopology 𝕜 where
  isClosed_le' := by
    conv => enter [1, 1, p]; rw [RCLike.le_iff_re_im]
    simp_rw [Set.ofPred_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> continuity

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosed

variable (A B : HermitianMat d 𝕜)

variable {A B} in
theorem dist_le_of_mem_Icc (x : HermitianMat d 𝕜) (hA : A ≤ x) (hB : x ≤ B) :
    ‖x - A‖ ≤ ‖B - A‖ := by
  classical
  conv => enter [2, 1]; equals (B - x) + (x - A) => abel
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_add_pow_two_real, le_add_iff_nonneg_left]
  suffices 0 ≤ ⟪B - x, x - A⟫ by positivity
  apply inner_ge_zero <;> rwa [sub_nonneg]

omit [Fintype n] in
theorem Matrix.IsHermitian_isClosed : IsClosed { A : Matrix n n 𝕜 | A.IsHermitian } := by
  conv =>
    enter [1, 1, A]
    rw [Matrix.IsHermitian, ← sub_eq_zero]
  convert! isClosed_singleton.preimage (f := fun (x : Matrix n n 𝕜) ↦ (x.conjTranspose - x))
    (by fun_prop) using 1

open ComplexOrder

theorem Matrix.PosSemiDef_isClosed : IsClosed { A : Matrix n n 𝕜 | A.PosSemidef } := by
  rw [show { A : Matrix n n 𝕜 | A.PosSemidef } = { A | A.IsHermitian } ∩ { A | ∀ x : n → 𝕜, 0 ≤ star x ⬝ᵥ A.mulVec x } from by
    ext A; simp [Matrix.posSemidef_iff_dotProduct_mulVec]]
  refine IsHermitian_isClosed.inter ?_
  suffices IsClosed (⋂ x : n → 𝕜, { A : Matrix n n 𝕜 | 0 ≤ star x ⬝ᵥ A.mulVec x }) by
    rwa [← Set.ofPred_forall] at this
  exact isClosed_iInter fun _ ↦ (isClosed_Ici (a := 0)).preimage (by fun_prop)

theorem isClosed_nonneg : IsClosed { A : HermitianMat n 𝕜 | 0 ≤ A } := by
  simp_rw [zero_le_iff]
  exact Matrix.PosSemiDef_isClosed.preimage_val

--TODO: The PosDef matrices are open *within* the HermitianMat space (not in the ambient space of matrices.)

instance : OrderClosedTopology (HermitianMat d 𝕜) where
  isClosed_le' := by
    classical
    convert IsClosed.preimage (X := (HermitianMat d 𝕜 × HermitianMat d 𝕜))
      (f := fun xy ↦ (xy.2 - xy.1)) (by fun_prop) isClosed_nonneg
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, ← sub_nonneg (b := x)]

set_option backward.isDefEq.respectTransparency false in
/-- Equivalently: the matrices `X` such that `X - A` is PSD and `B - X` is PSD, form a compact set. -/
instance : CompactIccSpace (HermitianMat d 𝕜) where
  isCompact_Icc := by
    intros A B
    apply Metric.isCompact_of_isClosed_isBounded isClosed_Icc
    rw [Metric.isBounded_iff]
    use 2 * ‖B - A‖
    rintro x ⟨hxA, hxB⟩ y ⟨hyA, hyB⟩
    grw [dist_triangle_right (z := A), dist_eq_norm, dist_eq_norm]
    grw [dist_le_of_mem_Icc x hxA hxB, dist_le_of_mem_Icc y hyA hyB]
    rw [two_mul]

variable [DecidableEq d]

/-- The PSD matrices that are `≤ 1` are a compact set. More generally, this is true of any closed interval,
but stating that is a bit different because of how numerals are treated. The `0` and `1` here are already
directly matrices, putting in an `(a : ℝ) • 1 ≤ m ∧ m ≤ (b : ℝ) • 1` involves casts. But that theorem should follow
easily from this. More generally `A ≤ m ∧ m ≤ B` is compact.
-/
theorem unitInterval_IsCompact : IsCompact {m : HermitianMat d 𝕜 | 0 ≤ m ∧ m ≤ 1} :=
  CompactIccSpace.isCompact_Icc

@[simp]
theorem norm_one : ‖(1 : HermitianMat d 𝕜)‖ = √(Fintype.card d : ℝ) := by
  rw [norm_eq_sqrt_real_inner (F := HermitianMat d 𝕜)]
  congr 1
  simp [-inner_self_eq_norm_sq_to_K, inner_def]

theorem norm_eq_trace_sq : ‖A‖ ^ 2 = (A.mat ^ 2).trace := by
  rw [norm_eq_frobenius, ← RCLike.ofReal_pow, ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀, Real.rpow_one]
  simp only [sq A.mat, map_sum, map_pow, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply]
  congr! with i _ j _
  rw [← star_star (A j i), ← A.mat_apply (i := j)]
  rw [← A.mat.conjTranspose_apply j i, A.H, eq_comm]
  exact RCLike.mul_conj (A.mat i j)

end innerproductspace

--TODO: Cleanup, ew what?
/--
The inner product ⟪A, B⟫ equals ∑_{ij} a_i b_j w_{ij} where a_i, b_j are eigenvalues
and w_{ij} = ‖C_{ij}‖² for C = U_A^* U_B unitary.
-/
lemma inner_eq_doubly_stochastic_sum {d : Type*} [Fintype d] [DecidableEq d]
    (A B : HermitianMat d ℂ) :
    let C := A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val
    ⟪A, B⟫_ℝ = ∑ i, ∑ j,
      A.H.eigenvalues i * B.H.eigenvalues j * (‖C i j‖^2) := by
  intro C
  set U : Matrix d d ℂ := A.H.eigenvectorUnitary.val
  set V : Matrix d d ℂ := B.H.eigenvectorUnitary.val
  -- `U`, `V` are unitary and diagonalize `A`, `B`; `C = Uᴴ V`.
  have hUU : star U * U = 1 := A.H.eigenvectorUnitary.2.1
  have hUU' : U * star U = 1 := A.H.eigenvectorUnitary.2.2
  have hAeq : A.mat = U * Matrix.diagonal (RCLike.ofReal ∘ A.H.eigenvalues) * star U := by
    simpa [Unitary.conjStarAlgAut_apply] using A.H.spectral_theorem
  have hBeq : B.mat = V * Matrix.diagonal (RCLike.ofReal ∘ B.H.eigenvalues) * star V := by
    simpa [Unitary.conjStarAlgAut_apply] using B.H.spectral_theorem
  have hC : C = star U * V := rfl
  have hCH : C.conjTranspose = star V * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
  -- Conjugating `A * B` by `U` turns it into a product of two diagonals and `C`, `Cᴴ`.
  have key : A.mat * B.mat =
      U * (Matrix.diagonal (RCLike.ofReal ∘ A.H.eigenvalues) * C *
        Matrix.diagonal (RCLike.ofReal ∘ B.H.eigenvalues) * C.conjTranspose) * star U := by
    conv_lhs => rw [hAeq, hBeq]
    rw [hCH, hC]
    simp only [Matrix.mul_assoc, hUU', mul_one]
  have hC_norm : ∀ i j, (‖C i j‖ ^ 2 : ℂ) = C i j * star (C i j) := fun i j => by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- The trace of the diagonal product expands entrywise to the doubly-stochastic sum.
  have hC_trace : (Matrix.diagonal (RCLike.ofReal ∘ A.H.eigenvalues) * C *
      Matrix.diagonal (RCLike.ofReal ∘ B.H.eigenvalues) * C.conjTranspose).trace =
      ((∑ i, ∑ j, A.H.eigenvalues i * B.H.eigenvalues j * ‖C i j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hC_norm]
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply,
      Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      simp only [RCLike.ofReal_eq_complex_ofReal]; ring
  rw [inner_eq_re_trace, key, Matrix.trace_mul_cycle, hUU, one_mul, hC_trace]
  exact Complex.ofReal_re _

section kronecker

open Kronecker

variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [RCLike 𝕜]

/-- Pairing against `A ⊗ₖ 1` is pairing the right partial trace against `A`. -/
theorem inner_kron_one [DecidableEq m] (A : HermitianMat n 𝕜) (M : HermitianMat (n × m) 𝕜) :
    ⟪A ⊗ₖ (1 : HermitianMat m 𝕜), M⟫ = ⟪A, M.traceRight⟫ := by
  rw [inner_comm, inner_comm A, inner_eq_re_trace, inner_eq_re_trace, kronecker_mat, mat_one,
    Matrix.trace_mul_kron_one_right, traceRight_mat]

/-- Pairing against `1 ⊗ₖ B` is pairing the left partial trace against `B`. -/
theorem inner_one_kron [DecidableEq n] (B : HermitianMat m 𝕜) (M : HermitianMat (n × m) 𝕜) :
    ⟪(1 : HermitianMat n 𝕜) ⊗ₖ B, M⟫ = ⟪B, M.traceLeft⟫ := by
  rw [inner_comm, inner_comm B, inner_eq_re_trace, inner_eq_re_trace, kronecker_mat, mat_one,
    Matrix.trace_mul_one_kron_right, traceLeft_mat]

end kronecker

theorem inner_eq_zero_of_mul_eq_zero {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A B : HermitianMat n 𝕜} (h : A.mat * B.mat = 0) : ⟪A, B⟫ = 0 := by
  rw [inner_eq_re_trace, h, Matrix.trace_zero, map_zero]
