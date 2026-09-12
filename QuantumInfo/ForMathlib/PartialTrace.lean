/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Trace
public import QuantumInfo.ForMathlib.HermitianOp

public import Mathlib.LinearAlgebra.Contraction

/-!
# Partial traces

Mathlib knows the trace of an operator, but not the *partial* trace: the map that takes an operator
on `E ⊗[𝕜] F` and traces out one of the two factors. This file defines it.

The partial trace over the left factor of `A : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F` is characterised by

  `⟪y, A.traceLeft y'⟫ = ∑ i, ⟪b i ⊗ₜ y, A (b i ⊗ₜ y')⟫`

for any orthonormal basis `b` of `E`. Taking this as the *definition* would make it depend on a
basis, so instead it is defined using `stdOrthonormalBasis`, and the displayed formula is proved
for an arbitrary orthonormal basis. The proof that the right-hand side does not depend on `b` is
the only real content here: both sides are linear in `A`, and every operator on `E ⊗[𝕜] F` is a
sum of operators of the form `TensorProduct.map f g`, for which the sum evaluates to
`(LinearMap.trace f) * ⟪y, g y'⟫`.

## Main definitions

* `TensorProduct.tmulLeftL`, `TensorProduct.tmulRightL`: tensoring with a fixed vector, as a
  continuous linear map.
* `ContinuousLinearMap.traceLeft`, `ContinuousLinearMap.traceRight`: the partial traces.
* `HermitianOp.traceLeft`, `HermitianOp.traceRight`: the partial traces of a self-adjoint operator.

## Main results

* `ContinuousLinearMap.inner_traceLeft`, `ContinuousLinearMap.inner_traceRight`: the defining
  formula, for an arbitrary orthonormal basis of the factor being traced out.
* `ContinuousLinearMap.trace_traceLeft`, `ContinuousLinearMap.trace_traceRight`: the partial trace
  preserves the trace.
* `ContinuousLinearMap.IsPositive.traceLeft`, `ContinuousLinearMap.IsPositive.traceRight`: the
  partial trace preserves positivity.
* `HermitianOp.toMat_traceLeft`, `HermitianOp.toMat_traceRight`: the **matrix analogues**, saying
  that in the preferred basis the partial trace is `HermitianMat.traceLeft` / `traceRight`.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace TensorProduct

namespace TensorProduct

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (𝕜) in
/-- Tensoring with a fixed vector on the left, `y ↦ x ⊗ₜ y`, as a continuous linear map. -/
noncomputable def tmulLeftL (x : E) : F →L[𝕜] E ⊗[𝕜] F :=
  (TensorProduct.mk 𝕜 E F x).mkContinuous ‖x‖ fun y ↦ le_of_eq (by simp)

variable (𝕜) in
/-- Tensoring with a fixed vector on the right, `x ↦ x ⊗ₜ y`, as a continuous linear map. -/
noncomputable def tmulRightL (y : F) : E →L[𝕜] E ⊗[𝕜] F :=
  ((TensorProduct.mk 𝕜 E F).flip y).mkContinuous ‖y‖ fun x ↦ le_of_eq (by simp [mul_comm])

@[simp]
theorem tmulLeftL_apply (x : E) (y : F) : tmulLeftL 𝕜 x y = x ⊗ₜ[𝕜] y :=
  rfl

@[simp]
theorem tmulRightL_apply (x : E) (y : F) : tmulRightL 𝕜 y x = x ⊗ₜ[𝕜] y :=
  rfl

end TensorProduct

namespace ContinuousLinearMap

open TensorProduct

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable [Fintype ι] [Fintype κ]

section BasisIndependence

/-- The matrix elements of `A` summed over an orthonormal basis of the left factor do not depend
on the choice of that basis. This is what makes `ContinuousLinearMap.traceLeft` well defined. -/
private theorem sum_inner_tmulLeft_congr (b : OrthonormalBasis ι 𝕜 E)
    (c : OrthonormalBasis κ 𝕜 E) (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F) (y y' : F) :
    ∑ i, ⟪b i ⊗ₜ[𝕜] y, A (b i ⊗ₜ[𝕜] y')⟫_𝕜 = ∑ j, ⟪c j ⊗ₜ[𝕜] y, A (c j ⊗ₜ[𝕜] y')⟫_𝕜 := by
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv 𝕜 E F E F).surjective A
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [homTensorHomEquiv_apply, homTensorHomMap_apply, map_tmul, inner_tmul]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← LinearMap.trace_eq_sum_inner f b,
      ← LinearMap.trace_eq_sum_inner f c]
  | add t₁ t₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib, h₁, h₂]

/-- The mirror image of `sum_inner_tmulLeft_congr`, for the right factor. -/
private theorem sum_inner_tmulRight_congr (b : OrthonormalBasis ι 𝕜 F)
    (c : OrthonormalBasis κ 𝕜 F) (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F) (x x' : E) :
    ∑ i, ⟪x ⊗ₜ[𝕜] b i, A (x' ⊗ₜ[𝕜] b i)⟫_𝕜 = ∑ j, ⟪x ⊗ₜ[𝕜] c j, A (x' ⊗ₜ[𝕜] c j)⟫_𝕜 := by
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv 𝕜 E F E F).surjective A
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [homTensorHomEquiv_apply, homTensorHomMap_apply, map_tmul, inner_tmul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← LinearMap.trace_eq_sum_inner g b,
      ← LinearMap.trace_eq_sum_inner g c]
  | add t₁ t₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib, h₁, h₂]

end BasisIndependence

section Ext

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Two operators that have the same inner products against all pairs of vectors are equal. -/
private theorem ext_of_inner {S T : G →L[𝕜] G} (h : ∀ y y', ⟪y, S y'⟫_𝕜 = ⟪y, T y'⟫_𝕜) : S = T :=
  ContinuousLinearMap.ext fun y' ↦ ext_inner_left 𝕜 fun y ↦ h y y'

end Ext

section Left

variable [CompleteSpace F]

/-- The **partial trace** of an operator on `E ⊗[𝕜] F` over the left factor. -/
noncomputable def traceLeft (A : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F) : F →L[𝕜] F :=
  ∑ i, adjoint (tmulLeftL 𝕜 (stdOrthonormalBasis 𝕜 E i)) ∘L A ∘L
    tmulLeftL 𝕜 (stdOrthonormalBasis 𝕜 E i)

variable (A B : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F)

/-- The defining property of the partial trace over the left factor, for an arbitrary orthonormal
basis of the factor being traced out. -/
theorem inner_traceLeft (b : OrthonormalBasis ι 𝕜 E) (y y' : F) :
    ⟪y, A.traceLeft y'⟫_𝕜 = ∑ i, ⟪b i ⊗ₜ[𝕜] y, A (b i ⊗ₜ[𝕜] y')⟫_𝕜 := by
  rw [traceLeft, _root_.sum_apply, inner_sum]
  simp only [ContinuousLinearMap.comp_apply, adjoint_inner_right, tmulLeftL_apply]
  exact sum_inner_tmulLeft_congr _ b (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F) y y'

@[simp]
theorem traceLeft_zero : traceLeft (0 : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F) = 0 :=
  ext_of_inner fun y y' ↦ by
    rw [inner_traceLeft _ (stdOrthonormalBasis 𝕜 E)]; simp

@[simp]
theorem traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft :=
  ext_of_inner fun y y' ↦ by
    simp only [inner_traceLeft _ (stdOrthonormalBasis 𝕜 E), _root_.add_apply,
      inner_add_right, Finset.sum_add_distrib]

@[simp]
theorem traceLeft_smul (r : 𝕜) : (r • A).traceLeft = r • A.traceLeft :=
  ext_of_inner fun y y' ↦ by
    simp only [inner_traceLeft _ (stdOrthonormalBasis 𝕜 E), _root_.smul_apply,
      inner_smul_right, Finset.mul_sum]

@[simp]
theorem traceLeft_neg : (-A).traceLeft = -A.traceLeft :=
  ext_of_inner fun y y' ↦ by
    simp only [inner_traceLeft _ (stdOrthonormalBasis 𝕜 E), _root_.neg_apply,
      inner_neg_right, Finset.sum_neg_distrib]

@[simp]
theorem traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft := by
  rw [sub_eq_add_neg, traceLeft_add, traceLeft_neg, ← sub_eq_add_neg]

/-- The partial trace over the left factor preserves symmetry. -/
theorem IsSymmetric.traceLeft (hA : (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F).IsSymmetric) :
    (A.traceLeft : F →ₗ[𝕜] F).IsSymmetric := by
  intro y y'
  rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm (A.traceLeft y) y',
    inner_traceLeft _ (stdOrthonormalBasis 𝕜 E), inner_traceLeft _ (stdOrthonormalBasis 𝕜 E),
    map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [inner_conj_symm]; exact hA _ _

/-- The partial trace over the left factor preserves positivity. -/
theorem IsPositive.traceLeft (hA : A.IsPositive) : A.traceLeft.IsPositive := by
  refine ⟨IsSymmetric.traceLeft A hA.1, fun y ↦ ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, ← RCLike.conj_re (⟪A.traceLeft y, y⟫_𝕜),
    inner_conj_symm, inner_traceLeft _ (stdOrthonormalBasis 𝕜 E), map_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  have h := hA.2 (stdOrthonormalBasis 𝕜 E i ⊗ₜ[𝕜] y)
  rwa [ContinuousLinearMap.reApplyInnerSelf, ← inner_conj_symm, RCLike.conj_re] at h

/-- The partial trace over the left factor preserves the trace. -/
@[simp]
theorem trace_traceLeft :
    LinearMap.trace 𝕜 F (A.traceLeft : F →ₗ[𝕜] F) =
      LinearMap.trace 𝕜 (E ⊗[𝕜] F) (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F) := by
  classical
  set b := stdOrthonormalBasis 𝕜 E
  set c := stdOrthonormalBasis 𝕜 F
  rw [LinearMap.trace_eq_sum_inner _ c, LinearMap.trace_eq_sum_inner _ (b.tensorProduct c),
    Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun j _ ↦ by
    simpa using inner_traceLeft A b (c j) (c j)

end Left

section Right

variable [CompleteSpace E]

/-- The **partial trace** of an operator on `E ⊗[𝕜] F` over the right factor. -/
noncomputable def traceRight (A : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F) : E →L[𝕜] E :=
  ∑ i, adjoint (tmulRightL 𝕜 (stdOrthonormalBasis 𝕜 F i)) ∘L A ∘L
    tmulRightL 𝕜 (stdOrthonormalBasis 𝕜 F i)

variable (A B : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F)

/-- The defining property of the partial trace over the right factor, for an arbitrary orthonormal
basis of the factor being traced out. -/
theorem inner_traceRight (b : OrthonormalBasis ι 𝕜 F) (x x' : E) :
    ⟪x, A.traceRight x'⟫_𝕜 = ∑ i, ⟪x ⊗ₜ[𝕜] b i, A (x' ⊗ₜ[𝕜] b i)⟫_𝕜 := by
  rw [traceRight, _root_.sum_apply, inner_sum]
  simp only [ContinuousLinearMap.comp_apply, adjoint_inner_right, tmulRightL_apply]
  exact sum_inner_tmulRight_congr _ b (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F) x x'

@[simp]
theorem traceRight_zero : traceRight (0 : (E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F) = 0 :=
  ext_of_inner fun x x' ↦ by
    rw [inner_traceRight _ (stdOrthonormalBasis 𝕜 F)]; simp

@[simp]
theorem traceRight_add : (A + B).traceRight = A.traceRight + B.traceRight :=
  ext_of_inner fun x x' ↦ by
    simp only [inner_traceRight _ (stdOrthonormalBasis 𝕜 F), _root_.add_apply,
      inner_add_right, Finset.sum_add_distrib]

@[simp]
theorem traceRight_smul (r : 𝕜) : (r • A).traceRight = r • A.traceRight :=
  ext_of_inner fun x x' ↦ by
    simp only [inner_traceRight _ (stdOrthonormalBasis 𝕜 F), _root_.smul_apply,
      inner_smul_right, Finset.mul_sum]

@[simp]
theorem traceRight_neg : (-A).traceRight = -A.traceRight :=
  ext_of_inner fun x x' ↦ by
    simp only [inner_traceRight _ (stdOrthonormalBasis 𝕜 F), _root_.neg_apply,
      inner_neg_right, Finset.sum_neg_distrib]

@[simp]
theorem traceRight_sub : (A - B).traceRight = A.traceRight - B.traceRight := by
  rw [sub_eq_add_neg, traceRight_add, traceRight_neg, ← sub_eq_add_neg]

/-- The partial trace over the right factor preserves symmetry. -/
theorem IsSymmetric.traceRight (hA : (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F).IsSymmetric) :
    (A.traceRight : E →ₗ[𝕜] E).IsSymmetric := by
  intro x x'
  rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm (A.traceRight x) x',
    inner_traceRight _ (stdOrthonormalBasis 𝕜 F), inner_traceRight _ (stdOrthonormalBasis 𝕜 F),
    map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [inner_conj_symm]; exact hA _ _

/-- The partial trace over the right factor preserves positivity. -/
theorem IsPositive.traceRight (hA : A.IsPositive) : A.traceRight.IsPositive := by
  refine ⟨IsSymmetric.traceRight A hA.1, fun x ↦ ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, ← RCLike.conj_re (⟪A.traceRight x, x⟫_𝕜),
    inner_conj_symm, inner_traceRight _ (stdOrthonormalBasis 𝕜 F), map_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  have h := hA.2 (x ⊗ₜ[𝕜] stdOrthonormalBasis 𝕜 F i)
  rwa [ContinuousLinearMap.reApplyInnerSelf, ← inner_conj_symm, RCLike.conj_re] at h

/-- The partial trace over the right factor preserves the trace. -/
@[simp]
theorem trace_traceRight :
    LinearMap.trace 𝕜 E (A.traceRight : E →ₗ[𝕜] E) =
      LinearMap.trace 𝕜 (E ⊗[𝕜] F) (A : (E ⊗[𝕜] F) →ₗ[𝕜] E ⊗[𝕜] F) := by
  classical
  set b := stdOrthonormalBasis 𝕜 E
  set c := stdOrthonormalBasis 𝕜 F
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ (b.tensorProduct c),
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simpa using inner_traceRight A c (b i) (b i)

end Right

end ContinuousLinearMap

namespace HermitianOp

open TensorProduct

variable {E F ι κ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

section Left

/-- The partial trace of a self-adjoint operator over the left factor. -/
noncomputable def traceLeft (A : HermitianOp (E ⊗[ℂ] F)) : HermitianOp F :=
  ⟨A.op.traceLeft, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    (ContinuousLinearMap.IsSymmetric.traceLeft A.op
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 A.H))⟩

@[simp]
theorem op_traceLeft (A : HermitianOp (E ⊗[ℂ] F)) : A.traceLeft.op = A.op.traceLeft :=
  rfl

variable (A B : HermitianOp (E ⊗[ℂ] F))

@[simp] theorem traceLeft_zero : (0 : HermitianOp (E ⊗[ℂ] F)).traceLeft = 0 :=
  HermitianOp.ext <| by simp

@[simp] theorem traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft :=
  HermitianOp.ext <| by simp

@[simp] theorem traceLeft_neg : (-A).traceLeft = -A.traceLeft :=
  HermitianOp.ext <| by simp

@[simp] theorem traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft :=
  HermitianOp.ext <| by simp

@[simp] theorem traceLeft_smul (r : ℝ) : (r • A).traceLeft = r • A.traceLeft :=
  HermitianOp.ext <| by
    show ((r : ℂ) • A.op).traceLeft = (r : ℂ) • A.op.traceLeft
    exact ContinuousLinearMap.traceLeft_smul A.op r

/-- The partial trace over the left factor preserves nonnegativity. -/
theorem traceLeft_nonneg (h : 0 ≤ A) : 0 ≤ A.traceLeft :=
  zero_le_iff.2 (ContinuousLinearMap.IsPositive.traceLeft A.op (zero_le_iff.1 h))

@[simp]
theorem trace_traceLeft : A.traceLeft.trace = A.trace := by
  rw [trace, trace, op_traceLeft, ContinuousLinearMap.trace_traceLeft]

/-- **Matrix analogue of `HermitianOp.traceLeft`.** In the preferred basis, the partial trace over
the left factor is `HermitianMat.traceLeft`. -/
@[simp]
theorem toMat_traceLeft [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ] :
    toMat (ι := κ) A.traceLeft = (toMat (ι := ι × κ) A).traceLeft := by
  apply HermitianMat.ext
  ext j j'
  simp only [HermitianMat.traceLeft_mat, Matrix.traceLeft, Matrix.of_apply, toMat_mat,
    op_traceLeft, StdBasis.toMat_apply]
  rw [ContinuousLinearMap.inner_traceLeft _ (stdBasis (𝕜 := ℂ) (E := E))]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp [OrthonormalBasis.tensorProduct_apply]

end Left

section Right

/-- The partial trace of a self-adjoint operator over the right factor. -/
noncomputable def traceRight (A : HermitianOp (E ⊗[ℂ] F)) : HermitianOp E :=
  ⟨A.op.traceRight, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    (ContinuousLinearMap.IsSymmetric.traceRight A.op
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 A.H))⟩

@[simp]
theorem op_traceRight (A : HermitianOp (E ⊗[ℂ] F)) : A.traceRight.op = A.op.traceRight :=
  rfl

variable (A B : HermitianOp (E ⊗[ℂ] F))

@[simp] theorem traceRight_zero : (0 : HermitianOp (E ⊗[ℂ] F)).traceRight = 0 :=
  HermitianOp.ext <| by simp

@[simp] theorem traceRight_add : (A + B).traceRight = A.traceRight + B.traceRight :=
  HermitianOp.ext <| by simp

@[simp] theorem traceRight_neg : (-A).traceRight = -A.traceRight :=
  HermitianOp.ext <| by simp

@[simp] theorem traceRight_sub : (A - B).traceRight = A.traceRight - B.traceRight :=
  HermitianOp.ext <| by simp

@[simp] theorem traceRight_smul (r : ℝ) : (r • A).traceRight = r • A.traceRight :=
  HermitianOp.ext <| by
    show ((r : ℂ) • A.op).traceRight = (r : ℂ) • A.op.traceRight
    exact ContinuousLinearMap.traceRight_smul A.op r

/-- The partial trace over the right factor preserves nonnegativity. -/
theorem traceRight_nonneg (h : 0 ≤ A) : 0 ≤ A.traceRight :=
  zero_le_iff.2 (ContinuousLinearMap.IsPositive.traceRight A.op (zero_le_iff.1 h))

@[simp]
theorem trace_traceRight : A.traceRight.trace = A.trace := by
  rw [trace, trace, op_traceRight, ContinuousLinearMap.trace_traceRight]

/-- **Matrix analogue of `HermitianOp.traceRight`.** In the preferred basis, the partial trace over
the right factor is `HermitianMat.traceRight`. -/
@[simp]
theorem toMat_traceRight [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ] :
    toMat (ι := ι) A.traceRight = (toMat (ι := ι × κ) A).traceRight := by
  apply HermitianMat.ext
  ext i i'
  simp only [HermitianMat.traceRight_mat, Matrix.traceRight, Matrix.of_apply, toMat_mat,
    op_traceRight, StdBasis.toMat_apply]
  rw [ContinuousLinearMap.inner_traceRight _ (stdBasis (𝕜 := ℂ) (E := F))]
  exact Finset.sum_congr rfl fun j _ ↦ by
    simp [OrthonormalBasis.tensorProduct_apply]

end Right

end HermitianOp
