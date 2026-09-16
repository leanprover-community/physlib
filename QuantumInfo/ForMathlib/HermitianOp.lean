/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Inner
public import QuantumInfo.ForMathlib.HermitianMat.Rpow
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.ForMathlib.StdBasis

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Self-adjoint operators on a Hilbert space

`HermitianOp E` is the type of self-adjoint continuous linear operators on a complex inner product
space `E`. It is the basis-free counterpart of `HermitianMat ι ℂ`, and it is the type in which
observables, density operators and POVM elements naturally live.

Given a preferred orthonormal basis (a `StdBasis ℂ E ι` instance), `HermitianOp.toMat` identifies
`HermitianOp E` with `HermitianMat ι ℂ`. Because `StdBasis.toMat` is a ⋆-algebra equivalence, the
identification is compatible with everything of interest: the additive and `ℝ`-module structures,
the Loewner order, the trace, the spectrum, and the continuous functional calculus. The lemmas
transporting those are the *matrix analogues* of the operator-level statements, and they are what
lets an existing matrix definition be reused verbatim on operators.

## Main definitions

* `HermitianOp E`: self-adjoint operators on `E`.
* `HermitianOp.toMat`, `HermitianOp.ofMat`: the mutually inverse maps to and from
  `HermitianMat ι ℂ` determined by the preferred basis.
* `HermitianOp.trace`, `HermitianOp.cfc`: the trace and the continuous functional calculus,
  defined operator-side.
* `HermitianOp.sqrt`, `HermitianOp.rpow`, `HermitianOp.log`, `HermitianOp.exp`,
  `HermitianOp.abs`: the standard operator functions, all instances of `HermitianOp.cfc`.
* `HermitianOp.conj`: conjugation `A ↦ B A B⋆`.
* `HermitianOp.traceNorm`: the Schatten 1-norm, i.e. the sum of the absolute values of the
  eigenvalues.

## Main results

* `HermitianOp.matEquiv`: the identification with `HermitianMat ι ℂ` as an `ℝ`-linear equivalence.
* `HermitianOp.toMat_cfc`, `HermitianOp.trace_toMat`, `HermitianOp.toMat_le_toMat`: the matrix
  analogues of the operator-level `cfc`, `trace` and order.
-/

@[expose] public section

open scoped ComplexOrder

/-- The type of self-adjoint continuous linear operators on `E`, as a `Subtype`.

This is the basis-free analogue of `HermitianMat`; see `HermitianOp.matEquiv` for the
identification of the two given a preferred orthonormal basis. -/
def HermitianOp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :=
  (selfAdjoint (E →L[ℂ] E) : Type _)

namespace HermitianOp

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The underlying operator of a `HermitianOp`. -/
@[coe] def op : HermitianOp E → (E →L[ℂ] E) :=
  Subtype.val

instance : Coe (HermitianOp E) (E →L[ℂ] E) := ⟨op⟩

/-- The underlying operator of a `HermitianOp` is self-adjoint. -/
theorem H (A : HermitianOp E) : IsSelfAdjoint A.op :=
  A.2

@[simp]
theorem op_mk (A : E →L[ℂ] E) (h) : op ⟨A, h⟩ = A :=
  rfl

@[ext] protected theorem ext {A B : HermitianOp E} : A.op = B.op → A = B :=
  Subtype.ext

theorem op_injective : Function.Injective (op (E := E)) :=
  fun _ _ ↦ HermitianOp.ext

noncomputable instance : AddCommGroup (HermitianOp E) :=
  inferInstanceAs (AddCommGroup (selfAdjoint (E →L[ℂ] E)))

noncomputable instance : Module ℝ (HermitianOp E) :=
  inferInstanceAs (Module ℝ (selfAdjoint (E →L[ℂ] E)))

noncomputable instance : PartialOrder (HermitianOp E) :=
  inferInstanceAs (PartialOrder (selfAdjoint (E →L[ℂ] E)))

@[simp] theorem op_zero : (0 : HermitianOp E).op = 0 := rfl

@[simp] theorem op_add (A B : HermitianOp E) : (A + B).op = A.op + B.op := rfl

@[simp] theorem op_neg (A : HermitianOp E) : (-A).op = -A.op := rfl

@[simp] theorem op_sub (A B : HermitianOp E) : (A - B).op = A.op - B.op := rfl

@[simp] theorem op_smul (r : ℝ) (A : HermitianOp E) : (r • A).op = r • A.op := rfl

theorem le_def {A B : HermitianOp E} : A ≤ B ↔ A.op ≤ B.op :=
  Iff.rfl

/-- A self-adjoint operator is nonnegative exactly when it is a positive operator. -/
theorem zero_le_iff {A : HermitianOp E} : 0 ≤ A ↔ A.op.IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive A.op

/-- The trace of a self-adjoint operator. It is real because the operator is self-adjoint. -/
noncomputable def trace [FiniteDimensional ℂ E] (A : HermitianOp E) : ℝ :=
  RCLike.re (LinearMap.trace ℂ E (A.op : E →ₗ[ℂ] E))

/-- The continuous functional calculus applied to a self-adjoint operator. -/
noncomputable def cfc (A : HermitianOp E) (f : ℝ → ℝ) : HermitianOp E :=
  ⟨_root_.cfc f A.op, cfc_predicate _ _⟩

@[simp]
theorem op_cfc (A : HermitianOp E) (f : ℝ → ℝ) : (A.cfc f).op = _root_.cfc f A.op :=
  rfl

/-- The square root of a self-adjoint operator. Negative spectrum is mapped to zero. -/
noncomputable def sqrt (A : HermitianOp E) : HermitianOp E :=
  A.cfc Real.sqrt

/-- Real powers of a self-adjoint operator. This carries the usual `Real.rpow` caveats: for
instance the zero operator to the power `-1` is zero. -/
noncomputable def rpow (A : HermitianOp E) (r : ℝ) : HermitianOp E :=
  A.cfc (Real.rpow · r)

noncomputable instance instRPow : Pow (HermitianOp E) ℝ :=
  ⟨rpow⟩

theorem pow_eq_rpow (A : HermitianOp E) (r : ℝ) : A ^ r = A.rpow r :=
  rfl

/-- The logarithm of a self-adjoint operator. Nonpositive spectrum is mapped to zero, following
the convention of `Real.log`. -/
noncomputable def log (A : HermitianOp E) : HermitianOp E :=
  A.cfc Real.log

/-- The exponential of a self-adjoint operator. -/
noncomputable def exp (A : HermitianOp E) : HermitianOp E :=
  A.cfc Real.exp

/-- The absolute value of a self-adjoint operator, i.e. `|·|` applied to its spectrum. -/
noncomputable def abs (A : HermitianOp E) : HermitianOp E :=
  A.cfc (|·|)

/-- Conjugation of a self-adjoint operator, `A ↦ B A B⋆`. -/
noncomputable def conj (A : HermitianOp E) (B : E →L[ℂ] E) : HermitianOp E :=
  ⟨B * A.op * star B, A.H.conjugate B⟩

@[simp]
theorem op_conj (A : HermitianOp E) (B : E →L[ℂ] E) : (A.conj B).op = B * A.op * star B :=
  rfl

@[simp]
theorem conj_one (A : HermitianOp E) : A.conj 1 = A :=
  op_injective <| by rw [op_conj, star_one, mul_one, one_mul]

theorem conj_conj (A : HermitianOp E) (B C : E →L[ℂ] E) : (A.conj B).conj C = A.conj (C * B) :=
  op_injective <| by simp only [op_conj, star_mul, mul_assoc]

/-- Conjugation preserves nonnegativity. -/
theorem conj_nonneg {A : HermitianOp E} (h : 0 ≤ A) (B : E →L[ℂ] E) : 0 ≤ A.conj B := by
  rw [zero_le_iff, op_conj, mul_assoc]
  exact (zero_le_iff.1 h).conj_adjoint B

/-- The Hilbert–Schmidt inner product `Tr[A B]` of two self-adjoint operators. It is real
because both operators are. -/
noncomputable instance [FiniteDimensional ℂ E] : Inner ℝ (HermitianOp E) where
  inner A B := RCLike.re (LinearMap.trace ℂ E ((A.op * B.op : E →L[ℂ] E) : E →ₗ[ℂ] E))

theorem inner_def [FiniteDimensional ℂ E] (A B : HermitianOp E) :
    (inner ℝ A B : ℝ) = RCLike.re (LinearMap.trace ℂ E ((A.op * B.op : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
  rfl

/-- The kernel of a self-adjoint operator, equivalently its zero eigenspace. -/
def ker (A : HermitianOp E) : Submodule ℂ E :=
  LinearMap.ker (A.op : E →ₗ[ℂ] E)

theorem mem_ker_iff {A : HermitianOp E} {x : E} : x ∈ A.ker ↔ A.op x = 0 :=
  Iff.rfl

/-- The support of a self-adjoint operator: the span of its nonzero eigenspaces. -/
def support (A : HermitianOp E) : Submodule ℂ E :=
  LinearMap.range (A.op : E →ₗ[ℂ] E)

@[simp]
theorem ker_zero : (0 : HermitianOp E).ker = ⊤ := by
  simp [ker]

@[simp]
theorem support_zero : (0 : HermitianOp E).support = ⊥ := by
  simp [support]

/-- The trace norm (Schatten 1-norm) of a self-adjoint operator: the sum of the absolute values
of its eigenvalues. -/
noncomputable def traceNorm [FiniteDimensional ℂ E] (A : HermitianOp E) : ℝ :=
  A.abs.trace

section Congr

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Transport a self-adjoint operator along a linear isometry equivalence. -/
noncomputable def congr (A : HermitianOp E) (e : E ≃ₗᵢ[ℂ] F) : HermitianOp F :=
  ⟨e.conjStarAlgEquiv A.op, by
    show star (e.conjStarAlgEquiv A.op) = _
    rw [← map_star, A.H.star_eq]⟩

@[simp]
theorem op_congr (A : HermitianOp E) (e : E ≃ₗᵢ[ℂ] F) :
    (A.congr e).op = e.conjStarAlgEquiv A.op :=
  rfl

/-- Transport along a linear isometry equivalence preserves nonnegativity. -/
theorem congr_nonneg {A : HermitianOp E} (h : 0 ≤ A) (e : E ≃ₗᵢ[ℂ] F) : 0 ≤ A.congr e :=
  zero_le_iff.2 ((zero_le_iff.1 h).conjStarAlgEquiv e)

/-- Transport along a linear isometry equivalence preserves the trace. -/
@[simp]
theorem trace_congr [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (A : HermitianOp E)
    (e : E ≃ₗᵢ[ℂ] F) : (A.congr e).trace = A.trace := by
  have hb := stdOrthonormalBasis ℂ E
  rw [trace, trace, LinearMap.trace_eq_sum_inner _ (hb.map e),
    LinearMap.trace_eq_sum_inner _ hb]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [ContinuousLinearMap.coe_coe, op_congr, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    e.inner_map_map]
  rfl

end Congr

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]

/-- The matrix of a self-adjoint operator in the preferred basis. -/
noncomputable def toMat (A : HermitianOp E) : HermitianMat ι ℂ :=
  ⟨StdBasis.toMat ℂ E ι A.op, (StdBasis.isHermitian_toMat_iff _).2 A.H⟩

/-- The self-adjoint operator with a given matrix in the preferred basis. -/
noncomputable def ofMat (M : HermitianMat ι ℂ) : HermitianOp E :=
  ⟨(StdBasis.toMat ℂ E ι).symm M.mat, by
    show star ((StdBasis.toMat ℂ E ι).symm M.mat) = _
    rw [← map_star, Matrix.star_eq_conjTranspose, M.H]⟩

@[simp]
theorem toMat_mat (A : HermitianOp E) : (toMat (ι := ι) A).mat = StdBasis.toMat ℂ E ι A.op :=
  rfl

@[simp]
theorem ofMat_op (M : HermitianMat ι ℂ) :
    (ofMat (E := E) M).op = (StdBasis.toMat ℂ E ι).symm M.mat :=
  rfl

@[simp]
theorem toMat_ofMat (M : HermitianMat ι ℂ) : toMat (ofMat (E := E) M) = M := by
  ext1
  simp

@[simp]
theorem ofMat_toMat (A : HermitianOp E) : ofMat (toMat (ι := ι) A) = A := by
  ext1
  simp

theorem toMat_injective : Function.Injective (toMat (E := E) (ι := ι)) :=
  Function.LeftInverse.injective ofMat_toMat

@[simp] theorem toMat_zero : toMat (0 : HermitianOp E) = (0 : HermitianMat ι ℂ) := by
  ext1; simp

@[simp] theorem toMat_add (A B : HermitianOp E) :
    toMat (ι := ι) (A + B) = toMat A + toMat B := by
  ext1; simp

@[simp] theorem toMat_neg (A : HermitianOp E) : toMat (ι := ι) (-A) = -toMat A := by
  ext1; simp

@[simp] theorem toMat_sub (A B : HermitianOp E) :
    toMat (ι := ι) (A - B) = toMat A - toMat B := by
  ext1; simp

@[simp] theorem toMat_smul (r : ℝ) (A : HermitianOp E) :
    toMat (ι := ι) (r • A) = r • toMat A := by
  ext1
  show StdBasis.toMat ℂ E ι ((r : ℂ) • A.op) = (r : ℂ) • StdBasis.toMat ℂ E ι A.op
  exact map_smul _ _ _

/-- **Matrix analogue of the operator order.** An inequality of self-adjoint operators is exactly
the Loewner inequality of their matrices in the preferred basis. -/
@[simp]
theorem toMat_le_toMat {A B : HermitianOp E} : toMat (ι := ι) A ≤ toMat B ↔ A ≤ B := by
  rw [HermitianMat.le_iff, le_def, ContinuousLinearMap.le_def,
    ← StdBasis.posSemidef_toMat_iff (ι := ι)]
  congr! 1
  show (toMat (ι := ι) B - toMat A).mat = _
  rw [HermitianMat.mat_sub, toMat_mat, toMat_mat, ← map_sub]

/-- The identification of self-adjoint operators with Hermitian matrices determined by the
preferred basis, as an `ℝ`-linear equivalence. -/
@[simps apply symm_apply]
noncomputable def matEquiv : HermitianOp E ≃ₗ[ℝ] HermitianMat ι ℂ where
  toFun := toMat
  invFun := ofMat
  left_inv := ofMat_toMat
  right_inv := toMat_ofMat
  map_add' := toMat_add
  map_smul' := toMat_smul

/-- **Matrix analogue of the operator trace.** -/
@[simp]
theorem trace_toMat (A : HermitianOp E) : (toMat (ι := ι) A).trace = A.trace := by
  rw [HermitianMat.trace_eq_re_trace, trace, toMat_mat, StdBasis.trace_toMat]

/-- The spectrum of a self-adjoint operator is the spectrum of its matrix. -/
theorem spectrum_toMat (A : HermitianOp E) :
    spectrum ℝ (toMat (ι := ι) A).mat = spectrum ℝ A.op :=
  AlgEquiv.spectrum_eq ((StdBasis.toMat ℂ E ι).toAlgEquiv.restrictScalars ℝ) A.op

/-- The spectrum of an operator on a space with a preferred basis is finite: it is the spectrum of
a matrix. -/
instance finite_spectrum (A : E →L[ℂ] E) : Finite (spectrum ℝ A) := by
  rw [← AlgEquiv.spectrum_eq ((StdBasis.toMat ℂ E ι).toAlgEquiv.restrictScalars ℝ) A]
  infer_instance

/-- **Matrix analogue of the operator continuous functional calculus.** -/
@[simp]
theorem toMat_cfc (A : HermitianOp E) (f : ℝ → ℝ) :
    toMat (ι := ι) (A.cfc f) = (toMat A).cfc f := by
  ext1
  rw [toMat_mat, op_cfc, HermitianMat.mat_cfc, toMat_mat]
  refine StarAlgHomClass.map_cfc (S := ℂ) _ f A.op
    (HermitianMat.continuousOn_finite f _) ?_ A.H ((StdBasis.isHermitian_toMat_iff _).2 A.H)
  exact (StdBasis.toMat ℂ E ι).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

/-- **Matrix analogue of `HermitianOp.sqrt`.** -/
@[simp]
theorem toMat_sqrt (A : HermitianOp E) : toMat (ι := ι) A.sqrt = (toMat A).sqrt :=
  toMat_cfc A _

/-- **Matrix analogue of `HermitianOp.rpow`.** -/
@[simp]
theorem toMat_rpow (A : HermitianOp E) (r : ℝ) : toMat (ι := ι) (A ^ r) = (toMat A) ^ r :=
  toMat_cfc A _

/-- **Matrix analogue of `HermitianOp.log`.** -/
@[simp]
theorem toMat_log (A : HermitianOp E) : toMat (ι := ι) A.log = (toMat A).log :=
  toMat_cfc A _

/-- **Matrix analogue of `HermitianOp.exp`.** -/
@[simp]
theorem toMat_exp (A : HermitianOp E) : toMat (ι := ι) A.exp = (toMat A).exp :=
  toMat_cfc A _

/-- **Matrix analogue of `HermitianOp.abs`.** -/
@[simp]
theorem toMat_abs (A : HermitianOp E) : toMat (ι := ι) A.abs = (toMat A).cfc (|·|) :=
  toMat_cfc A _

/-- **Matrix analogue of `HermitianOp.conj`.** -/
@[simp]
theorem toMat_conj (A : HermitianOp E) (B : E →L[ℂ] E) :
    toMat (ι := ι) (A.conj B) = (toMat A).conj (StdBasis.toMat ℂ E ι B) := by
  ext1
  rw [toMat_mat, op_conj, HermitianMat.conj_apply_mat, map_mul, map_mul, toMat_mat,
    ← Matrix.star_eq_conjTranspose, ← map_star]

/-- **Matrix analogue of the Hilbert–Schmidt inner product.** -/
@[simp]
theorem inner_toMat (A B : HermitianOp E) :
    (inner ℝ (toMat (ι := ι) A) (toMat B) : ℝ) = inner ℝ A B := by
  rw [HermitianMat.inner_def, IsMaximalSelfAdjoint.RCLike_selfadjMap, inner_def, toMat_mat,
    toMat_mat, ← map_mul, StdBasis.trace_toMat]

/-- **Matrix analogue of `HermitianOp.traceNorm`.** -/
theorem traceNorm_toMat (A : HermitianOp E) :
    A.traceNorm = Matrix.traceNorm (HermitianMat.mat (toMat (ι := ι) A)) := by
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues (toMat (ι := ι) A).H, traceNorm, abs,
    ← trace_toMat (ι := ι), toMat_cfc, ← HermitianMat.sum_eigenvalues_eq_trace]
  obtain ⟨e, he⟩ := (toMat (ι := ι) A).cfc_eigenvalues (f := (|·|))
  refine Finset.sum_equiv e (by simp) fun i _ ↦ ?_
  simp only [he, Function.comp_apply]
  congr!

/-- The matrix of `A` in the preferred basis acts on `EuclideanSpace ℂ ι` as `A` does on `E`,
transported along the coordinate isometry. -/
theorem lin_toMat_apply (A : HermitianOp E) (x : EuclideanSpace ℂ ι) :
    (toMat (ι := ι) A).lin x =
      (stdBasis (𝕜 := ℂ) (E := E)).repr (A.op ((stdBasis (𝕜 := ℂ) (E := E)).repr.symm x)) := by
  have h : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (toMat (ι := ι) A).mat =
      (stdBasis (𝕜 := ℂ) (E := E)).repr.conjStarAlgEquiv A.op := by
    rw [toMat_mat, StdBasis.toMat_def, StdBasis.toMatOf, StarAlgEquiv.trans_apply,
      StarAlgEquiv.apply_symm_apply]
  have hx : (toMat (ι := ι) A).lin x = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
      (toMat (ι := ι) A).mat x := by
    rw [← ContinuousLinearMap.coe_coe (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) _),
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  rw [hx, h, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- **Matrix analogue of `HermitianOp.ker`**: the kernel of the matrix in the preferred basis is
the kernel of the operator, read in coordinates. -/
theorem mem_ker_toMat_iff (A : HermitianOp E) (x : EuclideanSpace ℂ ι) :
    x ∈ (toMat (ι := ι) A).ker ↔ (stdBasis (𝕜 := ℂ) (E := E)).repr.symm x ∈ A.ker := by
  rw [HermitianMat.ker, LinearMap.mem_ker, mem_ker_iff]
  show (toMat (ι := ι) A).lin x = 0 ↔ _
  rw [lin_toMat_apply, map_eq_zero_iff _ (stdBasis (𝕜 := ℂ) (E := E)).repr.injective]

theorem ker_toMat_le_ker_toMat {A B : HermitianOp E} :
    (toMat (ι := ι) A).ker ≤ (toMat (ι := ι) B).ker ↔ A.ker ≤ B.ker := by
  constructor
  · intro h y hy
    have hy' : (stdBasis (𝕜 := ℂ) (E := E)).repr y ∈ (toMat (ι := ι) A).ker := by
      rw [mem_ker_toMat_iff]
      simpa using hy
    simpa using (mem_ker_toMat_iff (ι := ι) B _).1 (h hy')
  · intro h x hx
    rw [mem_ker_toMat_iff] at hx ⊢
    exact h hx

/-- **Matrix analogue of `HermitianOp.conj` by a unitary**: conjugation by the unitary matrix of
the operator in the preferred basis. -/
@[simp]
theorem toMat_conj_unitary (A : HermitianOp E) (U : unitary (E →L[ℂ] E)) :
    toMat (ι := ι) (A.conj U.val) = (toMat A).conj (StdBasis.toMatUnitary (ι := ι) U).val :=
  toMat_conj A U.val

end StdBasis

section StdBasisCongr

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]

/-- **Matrix analogue of `HermitianOp.congr`** along an isometry that carries the preferred basis
of `E` to that of `F` up to a relabelling `σ` of the index: the matrix is relabelled along `σ`. -/
theorem toMat_congr_of_stdBasis {κ : Type*} [Fintype κ] [DecidableEq κ] [StdBasis ℂ F κ]
    (A : HermitianOp E) (e : E ≃ₗᵢ[ℂ] F) (σ : ι ≃ κ)
    (he : ∀ i, e (stdBasis (𝕜 := ℂ) (E := E) i) = stdBasis (𝕜 := ℂ) (E := F) (σ i)) :
    toMat (ι := κ) (A.congr e) = (toMat (ι := ι) A).reindex σ := by
  ext1
  rw [toMat_mat, op_congr, StdBasis.toMat_conjStarAlgEquiv_of_stdBasis _ σ he,
    HermitianMat.mat_reindex, toMat_mat]
  rfl

variable [StdBasis ℂ F ι]

/-- **Matrix analogue of `HermitianOp.congr`** along `StdBasis.equiv`: the matrix is unchanged. -/
@[simp]
theorem toMat_congr_equiv (A : HermitianOp E) :
    toMat (A.congr (StdBasis.equiv ℂ E F ι)) = toMat (ι := ι) A := by
  ext1
  rw [toMat_mat, op_congr, StdBasis.toMat_conjStarAlgEquiv_equiv, toMat_mat]

end StdBasisCongr

section FiniteDimensional

variable [FiniteDimensional ℂ E] {A B : HermitianOp E}

/-- The index type of the basis `StdBasis.some ℂ E` picks out.

Each fact in this section is basis-free, so it may be proved by choosing an arbitrary basis and
appealing to the matrix analogue; `local notation` keeps those proofs readable. -/
local notation "ι₀" => Fin (Module.finrank ℂ E)

theorem cfc_nonneg (A : HermitianOp E) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ A.cfc f := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [← toMat_le_toMat (ι := ι₀), toMat_zero, toMat_cfc]
  exact (HermitianMat.cfc_nonneg_iff _ f).2 fun i ↦ hf _

theorem sqrt_nonneg (A : HermitianOp E) : 0 ≤ A.sqrt :=
  A.cfc_nonneg Real.sqrt_nonneg

theorem abs_nonneg (A : HermitianOp E) : 0 ≤ A.abs :=
  A.cfc_nonneg _root_.abs_nonneg

theorem trace_nonneg (h : 0 ≤ A) : 0 ≤ A.trace := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [← trace_toMat (ι := ι₀)]
  exact HermitianMat.trace_nonneg (by simpa using toMat_le_toMat.2 h)

theorem traceNorm_nonneg (A : HermitianOp E) : 0 ≤ A.traceNorm := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [traceNorm_toMat (ι := ι₀)]
  exact Matrix.traceNorm_nonneg _

@[simp]
theorem traceNorm_neg (A : HermitianOp E) : (-A).traceNorm = A.traceNorm := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  simp only [traceNorm_toMat (ι := ι₀), toMat_neg, HermitianMat.mat_neg]
  exact Matrix.traceNorm_neg _

theorem traceNorm_add_le (A B : HermitianOp E) :
    (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  simp only [traceNorm_toMat (ι := ι₀), toMat_add, HermitianMat.mat_add]
  exact Matrix.traceNorm_add_le _ _

theorem traceNorm_sub_le (A B : HermitianOp E) :
    (A - B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  simp only [traceNorm_toMat (ι := ι₀), toMat_sub, HermitianMat.mat_sub]
  exact Matrix.traceNorm_sub_le _ _

/-- On a nonnegative operator the trace norm is just the trace. -/
theorem traceNorm_of_nonneg (h : 0 ≤ A) : A.traceNorm = A.trace := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  have hpsd : (HermitianMat.mat (toMat (ι := ι₀) A)).PosSemidef := by
    rw [← HermitianMat.zero_le_iff]
    simpa using toMat_le_toMat.2 h
  rw [traceNorm_toMat (ι := ι₀), ← trace_toMat (ι := ι₀), HermitianMat.trace_eq_re_trace,
    ← hpsd.traceNorm_eq_trace]
  simp

section Unitary

variable (U : unitary (E →L[ℂ] E))

@[simp]
theorem trace_conj_unitary (A : HermitianOp E) : (A.conj U.val).trace = A.trace := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [← trace_toMat (ι := ι₀), ← trace_toMat (ι := ι₀), toMat_conj_unitary]
  exact HermitianMat.trace_conj_unitary _ _

@[simp]
theorem conj_unitary_le_conj_unitary : A.conj U.val ≤ B.conj U.val ↔ A ≤ B := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [← toMat_le_toMat (ι := ι₀), toMat_conj_unitary, toMat_conj_unitary,
    HermitianMat.le_conj_unitary, toMat_le_toMat]

@[simp]
theorem inner_conj_unitary (A B : HermitianOp E) :
    (inner ℝ (A.conj U.val) (B.conj U.val) : ℝ) = inner ℝ A B := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [← inner_toMat (ι := ι₀), ← inner_toMat (ι := ι₀), toMat_conj_unitary, toMat_conj_unitary]
  exact HermitianMat.inner_conj_unitary _ _ _

end Unitary

end FiniteDimensional

end HermitianOp
