/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Reindex

/-! # Trace of Hermitian Matrices

While the trace of a Hermitian matrix is, in informal math, typically just "the same as" a trace of
a matrix that happens to be Hermitian - it is a real number, not a complex number. Or more generally,
it is a self-adjoint element of the base `StarAddMonoid`.

Working directly with `Matrix.trace` then means that there would be constant casts between rings,
chasing imaginary parts and inequalities and so on. By defining `HermitianMat.trace` as its own
operation, we encapsulate the mess and give a clean interface.

The `IsMaximalSelfAdjoint` class is used so that (for example) for matrices over ℤ or ℝ,
`HermitianMat.trace` works as well and is in fact defeq to `Matrix.trace`. For ℂ or `RCLike`,
it uses the real part.
-/

@[expose] public section

namespace HermitianMat

variable {R n m α : Type*} [Star R] [TrivialStar R] [Fintype n] [Fintype m]

section star
variable [AddGroup α] [StarAddMonoid α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α]

set_option linter.overlappingInstances false in
/-- The trace of the matrix. This requires a `IsMaximalSelfAdjoint R α` instance, and then maps from
  `HermitianMat n α` to `R`. This means that the trace of (say) a `HermitianMat n ℤ` gives values in ℤ,
  but that the trace of a `HermitianMat n ℂ` gives values in ℝ. The fact that traces are "automatically"
  real reduces coercions down the line. -/
def trace (A : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap (A.mat.trace)

set_option linter.overlappingInstances false in
/-- `HermitianMat.trace` reduces to `Matrix.trace` in the algebra.-/
theorem trace_eq_trace (A : HermitianMat n α) : algebraMap R α A.trace = Matrix.trace A.mat := by
  rw [trace, Matrix.trace, map_sum, map_sum]
  congr! 1
  exact IsMaximalSelfAdjoint.selfadj_algebra (Matrix.IsHermitian.apply A.H _ _)

set_option linter.overlappingInstances false in
variable [StarModule R α] in
@[simp]
theorem trace_smul (A : HermitianMat n α) (r : R) : (r • A).trace = r * A.trace := by
  simp [trace, IsMaximalSelfAdjoint.selfadj_smul]

end star
section semiring
variable [CommSemiring R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]

@[simp]
theorem trace_zero : (0 : HermitianMat n α).trace = 0 := by
  simp [trace]

@[simp]
theorem trace_add (A B : HermitianMat n α) : (A + B).trace = A.trace + B.trace := by
  simp [trace]

theorem trace_sum {ι : Type*} (s : Finset ι) (A : ι → HermitianMat n α) :
    (∑ i ∈ s, A i).trace = ∑ i ∈ s, (A i).trace := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, trace_add, ih]

end semiring
section ring

variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
@[simp]
theorem trace_neg (A : HermitianMat n α) : (-A).trace = -A.trace := by
  simp [trace]

@[simp]
theorem trace_sub (A B : HermitianMat n α) : (A - B).trace = A.trace - B.trace := by
  simp [trace]

end ring
section starring

variable [CommRing R] [CommRing α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α]

--Move somewhere else? Needs to import `IsMaximalSelfAdjoint`, so maybe just here.
theorem _root_.Matrix.IsHermitian.isSelfAdjoint_trace {A : Matrix n n α} (hA : A.IsHermitian) :
    IsSelfAdjoint A.trace := by
  simp [Matrix.trace, IsSelfAdjoint, ← Matrix.star_apply, show star A = A from hA]

variable (A : HermitianMat m α) (B : HermitianMat n α)

@[simp]
theorem trace_kronecker [FaithfulSMul R α] : (A ⊗ₖ B).trace = A.trace * B.trace := by
  apply FaithfulSMul.algebraMap_injective R α
  simp only [trace, kronecker_mat]
  rw [Matrix.trace_kronecker A.mat B.mat]
  simp only [map_mul]
  have hA := A.H.isSelfAdjoint_trace
  have hB := B.H.isSelfAdjoint_trace
  open IsMaximalSelfAdjoint in
  rw [selfadj_algebra hA, selfadj_algebra hB, selfadj_algebra (hA.mul hB)]

end starring

section trivialstar

variable [Star α] [TrivialStar α] [CommSemiring α]

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are a `TrivialStar`. -/
@[simp]
theorem trace_eq_trace_trivial (A : HermitianMat n ℝ) : A.trace = A.mat.trace := by
  rw [← trace_eq_trace]
  rfl

end trivialstar

section RCLike

variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [RCLike 𝕜]

theorem trace_eq_re_trace (A : HermitianMat n 𝕜) : A.trace = RCLike.re A.mat.trace := by
  rfl

@[fun_prop]
theorem trace_Continuous : Continuous (HermitianMat.trace : HermitianMat n 𝕜 → ℝ) := by
  rw [funext (trace_eq_re_trace (n := n) (𝕜 := 𝕜))]
  fun_prop

@[simp]
theorem trace_one [DecidableEq n] : (1 : HermitianMat n 𝕜).trace = Fintype.card n := by
  simp [trace_eq_re_trace]

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are `RCLike`. -/
@[simp]
theorem trace_eq_trace_rc (A : HermitianMat n 𝕜) : A.trace = A.mat.trace := by
  rw [trace, Matrix.trace, map_sum, RCLike.ofReal_sum]
  congr 1
  exact Matrix.IsHermitian.coe_re_diag A.H

theorem trace_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) :
    (diagonal 𝕜 f).trace = ∑ i, f i := by
  rw [trace_eq_re_trace]
  simp [HermitianMat.diagonal, Matrix.trace]

theorem sum_eigenvalues_eq_trace [DecidableEq n] (A : HermitianMat n 𝕜) :
    ∑ i, A.H.eigenvalues i = A.trace := by
  convert! congrArg RCLike.re A.H.sum_eigenvalues_eq_trace
  rw [RCLike.ofReal_re]

--Proving that traces are 0 or 1 is common enough that we have a convenience lemma here for turning
--statements about HermitianMat traces into Matrix traces.
theorem trace_eq_zero_iff (A : HermitianMat n 𝕜) : A.trace = 0 ↔ A.mat.trace = 0 := by
  rw [← trace_eq_trace_rc]
  exact ⟨mod_cast id, mod_cast id⟩

theorem trace_eq_one_iff (A : HermitianMat n 𝕜) : A.trace = 1 ↔ A.mat.trace = 1 := by
  rw [← trace_eq_trace_rc]
  exact ⟨mod_cast id, mod_cast id⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem trace_reindex (A : HermitianMat n ℂ) (e : n ≃ m) :
    (A.reindex e).trace = A.trace := by
  simp [reindex, trace_eq_re_trace]

end RCLike
section partialTrace
section addCommGroup

variable [AddCommGroup α] [StarAddMonoid α]
omit [Fintype n]

def traceLeft (A : HermitianMat (m × n) α) : HermitianMat n α :=
  ⟨A.mat.traceLeft, A.H.traceLeft⟩

def traceRight (A : HermitianMat (m × n) α) : HermitianMat m α :=
  ⟨A.mat.traceRight, A.H.traceRight⟩

variable (A B : HermitianMat (m × n) α)

@[simp]
theorem traceLeft_mat : A.traceLeft.mat = A.mat.traceLeft := by
  rfl

theorem traceLeft_apply (i j : n) : A.traceLeft i j = ∑ k, A (k, i) (k, j) := by
  rfl

@[simp]
theorem traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft := by
  ext1; simp

@[simp]
theorem traceLeft_neg : (-A).traceLeft = -A.traceLeft := by
  ext1; simp

@[simp]
theorem traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft := by
  ext1; simp

variable (A B : HermitianMat (n × m) α)

@[simp]
theorem traceRight_mat :
    (traceRight A).mat = A.mat.traceRight := by
  rfl

theorem traceRight_apply (i j : n) : A.traceRight i j = ∑ k, A (i, k) (j, k) := by
  rfl

@[simp]
theorem traceRight_add : (A + B).traceRight = A.traceRight + B.traceRight := by
  ext1; simp

@[simp]
theorem traceRight_neg : (-A).traceRight = -A.traceRight := by
  ext1; simp

@[simp]
theorem traceRight_sub : (A - B).traceRight = A.traceRight - B.traceRight := by
  ext1; simp

end addCommGroup
section rcLike

variable {𝕜} [RCLike 𝕜]
variable (A : HermitianMat (m × n) 𝕜)

omit [Fintype n] in
@[simp]
theorem traceLeft_smul (r : ℝ) : (r • A).traceLeft = r • A.traceLeft := by
  ext1; simp

omit [Fintype m] in
@[simp]
theorem traceRight_smul (r : ℝ) : (r • A).traceRight = r • A.traceRight := by
  ext1; simp

@[simp]
theorem traceLeft_trace : A.traceLeft.trace = A.trace := by
  simp [trace_eq_re_trace]

@[simp]
theorem traceRight_trace : A.traceRight.trace = A.trace := by
  simp [trace_eq_re_trace]

end rcLike
section kron

variable {m n 𝕜 : Type*} [RCLike 𝕜]
variable (A : HermitianMat m 𝕜) (B : HermitianMat n 𝕜)

@[simp]
theorem traceLeft_kron [Fintype m] : (A ⊗ₖ B).traceLeft = A.trace • B := by
  ext : 2
  simp only [HermitianMat.traceLeft, Matrix.traceLeft, kronecker_mat, mat_mk]
  simp [Matrix.trace, RCLike.real_smul_eq_coe_mul, ← Finset.sum_mul]

@[simp]
theorem traceRight_kron [Fintype n] : (A ⊗ₖ B).traceRight = B.trace • A := by
  ext : 2
  simp only [HermitianMat.traceRight, Matrix.traceRight, kronecker_mat, mat_mk]
  simp [Matrix.trace, RCLike.real_smul_eq_coe_mul, ← Finset.mul_sum, mul_comm]

variable [DecidableEq m] [DecidableEq n]

theorem one_traceRight [Fintype n] :
    (1 : HermitianMat (m × n) 𝕜).traceRight = (Fintype.card n : ℝ) • 1 := by
  conv_lhs => rw [← kronecker_one_one]
  rw [traceRight_kron, trace_one]

theorem traceRight_add_smul_one [Fintype n] (A : HermitianMat (m × n) 𝕜) (ε : ℝ) :
    (A + ε • 1).traceRight = A.traceRight + (ε * Fintype.card n) • 1 := by
  rw [traceRight_add, traceRight_smul, one_traceRight, smul_smul]

end kron
end partialTrace
