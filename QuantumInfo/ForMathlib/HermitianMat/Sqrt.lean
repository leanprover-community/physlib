/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Proj
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

@[expose] public section

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {f g : ℝ → ℝ}

noncomputable section

open scoped MatrixOrder ComplexOrder Matrix Kronecker

namespace HermitianMat

/-- The square root of a Hermitian matrix. Negative eigenvalues are mapped to zero. -/
noncomputable def sqrt (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.sqrt

theorem sqrt_sq_eq_proj (A : HermitianMat d 𝕜) :
    A.sqrt.mat * A.sqrt.mat = A⁺ := by
  rw [sqrt, ← mat_cfc_mul, ← HermitianMat.ext_iff, posPart_eq_cfc_ite]
  congr! 2 with x
  grind [Pi.mul_apply, Real.mul_self_sqrt, Real.sqrt_eq_zero']

theorem sqrt_sq (hA : 0 ≤ A) :
    A.sqrt.mat * A.sqrt.mat = A := by
  rw [sqrt_sq_eq_proj, posPart_eq_self hA]

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem commute_sqrt_left (hAB : Commute A.mat B.mat) :
    Commute A.sqrt.mat B.mat := by
  rw [sqrt]
  commutes

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem commute_sqrt_right (hAB : Commute A.mat B.mat) :
    Commute A.mat B.sqrt.mat := by
  commutes

/--
For a positive definite matrix A, A^{-1/2} * A * A^{-1/2} = I.
-/
lemma sqrt_inv_mul_self_mul_sqrt_inv_eq_one {A : HermitianMat d 𝕜} (hA : A.mat.PosDef) :
    A⁻¹.sqrt.mat * A.mat * A⁻¹.sqrt.mat = 1 := by
  have h_inv_def : A⁻¹.sqrt.mat * A⁻¹.sqrt.mat = A⁻¹ := by
    apply HermitianMat.sqrt_sq
    rw [zero_le_iff]
    exact hA.inv.posSemidef
  have h_inv_comm : Commute A⁻¹.sqrt.mat A.mat := by
    commutes
  rw [h_inv_comm, mul_assoc, h_inv_def]
  apply Matrix.mul_nonsing_inv
  exact isUnit_iff_ne_zero.mpr hA.det_pos.ne'

theorem sqrt_nonneg (A : HermitianMat d 𝕜) : 0 ≤ A.sqrt := by
  rw [sqrt, cfc_nonneg_iff]
  intro; positivity

/-- On nonnegative matrices, `HermitianMat.sqrt` is the C⋆-algebra square root `CFC.sqrt` of the
underlying matrix. -/
theorem mat_sqrt (hA : 0 ≤ A) : A.sqrt.mat = CFC.sqrt A.mat :=
  (CFC.sqrt_unique (b := A.sqrt.mat) (sqrt_sq hA)
    (Matrix.nonneg_iff_posSemidef.mpr (zero_le_iff.mp A.sqrt_nonneg))).symm

theorem trace_sqrt (hA : 0 ≤ A) : A.sqrt.trace = RCLike.re (CFC.sqrt A.mat).trace := by
  rw [trace_eq_re_trace, mat_sqrt hA]

/-- A nonnegative idempotent, that is, an orthogonal projector, is its own square root. -/
theorem sqrt_eq_self (hA : 0 ≤ A) (h : A.mat * A.mat = A.mat) : A.sqrt = A := by
  ext1
  rw [mat_sqrt hA]
  exact CFC.sqrt_unique h (Matrix.nonneg_iff_posSemidef.mpr (zero_le_iff.mp hA))

/-- Scaling a nonnegative matrix by `c ≥ 0` scales its square root by `√c`. -/
theorem sqrt_smul (hA : 0 ≤ A) {c : ℝ} (hc : 0 ≤ c) : (c • A).sqrt = Real.sqrt c • A.sqrt := by
  have h₁ : (0 : HermitianMat d 𝕜) ≤ c • A := smul_nonneg hc hA
  have h₂ : (0 : HermitianMat d 𝕜) ≤ Real.sqrt c • A.sqrt :=
    smul_nonneg (Real.sqrt_nonneg c) (sqrt_nonneg A)
  ext1
  rw [mat_sqrt h₁]
  refine CFC.sqrt_unique ?_ (Matrix.nonneg_iff_posSemidef.mpr (zero_le_iff.mp h₂))
  rw [mat_smul, mat_smul, smul_mul_smul_comm, sqrt_sq hA, Real.mul_self_sqrt hc]

theorem sqrt_pos (h : 0 < A) : 0 < A.sqrt := by
  rw [sqrt]
  apply cfc_pos_of_pos h (by intros; positivity) (by simp)

theorem sqrt_posDef {A : HermitianMat d 𝕜} (hA : A.mat.PosDef) :
    A.sqrt.mat.PosDef := by
  rw [sqrt, cfc_posDef]
  simp [hA.eigenvalues_pos]

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.sqrt` -/
@[positivity HermitianMat.sqrt _]
meta def evalHermitianMatSqrt : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app _sqrt (A : Expr) ← whnfR e | throwError "not sqrt application"
  try
    let (isStrictA, pfA) ← bestResult A
    if isStrictA then
      pure (.positive (← mkAppM ``HermitianMat.sqrt_pos #[pfA]))
    else
      throwError "Not strictly positive, falling back to nonnegativity"
  catch _ =>
    pure (.nonnegative (← mkAppM ``HermitianMat.sqrt_nonneg #[A]))

open RealInnerProductSpace in
/-- If a positive semidefinite matrix `A` has zero inner product with an idempotent `X`, then
their product vanishes. -/
theorem mul_eq_zero_of_inner_eq_zero {A X : HermitianMat d 𝕜} (hA : 0 ≤ A)
    (hX : X.mat * X.mat = X.mat) (h : ⟪A, X⟫ = 0) : A.mat * X.mat = 0 := by
  have hY : A.sqrt.mat * X.mat = 0 := by
    apply Matrix.eq_zero_of_re_trace_conjTranspose_mul_self_eq_zero
    rw [Matrix.conjTranspose_mul, A.sqrt.conjTranspose_mat, X.conjTranspose_mat]
    have h1 : X.mat * A.sqrt.mat * (A.sqrt.mat * X.mat) = X.mat * (A.mat * X.mat) := by
      rw [mul_assoc, ← mul_assoc A.sqrt.mat, sqrt_sq hA]
    rw [h1, Matrix.trace_mul_comm, mul_assoc, hX, ← inner_eq_re_trace]
    exact h
  calc A.mat * X.mat = A.sqrt.mat * (A.sqrt.mat * X.mat) := by rw [← mul_assoc, sqrt_sq hA]
    _ = 0 := by rw [hY, Matrix.mul_zero]

section traceNorm

/-- Whenever `A` is a Gram matrix `XᴴX`, the trace of `√A` is the trace norm of `X`. -/
theorem trace_sqrt_eq_traceNorm {X : Matrix d d 𝕜} (hAX : A.mat = Xᴴ * X) :
    A.sqrt.trace = X.traceNorm := by
  have h0 : 0 ≤ A := by
    rw [zero_le_iff, hAX]
    exact Matrix.posSemidef_conjTranspose_mul_self X
  rw [trace_sqrt h0, hAX]
  rfl

/-- The Gram matrix `XᴴX` written in terms of the square roots of `A` and `B`, where
`X = √A √B`: this is the matrix whose square root's trace is the fidelity of `A` and `B`. -/
private theorem conj_sqrt_eq_gram (hA : 0 ≤ A) :
    (A.conj B.sqrt.mat).mat = (A.sqrt.mat * B.sqrt.mat)ᴴ * (A.sqrt.mat * B.sqrt.mat) := by
  rw [conj_apply_mat, B.sqrt.conjTranspose_mat, Matrix.conjTranspose_mul,
    A.sqrt.conjTranspose_mat, B.sqrt.conjTranspose_mat, ← sqrt_sq hA]
  simp [mul_assoc]

/-- The trace of `√(√B A √B)`, that is, the fidelity of `A` and `B`, is the trace norm of
`√A √B`. -/
theorem trace_sqrt_conj_sqrt_eq_traceNorm (hA : 0 ≤ A) :
    (A.conj B.sqrt.mat).sqrt.trace = (A.sqrt.mat * B.sqrt.mat).traceNorm :=
  trace_sqrt_eq_traceNorm (conj_sqrt_eq_gram hA)

/-- The **fidelity is symmetric**: the trace of `√(√B A √B)` is unchanged when `A` and `B` are
swapped, because the two matrices are `XᴴX` and `XXᴴ` for `X = √A √B`. -/
theorem trace_sqrt_conj_sqrt_comm (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A.conj B.sqrt.mat).sqrt.trace = (B.conj A.sqrt.mat).sqrt.trace := by
  have h2 : (B.conj A.sqrt.mat).mat
      = ((A.sqrt.mat * B.sqrt.mat)ᴴ)ᴴ * (A.sqrt.mat * B.sqrt.mat)ᴴ := by
    rw [Matrix.conjTranspose_conjTranspose, conj_apply_mat, A.sqrt.conjTranspose_mat,
      Matrix.conjTranspose_mul, A.sqrt.conjTranspose_mat, B.sqrt.conjTranspose_mat, ← sqrt_sq hB]
    simp [mul_assoc]
  rw [trace_sqrt_eq_traceNorm (conj_sqrt_eq_gram hA), trace_sqrt_eq_traceNorm h2,
    Matrix.traceNorm_conjTranspose]

/-- The **fidelity is at most one** for states: the trace of `√(√B A √B)` is bounded by
`√(Tr A) * √(Tr B)`, which is Cauchy–Schwarz applied to the Hilbert–Schmidt inner product. -/
theorem trace_sqrt_conj_sqrt_le (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A.conj B.sqrt.mat).sqrt.trace ≤ Real.sqrt A.trace * Real.sqrt B.trace := by
  rw [trace_sqrt_eq_traceNorm (conj_sqrt_eq_gram hA)]
  obtain ⟨U, hU1, hU⟩ :=
    Matrix.exists_unitary_re_trace_eq_traceNorm (A.sqrt.mat * B.sqrt.mat)
  have hswap : (U * (A.sqrt.mat * B.sqrt.mat)).trace
      = ((A.sqrt.mat * Uᴴ)ᴴ * B.sqrt.mat).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, A.sqrt.conjTranspose_mat,
      mul_assoc]
  have e1 : RCLike.re ((A.sqrt.mat * Uᴴ)ᴴ * (A.sqrt.mat * Uᴴ)).trace = A.trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, A.sqrt.conjTranspose_mat,
      show U * A.sqrt.mat * (A.sqrt.mat * Uᴴ) = U * (A.sqrt.mat * A.sqrt.mat) * Uᴴ by
        simp [mul_assoc],
      sqrt_sq hA, Matrix.trace_mul_comm, hU1, ← trace_eq_re_trace]
  have e2 : RCLike.re ((B.sqrt.mat)ᴴ * B.sqrt.mat).trace = B.trace := by
    rw [B.sqrt.conjTranspose_mat, sqrt_sq hB, ← trace_eq_re_trace]
  calc (A.sqrt.mat * B.sqrt.mat).traceNorm
      = RCLike.re ((A.sqrt.mat * Uᴴ)ᴴ * B.sqrt.mat).trace := by rw [← hU, hswap]
    _ ≤ Real.sqrt (RCLike.re ((A.sqrt.mat * Uᴴ)ᴴ * (A.sqrt.mat * Uᴴ)).trace) *
          Real.sqrt (RCLike.re ((B.sqrt.mat)ᴴ * B.sqrt.mat).trace) :=
        Matrix.re_trace_conjTranspose_mul_le _ _
    _ = Real.sqrt A.trace * Real.sqrt B.trace := by rw [e1, e2]

/-- The **fidelity is one only for equal states**: if the trace of `√(√B A √B)` attains the bound
of `trace_sqrt_conj_sqrt_le` for unit-trace `A` and `B`, then `A = B`. This is the equality case of
Cauchy–Schwarz. -/
theorem eq_of_trace_sqrt_conj_sqrt_eq_one (hA : 0 ≤ A) (hB : 0 ≤ B) (hA1 : A.trace = 1)
    (hB1 : B.trace = 1) (h : (A.conj B.sqrt.mat).sqrt.trace = 1) : A = B := by
  rw [trace_sqrt_eq_traceNorm (conj_sqrt_eq_gram hA)] at h
  obtain ⟨U, hU1, hU⟩ :=
    Matrix.exists_unitary_re_trace_eq_traceNorm (A.sqrt.mat * B.sqrt.mat)
  have e1 : RCLike.re ((A.sqrt.mat * Uᴴ)ᴴ * (A.sqrt.mat * Uᴴ)).trace = A.trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, A.sqrt.conjTranspose_mat,
      show U * A.sqrt.mat * (A.sqrt.mat * Uᴴ) = U * (A.sqrt.mat * A.sqrt.mat) * Uᴴ by
        simp [mul_assoc],
      sqrt_sq hA, Matrix.trace_mul_comm, hU1, ← trace_eq_re_trace]
  have e2 : RCLike.re ((B.sqrt.mat)ᴴ * B.sqrt.mat).trace = B.trace := by
    rw [B.sqrt.conjTranspose_mat, sqrt_sq hB, ← trace_eq_re_trace]
  have e3 : RCLike.re ((A.sqrt.mat * Uᴴ)ᴴ * B.sqrt.mat).trace = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, A.sqrt.conjTranspose_mat,
      mul_assoc, hU, h]
  have key : A.sqrt.mat * Uᴴ = B.sqrt.mat :=
    Matrix.eq_of_re_trace_conjTranspose_mul_eq_one (e1.trans hA1) (e2.trans hB1) e3
  apply HermitianMat.ext
  calc A.mat = A.sqrt.mat * A.sqrt.mat := (sqrt_sq hA).symm
    _ = A.sqrt.mat * (Uᴴ * (U * A.sqrt.mat)) := by rw [hU1]
    _ = (A.sqrt.mat * Uᴴ) * (A.sqrt.mat * Uᴴ)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          A.sqrt.conjTranspose_mat]
        simp [mul_assoc]
    _ = B.sqrt.mat * (B.sqrt.mat)ᴴ := by rw [key]
    _ = B.mat := by rw [B.sqrt.conjTranspose_mat, sqrt_sq hB]

end traceNorm

example {A : HermitianMat d ℂ} : 0 ≤ A.sqrt := by
  positivity

example [Nonempty d] {A : HermitianMat d ℂ} : 0 < (1 + A.sqrt).sqrt  := by
  positivity
