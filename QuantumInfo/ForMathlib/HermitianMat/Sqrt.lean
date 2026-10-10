/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Proj

@[expose] public section

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {f g : ℝ → ℝ}

noncomputable section

open scoped MatrixOrder ComplexOrder Matrix Kronecker

namespace HermitianMat

/-- The square root of a Hermitian matrix. Negative eigenvalues are mapped to zero. -/
noncomputable def sqrt (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.sqrt

lemma sqrt_sq_eq_proj (A : HermitianMat d 𝕜) :
    A.sqrt.mat * A.sqrt.mat = A⁺ := by
  rw [sqrt, ← mat_cfc_mul, ← HermitianMat.ext_iff, posPart_eq_cfc_ite]
  congr! 2 with x
  grind [Pi.mul_apply, Real.mul_self_sqrt, Real.sqrt_eq_zero']

lemma sqrt_sq (hA : 0 ≤ A) :
    A.sqrt.mat * A.sqrt.mat = A := by
  rw [sqrt_sq_eq_proj, posPart_eq_self hA]

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
lemma commute_sqrt_left (hAB : Commute A.mat B.mat) :
    Commute A.sqrt.mat B.mat := by
  rw [sqrt]
  commutes

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
lemma commute_sqrt_right (hAB : Commute A.mat B.mat) :
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

lemma sqrt_nonneg (A : HermitianMat d 𝕜) : 0 ≤ A.sqrt := by
  rw [sqrt, cfc_nonneg_iff]
  intro; positivity

lemma sqrt_pos (h : 0 < A) : 0 < A.sqrt := by
  rw [sqrt]
  apply cfc_pos_of_pos h (by intros; positivity) (by simp)

lemma sqrt_posDef {A : HermitianMat d 𝕜} (hA : A.mat.PosDef) :
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

example {A : HermitianMat d ℂ} : 0 ≤ A.sqrt := by
  positivity

example [Nonempty d] {A : HermitianMat d ℂ} : 0 < (1 + A.sqrt).sqrt  := by
  positivity
