/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava-Gómez
-/
module

public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Bracket

/-!
# Robertson's uncertainty relation for mixed states

## i. Overview

In 1929, H. P. Robertson showed that two Hermitian observables on a quantum state satisfy a
fundamental trade-off: the sharper one observable is known, the less the other can be known.
Formally, for observables `G` and `O` on a state `ρ`:

    ⟨i[G,O]⟩² / 4 ≤ Var(G) · Var(O).

This module proves the relation for arbitrary finite-dimensional mixed states (`MState`),
via Cauchy–Schwarz on the Hilbert–Schmidt space. The pure-state version of this bound, for
partially defined operators on an inner product space, is in
`Physlib.QuantumMechanics.Operators.Uncertainty`; the mixed-state formulation here requires
the density-matrix framework of `MState`, which lives in `QuantumInfo`.

## ii. Key results

- `HermitianMat.bracket_mat` : the commutator bracket `⁅G, O⁆ = i(GO − OG)` on Hermitian
  matrices.
- `MState.robertson_uncertainty` : Robertson's relation for mixed states.
- `MState.robertson_normalized` : the multiplicative form `1 ≤ 4 · Var(O) · Var(G)` under
  the normalization `⟨i[G,O]⟩ = 1`, free of positivity hypotheses.

## iii. Table of contents

- A. Commutator bracket on Hermitian matrices
- B. Hilbert–Schmidt embedding
- C. Centered vectors and the commutator pairing
- D. Robertson's uncertainty relation
- E. Normalized form

## iv. References

- [H. P. Robertson, *The Uncertainty Principle* (1929)][robertson1929uncertainty].
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix

namespace HermitianMat

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## A. Commutator bracket on Hermitian matrices -/

/-- The commutator bracket `⁅G, O⁆ = i(GO − OG)` of two Hermitian matrices, as a
`HermitianMat`. -/
instance : Bracket (HermitianMat d ℂ) (HermitianMat d ℂ) where
  bracket G O := ⟨Complex.I • (G.mat * O.mat - O.mat * G.mat), by
    show (Complex.I • (G.mat * O.mat - O.mat * G.mat))ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, G.H.eq, O.H.eq, Complex.star_def, Complex.conj_I]
    module⟩

omit [DecidableEq d] in
@[simp]
theorem bracket_mat (G O : HermitianMat d ℂ) :
    ⁅G, O⁆.mat = Complex.I • (G.mat * O.mat - O.mat * G.mat) := by
  simp only [Bracket.bracket]; rfl

end HermitianMat

namespace MState

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

/-! ## B. Hilbert–Schmidt embedding

Cauchy–Schwarz is applied to `Tr(G O ρ)`, which requires embedding matrices into an inner
product space via `hsVec`. The HermitianMat inner product (`Tr(AB)`) gives a different
bilinear form and does not suffice for this argument. -/

/-- The entries of a matrix, placed into `EuclideanSpace ℂ (d × d)` where Mathlib's inner
product space API (in particular Cauchy–Schwarz) is available. -/
private def hsVec (M : Matrix d d ℂ) : EuclideanSpace ℂ (d × d) :=
  (WithLp.equiv 2 (d × d → ℂ)).symm (fun p => M p.1 p.2)

omit [Fintype d] [DecidableEq d] in
@[simp]
private lemma hsVec_apply (M : Matrix d d ℂ) (p : d × d) : hsVec M p = M p.1 p.2 := rfl

omit [DecidableEq d] in
/-- The EuclideanSpace inner product of two embedded matrices is the Hilbert–Schmidt
pairing `Tr(Aᴴ B)`. -/
private lemma hsVec_inner (A B : Matrix d d ℂ) :
    inner ℂ (hsVec A) (hsVec B) = (Aᴴ * B).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Matrix.trace]
  simp only [hsVec_apply, RCLike.inner_apply, starRingEnd_apply, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact mul_comm _ _

/-! ## C. Centered vectors and the commutator pairing -/

section observables

variable (ρ : MState d)

/-- The cyclic trace identity `Tr(√ρ X √ρ) = Tr(X ρ)`, the Hilbert–Schmidt engine of the
mixed-state calculation. -/
private lemma trace_sqrt_sandwich (X : Matrix d d ℂ) :
    (ρ.M.sqrt.mat * X * ρ.M.sqrt.mat).trace = (X * ρ.m).trace := by
  rw [Matrix.trace_mul_cycle, HermitianMat.sqrt_sq ρ.nonneg, MState.mat_M,
    Matrix.trace_mul_comm]

/-- The embedding of `A √ρ` against `√ρ` is the expectation value of `A`. -/
private lemma inner_sqrt_left (A : HermitianMat d ℂ) :
    inner ℂ (hsVec ρ.M.sqrt.mat) (hsVec (A.mat * ρ.M.sqrt.mat)) = (ρ.exp_val A : ℂ) := by
  rw [hsVec_inner, ρ.M.sqrt.H.eq,
    show ρ.M.sqrt.mat * (A.mat * ρ.M.sqrt.mat) = ρ.M.sqrt.mat * A.mat * ρ.M.sqrt.mat by
      simp [Matrix.mul_assoc],
    ρ.trace_sqrt_sandwich, ← exp_val_ℂ, exp_val_ℂ_hermitian]

/-- The embedded `√ρ` is a unit vector in Hilbert–Schmidt space. -/
private lemma inner_sqrt_self :
    inner ℂ (hsVec ρ.M.sqrt.mat) (hsVec ρ.M.sqrt.mat) = (1 : ℂ) := by
  rw [hsVec_inner, ρ.M.sqrt.H.eq, HermitianMat.sqrt_sq ρ.nonneg, MState.mat_M, ρ.tr']

/-- The embedding of `G √ρ` against `O √ρ` is the expectation value of the product `G O`. -/
private lemma inner_hsVec_hsVec (G O : HermitianMat d ℂ) :
    inner ℂ (hsVec (G.mat * ρ.M.sqrt.mat)) (hsVec (O.mat * ρ.M.sqrt.mat)) =
      ρ.exp_val_ℂ (G.mat * O.mat) := by
  rw [hsVec_inner, Matrix.conjTranspose_mul, ρ.M.sqrt.H.eq, (G.H).eq,
    show ρ.M.sqrt.mat * G.mat * (O.mat * ρ.M.sqrt.mat) =
        ρ.M.sqrt.mat * (G.mat * O.mat) * ρ.M.sqrt.mat by
      simp [Matrix.mul_assoc],
    ρ.trace_sqrt_sandwich, ← exp_val_ℂ]

/-- The centered vector `A √ρ − ⟨A⟩ √ρ` in Hilbert–Schmidt space. -/
private def centeredVec (A : HermitianMat d ℂ) : EuclideanSpace ℂ (d × d) :=
  hsVec (A.mat * ρ.M.sqrt.mat) - (ρ.exp_val A : ℂ) • hsVec ρ.M.sqrt.mat

/-- The squared Hilbert–Schmidt norm of the centered vector is the variance of `A`. -/
private lemma norm_centered_sq (A : HermitianMat d ℂ) :
    ‖ρ.centeredVec A‖ ^ 2 = ρ.variance A := by
  have hself := ρ.inner_sqrt_self
  have hleft := ρ.inner_sqrt_left A
  have hright : inner ℂ (hsVec (A.mat * ρ.M.sqrt.mat)) (hsVec ρ.M.sqrt.mat) =
      (ρ.exp_val A : ℂ) := by
    rw [← inner_conj_symm, hleft, Complex.conj_ofReal]
  have hAA := ρ.inner_hsVec_hsVec A A
  have hAsq : ρ.exp_val_ℂ (A.mat * A.mat) = (ρ.exp_val (A ^ 2) : ℂ) := by
    rw [← ρ.exp_val_ℂ_hermitian (A ^ 2), HermitianMat.mat_pow, pow_two]
  have hexpand : (inner ℂ (ρ.centeredVec A) (ρ.centeredVec A) : ℂ) =
      ρ.exp_val_ℂ (A.mat * A.mat) - (ρ.exp_val A : ℂ) * (ρ.exp_val A : ℂ) := by
    unfold centeredVec
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hself, hleft, hright, hAA]
    ring
  have hre : ‖ρ.centeredVec A‖ ^ 2 = (inner ℂ (ρ.centeredVec A) (ρ.centeredVec A) : ℂ).re :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) (ρ.centeredVec A)).symm
  rw [hre, hexpand, variance, hAsq, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  ring

/-- The expectation of a product of Hermitian matrices is conjugate-symmetric in the
factors. -/
private lemma exp_val_ℂ_swap (G O : HermitianMat d ℂ) :
    (starRingEnd ℂ) (ρ.exp_val_ℂ (G.mat * O.mat)) = ρ.exp_val_ℂ (O.mat * G.mat) := by
  simp only [MState.exp_val_ℂ, starRingEnd_apply, ← Matrix.trace_conjTranspose]
  rw [show ((G.mat * O.mat) * ρ.m)ᴴ = ρ.m * O.mat * G.mat by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ρ.Hermitian.eq, (G.H).eq,
          (O.H).eq, ← Matrix.mul_assoc],
      Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- The inner product of the centered vectors of `G` and `O` is the covariance pairing
`⟨GO⟩ − ⟨G⟩⟨O⟩`. -/
private lemma inner_centered_centered (G O : HermitianMat d ℂ) :
    (inner ℂ (ρ.centeredVec G) (ρ.centeredVec O) : ℂ) =
      ρ.exp_val_ℂ (G.mat * O.mat) - (ρ.exp_val G : ℂ) * (ρ.exp_val O : ℂ) := by
  have hself := ρ.inner_sqrt_self
  have hGl := ρ.inner_sqrt_left G
  have hOl := ρ.inner_sqrt_left O
  have hGr : inner ℂ (hsVec (G.mat * ρ.M.sqrt.mat)) (hsVec ρ.M.sqrt.mat) =
      (ρ.exp_val G : ℂ) := by
    rw [← inner_conj_symm, hGl, Complex.conj_ofReal]
  have hGO := ρ.inner_hsVec_hsVec G O
  unfold centeredVec
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hself, hOl, hGr, hGO]
  ring

/-! ## D. Robertson's uncertainty relation -/

/-- **Robertson's uncertainty relation** (H. P. Robertson, Phys. Rev. **34**, 163–164 (1929)),
for two Hermitian observables on an arbitrary finite-dimensional mixed state: the product of
variances dominates a quarter of the squared commutator pairing. -/
theorem robertson_uncertainty (G O : HermitianMat d ℂ) :
    (ρ.exp_val ⁅G, O⁆) ^ 2 / 4 ≤ ρ.variance G * ρ.variance O := by
  set z : ℂ := inner ℂ (ρ.centeredVec G) (ρ.centeredVec O) with hz
  have hCS : ‖z‖ ≤ ‖ρ.centeredVec G‖ * ‖ρ.centeredVec O‖ := norm_inner_le_norm _ _
  have hprodsq : (‖ρ.centeredVec G‖ * ‖ρ.centeredVec O‖) ^ 2 = ρ.variance G * ρ.variance O := by
    rw [mul_pow, ρ.norm_centered_sq G, ρ.norm_centered_sq O]
  have hz_sub : z - conj z =
      ρ.exp_val_ℂ (G.mat * O.mat) - ρ.exp_val_ℂ (O.mat * G.mat) := by
    have hzz : z =
        ρ.exp_val_ℂ (G.mat * O.mat) - (ρ.exp_val G : ℂ) * (ρ.exp_val O : ℂ) := by
      rw [hz]; exact ρ.inner_centered_centered G O
    rw [hzz, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ρ.exp_val_ℂ_swap]
    ring
  have hlin : ρ.exp_val_ℂ ⁅G, O⁆.mat =
      Complex.I * (ρ.exp_val_ℂ (G.mat * O.mat) - ρ.exp_val_ℂ (O.mat * G.mat)) := by
    rw [HermitianMat.bracket_mat]
    simp only [MState.exp_val_ℂ, Matrix.smul_mul, Matrix.sub_mul,
      Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  have hw : z - conj z = 2 * Complex.I * (z.im : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.mul_im]
    · simp [Complex.sub_im, Complex.conj_im, Complex.mul_re, Complex.mul_im]
      ring
  have hcomm : ρ.exp_val ⁅G, O⁆ = -2 * z.im := by
    have hval : ρ.exp_val_ℂ ⁅G, O⁆.mat = ((-2 * z.im : ℝ) : ℂ) := by
      rw [hlin, ← hz_sub, hw]
      push_cast
      rw [show Complex.I * (2 * Complex.I * (z.im : ℂ)) =
          2 * (Complex.I * Complex.I) * (z.im : ℂ) by ring, Complex.I_mul_I]
      ring
    rw [show ρ.exp_val ⁅G, O⁆ = (ρ.exp_val_ℂ ⁅G, O⁆.mat).re from by
      rw [exp_val_ℂ_hermitian]; simp, hval, Complex.ofReal_re]
  have hnormsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [sq, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
  have hzim : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hnormsq, sq]; nlinarith [sq_nonneg z.re]
  have hfinal : (ρ.exp_val ⁅G, O⁆) ^ 2 / 4 ≤ ‖z‖ ^ 2 := by
    rw [hcomm]; nlinarith [hzim]
  calc (ρ.exp_val ⁅G, O⁆) ^ 2 / 4
      ≤ ‖z‖ ^ 2 := hfinal
    _ ≤ (‖ρ.centeredVec G‖ * ‖ρ.centeredVec O‖) ^ 2 := by gcongr
    _ = ρ.variance G * ρ.variance O := hprodsq

/-! ## E. Normalized form -/

/-- Robertson's uncertainty relation in **multiplicative form**: under the normalization
`⟨i[G,O]⟩_ρ = 1`, the product of variances is at least `1/4`. -/
theorem robertson_normalized (G O : HermitianMat d ℂ)
    (hnorm : ρ.exp_val ⁅G, O⁆ = 1) :
    1 ≤ 4 * ρ.variance O * ρ.variance G := by
  have hR := ρ.robertson_uncertainty G O
  rw [hnorm] at hR; norm_num at hR
  nlinarith [ρ.variance_nonneg G, ρ.variance_nonneg O]

end observables

end

end MState

end
