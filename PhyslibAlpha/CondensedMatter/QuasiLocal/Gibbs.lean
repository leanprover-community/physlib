/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.GNS
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!

# Gibbs weights and states of a finite-dimensional system

The Gibbs state of a Hermitian energy operator, and the canonical and grand canonical ensembles.

## i. Overview

For a Hermitian matrix `h`, thought of as `β` times an energy, the *Gibbs weight* is `e^{-h}`,
and the *Gibbs state* is `a ↦ tr(e^{-h} a) / tr(e^{-h})`. It is a state of the matrix algebra: it
is normalized, Hermitian, and positive, because the weight is the square `r²` of the Hermitian
matrix `r = e^{-h/2}`, so that `tr(r² a* a) = tr((a r)* (a r)) ≥ 0`, and the partition function
`tr(r²)` is positive.

Every ensemble is a special case.

* The *canonical ensemble* at inverse temperature `β` for a Hamiltonian `H` has `h = β H`.
* The *grand canonical ensemble* at inverse temperature `β` and chemical potential `μ`, for a
  Hamiltonian `H` and a charge `N` such as the particle number, has `h = β (H - μ N)`.
  When the charge is conserved, `H` and `N` commute and the weight factorizes as
  `e^{-βH} e^{βμN}`: the canonical weight times a fugacity `e^{βμ}` per unit charge.

No structure of the system enters, so the same definitions serve a finite region of any lattice,
quantum or classical. A classical system is the case of diagonal matrices, where the Gibbs weight
is the Boltzmann factor `e^{-E(c)}` of each configuration `c`.

## ii. Key results

- `gibbsWeight` : the weight `e^{-h}`.
- `gibbsState` : the Gibbs state of a Hermitian operator, as a state of the matrix algebra.
- `canonicalState` : the canonical ensemble.
- `grandCanonicalState` : the grand canonical ensemble.
- `grandCanonicalWeight_of_commute` : factorization for a conserved charge.

## iii. Table of contents

- A. The Gibbs weight
- B. The Gibbs state
- C. The canonical and grand canonical ensembles
- D. Classical systems

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.3.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory
open scoped Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A. The Gibbs weight -/

/-- The Gibbs weight `e^{-h}` of an energy operator `h`. -/
def gibbsWeight (h : Matrix n n ℂ) : Matrix n n ℂ := NormedSpace.exp (-h)

/-- The square root `e^{-h/2}` of the Gibbs weight. -/
def gibbsRoot (h : Matrix n n ℂ) : Matrix n n ℂ := NormedSpace.exp (-((1 / 2 : ℂ) • h))

lemma gibbsWeight_eq_root_mul (h : Matrix n n ℂ) : gibbsWeight h = gibbsRoot h * gibbsRoot h := by
  rw [gibbsWeight, gibbsRoot, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
  congr 1
  rw [← two_smul ℂ (-((1 / 2 : ℂ) • h)), smul_neg, smul_smul]
  norm_num

lemma gibbsRoot_isHermitian {h : Matrix n n ℂ} (hh : h.IsHermitian) :
    (gibbsRoot h).IsHermitian := by
  refine Matrix.IsHermitian.exp ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hh.eq]
  simp

lemma gibbsWeight_isHermitian {h : Matrix n n ℂ} (hh : h.IsHermitian) :
    (gibbsWeight h).IsHermitian := by
  rw [gibbsWeight_eq_root_mul]
  have := gibbsRoot_isHermitian hh
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, this.eq]

/-- The **partition function** `tr e^{-h}`. -/
def partition (h : Matrix n n ℂ) : ℂ := (gibbsWeight h).trace

lemma partition_eq (h : Matrix n n ℂ) (hh : h.IsHermitian) :
    partition h = ((gibbsRoot h)ᴴ * gibbsRoot h).trace := by
  rw [partition, gibbsWeight_eq_root_mul, (gibbsRoot_isHermitian hh).eq]

lemma gibbsRoot_ne_zero [Nonempty n] (h : Matrix n n ℂ) : gibbsRoot h ≠ 0 := by
  intro h0
  have hu : IsUnit (gibbsRoot h) := Matrix.isUnit_exp _
  rw [h0] at hu
  exact not_isUnit_zero hu

/-- **The partition function of a Hermitian operator is positive.** -/
lemma partition_pos [Nonempty n] {h : Matrix n n ℂ} (hh : h.IsHermitian) : 0 < partition h := by
  rw [partition_eq h hh]
  have hnn : (0 : ℂ) ≤ ((gibbsRoot h)ᴴ * gibbsRoot h).trace :=
    (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  refine lt_of_le_of_ne hnn fun h0 => gibbsRoot_ne_zero h ?_
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0.symm

lemma partition_ne_zero [Nonempty n] {h : Matrix n n ℂ} (hh : h.IsHermitian) :
    partition h ≠ 0 := (partition_pos hh).ne'

/-! ## B. The Gibbs state -/

/-- The Gibbs functional `a ↦ tr(e^{-h} a) / tr(e^{-h})`. -/
def gibbsFunctional (h : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] ℂ :=
  (partition h)⁻¹ • ((Matrix.traceLinearMap n ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ (gibbsWeight h))

lemma gibbsFunctional_apply (h a : Matrix n n ℂ) :
    gibbsFunctional h a = (partition h)⁻¹ * (gibbsWeight h * a).trace := rfl

/-- The inverse of the partition function is a nonnegative real number. -/
lemma inv_partition_nonneg [Nonempty n] {h : Matrix n n ℂ} (hh : h.IsHermitian) :
    0 ≤ (partition h)⁻¹ := by
  have hpos := partition_pos hh
  rw [Complex.lt_def] at hpos
  have hZ : partition h = ((partition h).re : ℂ) := Complex.ext (by simp)
    (by simpa using hpos.2.symm)
  rw [hZ, ← Complex.ofReal_inv]
  exact Complex.zero_le_real.2 (inv_nonneg.2 hpos.1.le)

/-- **The Gibbs state of a Hermitian operator** is a state of the matrix algebra: normalized,
Hermitian and positive. -/
def gibbsState [Nonempty n] (h : Matrix n n ℂ) (hh : h.IsHermitian) : AlgState (Matrix n n ℂ) where
  toLinearMap := gibbsFunctional h
  map_one' := by
    rw [gibbsFunctional_apply, Matrix.mul_one]
    exact inv_mul_cancel₀ (partition_ne_zero hh)
  map_star' a := by
    have hZ := partition_pos hh
    rw [Complex.lt_def] at hZ
    have hreal : star (partition h)⁻¹ = (partition h)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact Complex.conj_eq_iff_im.2 hZ.2.symm
    have htr : (gibbsWeight h * star a).trace = star (gibbsWeight h * a).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (gibbsWeight_isHermitian hh).eq,
        Matrix.trace_mul_comm, Matrix.star_eq_conjTranspose]
    rw [gibbsFunctional_apply, gibbsFunctional_apply, star_mul, hreal, mul_comm, htr]
  nonneg' a := by
    rw [gibbsFunctional_apply, Matrix.star_eq_conjTranspose]
    refine mul_nonneg (inv_partition_nonneg hh) ?_
    have hr := gibbsRoot_isHermitian hh
    have : (gibbsWeight h * (aᴴ * a)).trace = ((a * gibbsRoot h)ᴴ * (a * gibbsRoot h)).trace := by
      rw [gibbsWeight_eq_root_mul, Matrix.conjTranspose_mul, hr.eq]
      have := Matrix.trace_mul_comm (gibbsRoot h) (gibbsRoot h * (aᴴ * a))
      simp only [Matrix.mul_assoc] at this ⊢
      exact this
    rw [this]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg

/-! ## C. The canonical and grand canonical ensembles -/

/-- **The canonical ensemble** at inverse temperature `β` for a Hamiltonian `H`. -/
def canonicalState [Nonempty n] (β : ℝ) (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    AlgState (Matrix n n ℂ) :=
  gibbsState ((β : ℂ) • H) (by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp)

/-- The operator whose Gibbs weight is the grand canonical weight: `β (H - μ N)`. -/
def grandCanonicalOp (β μ : ℝ) (H N : Matrix n n ℂ) : Matrix n n ℂ :=
  (β : ℂ) • (H - (μ : ℂ) • N)

omit [Fintype n] [DecidableEq n] in
lemma grandCanonicalOp_isHermitian {H N : Matrix n n ℂ} (hH : H.IsHermitian) (hN : N.IsHermitian)
    (β μ : ℝ) : (grandCanonicalOp β μ H N).IsHermitian := by
  rw [grandCanonicalOp, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, hH.eq, hN.eq]
  simp

/-- **The grand canonical ensemble** at inverse temperature `β` and chemical potential `μ`, for a
Hamiltonian `H` and a charge `N`. -/
def grandCanonicalState [Nonempty n] (β μ : ℝ) (H N : Matrix n n ℂ) (hH : H.IsHermitian)
    (hN : N.IsHermitian) : AlgState (Matrix n n ℂ) :=
  gibbsState (grandCanonicalOp β μ H N) (grandCanonicalOp_isHermitian hH hN β μ)

omit [Fintype n] [DecidableEq n] in
/-- At zero chemical potential the grand canonical ensemble is the canonical one. -/
lemma grandCanonicalOp_zero (β : ℝ) (H N : Matrix n n ℂ) :
    grandCanonicalOp β 0 H N = (β : ℂ) • H := by
  simp [grandCanonicalOp]

/-- **Factorization for a conserved charge**: if `H` and `N` commute, the grand canonical weight is
the canonical weight times the fugacity factor `e^{βμ N}`. -/
lemma grandCanonicalWeight_of_commute (β μ : ℝ) {H N : Matrix n n ℂ} (hc : Commute H N) :
    gibbsWeight (grandCanonicalOp β μ H N) =
      gibbsWeight ((β : ℂ) • H) * NormedSpace.exp (((β * μ : ℝ) : ℂ) • N) := by
  have e : -(grandCanonicalOp β μ H N) = -((β : ℂ) • H) + ((β * μ : ℝ) : ℂ) • N := by
    simp only [grandCanonicalOp, smul_sub, smul_smul]
    push_cast
    abel
  have hcm : Commute (-((β : ℂ) • H)) (((β * μ : ℝ) : ℂ) • N) :=
    ((hc.smul_left (β : ℂ)).neg_left).smul_right _
  rw [gibbsWeight, gibbsWeight, e, Matrix.exp_add_of_commute _ _ hcm]

/-! ## D. Classical systems -/

/-- **For a diagonal energy operator the Gibbs weight is the Boltzmann factor** `e^{-E(c)}` of each
configuration `c`: the classical Gibbs distribution. -/
lemma gibbsWeight_diagonal (v : n → ℂ) :
    gibbsWeight (Matrix.diagonal v) = Matrix.diagonal fun c => Complex.exp (-v c) := by
  rw [gibbsWeight, Matrix.diagonal_neg, Matrix.exp_diagonal]
  congr 1
  funext c
  rw [Pi.coe_exp]
  exact congrFun Complex.exp_eq_exp_ℂ.symm _

/-- The partition function of a diagonal energy operator is the sum of the Boltzmann factors. -/
lemma partition_diagonal (v : n → ℂ) : partition (Matrix.diagonal v) = ∑ c, Complex.exp (-v c) := by
  rw [partition, gibbsWeight_diagonal, Matrix.trace_diagonal]

end QuasiLocal

end CondensedMatter

end
