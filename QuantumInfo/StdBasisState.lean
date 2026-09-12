/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.StdBasis
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Operators.Unitary

/-!
# Mixed states of an abstract Hilbert space

`MState d` is a matrix-level notion: it is a positive semidefinite `Matrix d d ℂ` of trace one.
Physically, a mixed state is an operator on a Hilbert space, and the matrix only appears after a
choice of orthonormal basis. This file bridges the two, using `StdBasis`.

`MState.ofOp` turns a positive trace-one operator `A : E →L[ℂ] E` into an `MState d`, given an
orthonormal basis of `E` indexed by `d`. The main results say that the quantities computed from the
resulting matrix do not depend on which orthonormal basis was used: changing the basis conjugates
the matrix by a unitary (`MState.ofOp_eq_uConj`), and the von Neumann entropy is therefore
basis-independent (`MState.Sᵥₙ_ofOp_congr`).

This is the pattern intended for migrating the rest of the library: a matrix-level definition is
first shown to be insensitive to the choice of `StdBasis`, after which it can be restated for the
operator directly.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped ComplexOrder MState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]

namespace MState

/-- The mixed state whose matrix, in the orthonormal basis `b`, is the matrix of the positive
trace-one operator `A`. -/
def ofOp (b : OrthonormalBasis d ℂ E) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) : MState d :=
  DensityOp.ofMat
    ⟨StdBasis.toMatOf b A, ((StdBasis.posSemidef_toMatOf_iff_nonneg b A).mpr hA).isHermitian⟩
    (HermitianMat.zero_le_iff.mpr ((StdBasis.posSemidef_toMatOf_iff_nonneg b A).mpr hA))
    (by
      rw [HermitianMat.trace_eq_one_iff]
      exact (StdBasis.trace_toMatOf b A).trans htr)

@[simp]
theorem ofOp_m (b : OrthonormalBasis d ℂ E) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) :
    (ofOp b A hA htr).m = StdBasis.toMatOf b A := by
  rw [ofOp, DensityOp.m_ofMat, HermitianMat.mat_mk]

/-- On `EuclideanSpace ℂ d` with its standard basis, `MState.ofOp` is just the existing matrix
description of a state: the current matrix-level development is the special case
`E := EuclideanSpace ℂ d` of the abstract one. -/
@[simp]
theorem ofOp_basisFun (A : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ (EuclideanSpace ℂ d) (A : _ →ₗ[ℂ] _) = 1) :
    (ofOp (EuclideanSpace.basisFun d ℂ) A hA htr).m =
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := d)).symm A := by
  rw [ofOp_m]
  rfl

/-- Von Neumann entropy is unchanged by conjugating a state by a unitary. -/
@[simp]
theorem Sᵥₙ_uConj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) : Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ := by
  rw [Sᵥₙ_eq_Hₛ_spectrum, Sᵥₙ_eq_Hₛ_spectrum, uConj_spectrum_eq]

/-- Changing the orthonormal basis used to represent an operator conjugates the resulting state by
the (unitary) change-of-basis matrix. -/
theorem ofOp_eq_uConj (b b' : OrthonormalBasis d ℂ E) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) :
    ofOp b' A hA htr = star (StdBasis.changeOfBasis b b') ◃ ofOp b A hA htr := by
  apply DensityOp.ext_m
  rw [ofOp_m, uConj_m, ofOp_m, StdBasis.toMatOf_conj b b']
  simp [Matrix.star_eq_conjTranspose]

/-- **The von Neumann entropy of an operator does not depend on the choice of orthonormal basis.**

This is the insensitivity lemma that licenses defining the entropy of an abstract density
operator: the matrix-level `Sᵥₙ` descends through `MState.ofOp`. -/
theorem Sᵥₙ_ofOp_congr (b b' : OrthonormalBasis d ℂ E) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) :
    Sᵥₙ (ofOp b' A hA htr) = Sᵥₙ (ofOp b A hA htr) := by
  rw [ofOp_eq_uConj b b', Sᵥₙ_uConj]

/-- The same insensitivity, phrased for two `StdBasis` instances on the same space. -/
theorem Sᵥₙ_ofOp_congr_instances (inst inst' : StdBasis ℂ E d) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) :
    Sᵥₙ (ofOp inst'.stdBasis A hA htr) = Sᵥₙ (ofOp inst.stdBasis A hA htr) :=
  Sᵥₙ_ofOp_congr _ _ A hA htr

/-- Relabelling the index type of the orthonormal basis relabels the state. -/
theorem ofOp_reindex (b : OrthonormalBasis d ℂ E) (e : d ≃ d₂) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) :
    ofOp (b.reindex e) A hA htr = (ofOp b A hA htr).relabel e.symm := by
  apply DensityOp.ext_m
  rw [ofOp_m, relabel_m, ofOp_m, StdBasis.toMatOf_reindex]
  rfl

/-- Von Neumann entropy is also insensitive to the index type of the orthonormal basis. -/
theorem Sᵥₙ_ofOp_reindex (b : OrthonormalBasis d ℂ E) (e : d ≃ d₂) (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (htr : LinearMap.trace ℂ E (A : E →ₗ[ℂ] E) = 1) :
    Sᵥₙ (ofOp (b.reindex e) A hA htr) = Sᵥₙ (ofOp b A hA htr) := by
  rw [ofOp_reindex, Sᵥₙ_relabel]

end MState
