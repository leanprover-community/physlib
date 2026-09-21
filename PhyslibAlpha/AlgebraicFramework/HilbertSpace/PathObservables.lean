/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable

/-!

# Path observables on `ℂ^d`

The transport `T_d` (the adjacency matrix of `SimpleGraph.pathGraph d`, normalised by its spectral
radius) and the position `P_d` (the diagonal of the centered coordinate), as observables of
`ℂ^d →L[ℂ] ℂ^d`.

For `d = 1` the spectral radius is `0` and `coordinate` divides by `d - 1 = 0`, so both matrices
take Lean's junk values there. They are meant for `2 ≤ d`, which every later statement assumes.

-/

@[expose] public section

open Matrix SimpleGraph

namespace PathObservables

/-- The spectral radius `2 cos (π / (d + 1))` of the adjacency matrix of the path on `d`
vertices. -/
noncomputable def spectralRadius (d : ℕ) : ℝ :=
  2 * Real.cos (Real.pi / ((d : ℝ) + 1))

open scoped Classical in
/-- The transport matrix `T_d`. -/
noncomputable def transport (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  ((spectralRadius d : ℝ) : ℂ)⁻¹ • (pathGraph d).adjMatrix ℂ

/-- The centered coordinate of the `j`-th basis vector; for `2 ≤ d` it ranges over `[-1, 1]`,
from `-1` at `j = 0` to `1` at `j = d - 1`. -/
noncomputable def coordinate (d : ℕ) (j : Fin d) : ℝ :=
  (2 * ((j : ℕ) + 1) - ((d : ℝ) + 1)) / ((d : ℝ) - 1)

/-- The position matrix `P_d`. -/
noncomputable def position (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j => (coordinate d j : ℂ)

/-- The transport matrix is Hermitian. -/
lemma transport_isHermitian (d : ℕ) : (transport d).IsHermitian := by
  classical
  ext i j
  by_cases h : (pathGraph d).Adj i j
  · simp [transport, h, h.symm, adjMatrix_apply, Complex.conj_ofReal]
  · have h' : ¬ (pathGraph d).Adj j i := fun h' => h h'.symm
    simp [transport, h, h', adjMatrix_apply]

/-- The position matrix is Hermitian. -/
lemma position_isHermitian (d : ℕ) : (position d).IsHermitian :=
  isHermitian_diagonal_iff.mpr fun _ => Complex.conj_ofReal _

/-- A Hermitian matrix acts on `ℂ^d` as a self-adjoint operator. -/
lemma isSelfAdjoint_toEuclideanCLM {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M) := by
  rw [IsSelfAdjoint, ← map_star, star_eq_conjTranspose, hM.eq]

/-- The transport `T_d` as an observable of the operators on `ℂ^d`. -/
noncomputable def transportObservable (d : ℕ) :
    Observable (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
  ⟨Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d),
    isSelfAdjoint_toEuclideanCLM (transport_isHermitian d)⟩

/-- The position `P_d` as an observable of the operators on `ℂ^d`. -/
noncomputable def positionObservable (d : ℕ) :
    Observable (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
  ⟨Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d),
    isSelfAdjoint_toEuclideanCLM (position_isHermitian d)⟩

end PathObservables
