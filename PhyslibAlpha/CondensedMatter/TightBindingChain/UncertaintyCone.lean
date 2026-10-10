/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.UncertaintyCone
/-!

# The uncertainty cone of the maximal current state

## i. Overview

In the maximal current state of the open tight binding chain the energy and position
fluctuations are uncorrelated, so their Gram four-vector has no `v₁` component. It lies on the
light cone exactly for `N = 2` and `N = 3`, where the Robertson–Schrödinger relation is an
equality, and strictly inside the future cone from four sites on.

On the cube `Nx × Ny × Nz` each axis carries its own Lorentz vector, whose Minkowski square is
the centered Gram defect of that axis: it vanishes iff the axis has `2` or `3` sites, and the
three are timelike together from `4 × 4 × 4` on (`nava_robertson_schrodinger_cube`).

## ii. Key results

- `vectorCoeff_gramMatrix_maxCurrentState` : the covariance component vanishes.
- `pauliRadius_gramMatrix_maxCurrentState_eq_iff` : the four-vector is null iff `N = 2, 3`.
- `pauliRadius_gramMatrix_maxCurrentState_lt` : it is timelike for `N ≥ 4`.
- `axisVectorX`, `axisVectorY`, `axisVectorZ` : the Lorentz vector of each axis of the cube.
- `minkowski_axisVectorX_eq_zero_iff` (and `Y`, `Z`) : an axis is null iff it has `2` or `3`
  sites.
- `minkowski_axisVector_cube_pos` : the three axes are timelike from `4 × 4 × 4` on.

## iii. Table of contents

- A. The four-vector of the maximal current state
- B. The three Lorentz vectors of the cube

## iv. References

* B. L. van der Waerden, *Spinoranalyse*, Nachrichten von der Gesellschaft der Wissenschaften
  zu Göttingen (1929) 100–109.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap PauliMatrix
open scoped TensorProduct

variable (T : TightBindingChain)

/-!

## A. The four-vector of the maximal current state

-/

/-- In the maximal current state the covariance component of the Gram four-vector vanishes. -/
lemma vectorCoeff_gramMatrix_maxCurrentState :
    vectorCoeff (gramMatrix T.maxCurrentVectorState T.openHamiltonianObservable
      T.positionObservable) 0 = 0 := by
  rw [(vectorCoeff_gramMatrix _ _ _).1, covariance_maxCurrentState]

/-- The Gram four-vector of the maximal current state is null exactly for `N = 2` and `N = 3`. -/
theorem pauliRadius_gramMatrix_maxCurrentState_eq_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    pauliRadius (gramMatrix T.maxCurrentVectorState T.openHamiltonianObservable
        T.positionObservable) =
      scalarCoeff (gramMatrix T.maxCurrentVectorState T.openHamiltonianObservable
        T.positionObservable) ↔ T.N = 2 ∨ T.N = 3 := by
  rw [pauliRadius_gramMatrix_eq_iff, T.centeredGramDefect_maxCurrentState_eq_zero_iff ht hN]

/-- From four sites on, the Gram four-vector of the maximal current state is timelike. -/
theorem pauliRadius_gramMatrix_maxCurrentState_lt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    pauliRadius (gramMatrix T.maxCurrentVectorState T.openHamiltonianObservable
        T.positionObservable) <
      scalarCoeff (gramMatrix T.maxCurrentVectorState T.openHamiltonianObservable
        T.positionObservable) :=
  (pauliRadius_gramMatrix_le _ _ _).2.lt_of_ne fun h => by
    rcases (T.pauliRadius_gramMatrix_maxCurrentState_eq_iff ht (by omega)).mp h with h | h <;>
      omega

/-!

## B. The three Lorentz vectors of the cube

-/

variable (Tx Ty Tz : TightBindingChain)

/-- The Minkowski square of a contravariant Lorentz vector. -/
local notation "⟪" ψ "," φ "⟫ₘ" => Lorentz.contrContrContractField (ψ ⊗ₜ φ)

/-- The Lorentz vector of the `x` axis of the cube in its maximal current state. -/
noncomputable def axisVectorX : Lorentz.ContrMod 3 :=
  gramVector (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz Tx.openHamiltonianObservable)
    (Tx.alongX Ty Tz Tx.positionObservable)

/-- The Lorentz vector of the `y` axis of the cube in its maximal current state. -/
noncomputable def axisVectorY : Lorentz.ContrMod 3 :=
  gramVector (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz Ty.openHamiltonianObservable)
    (Tx.alongY Ty Tz Ty.positionObservable)

/-- The Lorentz vector of the `z` axis of the cube in its maximal current state. -/
noncomputable def axisVectorZ : Lorentz.ContrMod 3 :=
  gramVector (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz Tz.openHamiltonianObservable)
    (Tx.alongZ Ty Tz Tz.positionObservable)

/-- On the cube, the Lorentz vector of the `x` axis is null iff the axis has `2` or `3` sites. -/
lemma minkowski_axisVectorX_eq_zero_iff (ht : Tx.t ≠ 0) (hN : 2 ≤ Tx.N) :
    ⟪Tx.axisVectorX Ty Tz, Tx.axisVectorX Ty Tz⟫ₘ = 0 ↔ Tx.N = 2 ∨ Tx.N = 3 := by
  rw [axisVectorX, minkowski_gramVector, Tx.centeredGramDefect_alongX_eq_zero_iff Ty Tz ht hN]

/-- On the cube, the Lorentz vector of the `y` axis is null iff the axis has `2` or `3` sites. -/
lemma minkowski_axisVectorY_eq_zero_iff (ht : Ty.t ≠ 0) (hN : 2 ≤ Ty.N) :
    ⟪Tx.axisVectorY Ty Tz, Tx.axisVectorY Ty Tz⟫ₘ = 0 ↔ Ty.N = 2 ∨ Ty.N = 3 := by
  rw [axisVectorY, minkowski_gramVector, Tx.centeredGramDefect_alongY_eq_zero_iff Ty Tz ht hN]

/-- On the cube, the Lorentz vector of the `z` axis is null iff the axis has `2` or `3` sites. -/
lemma minkowski_axisVectorZ_eq_zero_iff (ht : Tz.t ≠ 0) (hN : 2 ≤ Tz.N) :
    ⟪Tx.axisVectorZ Ty Tz, Tx.axisVectorZ Ty Tz⟫ₘ = 0 ↔ Tz.N = 2 ∨ Tz.N = 3 := by
  rw [axisVectorZ, minkowski_gramVector, Tx.centeredGramDefect_alongZ_eq_zero_iff Ty Tz ht hN]

/-- **The Minkowski metric of the cube.** From `4 × 4 × 4` on, the Lorentz vectors of the three
axes of the maximal current state are timelike: each Minkowski square is the positive centered
Gram defect of its axis. -/
theorem minkowski_axisVector_cube_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    0 < ⟪Tx.axisVectorX Ty Tz, Tx.axisVectorX Ty Tz⟫ₘ ∧
      0 < ⟪Tx.axisVectorY Ty Tz, Tx.axisVectorY Ty Tz⟫ₘ ∧
      0 < ⟪Tx.axisVectorZ Ty Tz, Tx.axisVectorZ Ty Tz⟫ₘ := by
  simp only [axisVectorX, axisVectorY, axisVectorZ, minkowski_gramVector]
  exact Tx.nava_robertson_schrodinger_cube Ty Tz hx hy hz hNx hNy hNz

end TightBindingChain
end CondensedMatter
