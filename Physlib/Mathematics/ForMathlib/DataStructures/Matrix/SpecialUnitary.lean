/-
Copyright (c) 2026 Nikolai Kashcheev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.LieTrace
public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.Topology

/-!
# Special unitary generators and matrix exponentiation

The real model space and global matrix exponential of the special unitary group.

## i. Overview

Traceless skew-Hermitian matrices describe infinitesimal special unitary transformations.
Matrix exponentiation sends them into the group: skew-Hermitian matrices exponentiate to
unitary matrices, and zero trace forces the determinant to one by Lie's trace formula.
The construction works for every finite matrix index type.
The exponential is continuous in the usual matrix topology.

The operator norm induced by the coordinate `ℓ∞` norm supplies a real normed structure
on the generators, with the usual topology of matrix entries. These coordinates can
therefore be used for real analysis of matrix-valued families without choosing local
charts on the group.

## ii. Key results

* `Matrix.specialUnitaryGroup.modelSubmodule`: the traceless skew-Hermitian model space.
* `Matrix.specialUnitaryGroup.exp`: the global matrix exponential into the group.
* `Matrix.specialUnitaryGroup.coe_exp`: its underlying matrix formula.
* `Matrix.specialUnitaryGroup.exp_zero`: zero exponentiates to the identity.
* `Matrix.specialUnitaryGroup.continuous_exp`: continuity of the exponential into the group.

## iii. Table of contents

- A. The model space
- B. The matrix exponential
- C. Normed coordinates

## iv. References

* None.
-/

public section

open scoped Matrix

noncomputable section

namespace Matrix.specialUnitaryGroup

local notation "Mat[" ι "]" => Matrix ι ι ℂ
local notation "SU[" ι "]" => Matrix.specialUnitaryGroup ι ℂ

/-!
## A. The model space
-/

/-- The real model subspace of the special unitary group: trace-zero skew-Hermitian matrices. -/
@[expose] def modelSubmodule (ι : Type*) [Fintype ι] : Submodule ℝ (Mat[ι]) :=
  skewAdjoint.submodule ℝ (Mat[ι]) ⊓ LinearMap.ker (Matrix.traceLinearMap ι ℝ ℂ)

/-- A matrix is a model coordinate exactly when it is skew-Hermitian and traceless. -/
lemma mem_modelSubmodule_iff {ι : Type*} [Fintype ι] {A : Mat[ι]} :
    A ∈ modelSubmodule ι ↔ Aᴴ = -A ∧ A.trace = 0 := Iff.rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator

/-!
## B. The matrix exponential
-/

/-- The exponential of a trace-zero skew-Hermitian matrix belongs to the special unitary group. -/
lemma exp_mem {A : Mat[ι]} (hA : A ∈ modelSubmodule ι) :
    NormedSpace.exp A ∈ Matrix.specialUnitaryGroup ι ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨@NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (Mat[ι]) _ _ _ _
    ⟨continuous_id.matrix_conjTranspose⟩ A hA.1, ?_⟩
  rw [Matrix.det_exp_of_fintype, (mem_modelSubmodule_iff.mp hA).2, NormedSpace.exp_zero]

/-- Matrix exponentiation of traceless skew-Hermitian matrices into the special unitary group. -/
def exp (A : modelSubmodule ι) : SU[ι] := ⟨NormedSpace.exp A.val, exp_mem A.property⟩

/-- The underlying matrix of the special unitary exponential is the matrix exponential. -/
@[simp] lemma coe_exp (A : modelSubmodule ι) : (exp A).val = NormedSpace.exp A.val := by
  unfold exp
  rfl

/-- The special unitary exponential sends zero to the identity. -/
@[simp] lemma exp_zero (ι : Type*) [Fintype ι] [DecidableEq ι] :
    exp (0 : modelSubmodule ι) = 1 := by
  apply Subtype.ext
  rw [coe_exp]
  exact NormedSpace.exp_zero

/-- The special unitary exponential is continuous in the usual matrix topology. -/
@[fun_prop] lemma continuous_exp : Continuous (exp : modelSubmodule ι → SU[ι]) := by
  simp only [continuous_induced_rng, Function.comp_def, coe_exp]
  exact NormedSpace.exp_continuous.comp continuous_subtype_val

/-!
## C. Normed coordinates
-/

/-- Exponential coordinates inherit the matrix operator norm induced by the coordinate `ℓ∞` norm. -/
instance instNormedAddCommGroupModel (ι : Type*) [Fintype ι] :
    NormedAddCommGroup (modelSubmodule ι) := inferInstance

/-- The normed coordinate space has its usual real scalar multiplication. -/
instance instNormedSpaceModel (ι : Type*) [Fintype ι] :
    NormedSpace ℝ (modelSubmodule ι) := inferInstance

/-- The coordinate subspace has a countable basis of open sets. -/
instance instSecondCountableTopologyModel (ι : Type*) [Fintype ι] :
    SecondCountableTopology (modelSubmodule ι) :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The finite-dimensional real coordinate subspace is locally compact. -/
instance instLocallyCompactSpaceModel (ι : Type*) [Fintype ι] :
    LocallyCompactSpace (modelSubmodule ι) :=
  @locallyCompact_of_proper (modelSubmodule ι) _ (FiniteDimensional.proper ℝ _)

/-- The special unitary group has a countable basis in its usual matrix topology. -/
instance instSecondCountableTopology (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (SU[ι]) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end Matrix.specialUnitaryGroup
