/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint

/-!

# Spectral theory for essentially self-adjoint operators

## i. Overview

An operator `T` is essentially self-adjoint if its closure is self-adjoint. Many properties of
`T` follow from the corresponding results for the self-adjoint operator `T.closure`. In this
module we collect such properties.

For non-real `z` the operator `T.closure - z • 1` is surjective. Since `T` and `T.closure` have
the same defect numbers off the real axis, the defect numbers of `T` vanish there, and the range
of `T - z • 1` is dense.

## ii. Key results

- `IsEssentiallySelfAdjoint.mem_regularityDomain_of_im_ne_zero` : every non-real `z` lies in the
    regularity domain of an essentially self-adjoint operator.
- `IsEssentiallySelfAdjoint.defectNumber_eq_zero` : the defect numbers of an essentially
    self-adjoint operator vanish at every non-real `z`.
- `IsEssentiallySelfAdjoint.dense_range_sub_smul` : for an essentially self-adjoint operator the
    range of `T - z • 1` is dense for every non-real `z`.

## iii. Table of contents

- A. Defect numbers and dense ranges

## iv. References

* None.

-/

@[expose] public section

namespace LinearPMap

namespace IsEssentiallySelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H} (hT : T.IsEssentiallySelfAdjoint)
include hT

/-!

## A. Defect numbers and dense ranges

-/

/-- Every non-real `z` lies in the regularity domain of an essentially self-adjoint operator. -/
lemma mem_regularityDomain_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ T.regularityDomain :=
  hT.isSymmetric.mem_regularityDomain_of_im_ne_zero hz

/-- The defect numbers of an essentially self-adjoint operator vanish at every non-real `z`:
`T.closure - z • 1` is surjective, and `T` has the same defect number as its closure. -/
lemma defectNumber_eq_zero {z : ℂ} (hz : z.im ≠ 0) : T.defectNumber z = 0 := by
  have hreg := hT.mem_regularityDomain_of_im_ne_zero hz
  rw [← defectNumber_closure hreg, hT.isClosable.closure_isClosed.defectNumber_eq_zero_iff
    (by rwa [regularityDomain_closure])]
  exact LinearMap.range_eq_top.mpr (IsSelfAdjoint.sub_smul_surjective hT hz)

/-- For an essentially self-adjoint operator the range of `T - z • 1` is dense for every
non-real `z`. -/
lemma dense_range_sub_smul {z : ℂ} (hz : z.im ≠ 0) :
    Dense ((T - z • 1).toFun.range : Set H) :=
  defectNumber_eq_zero_iff_dense.mp (hT.defectNumber_eq_zero hz)

end IsEssentiallySelfAdjoint

end LinearPMap
