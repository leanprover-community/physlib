/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# The commutator of observables

The commutator of two observables is an observable. It measures how much they fail to commute.

## i. Overview

The product `a b` of two observables is in general not an observable. Its real part is the
symmetryzed product `(a b + b a) / 2`. Its imaginary or antisymmetric part is the commutator
`⁅a, b⁆ = -(i / 2) (a b - b a)`.
Both are observables. So the product splits as `a b = Re (a b) + i ⁅a, b⁆`.

## ii. Key results

- `Observable.commutator` : the commutator of two observables.
- `Observable.coe_bracket` : `⁅a, b⁆ = -(i / 2) (a b - b a)`.
- `Observable.mul_eq_realPart_add_I_smul_bracket` : `a b = Re (a b) + i ⁅a, b⁆`.
- `Observable.isSelfAdjoint_mul_iff_commute` : the product of two observables is an observable
  exactly when they commute.
- `Observable.bracket_sub_smul_one` : shifts by multiples of `1` do not change the commutator.

## iii. Table of contents

- A. The commutator
- B. Splitting the product

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexStarModule

namespace Observable

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]

/-! ## A. The commutator -/

/-- The commutator `⁅a, b⁆ = -(i / 2) (a b - b a)` of two observables. It is the imaginary part of
their product. -/
noncomputable def commutator (a b : Observable 𝒜) : Observable 𝒜 :=
  ℑ ((a : 𝒜) * b)

noncomputable instance instBracket : Bracket (Observable 𝒜) (Observable 𝒜) := ⟨commutator⟩

lemma bracket_def (a b : Observable 𝒜) : ⁅a, b⁆ = ℑ ((a : 𝒜) * b) := rfl

/-- The commutator is `-(i / 2) (a b - b a)`. -/
@[simp]
lemma coe_bracket (a b : Observable 𝒜) :
    ((⁅a, b⁆ : Observable 𝒜) : 𝒜) = (-(Complex.I / 2)) • ((a : 𝒜) * b - (b : 𝒜) * a) := by
  rw [bracket_def, imaginaryPart_apply_coe, star_mul, a.2.star_eq, b.2.star_eq]
  module

/-- Shifting observables by multiples of `1` does not change their commutator. -/
@[simp]
lemma bracket_sub_smul_one (a b : Observable 𝒜) (r s : ℝ) :
    ⁅a - r • 1, b - s • 1⁆ = ⁅a, b⁆ := by
  refine Subtype.ext ?_
  simp only [coe_bracket, AddSubgroupClass.coe_sub, selfAdjoint.val_smul, selfAdjoint.val_one]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  congr 1
  module

/-! ## B. Splitting the product -/

/-- The product of two observables is its real part plus `i` times the commutator. -/
lemma mul_eq_realPart_add_I_smul_bracket (a b : Observable 𝒜) :
    (a : 𝒜) * b = (ℜ ((a : 𝒜) * b) : 𝒜) + Complex.I • ((⁅a, b⁆ : Observable 𝒜) : 𝒜) :=
  (realPart_add_I_smul_imaginaryPart ((a : 𝒜) * b)).symm

end Observable

TODO "Connect the commutator to the Lie algebra structure on observables. PhyslibAlpha has it in
  `ProbabilisticTheory/StarAlgebra/Lie.lean`."

TODO "Connect the real part of the product to the Jordan product of observables. PhyslibAlpha has
  it in `ProbabilisticTheory/StarAlgebra/Jordan.lean`."
