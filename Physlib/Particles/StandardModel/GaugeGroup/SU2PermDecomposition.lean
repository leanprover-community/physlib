/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
/-!
# The `SU(2)` Weyl element

## i. Overview

The Weyl reflection of `SU(2)`,

  `su2Perm = !![0, -1; 1, 0]`,

sends a doublet `(a, b)` to `(-b, a)`, exchanging the two isospin components and so
exchanging the isospin weights `+1` and `-1` that the third coordinate of a `GaugeWeight`
records. `gaugeSU2Perm` is its image in the gauge group.

`su2Perm` squares to `-1`, so it has order four in `SU(2)`, and its spectrum is contained in
the fourth roots of unity: `su2PermSign` is the character `k ↦ i ^ k` on `ZMod 4` attaching
the eigenvalue to each grade.

## ii. Key results

- `su2Perm` : the `SU(2)` Weyl element `!![0, -1; 1, 0]`, and `gaugeSU2Perm` its image in
  the gauge group.
- `su2PermSign` : the character `k ↦ i ^ k` on `ZMod 4`, injective and multiplicative.

## iii. Table of contents

- A. The `SU(2)` Weyl element
- B. The sign character of `ZMod 4`

-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The `SU(2)` Weyl element

-/

/-- The `SU(2)` Weyl element `!![0, -1; 1, 0]`. On a doublet it sends `(a, b)` to `(-b, a)`,
  exchanging the two isospin components; it squares to `-1`, so it has order four in
  `SU(2)`. -/
noncomputable def su2Perm : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two_of]⟩

lemma su2Perm_coe : (su2Perm : specialUnitaryGroup (Fin 2) ℂ).1 = !![0, -1; 1, 0] := rfl

/-- The inverse Weyl element is `!![0, 1; -1, 0]`. -/
lemma su2Perm_inv_coe :
    (su2Perm⁻¹ : specialUnitaryGroup (Fin 2) ℂ).1 = !![0, 1; -1, 0] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, su2Perm_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-- The Weyl element as a gauge transformation: trivial on colour and hypercharge. -/
noncomputable def gaugeSU2Perm : GaugeGroupI := ⟨1, su2Perm, 1⟩

/-!

## B. The sign character of `ZMod 4`

-/

/-- The fourth root of unity `i ^ k` attached to a grade `k : ZMod 4`: the eigenvalue of the
  Weyl element on the `k` piece of a decomposition. -/
noncomputable def su2PermSign (k : ZMod 4) : ℂ :=
  if k = 0 then 1 else if k = 1 then Complex.I else if k = 2 then -1 else -Complex.I

@[simp] lemma su2PermSign_zero : su2PermSign 0 = 1 := rfl

@[simp] lemma su2PermSign_one : su2PermSign 1 = Complex.I := rfl

@[simp] lemma su2PermSign_two : su2PermSign 2 = -1 := rfl

@[simp] lemma su2PermSign_three : su2PermSign 3 = -Complex.I := rfl

/-- The sign is a character: grades **add** under multiplication because the fourth roots of
  unity multiply. -/
lemma su2PermSign_add (k l : ZMod 4) :
    su2PermSign (k + l) = su2PermSign k * su2PermSign l := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hcases k with rfl | rfl | rfl | rfl <;> rcases hcases l with rfl | rfl | rfl | rfl <;>
    simp [show (1 + 1 : ZMod 4) = 2 from by decide,
      show (1 + 2 : ZMod 4) = 3 from by decide, show (1 + 3 : ZMod 4) = 0 from by decide,
      show (2 + 1 : ZMod 4) = 3 from by decide, show (2 + 2 : ZMod 4) = 0 from by decide,
      show (2 + 3 : ZMod 4) = 1 from by decide, show (3 + 1 : ZMod 4) = 0 from by decide,
      show (3 + 2 : ZMod 4) = 1 from by decide, show (3 + 3 : ZMod 4) = 2 from by decide,
      Complex.I_mul_I]

lemma su2PermSign_ne_zero (k : ZMod 4) : su2PermSign k ≠ 0 := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hcases k with rfl | rfl | rfl | rfl <;> simp

/-- The four fourth roots of unity are distinct, so the pieces of a decomposition sit in
  eigenspaces at distinct eigenvalues and are automatically independent. -/
lemma su2PermSign_injective : Function.Injective su2PermSign := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  intro k l hkl
  rcases hcases k with rfl | rfl | rfl | rfl <;> rcases hcases l with rfl | rfl | rfl | rfl <;>
    simp_all [Complex.ext_iff] <;> norm_num at hkl

end StandardModel
