/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.OneParameter
/-!
# The adjoint action of a global gauge group on its Lie algebra

The action `X ↦ g X g⁻¹` of a global gauge group on its Lie algebra.

## i. Overview

A global gauge group `G` acts on its Lie algebra `𝔤` by conjugation, `X ↦ g X g⁻¹`. This is
the adjoint action, the way an infinitesimal gauge transformation changes under a global
one, and it is how the gauge fields transform under `G`. It maps the one-parameter subgroup
of `X` to the conjugate by `g` of that subgroup, since `exp (t g X g⁻¹) = g exp (t X) g⁻¹`.

## ii. Key results

- `GlobalGaugeGroup.adjoint` : the adjoint action of the group on its Lie algebra.
- `GlobalGaugeGroup.oneParameterSubgroup_adjoint` : the one-parameter subgroup of `g X g⁻¹`
  is the conjugate of that of `X`.

## iii. Table of contents

- A. The adjoint action
- B. The adjoint action on one-parameter subgroups

## iv. References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

open Matrix NormedSpace

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The adjoint action

-/

/-- The adjoint action `X ↦ g X g⁻¹` of an element `g` of the group on its Lie algebra. -/
def adjoint (g : G.group) (X : G.lieAlgebra) : G.lieAlgebra :=
  ⟨(g.1 : Matrix κ κ ℂ) * X * (↑g.1⁻¹ : Matrix κ κ ℂ),
    conj_mem_lieAlgebraOfIsClosed (hH := G.isClosed) g X.2⟩

variable {G}

@[simp]
lemma adjoint_val (g : G.group) (X : G.lieAlgebra) :
    (G.adjoint g X : Matrix κ κ ℂ) = (g.1 : Matrix κ κ ℂ) * X * (↑g.1⁻¹ : Matrix κ κ ℂ) := rfl

/-!

## B. The adjoint action on one-parameter subgroups

-/

/-- The one-parameter subgroup of `g X g⁻¹` is the conjugate by `g` of that of `X`. -/
lemma oneParameterSubgroup_adjoint (g : G.group) (X : G.lieAlgebra) (t : ℝ) :
    G.oneParameterSubgroup (G.adjoint g X) t = g * G.oneParameterSubgroup X t * g⁻¹ := by
  refine (eq_oneParameterSubgroup ?_).symm
  have hinv : (↑g.1⁻¹ : Matrix κ κ ℂ) = (g.1 : Matrix κ κ ℂ)⁻¹ := Matrix.coe_units_inv g.1
  rw [adjoint_val, hinv, show t • ((g.1 : Matrix κ κ ℂ) * X * (g.1 : Matrix κ κ ℂ)⁻¹) =
      (g.1 : Matrix κ κ ℂ) * (t • (X : Matrix κ κ ℂ)) * (g.1 : Matrix κ κ ℂ)⁻¹ by
    rw [mul_smul_comm, smul_mul_assoc], Matrix.exp_conj _ _ g.1.isUnit,
    ← oneParameterSubgroup_val, ← hinv]
  rfl

end GlobalGaugeGroup
