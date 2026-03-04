/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Kronecker delta

This file defines the Kronecker delta, `δ[i,j] ≔ if (i = j) then 1 else 0`.

-/
TODO "YVABB" "Build full API for working with sums involving Kronecker deltas."

namespace KroneckerDelta

/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kroneckerDelta (i j : Fin d) : ℝ := if (i = j) then 1 else 0

@[inherit_doc kroneckerDelta]
notation "δ[" i "," j "]" => kroneckerDelta i j

lemma kroneckerDelta_symm (i j : Fin d) : δ[i,j] = δ[j,i] :=
  ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

lemma kroneckerDelta_self {i : Fin d} : δ[i,i] = 1 := if_pos rfl

lemma kroneckerDelta_diff {i j : Fin d} (h : i ≠ j) : δ[i,j] = 0 := if_neg h

lemma sum_kroneckerDelta [AddCommGroup M] [Module ℂ M]
    (c : ℂ) (i : Fin d) (f : Fin d → M) : ∑ j, (c * δ[i,j]) • f j = c • f i := by
  dsimp [kroneckerDelta]
  have (j : Fin d) : c * Complex.ofReal (ite (i = j) 1 0) = ite (i = j) c 0 := by
    rcases eq_or_ne i j with (rfl | hne)
    · simp
    · simp [if_neg hne]
  simp [this]

lemma sum_kroneckerDelta' [AddCommGroup M] [Module ℂ M]
    (c : ℂ) (i : Fin d) (f : Fin d → M) : ∑ j, (c * δ[j,i]) • f j = c • f i := by
  simp [kroneckerDelta_symm, sum_kroneckerDelta]

end KroneckerDelta
