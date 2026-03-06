/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Complex.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Kronecker delta

This file defines the Kronecker delta, `δ[i,j] ≔ if (i = j) then 1 else 0`.

TODO ideas:
- Double sums
- Symmetrization (i.e. `δᵢⱼfᵢⱼ = ½ δᵢⱼ(fᵢⱼ + fⱼᵢ)`) and `∑ᵢ∑ⱼ δᵢⱼfᵢⱼ = 0` if f is antisymmetric

-/
TODO "YVABB" "Build full API for working with sums involving Kronecker deltas."

namespace KroneckerDelta

variable
  {R : Type*} [Ring R]
  {d : ℕ} (i j : Fin d)

/-!

## A. Definition and basic properties

-/

/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kroneckerDelta : R := if (i = j) then 1 else 0

@[inherit_doc kroneckerDelta]
notation "δ[" i "," j "]" => kroneckerDelta i j

@[inherit_doc kroneckerDelta]
notation "δ[" R' "," i "," j "]" => kroneckerDelta (R := R') i j

lemma kroneckerDelta_eq : δ[R,i,j] = ite (i = j) 1 0 := rfl

lemma kroneckerDelta_symm : δ[R,i,j] = δ[R,j,i] := ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

lemma kroneckerDelta_self : δ[R,i,i] = 1 := if_pos rfl

lemma kroneckerDelta_diff {i j : Fin d} (h : i ≠ j) : δ[R,i,j] = 0 := if_neg h

/-!

## B. Coercion

-/

@[simp]
lemma kroneckerDelta_coe {R' : Subring R} : δ[R',i,j] = δ[R,i,j] := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [kroneckerDelta_self]
  · simp [kroneckerDelta_diff hne]

@[simp]
lemma kroneckerDelta_ofReal : δ[ℝ,i,j] = δ[ℂ,i,j] := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [kroneckerDelta_self]
  · simp [kroneckerDelta_diff hne]

/-!

## C. Sums

-/

variable {M : Type*} [AddCommMonoid M] [Module R M]

lemma sum_kroneckerDelta (c : R) (f : Fin d → M) : ∑ j, (c * δ[i,j]) • f j = c • f i := by
  simp [kroneckerDelta_eq]

lemma sum_kroneckerDelta' (c : R) (f : Fin d → M) : ∑ j, (c * δ[j,i]) • f j = c • f i := by
  simp [kroneckerDelta_symm, sum_kroneckerDelta]

lemma sum_kroneckerDelta_self (c : R) (f : M) : ∑ (i : Fin d), (c * δ[i,i]) • f = (d * c) • f := by
  simp [kroneckerDelta_self, ← Nat.cast_smul_eq_nsmul R, smul_smul]

end KroneckerDelta
