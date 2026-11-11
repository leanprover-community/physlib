/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Tactic.Commutes.Attribute
public import Mathlib.LinearAlgebra.Matrix.ZPow

/-!

# Tactic for `Commute`

This tactic uses `aesop` to discharge goals relating to the `Commute` relation. It mostly
tries to do straightforward recursion on expressions, along with some basic normalization
of ring operations.
-/

@[expose] public section

/-- A tactic for proving goals of the `Commute` relation.

You can use `commutes?` to get a corresponding proof script.
-/
syntax (name := commutesTac) "commutes" : tactic
macro_rules
  | `(tactic| commutes) => `(tactic|
    (aesop
      (config := { introsTransparency? := some .reducible, terminal := true,
                   useSimpAll := false, useDefaultSimpSet := false })
      (rule_sets := [$(Lean.mkIdent `Commutes):ident, -default]))) --include `builtin`

/-- A variant of the `commutes` tactic for proving `Commute` goals that produces
a proof script. -/
syntax (name := commutesTac?) "commutes?" : tactic
macro_rules
  | `(tactic| commutes?) => `(tactic|
    (aesop?
      (config := { introsTransparency? := some .reducible, terminal := true,
                   useSimpAll := false, useDefaultSimpSet := false })
      (rule_sets := [$(Lean.mkIdent `Commutes):ident, -default])))

attribute [aesop safe apply (rule_sets := [Commutes])]
  Commute.all Commute.refl
  Commute.one_left Commute.one_right
  Commute.pow_self Commute.self_pow Commute.pow_pow_self
  Units.commute_coe_inv Units.commute_inv_coe
  Commute.self_zpow Commute.zpow_self Commute.zpow_zpow_self
  Commute.self_zpow₀ Commute.zpow_self₀ Commute.zpow_zpow_self₀
  Commute.zero_left Commute.zero_right
  Commute.neg_one_left Commute.neg_one_right
  Nat.cast_commute Nat.commute_cast
  Commute.intCast_left Commute.intCast_right
  -- Commute.natCast_mul_self Commute.self_natCast_mul --redundant
  -- Commute.intCast_mul_self Commute.intCast_mul_self_right --redundant
  commute_invOf
  NNRat.cast_commute NNRat.commute_cast
  Rat.cast_commute Rat.commute_cast
  Polynomial.commute_X Polynomial.commute_X_pow
  Matrix.commute_diagonal Matrix.scalar_commute
  IsStarNormal.star_comm_self
  Matrix.Commute.self_zpow Matrix.Commute.zpow_self Matrix.Commute.zpow_zpow_self

--It's extremely rare that we need to use Commute.symm in the middle of a proof. But it's
--quite common that we specifically need it at the end (or equivalently, at the beginning)
--which is why we give a safe + fast tactic to apply. This often cuts heartbeats by a large
--factor.
attribute [aesop unsafe apply 5% (rule_sets := [Commutes])] Commute.symm

--This essentially does `symm + assumption`. Note that `assumption` is already a builtin.
add_aesop_rules safe tactic (rule_sets := [Commutes]) (by exact Commute.symm ‹_›)

--Due to indexing OfNat issues, these don't work as `apply` rules. We add them as a tactic.
add_aesop_rules safe tactic (rule_sets := [Commutes]) (by apply Commute.ofNat_left)
add_aesop_rules safe tactic (rule_sets := [Commutes]) (by apply Commute.ofNat_right)

--Try to normalize ring operations
add_aesop_rules safe tactic (rule_sets := [Commutes]) (by apply Commute.ofNat_right)

attribute [aesop unsafe apply 50% (rule_sets := [Commutes])]
  Commute.mul_left Commute.mul_right
  Commute.pow_left Commute.pow_right --Commute.pow_pow (redundant)
  Commute.smul_left Commute.smul_right
  Commute.op Commute.unop
  Commute.prod
  Commute.zpow_left Commute.zpow_right --Commute.zpow_zpow (redundant)
  Commute.zpow_left₀ Commute.zpow_right₀ --Commute.zpow_zpow_self₀ (redundant)
  Commute.units_of_val Commute.units_val
  Commute.units_inv_left Commute.units_inv_right
  Commute.units_zpow_left Commute.units_zpow_right
  Commute.ringInverse_ringInverse
  Commute.inv_left₀ Commute.inv_right₀
  Commute.div_left Commute.div_right
  Commute.neg_left Commute.neg_right
  Commute.add_left Commute.add_right
  Commute.sub_left Commute.sub_right
  -- Commute.natCast_mul_left Commute.natCast_mul_right --redundant
  -- Commute.intCast_mul_left Commute.intCast_mul_right --redundant
  Commute.invOf_left Commute.invOf_right
  Commute.inv_left Commute.inv_right --Commute.inv_inv (redundant)
  Commute.list_prod_left Commute.list_prod_right
  Commute.list_sum_left Commute.list_sum_right
  Commute.sum_left Commute.sum_right
  Commute.conj
  Commute.pi
  Commute.map
  Commute.star_star --Commute.star_left Commute.star_right
  Matrix.Commute.zpow_left Matrix.Commute.zpow_right --Matrix.Commute.zpow_zpow (redundant)

--TODO: In `Mathlib.Analysis.Normed.Algebra.Exponential`, tag
--   `Commute.exp_left`, `Commute.exp_right`, `Commute.exp`

--TODO: In cfc-relatated files, tag `Commute.cfc`, `IsSelfAdjoint.commute_cfc`,
-- `Commute.cfc_real`, `cfc_commute_cfc`, `cfcₙ_commute_cfcₙ`, `Commute.expUnitary`

attribute [aesop simp (rule_sets := [Commutes])]
  List.mem_map --Needed for `Commute.list_prod_left` to be interesting
  --Do some weak normalization of ring operations. This is similar to the list
  -- of lemmas used in `noncomm_ring`.
  mul_one one_mul mul_zero zero_mul add_zero zero_add pow_one pow_zero
  one_pow zero_pow

--Chekcing that `commutes` can now prove several other lemmas, which were not part
-- of the set of rules given above.
example : type_of% @Commute.natCast_mul_self := by
  commutes

example : type_of% @Commute.natCast_mul_left := by
  commutes

example : type_of% @Commute.zpow_zpow_self₀ := by
  commutes

example : type_of% @Commute.natCast_mul_natCast_mul := by
  commutes

example : type_of% @Commute.intCast_mul_self := by
  commutes

example : type_of% @Commute.intCast_mul_left := by
  commutes

example : type_of% @Matrix.Commute.zpow_zpow := by
  commutes

--Very basic example: all natural numbers commute.
example (A B : Nat) : Commute A B := by
  commutes

--Check that we can also recognize assumptions stated in equivalent forms
example (R : Type*) [NonUnitalNonAssocSemiring R] (x y : R) (h : SemiconjBy y x x) :
    Commute (x + y) x := by
  commutes

example (R : Type*) [Semiring R] (x y : R) (h : x * y * 1 = 0 + y * x) :
    Commute (y ^ 2) (x + 1) := by
  commutes

--Example of a more complex goal that it can prove.
example (l : List ℕ) (R : Type*) [Ring R] (x y : R) (h : Commute y x) :
    Commute (l.map (fun n ↦ n • x + y ^ n - 37)).prod x := by
  commutes --Runs in 5676 heartbeats

--Produced proof script from `commutes?` for the above goal. Takes 850 heartbeats
example (l : List ℕ) (R : Type*) [Ring R] (x y : R) (h : Commute y x) :
    Commute (l.map (fun n ↦ n • x + y ^ n - 37)).prod x := by
  apply Commute.list_prod_left
  intro x_1 a
  simp only [List.mem_map] at *
  obtain ⟨w, h_1⟩ := a
  obtain ⟨left, right⟩ := h_1
  subst right
  apply Commute.sub_left
  · apply Commute.add_left
    · apply Commute.smul_left
      rfl
    · apply Commute.pow_left
      exact h
  · apply Commute.ofNat_left
