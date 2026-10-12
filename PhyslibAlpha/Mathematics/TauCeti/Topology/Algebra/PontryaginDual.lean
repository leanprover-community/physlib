/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
public import PhyslibAlpha.Mathematics.TauCeti.Topology.Algebra.ContinuousMonoidHom.Polish

/-!
# Topology of Pontryagin duals

The Pontryagin dual of a second-countable locally compact monoid is Polish.

## i. Overview

The Pontryagin dual of a second-countable locally compact monoid is Polish. For locally compact
abelian groups this ensures that finite Borel measures on the dual are tight and determined by
their Fourier–Stieltjes transforms.

A continuous character of the discrete group `ℤ` is determined by its value at `1`, which may be
any point of the unit circle. This file packages that correspondence as an isomorphism of
topological groups between the unit circle and the Pontryagin dual of `ℤ`. It lets statements
about the dual of `ℤ`, such as Fourier–Stieltjes transforms of measures on it, be read on the
concrete unit circle, where a character becomes the monomial `z ↦ zⁿ`.

## ii. Key results

* `TauCeti.circleEquivPontryaginDualInt`: the point `z` of the unit circle corresponds to the
  character `n ↦ zⁿ` of `ℤ`.

## iii. Table of contents

- A. Development

## iv. References

* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), §1.2 (the dual group).
-/

public section

/-! ## A. Development -/

noncomputable section

namespace TauCeti

/-- The Pontryagin dual of a second-countable locally compact monoid is Polish. -/
instance instPolishSpacePontryaginDual {A : Type*} [Monoid A] [TopologicalSpace A]
    [LocallyCompactSpace A] [SecondCountableTopology A] : PolishSpace (PontryaginDual A) :=
  inferInstanceAs (PolishSpace (A →ₜ* Circle))

/-- The unit circle is the Pontryagin dual of `ℤ`: the point `z` corresponds to the character
`n ↦ zⁿ`, and a character corresponds to its value at `1`. -/
def circleEquivPontryaginDualInt : Circle ≃ₜ* PontryaginDual (Multiplicative ℤ) where
  toFun z := (⟨zpowersHom Circle z, continuous_of_discreteTopology⟩ : Multiplicative ℤ →ₜ* Circle)
  invFun χ := χ (Multiplicative.ofAdd 1)
  left_inv z := zpow_one z
  right_inv χ := PontryaginDual.ext fun n ↦
    DFunLike.congr_fun ((zpowersHom Circle).apply_symm_apply χ.toMonoidHom) n
  map_mul' z w := PontryaginDual.ext fun n ↦ mul_zpow z w n.toAdd
  continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry _ <|
    continuous_prod_of_discrete_right.mpr fun n ↦ continuous_zpow n.toAdd
  continuous_invFun :=
    continuous_eval_const (F := Multiplicative ℤ →ₜ* Circle) (Multiplicative.ofAdd 1)

/-- The character attached to `z` sends `n` to `zⁿ`. -/
@[simp]
lemma circleEquivPontryaginDualInt_apply_apply (z : Circle) (n : Multiplicative ℤ) :
    circleEquivPontryaginDualInt z n = z ^ n.toAdd :=
  (rfl)

/-- The point of the circle attached to a character of `ℤ` is its value at `1`. -/
@[simp]
lemma circleEquivPontryaginDualInt_symm_apply (χ : PontryaginDual (Multiplicative ℤ)) :
    circleEquivPontryaginDualInt.symm χ = χ (Multiplicative.ofAdd 1) :=
  (rfl)

end TauCeti
