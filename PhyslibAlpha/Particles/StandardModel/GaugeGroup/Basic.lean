/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
/-!
# A primitive cube root of unity

The root of unity `ω = exp (2 π i / 3)`, which both non-abelian factors of the gauge group see.

## i. Overview

`Physlib.Particles.StandardModel.Basic` carries the gauge group `GaugeGroupI` of the Standard
Model and its discrete quotients. One scalar recurs throughout the structure of its
non-abelian factors: the primitive cube root of unity `ω = exp (2 π i / 3)`. The element
`ω • 1` generates the centre of `SU(3)`, the cyclic colour permutation has eigenvalues the
powers of `ω`, and `diag(ω, ω²)` lies in `SU(2)`. Collected here are the facts about `ω` those
uses need: that it is a primitive cube root of unity, that it cubes to one, that it is nonzero
and of modulus one, and that its powers only see the exponent modulo three.

## ii. Key results

- `StandardModel.cubeRootOfUnity` : the primitive cube root of unity `ω = exp (2 π i / 3)`.
- `StandardModel.cubeRootOfUnity_isPrimitiveRoot` : it is a primitive cube root of unity.
- `StandardModel.cubeRootOfUnity_pow_three`, `StandardModel.cubeRootOfUnity_pow_mod` : it cubes
  to one, so its powers only see the exponent modulo three.
- `StandardModel.cubeRootOfUnity_ne_zero`, `StandardModel.cubeRootOfUnity_mul_star` : it is
  nonzero and of modulus one.

## iii. Table of contents

- A. A primitive cube root of unity

## iv. References

The gauge group and its quotients are in `Physlib.Particles.StandardModel.Basic`.

-/

@[expose] public section

namespace StandardModel

open Matrix
open Complex
open ComplexConjugate

/-!

## A. A primitive cube root of unity

`ω = exp (2 π i / 3)` appears in both non-abelian factors: `ω • 1` generates the centre of
`SU(3)`, the cyclic colour permutation has eigenvalues the powers of `ω`, and `diag(ω, ω²)`
lies in `SU(2)`.

-/

/-- The primitive cube root of unity `ω = exp (2 π i / 3)`. -/
noncomputable def cubeRootOfUnity : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- `ω` is a primitive cube root of unity. -/
lemma cubeRootOfUnity_isPrimitiveRoot : IsPrimitiveRoot cubeRootOfUnity 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [cubeRootOfUnity] using h

/-- `ω` cubes to one. -/
@[simp] lemma cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 :=
  cubeRootOfUnity_isPrimitiveRoot.pow_eq_one

/-- `ω` is nonzero, being a value of the complex exponential. -/
lemma cubeRootOfUnity_ne_zero : cubeRootOfUnity ≠ 0 := Complex.exp_ne_zero _

/-- Powers of `ω` only see the exponent modulo three. -/
lemma cubeRootOfUnity_pow_mod (m : ℕ) :
    cubeRootOfUnity ^ (m % 3) = cubeRootOfUnity ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, cubeRootOfUnity_pow_three, one_pow, one_mul]

/-- `ω` has modulus one. -/
lemma cubeRootOfUnity_mul_star : cubeRootOfUnity * star cubeRootOfUnity = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    cubeRootOfUnity_isPrimitiveRoot.norm'_eq_one (by norm_num)]
  simp

end StandardModel
