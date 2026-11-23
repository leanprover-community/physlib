/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
/-!
# A cube root of unity and the factors of a gauge transformation

The root of unity `ω = exp (2 π i / 3)`, and the inverses and factors of gauge transformations.

## i. Overview

`Physlib.Particles.StandardModel.GaugeGroup.Basic` carries the gauge group `GaugeGroupI` of
the Standard Model and its discrete quotients. One scalar recurs throughout the structure of its
non-abelian factors, the primitive cube root of unity `ω = exp (2 π i / 3)`. The element
`ω • 1` generates the centre of `SU(3)`, the cyclic colour permutation has eigenvalues the
powers of `ω`, and `diag(ω, ω²)` lies in `SU(2)`. Collected here are the facts about `ω` those
uses need. It is a primitive cube root of unity, it cubes to one, it is nonzero and of modulus
one, and its powers only see the exponent modulo three.

The colour, isospin and hypercharge laws each constrain one factor of a gauge transformation
`(U, V, t)`. The inverse of a unitary matrix is its conjugate transpose, so the entries of the
inverse of an element of `SU(3)` or `SU(2)` are the conjugated transposed entries, and the
inverse of a unitary scalar is its conjugate. The inverse of a transformation acting in one
factor alone acts in that factor alone, by the inverse. Every gauge transformation is the
product of its three factors, so an element fixed by each factor separately is gauge invariant.

## ii. Key results

- `StandardModel.cubeRootOfUnity` : the primitive cube root of unity `ω = exp (2 π i / 3)`.
- `StandardModel.cubeRootOfUnity_isPrimitiveRoot` : it is a primitive cube root of unity.
- `StandardModel.cubeRootOfUnity_pow_three`, `StandardModel.cubeRootOfUnity_pow_mod` : it cubes
  to one, so its powers only see the exponent modulo three.
- `StandardModel.cubeRootOfUnity_ne_zero`, `StandardModel.cubeRootOfUnity_mul_star` : it is
  nonzero and of modulus one.
- `StandardModel.su3_inv_apply`, `StandardModel.su2_inv_apply` : the entries of an inverse in
  `SU(3)` or `SU(2)` are the conjugated transposed entries.
- `StandardModel.inv_su3Elt`, `StandardModel.inv_su2Elt` : the inverse of a colour or isospin
  transformation is the transformation of the inverse.
- `StandardModel.toSU3_su3Elt` and its eight companions : the three factors of a colour,
  isospin or hypercharge transformation.
- `StandardModel.forall_repGauge_eq_self` : an element fixed by each of the three factors of the
  gauge group is gauge invariant.

## iii. Table of contents

- A. A primitive cube root of unity
- B. Inverses and factors of gauge transformations

## iv. References

The gauge group and its quotients are in `Physlib.Particles.StandardModel.GaugeGroup.Basic`.

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

/-!

## B. Inverses and factors of gauge transformations

The inverse of a unitary matrix is its conjugate transpose. This section records what that says
for the entries of inverses in `SU(3)` and `SU(2)`, for unitary scalars, and for the colour and
isospin transformations `(U, 1, 1)` and `(1, V, 1)`, and the colour, isospin and hypercharge
factors of `(U, 1, 1)`, `(1, V, 1)` and `(1, 1, t)`. A gauge transformation `(U, V, t)` is the
product of these three, which turns three separate invariances into gauge invariance.

-/

/-- The entries of the inverse of an `SU(3)` element are the conjugated transposed
  entries, the inverse of a unitary matrix being its conjugate transpose. -/
lemma su3_inv_apply (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 3) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

/-- The entries of the inverse of an `SU(2)` element are the conjugated transposed
  entries. -/
lemma su2_inv_apply (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

/-- The inverse of a unitary scalar is its conjugate. -/
lemma unitary_inv_coe (t : unitary ℂ) : ((t⁻¹ : unitary ℂ) : ℂ) = star (t : ℂ) := rfl

/-- The inverse of a colour gauge transformation is the colour transformation of the
  inverse. -/
lemma inv_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    ((U, 1, 1) : GaugeGroupI)⁻¹ = ((U⁻¹, 1, 1) : GaugeGroupI) := by
  simp

/-- The inverse of an isospin gauge transformation is the isospin transformation of the
  inverse. -/
lemma inv_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) := by
  simp

/-- The colour factor of a colour gauge transformation. -/
@[simp] lemma toSU3_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toSU3 ((U, 1, 1) : GaugeGroupI) = U := rfl

/-- The isospin factor of a colour gauge transformation is trivial. -/
@[simp] lemma toSU2_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI) = 1 := rfl

/-- The hypercharge factor of a colour gauge transformation is trivial. -/
@[simp] lemma toU1_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toU1 ((U, 1, 1) : GaugeGroupI) = 1 := rfl

/-- The colour factor of an isospin gauge transformation is trivial. -/
@[simp] lemma toSU3_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toSU3 ((1, V, 1) : GaugeGroupI) = 1 := rfl

/-- The isospin factor of an isospin gauge transformation. -/
@[simp] lemma toSU2_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toSU2 ((1, V, 1) : GaugeGroupI) = V := rfl

/-- The hypercharge factor of an isospin gauge transformation is trivial. -/
@[simp] lemma toU1_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toU1 ((1, V, 1) : GaugeGroupI) = 1 := rfl

/-- The colour factor of a hypercharge gauge transformation is trivial. -/
@[simp] lemma toSU3_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toSU3 ((1, 1, t) : GaugeGroupI) = 1 := rfl

/-- The isospin factor of a hypercharge gauge transformation is trivial. -/
@[simp] lemma toSU2_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toSU2 ((1, 1, t) : GaugeGroupI) = 1 := rfl

/-- The hypercharge factor of a hypercharge gauge transformation. -/
@[simp] lemma toU1_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toU1 ((1, 1, t) : GaugeGroupI) = t := rfl

/-- A gauge transformation is the product of its colour, isospin and hypercharge parts, so
  an element fixed by each of the three factors separately is gauge invariant. -/
lemma forall_repGauge_eq_self {B : Type*} [AddCommGroup B] [Module ℂ B]
    {rep : Representation ℂ GaugeGroupI B} {x : B}
    (h3 : ∀ U : specialUnitaryGroup (Fin 3) ℂ, rep (U, 1, 1) x = x)
    (h2 : ∀ V : specialUnitaryGroup (Fin 2) ℂ, rep (1, V, 1) x = x)
    (h1 : ∀ t : unitary ℂ, rep (1, 1, t) x = x) (g : GaugeGroupI) : rep g x = x := by
  have hg : g = ((g.1, 1, 1) : GaugeGroupI) * (((1, g.2.1, 1) : GaugeGroupI)
      * ((1, 1, g.2.2) : GaugeGroupI)) := by
    simp [Prod.ext_iff]
  rw [hg, map_mul, mul_apply_eq_comp, map_mul, mul_apply_eq_comp, h1, h2, h3]

end StandardModel
