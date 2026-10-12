/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.AddGroup
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Pontryagin characters are positive-definite atoms

A continuous character of a topological abelian group becomes a continuous function on the additive
group after transporting `G` to `Multiplicative G`.

## i. Overview

A continuous character of a topological abelian group becomes a continuous function on the
additive group after transporting `G` to `Multiplicative G`. This file proves that every such
character is a continuous subtraction-positive-definite function. The character-level fact is
an atomic input for Fourier analysis on locally compact abelian groups; it does not assert a
measure-representation or Pontryagin-duality theorem.

## ii. Key results

* `PontryaginDual.isPositiveDefiniteSub`: a continuous Pontryagin character is a
  continuous positive-definite function in the additive subtraction form.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

open ComplexConjugate
open scoped ComplexOrder

namespace PontryaginDual

open TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Precomposing a Pontryagin character with `Multiplicative.ofAdd` gives a continuous function in
subtraction-positive-definite form. -/
lemma isPositiveDefiniteSub
    (χ : PontryaginDual (Multiplicative G)) :
    Continuous (fun g : G => (χ (Multiplicative.ofAdd g) : ℂ)) ∧
      IsPositiveDefiniteSub
        (fun g : G => (χ (Multiplicative.ofAdd g) : ℂ)) := by
  constructor
  · have hco : Continuous ((↑) : Circle → ℂ) :=
      (LipschitzWith.subtype_val (Submonoid.unitSphere ℂ).carrier).continuous
    have hid : Continuous (fun g : G => (g : Multiplicative G)) := continuous_ofAdd
    exact hco.comp (χ.continuous.comp hid)
  · rw [isPositiveDefiniteSub_iff_posSemidef]
    have heq : (fun g w : G => (χ (Multiplicative.ofAdd (g - w)) : ℂ)) =
        (fun g w : G => (χ (Multiplicative.ofAdd g) : ℂ) *
          ((χ (Multiplicative.ofAdd w) : ℂ))⁻¹) := by
      funext g w
      rw [ofAdd_sub, map_div, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv]
    rw [heq]
    simpa only [RCLike.star_def, ← Circle.coe_inv, Circle.coe_inv_eq_conj,
      Complex.conj_conj] using
      (posSemidef_rankOne (R := ℂ)
        (fun g : G => conj (χ (Multiplicative.ofAdd g))))

end PontryaginDual
