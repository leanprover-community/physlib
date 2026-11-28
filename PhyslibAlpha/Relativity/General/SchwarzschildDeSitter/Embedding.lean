/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic

/-!

# Embedding Schwarzschild spacetime in Schwarzschild–de Sitter spacetime

A Schwarzschild spacetime is the `Λ = 0` member of the Schwarzschild–de Sitter family.

## i. Overview

Setting the cosmological constant to `0` in a Schwarzschild–de Sitter spacetime returns the
Schwarzschild spacetime of the same mass: the metric function, the metric and its inverse agree
pointwise. This is the sense in which the Kottler family contains the Schwarzschild solution, and
it is what lets a Schwarzschild result be transported to `Λ = 0` inside the larger family.

## ii. Key results

- `SchwarzschildSpacetime.toDeSitter` : the embedding with mass `M` and `Λ = 0`.
- `SchwarzschildSpacetime.toDeSitter_M`, `SchwarzschildSpacetime.toDeSitter_Λ` : the embedding
  preserves the mass and sets the cosmological constant to zero.
- `SchwarzschildSpacetime.toDeSitter_metricFn`, `SchwarzschildSpacetime.toDeSitter_metric`,
  `SchwarzschildSpacetime.toDeSitter_metricInv` : the metric function, metric and inverse reduce to
  those of the Schwarzschild spacetime.

## iii. Table of contents

- A. The embedding at `Λ = 0`

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1) & Ch. 14.
  [ref: wald_1984_general_relativity]

-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

namespace SchwarzschildSpacetime

open SchwarzschildDeSitter

/-!

## A. The embedding at `Λ = 0`

-/

/-- Embed a Schwarzschild spacetime into `SchwarzschildDeSitterSpacetime` at `Λ = 0`. -/
def toDeSitter (S : SchwarzschildSpacetime) : SchwarzschildDeSitterSpacetime :=
  ⟨S.M, 0⟩

/-- Mass parameter of `S.toDeSitter` equals `S.M`. -/
@[simp]
lemma toDeSitter_M (S : SchwarzschildSpacetime) : S.toDeSitter.M = S.M := rfl

/-- Cosmological constant of `S.toDeSitter` vanishes. -/
@[simp]
lemma toDeSitter_Λ (S : SchwarzschildSpacetime) : S.toDeSitter.Λ = 0 := rfl

/-- At `Λ = 0`, `S.toDeSitter.metricFn` agrees pointwise with `S.metricFn`. -/
@[simp]
lemma toDeSitter_metricFn (S : SchwarzschildSpacetime) (r : ℝ) :
    S.toDeSitter.metricFn r = S.metricFn r :=
  SchwarzschildDeSitterSpacetime.metricFn_zero_lambda S.M r

/-- At `Λ = 0`, `S.toDeSitter.metric` reduces to `S.metric`. -/
lemma toDeSitter_metric (S : SchwarzschildSpacetime) : S.toDeSitter.metric = S.metric := by
  ext x i j
  simp [SchwarzschildDeSitterSpacetime.metric, SchwarzschildDeSitterSpacetime.toStaticSpherical,
    StaticSpherical.StaticSphericalMetric.metric, metric, toStaticSpherical]

/-- At `Λ = 0`, `S.toDeSitter.metricInv` reduces to `S.metricInv`. -/
lemma toDeSitter_metricInv (S : SchwarzschildSpacetime) :
    S.toDeSitter.metricInv = S.metricInv := by
  ext x i j
  simp [SchwarzschildDeSitterSpacetime.metricInv, SchwarzschildDeSitterSpacetime.toStaticSpherical,
    StaticSpherical.StaticSphericalMetric.metricInv, metricInv, toStaticSpherical]

end SchwarzschildSpacetime

end Schwarzschild

end GeneralRelativity
