/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Function.Kernel
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed

/-!
# Limits of positive-definite functions

This file derives pointwise- and locally-uniform-limit closure for `TauCeti.IsPositiveDefinite`, the
positive-definite function predicate on an involutive additive monoid, from Mathlib's closedness
theorem for the cone of positive-semidefinite matrices.

## i. Overview

This file derives pointwise- and locally-uniform-limit closure for
`TauCeti.IsPositiveDefinite`, the positive-definite function predicate on an involutive additive
monoid, from Mathlib's closedness theorem for the cone of positive-semidefinite matrices.

This is the limit-closure item from Part C of the `OneParameterSemigroups` roadmap. The result is
about positive-definiteness alone for pointwise limits; as the roadmap notes, continuity needs an
additional hypothesis. Mathlib's `TendstoLocallyUniformly.continuous` provides continuity of a
locally uniform limit when the approximating functions are frequently continuous, while this file
provides the positive-definiteness conclusion.

## ii. Key results

* `TauCeti.IsPositiveDefinite.of_tendsto`: filter-level pointwise-limit closure for
  positive-definite functions.
* `TauCeti.IsPositiveDefinite.of_forall_tendsto`: the same result when every function in the
  family is positive definite.
* `TauCeti.IsPositiveDefinite.of_seq_tendsto`: the sequential `atTop` specialization.
* `TauCeti.IsPositiveDefinite.of_tendstoLocallyUniformly`: locally uniform limits of eventually
  positive-definite functions are positive definite.

## iii. Table of contents

- A. Development

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

/-! ## A. Development -/

open Filter
open ComplexConjugate
open scoped Topology
open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

variable {M : Type*} [AddMonoid M] [StarAddMonoid M]

/-- Positive-definiteness is preserved under pointwise limits along a nontrivial filter. The
hypothesis on positive-definiteness is eventual, so this applies equally to nets that are
eventually positive definite. -/
lemma of_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : ∀ x : M, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_posSemidef <|
    Matrix.posSemidef_is_closed.mem_of_tendsto
      (tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hlim (a + star b))
      (hF.mono fun _ hi => hi.posSemidef)

/-- A pointwise limit of a family of positive-definite functions is positive definite. This is the
non-eventual form of `TauCeti.IsPositiveDefinite.of_tendsto`. -/
lemma of_forall_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ i, IsPositiveDefinite (F i)) (hlim : ∀ x : M, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_tendsto (Eventually.of_forall hF) hlim

/-- Sequential pointwise limits of eventually positive-definite functions are positive definite. -/
lemma of_seq_tendsto {F : ℕ → M → ℂ} {G : M → ℂ} (hF : ∀ᶠ n in atTop, IsPositiveDefinite (F n))
    (hlim : ∀ x : M, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_tendsto hF hlim

variable [TopologicalSpace M]

/-- A locally uniform limit of eventually positive-definite functions is positive definite.

Unlike continuity, positive-definiteness itself only needs pointwise convergence; local uniform
convergence is converted to pointwise convergence before applying
`TauCeti.IsPositiveDefinite.of_tendsto`. -/
lemma of_tendstoLocallyUniformly {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ᶠ i in l, IsPositiveDefinite (F i)) (hlim : TendstoLocallyUniformly F G l) :
    IsPositiveDefinite G :=
  of_tendsto hF fun x =>
    hlim.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

end IsPositiveDefinite

end TauCeti
