/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Real analysis lemmas

Intervals of `ℝ`.

## i. Overview

Used to extend identities from open to closed intervals.

## ii. Key results

- `Continuous.eqOn_Icc_of_eqOn_Ioo`

## iii. Table of contents

- A. Intervals

## iv. References

* None.
-/

@[expose] public section

open scoped ContDiff

/-!
## A. Intervals
-/

open Set in
/-- Continuous functions agreeing on `(a, b)` agree on `[a, b]`. -/
lemma Continuous.eqOn_Icc_of_eqOn_Ioo {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : ℝ → F} (hf : Continuous f) (hg : Continuous g) {a b : ℝ} (hab : a < b)
    (h : ∀ τ ∈ Ioo a b, f τ = g τ) : ∀ τ ∈ Icc a b, f τ = g τ :=
  Set.EqOn.of_subset_closure h hf.continuousOn hg.continuousOn Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
