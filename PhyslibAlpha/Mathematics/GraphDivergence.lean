/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# The divergence of a link field on a finite graph

The discrete divergence of a field on the links of a finite graph, and the summation by parts
formula that pairs it with a site field.

## i. Overview

A finite graph with site set `V` and link set `E` is given by the two endpoint maps `a, b : E → V`,
thought of as the tail and head of each link; a link field is a function `E → ℝ` and a site field a
function `V → ℝ`. The divergence at a site is the sum of the incoming links minus the sum of the
outgoing links. Summation by parts says that pairing a difference of a site field along the links
with a link field equals pairing the site field with the divergence of the link field. This is the
algebraic ingredient of every discrete variational derivation on a graph; the AQUAL discrete action
is the first application.

## ii. Key results

- `GraphDivergence.discreteDivergence` : the divergence of a link field at a site.
- `GraphDivergence.sum_link_mul_difference` : summation by parts on a finite graph.

## iii. Table of contents

- A. The divergence and summation by parts

## iv. References

* None.

-/

@[expose] public section

/-! ## A. The divergence and summation by parts -/

namespace GraphDivergence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The divergence of a link field: the sum of the incoming links minus the sum of
the outgoing links at a site. -/
noncomputable def discreteDivergence (a b : E → V) (d : E → ℝ) (x : V) : ℝ :=
  (∑ e : E, if b e = x then d e else 0) - ∑ e : E, if a e = x then d e else 0

/-- Summation by parts on a finite graph: the link pairing of a difference with
a link field equals the site pairing of the field with the divergence. -/
lemma sum_link_mul_difference (a b : E → V) (d : E → ℝ) (v : V → ℝ) :
    (∑ e : E, d e * (v (b e) - v (a e)))
      = ∑ x : V, v x * discreteDivergence a b d x := by
  have hb : (∑ x : V, v x * (∑ e : E, if b e = x then d e else 0))
      = ∑ e : E, d e * v (b e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (b e)]
    · simp [mul_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hmem
      exact absurd (Finset.mem_univ (b e)) hmem
  have ha : (∑ x : V, v x * (∑ e : E, if a e = x then d e else 0))
      = ∑ e : E, d e * v (a e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (a e)]
    · simp [mul_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hmem
      exact absurd (Finset.mem_univ (a e)) hmem
  simp only [discreteDivergence]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hb, ha]

end GraphDivergence
