/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Basic.Real.Basic

/-!

# Lattice gauge theories

The definition of a pure lattice gauge theory on a graph with a gauge group.

## i. Overview

A lattice gauge theory, introduced by Wilson, regularizes a gauge theory by placing it on a
lattice. The matter fields live on the sites, and the gauge field lives on the oriented links
between neighbouring sites.

In this file the lattice is a simple graph `Λ` on a type of sites `V`, and the gauge group is a
group `G`. The oriented links of the lattice are the darts `Λ.Dart` of the graph: ordered pairs
`(x, y)` of adjacent sites, with `Dart.symm` reversing the orientation. Working with a general
graph, rather than the hypercubic lattice, covers periodic and open boundary conditions and
lattices of any dimension at once.

A lattice gauge field `U` assigns to each oriented link `(x, y)` a link variable `U(x, y) ∈ G`,
the lattice version of the parallel transport from `y` to `x`. Traversing a link in the opposite
direction undoes the transport, so `U(y, x) = U(x, y)⁻¹`.

A lattice gauge transformation is a function `g : V → G`, an independent group element at each
site. It acts on a lattice gauge field by

`U(x, y) ↦ g(x) U(x, y) g(y)⁻¹`,

which defines an action of the group `V → G` on lattice gauge fields.

A pure lattice gauge theory is specified by a real Euclidean action on lattice gauge fields which
is invariant under all lattice gauge transformations. The standard example is the Wilson action,
which sums a class function of the ordered product of link variables around each elementary
square (plaquette) of a hypercubic lattice. On a finite lattice with a compact gauge group, the
Euclidean path integral of the theory is the integral over the product of Haar measures on the
links weighted by the exponential of minus the action. Neither the Wilson action nor the measure
is constructed in this file.

## ii. Key results

- `LatticeGaugeField` : a configuration of link variables on the oriented links of a lattice.
- `LatticeGaugeField.map_symm` : reversing a link inverts its link variable.
- `LatticeGaugeField.smul_apply` : the action of a lattice gauge transformation on a link.
- `LatticeGaugeTheory` : a gauge-invariant Euclidean action on lattice gauge fields.

## iii. Table of contents

- A. Lattice gauge fields
- B. Lattice gauge transformations
- C. Lattice gauge theories

## iv. References

* K. G. Wilson, Confinement of quarks, Phys. Rev. D 10 (1974) 2445.
* I. Montvay and G. Münster, Quantum Fields on a Lattice, Cambridge University Press (1994).

-/

@[expose] public section

namespace LatticeQFT

variable {V G : Type*} {Λ : SimpleGraph V} [Group G]

/-!

## A. Lattice gauge fields

-/

/-- A lattice gauge field on the lattice `Λ` with gauge group `G`. It assigns a link variable in
`G` to each oriented link (dart) of the lattice, such that reversing the orientation of a link
inverts its link variable. -/
structure LatticeGaugeField (Λ : SimpleGraph V) (G : Type*) [Group G] where
  /-- The link variable on each oriented link. -/
  toFun : Λ.Dart → G
  /-- Reversing the orientation of a link inverts its link variable. -/
  toFun_symm (d : Λ.Dart) : toFun d.symm = (toFun d)⁻¹

namespace LatticeGaugeField

instance : FunLike (LatticeGaugeField Λ G) Λ.Dart G where
  coe U := U.toFun
  coe_injective U U' h := by
    cases U
    cases U'
    congr

/-- Two lattice gauge fields are equal if they have the same link variable on every link. -/
@[ext]
lemma ext {U U' : LatticeGaugeField Λ G} (h : ∀ d, U d = U' d) : U = U' :=
  DFunLike.ext U U' h

@[simp]
lemma coe_mk (f : Λ.Dart → G) (hf : ∀ d, f d.symm = (f d)⁻¹) :
    ⇑(⟨f, hf⟩ : LatticeGaugeField Λ G) = f := rfl

/-- Reversing the orientation of a link inverts its link variable. -/
@[simp]
lemma map_symm (U : LatticeGaugeField Λ G) (d : Λ.Dart) : U d.symm = (U d)⁻¹ :=
  U.toFun_symm d

/-!

## B. Lattice gauge transformations

-/

/-- A lattice gauge transformation `g : V → G` acts on a lattice gauge field by
`U(x, y) ↦ g(x) U(x, y) g(y)⁻¹` on the oriented link `(x, y)`. -/
instance : SMul (V → G) (LatticeGaugeField Λ G) where
  smul g U := ⟨fun d => g d.fst * U d * (g d.snd)⁻¹, fun d => by simp [mul_assoc]⟩

/-- The link variable of a gauge-transformed field on the oriented link `(x, y)` is
`g(x) U(x, y) g(y)⁻¹`. -/
lemma smul_apply (g : V → G) (U : LatticeGaugeField Λ G) (d : Λ.Dart) :
    (g • U) d = g d.fst * U d * (g d.snd)⁻¹ := rfl

instance : MulAction (V → G) (LatticeGaugeField Λ G) where
  one_smul U := by
    ext d
    simp [smul_apply]
  mul_smul g h U := by
    ext d
    simp [smul_apply, mul_assoc]

end LatticeGaugeField

/-!

## C. Lattice gauge theories

-/

/-- A pure lattice gauge theory on the lattice `Λ` with gauge group `G`. It is specified by a
Euclidean action on lattice gauge fields, the weight of a field in the path integral being the
exponential of minus its action. The action is required to be invariant under lattice gauge
transformations, as is the Wilson action. -/
structure LatticeGaugeTheory (Λ : SimpleGraph V) (G : Type*) [Group G] where
  /-- The Euclidean action of a lattice gauge field. -/
  action : LatticeGaugeField Λ G → ℝ
  /-- The action is invariant under lattice gauge transformations. -/
  action_smul (g : V → G) (U : LatticeGaugeField Λ G) : action (g • U) = action U

attribute [simp] LatticeGaugeTheory.action_smul

end LatticeQFT
