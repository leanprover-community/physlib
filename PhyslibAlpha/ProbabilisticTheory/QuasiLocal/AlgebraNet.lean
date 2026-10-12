/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Order.Directed
public import Mathlib.Analysis.Complex.Basic

/-!

# Nets of algebras over the finite regions of a lattice and their quasi-local algebra

A net of `*`-algebras over the finite regions of a set of sites has a quasi-local algebra: the
direct limit of the local algebras.

## i. Overview

The observables of an infinite system are those of finite regions, extended by the identity. A
*net of algebras* assigns to each finite region `X` of a set of sites a unital `*`-algebra `A X`,
and to each pair of regions `X ≤ Y` a unital `*`-homomorphism `A X → A Y`, with the identity
for `X = Y` and composition respected. The finite regions are directed under inclusion: any two
regions lie in a third. The *quasi-local algebra* is the direct limit: its elements are the
observables of some finite region, two of them being identified when they agree in a common larger
region. It is a unital complex `*`-algebra, and each local algebra maps into it.

Nothing about the nature of the local algebras enters: they may be commutative, giving a
classical system, or matrix algebras, giving a quantum system, or anything in between. The
constructions that follow, the states and thermodynamic limits, the symmetries and the dynamics,
are made once for every net.

## ii. Key results

- `AlgebraNet` : a net of unital `*`-algebras over the finite regions of a set of sites.
- `AlgebraNet.Quasilocal` : the quasi-local algebra, as the direct limit.
- `AlgebraNet.of` : the embedding of a local algebra as a unital `*`-homomorphism.
- `AlgebraNet.of_incl` : the local algebras embed compatibly.
- `AlgebraNet.exists_of` : every quasi-local observable is supported in a finite region.
- `AlgebraNet.moveHom` : a map of the quasi-local algebra induced by region-moving local maps.

## iii. Table of contents

- A. Nets of algebras
- B. The quasi-local algebra

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 2.6.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace QuasiLocal

/-! ## A. Nets of algebras -/

/-- A net of unital complex `*`-algebras over the finite regions of a set of sites: the algebra of
each region, and the inclusion of the algebra of a region in that of a larger region. -/
structure AlgebraNet (S : Type*) where
  /-- The algebra of observables of a finite region. -/
  A : Finset S → Type*
  [ring : ∀ X, Ring (A X)]
  [algebra : ∀ X, Algebra ℂ (A X)]
  [starRing : ∀ X, StarRing (A X)]
  [starModule : ∀ X, StarModule ℂ (A X)]
  /-- The inclusion of the algebra of a region in the algebra of a larger region. -/
  incl : ∀ {X Y : Finset S}, X ≤ Y → A X →⋆ₐ[ℂ] A Y
  /-- The inclusion of a region in itself is the identity. -/
  incl_refl : ∀ (X : Finset S) (a : A X), incl (le_refl X) a = a
  /-- Inclusions compose. -/
  incl_trans : ∀ {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (a : A X),
    incl (h₁.trans h₂) a = incl h₂ (incl h₁ a)

attribute [instance] AlgebraNet.ring AlgebraNet.algebra AlgebraNet.starRing
  AlgebraNet.starModule

namespace AlgebraNet

variable {S : Type*} (N : AlgebraNet S)

instance : DirectedSystem N.A (fun X Y (h : X ≤ Y) => N.incl h) where
  map_self X a := N.incl_refl X a
  map_map _ _ _ h₁ h₂ a := (N.incl_trans h₁ h₂ a).symm

/-! ## B. The quasi-local algebra -/

variable [DecidableEq S]

/-- **The quasi-local algebra** of a net: the direct limit of the algebras of the finite
regions. -/
abbrev Quasilocal : Type _ := DirectLimit N.A (fun X Y (h : X ≤ Y) => N.incl h)

noncomputable example : Ring N.Quasilocal := inferInstance
noncomputable example : Algebra ℂ N.Quasilocal := inferInstance
noncomputable example : StarRing N.Quasilocal := inferInstance

/-- The embedding of the algebra of a region in the quasi-local algebra, as a unital
`*`-homomorphism. -/
noncomputable def of (X : Finset S) : N.A X →⋆ₐ[ℂ] N.Quasilocal where
  toAlgHom := DirectLimit.Algebra.of N.A (fun X Y (h : X ≤ Y) => N.incl h) X
  map_star' a := (DirectLimit.star_def (f := fun X Y (h : X ≤ Y) => N.incl h) X a).symm

omit [DecidableEq S] in
/-- The embeddings of the local algebras are compatible with the inclusions. -/
lemma of_incl {X Y : Finset S} (h : X ≤ Y) (a : N.A X) : N.of Y (N.incl h a) = N.of X a :=
  DirectLimit.Algebra.of_f (G := N.A) (f := fun X Y (h : X ≤ Y) => N.incl h) h a

omit [DecidableEq S] in
/-- Every element of the quasi-local algebra is an observable of some finite region. -/
lemma exists_of (x : N.Quasilocal) : ∃ (X : Finset S) (a : N.A X), N.of X a = x := by
  induction x using DirectLimit.induction with | _ X a => exact ⟨X, a, rfl⟩

/-- A map of the quasi-local algebra induced by maps of the local algebras that move regions: a
monotone map `ρ` of regions and, for each region `X`, a unital `*`-homomorphism of its algebra
into that of `ρ X`, natural with respect to the inclusions. -/
noncomputable def moveHom (ρ : Finset S → Finset S) (hρ : Monotone ρ)
    (φ : ∀ X, N.A X →⋆ₐ[ℂ] N.A (ρ X))
    (hφ : ∀ {X Y : Finset S} (h : X ≤ Y) (a : N.A X), φ Y (N.incl h a) = N.incl (hρ h) (φ X a)) :
    N.Quasilocal →⋆ₐ[ℂ] N.Quasilocal where
  toAlgHom := DirectLimit.Algebra.lift N.A (fun X Y (h : X ≤ Y) => N.incl h) N.Quasilocal
    (fun X => (N.of (ρ X)).toAlgHom.comp (φ X).toAlgHom) (fun X Y h a => by
      change N.of (ρ Y) (φ Y (N.incl h a)) = N.of (ρ X) (φ X a)
      rw [hφ h a, N.of_incl (hρ h)])
  map_star' x := by
    induction x using DirectLimit.induction with | _ X a =>
    rw [DirectLimit.star_def (f := fun X Y (h : X ≤ Y) => N.incl h) X a]
    change N.of (ρ X) (φ X (star a)) = star (N.of (ρ X) (φ X a))
    rw [map_star, map_star]

omit [DecidableEq S] in
lemma moveHom_of (ρ : Finset S → Finset S) (hρ : Monotone ρ) (φ : ∀ X, N.A X →⋆ₐ[ℂ] N.A (ρ X))
    (hφ : ∀ {X Y : Finset S} (h : X ≤ Y) (a : N.A X), φ Y (N.incl h a) = N.incl (hρ h) (φ X a))
    (X : Finset S) (a : N.A X) : N.moveHom ρ hρ φ hφ (N.of X a) = N.of (ρ X) (φ X a) := rfl

end AlgebraNet

end QuasiLocal

end ProbabilisticTheory
