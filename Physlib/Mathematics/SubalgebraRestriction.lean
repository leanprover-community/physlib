/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
/-!
# Restricting a polynomial-valued algebra map to a subalgebra

## i. Overview

A grading of an algebra `A` is often recorded by an algebra map `f : A →ₐ[R] A[X]`, the
weight-`n` part being the eigenspace on which `f` is the monomial `X ^ n`. A subalgebra `S`
of `A` inherits such a grading exactly when `f` carries `S` into the polynomials with
coefficients in `S`, and this file supplies the two steps that gives.

Section A reduces the closure condition to the generators: since `f` is an algebra map and
the polynomials with coefficients in `S` form a subalgebra of `A[X]`, it is enough that
each generator lands there. Section B turns the closure condition into an algebra map
`S →ₐ[R] S[X]`, through the injection of `S[X]` into `A[X]`, and records that an eigenvalue
equation in `S` is the ambient one.

Nothing here is about any particular algebra. It is stated for an arbitrary `S` so that it
can be used at concrete algebras, where unfolding instances to check the corresponding
statement directly would be expensive.

## ii. Key results

- `Subalgebra.mem_range_mapAlgHom_of_adjoin` : the closure condition follows from the
  generators.
- `Subalgebra.polyRestrict` : the restricted map `S →ₐ[R] S[X]`.
- `Subalgebra.polyRestrict_eq_monomial_iff` : an eigenvalue equation in `S` is the ambient
  one.

## iii. Table of contents

- A. Closure from the generators
- B. The restricted map

-/

@[expose] public section

namespace Subalgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-!

## A. Closure from the generators

-/

/-- The polynomials with coefficients in a subalgebra, as a subalgebra of the polynomials
  with coefficients in the ambient algebra. -/
noncomputable abbrev polyRange (S : Subalgebra R A) : Subalgebra R (Polynomial A) :=
  (Polynomial.mapAlgHom S.val).range

/-- A monomial with a coefficient in `S` has coefficients in `S`. -/
lemma monomial_mem_polyRange {S : Subalgebra R A} {n : ℕ} {y : A} (hy : y ∈ S) :
    Polynomial.monomial n y ∈ S.polyRange :=
  ⟨Polynomial.monomial n ⟨y, hy⟩, by simp⟩

/-- If an algebra map into the polynomials sends every generator of an adjoined subalgebra
  into the polynomials over `S`, it sends the whole subalgebra there: the condition cuts out
  a subalgebra, and the generators lie in it. -/
lemma mem_range_mapAlgHom_of_adjoin {G : Set A} {f : A →ₐ[R] Polynomial A}
    (S : Subalgebra R A) (hgen : ∀ y ∈ G, f y ∈ S.polyRange)
    {x : A} (hx : x ∈ Algebra.adjoin R G) : f x ∈ S.polyRange := by
  induction hx using Algebra.adjoin_induction with
  | mem b hb => exact hgen b hb
  | algebraMap c => exact ⟨algebraMap R (Polynomial S) c, by simp⟩
  | add a b _ _ iha ihb => rw [map_add]; exact add_mem iha ihb
  | mul a b _ _ iha ihb => rw [map_mul]; exact mul_mem iha ihb

/-!

## B. The restricted map

-/

/-- Polynomials over a subalgebra inject into polynomials over the ambient algebra. -/
lemma mapAlgHom_val_injective (S : Subalgebra R A) :
    Function.Injective (Polynomial.mapAlgHom S.val) := by
  rw [Polynomial.coe_mapAlgHom]
  exact Polynomial.map_injective _ Subtype.val_injective

/-- An algebra map into the polynomials, restricted to a subalgebra it carries into the
  polynomials over that subalgebra. -/
noncomputable def polyRestrict (S : Subalgebra R A) (f : A →ₐ[R] Polynomial A)
    (hf : ∀ x : S, f (x : A) ∈ S.polyRange) : S →ₐ[R] Polynomial S :=
  (AlgEquiv.ofInjective (Polynomial.mapAlgHom S.val) S.mapAlgHom_val_injective).symm.toAlgHom.comp
    (AlgHom.codRestrict (f.comp S.val) _ hf)

@[simp]
lemma mapAlgHom_polyRestrict {S : Subalgebra R A} {f : A →ₐ[R] Polynomial A}
    (hf : ∀ x : S, f (x : A) ∈ S.polyRange) (x : S) :
    Polynomial.mapAlgHom S.val (S.polyRestrict f hf x) = f (x : A) :=
  congrArg Subtype.val ((AlgEquiv.ofInjective (Polynomial.mapAlgHom S.val)
    S.mapAlgHom_val_injective).apply_symm_apply ⟨f (x : A), hf x⟩)

/-- An eigenvalue equation for the restricted map is the ambient eigenvalue equation. -/
lemma polyRestrict_eq_monomial_iff {S : Subalgebra R A} {f : A →ₐ[R] Polynomial A}
    (hf : ∀ x : S, f (x : A) ∈ S.polyRange) {n : ℕ} (x : S) :
    S.polyRestrict f hf x = Polynomial.monomial n x
      ↔ f (x : A) = Polynomial.monomial n (x : A) := by
  constructor
  · intro hx
    rw [← mapAlgHom_polyRestrict hf x, hx, Polynomial.mapAlgHom_monomial]
    rfl
  · intro hx
    refine S.mapAlgHom_val_injective ?_
    rw [mapAlgHom_polyRestrict hf x, hx, Polynomial.mapAlgHom_monomial]
    rfl

end Subalgebra
