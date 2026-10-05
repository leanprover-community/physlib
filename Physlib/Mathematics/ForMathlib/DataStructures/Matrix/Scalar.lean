/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
/-!
# Scalar matrices

## i. Overview

Lemmas on the scalar matrices `Matrix.scalar n x` of a commutative `*`-ring: they commute
with the conjugate transpose, with entrywise maps fixing zero and with scalar actions; they
are fixed by conjugation with a unitary scalar; and a self-adjoint element gives a scalar
matrix real-linearly. A `1 × 1` matrix is the scalar matrix of its entry.

## ii. Key results

- `Matrix.star_scalar`, `Matrix.map_scalar`, `Matrix.scalar_smul` : compatibilities.
- `Matrix.scalar_eq_conj` : conjugation by a unitary scalar fixes a scalar matrix.
- `Matrix.scalarSelfAdjoint` : self-adjoint elements as scalar matrices.
- `Matrix.eq_scalar_fin_one` : a `1 × 1` matrix is scalar.

## iii. Table of contents

- A. Scalar matrices

-/

@[expose] public section

namespace Matrix

/-!

## A. Scalar matrices

-/

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The conjugate transpose of a scalar matrix is the scalar matrix of the star. -/
lemma star_scalar [StarRing R] (x : R) : star (scalar n x) = scalar n (star x) := by
  rw [scalar_apply, scalar_apply, star_eq_conjTranspose, diagonal_conjTranspose]
  rfl

/-- An entrywise map fixing zero sends a scalar matrix to a scalar matrix. -/
lemma map_scalar {S : Type*} [CommRing S] (f : R → S) (hf : f 0 = 0) (x : R) :
    (scalar n x).map f = scalar n (f x) := by
  rw [scalar_apply, scalar_apply, diagonal_map hf]

/-- A scalar action passes into a scalar matrix. -/
lemma scalar_smul {M : Type*} [Monoid M] [DistribMulAction M R] (c : M) (x : R) :
    scalar n (c • x) = c • scalar n x := by
  rw [scalar_apply, scalar_apply, ← diagonal_smul]
  rfl

/-- Conjugation by a unitary scalar fixes a scalar matrix. -/
lemma scalar_eq_conj [StarRing R] {u : R} (hu : u * star u = 1) (x : R) :
    scalar n x = scalar n u * scalar n x * star (scalar n u) := by
  rw [star_scalar, ← map_mul, ← map_mul, mul_comm u, mul_assoc, hu, mul_one]

/-- A self-adjoint element as a scalar matrix, real-linearly. -/
noncomputable def scalarSelfAdjoint [StarRing R] [Algebra ℝ R] [StarModule ℝ R] :
    ↥(selfAdjoint R) →ₗ[ℝ] Matrix n n R where
  toFun a := scalar n a.1
  map_add' a b := by rw [AddSubgroup.coe_add, map_add]
  map_smul' r a := by rw [selfAdjoint.val_smul, scalar_smul, RingHom.id_apply]

@[simp]
lemma scalarSelfAdjoint_apply [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (a : ↥(selfAdjoint R)) : (scalarSelfAdjoint (n := n)) a = scalar n a.1 := rfl

/-- A `1 × 1` matrix is the scalar matrix of its entry. -/
lemma eq_scalar_fin_one (A : Matrix (Fin 1) (Fin 1) R) : A = scalar (Fin 1) (A 0 0) := by
  ext i j
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  simp

end Matrix
