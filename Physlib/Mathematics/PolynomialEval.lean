/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Roots
/-!

# Polynomials with coefficients in an algebra

## i. Overview

A polynomial whose coefficients lie in a `k`-algebra `A` can be evaluated at the image
`algebraMap k A c` of a scalar. This file records that such a polynomial is determined by
those evaluations alone, when `k` is an infinite field, and defines the polynomial obtained
by applying a `k`-linear map to every coefficient.

Both are used to transport grading statements between two equivalent descriptions of a
grading on a jet algebra: the *mass-weight polynomial*, whose `X ^ n` coefficient is the
weight-`n` part of an element, and the *mass-weight scaling*, the algebra map scaling each
weight-`n` part by `c ^ n`. The scaling is the evaluation of the polynomial, so a statement
about one transfers to the other.

The determinacy is not an instance of `Polynomial.funext`: the coefficient ring `A` is
neither commutative nor a domain in the intended applications. It holds because `A` is a
`k`-vector space, so its elements are separated by linear functionals, and a polynomial over
the infinite field `k` is determined by its values.

## ii. Key results

- `Polynomial.eq_zero_of_forall_eval_algebraMap_eq_zero` : a polynomial vanishing at every
  scalar is zero.
- `Polynomial.ext_of_forall_eval_algebraMap` : two polynomials agreeing at every scalar are
  equal.
- `Polynomial.mapCoeffs` : apply a linear map to every coefficient.
- `Polynomial.eval_algebraMap_mapCoeffs` : evaluation commutes with `mapCoeffs`.

## iii. Table of contents

- A. Determinacy by evaluation at scalars
- B. Applying a linear map to the coefficients

-/

@[expose] public section

namespace Polynomial

/-!

## A. Determinacy by evaluation at scalars

-/

/-- A polynomial with coefficients in an algebra over an infinite field vanishes as soon as
  it vanishes at the image of every scalar. Linear functionals separate the coefficients,
  and over an infinite field a polynomial is determined by its values. -/
lemma eq_zero_of_forall_eval_algebraMap_eq_zero {k A : Type*} [Field k] [Infinite k]
    [Ring A] [Algebra k A] {p : Polynomial A}
    (h : ∀ c : k, p.eval (algebraMap k A c) = 0) : p = 0 := by
  ext n
  rw [Polynomial.coeff_zero, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  set s : Polynomial k := ∑ m ∈ p.support, Polynomial.monomial m (φ (p.coeff m)) with hs
  have hcoeff : ∀ m, s.coeff m = φ (p.coeff m) := by
    intro m
    rw [hs, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' p.support m fun i => φ (p.coeff i)]
    by_cases hm : m ∈ p.support
    · rw [if_pos hm]
    · rw [if_neg hm, Polynomial.notMem_support_iff.mp hm, map_zero]
  have hzero : s = 0 := by
    refine Polynomial.funext fun c => ?_
    have h1 := congrArg φ (h c)
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum, map_zero] at h1
    rw [Polynomial.eval_zero, hs, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial]
    rw [← h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  rw [← hcoeff n, hzero, Polynomial.coeff_zero]

/-- Two polynomials with coefficients in an algebra over an infinite field are equal as soon
  as they agree at the image of every scalar. -/
lemma ext_of_forall_eval_algebraMap {k A : Type*} [Field k] [Infinite k]
    [Ring A] [Algebra k A] {p q : Polynomial A}
    (h : ∀ c : k, p.eval (algebraMap k A c) = q.eval (algebraMap k A c)) : p = q := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_eval_algebraMap_eq_zero (k := k) fun c => ?_
  rw [Polynomial.eval_sub, h c, sub_self]

/-!

## B. Applying a linear map to the coefficients

-/

/-- The polynomial obtained by applying a function to every coefficient. Unlike
  `Polynomial.map` this needs no multiplicativity, so it applies to derivations.

  The argument is a bare function rather than a linear map: on an algebra built as a tensor
  product the module structure coming from the algebra and the one coming from the tensor
  product are equal but not syntactically so, and bundling would force the caller to
  reconcile them. The properties needed are taken as hypotheses instead. -/
noncomputable def mapCoeffs {A : Type*} [Semiring A] (f : A → A) (p : Polynomial A) :
    Polynomial A :=
  ∑ m ∈ p.support, Polynomial.monomial m (f (p.coeff m))

lemma coeff_mapCoeffs {A : Type*} [Semiring A] {f : A → A} (hf0 : f 0 = 0)
    (p : Polynomial A) (n : ℕ) : (mapCoeffs f p).coeff n = f (p.coeff n) := by
  rw [mapCoeffs, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' p.support n fun i => f (p.coeff i)]
  by_cases hn : n ∈ p.support
  · rw [if_pos hn]
  · rw [if_neg hn, Polynomial.notMem_support_iff.mp hn, hf0]

@[simp]
lemma mapCoeffs_zero {A : Type*} [Semiring A] (f : A → A) : mapCoeffs f 0 = 0 := by
  simp [mapCoeffs]

lemma mapCoeffs_monomial {A : Type*} [Semiring A] {f : A → A} (hf0 : f 0 = 0)
    (n : ℕ) (a : A) :
    mapCoeffs f (Polynomial.monomial n a) = Polynomial.monomial n (f a) := by
  ext m
  rw [coeff_mapCoeffs hf0, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
  split_ifs
  · rfl
  · exact hf0

lemma mapCoeffs_add {A : Type*} [Semiring A] {f : A → A} (hf0 : f 0 = 0)
    (hadd : ∀ a b : A, f (a + b) = f a + f b) (p q : Polynomial A) :
    mapCoeffs f (p + q) = mapCoeffs f p + mapCoeffs f q := by
  ext m
  rw [coeff_mapCoeffs hf0, Polynomial.coeff_add, Polynomial.coeff_add, coeff_mapCoeffs hf0,
    coeff_mapCoeffs hf0, hadd]

/-- Evaluation at a scalar commutes with pushing a polynomial along an algebra map: an
  algebra map fixes the scalars. -/
lemma eval_algebraMap_mapAlgHom {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (p : Polynomial A) (c : k) :
    (Polynomial.mapAlgHom f p).eval (algebraMap k B c) = f (p.eval (algebraMap k A c)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.eval_add, Polynomial.eval_add, hp, hq, map_add]
  | monomial n a =>
    simp only [Polynomial.mapAlgHom, AlgHom.coe_mk, Polynomial.coe_mapRingHom,
      Polynomial.map_monomial]
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow,
      AlgHom.commutes]
    rfl

/-- Evaluation at a scalar commutes with applying a linear map to the coefficients: the
  powers of the scalar are central, so they pass through the linear map. -/
lemma eval_algebraMap_mapCoeffs {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (f : A →ₗ[k] A) (p : Polynomial A) (c : k) :
    (mapCoeffs f p).eval (algebraMap k A c) = f (p.eval (algebraMap k A c)) := by
  have hsmul : ∀ (m : ℕ) (a : A), a * (algebraMap k A c) ^ m = (c ^ m) • a := fun m a => by
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [mapCoeffs_add (map_zero f) (map_add f), Polynomial.eval_add, Polynomial.eval_add,
      hp, hq, map_add]
  | monomial n a =>
    rw [mapCoeffs_monomial (map_zero f), Polynomial.eval_monomial, Polynomial.eval_monomial,
      hsmul, hsmul, map_smul]

/-- Evaluation at one commutes with pushing a polynomial along an algebra map. -/
lemma eval_one_mapAlgHom {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (p : Polynomial A) :
    (Polynomial.mapAlgHom f p).eval 1 = f (p.eval 1) := by
  have h := eval_algebraMap_mapAlgHom f p 1
  rwa [map_one, map_one] at h

/-- A map satisfying the Leibniz rule satisfies it coefficientwise on polynomials. Applied to
  a total derivative this is the Leibniz rule for the mass-weight polynomial. -/
lemma mapCoeffs_mul_of_leibniz {A : Type*} [Ring A] {D : A → A} (hD0 : D 0 = 0)
    (hDadd : ∀ a b : A, D (a + b) = D a + D b)
    (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) (p q : Polynomial A) :
    mapCoeffs D (p * q) = mapCoeffs D p * q + p * mapCoeffs D q := by
  have hsum : ∀ (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → A),
      D (∑ m ∈ s, g m) = ∑ m ∈ s, D (g m) := by
    intro s g
    induction s using Finset.induction with
    | empty => simpa using hD0
    | insert a s ha ih => rw [Finset.sum_insert ha, hDadd, ih, Finset.sum_insert ha]
  ext n
  rw [coeff_mapCoeffs hD0, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
    Polynomial.coeff_mul, hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hD, coeff_mapCoeffs hD0, coeff_mapCoeffs hD0]

end Polynomial
