/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
public import Physlib.Mathematics.Modules.ConjModule
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Star
/-!
# Star, derivatives, truncation and the Euler operator on the jet ring

The further structure the jet ring of spacetime carries, beyond its ring structure.

## i. Overview

`Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic` carries `SpaceTimeAlgebra`, the ring of
formal power series in the spacetime coordinates, which is the ring of jets of a field at a
point. Four further pieces of structure on it are developed here, each needed to state a
Lagrangian as an element of a jet algebra.

The star operation is coefficientwise complex conjugation, fixing the formal variables: the
spacetime coordinates are self-adjoint. It makes the jet ring a `StarRing` and a `StarModule`
over both `ℝ` and `ℂ`, and `starConjEquiv` identifies the conjugate module of the jet ring with
the jet ring itself, honestly `ℂ`-linearly, since the conjugate-linearity of `star` cancels
against the twisted scalar action. That is what identifies the jets of a conjugate field with
the conjugates of the jets.

The formal partial derivative commutes with the star, and the iterated derivative
`iteratedPDeriv` is additive, homogeneous and satisfies a Leibniz rule over the antidiagonal of
the multiset of directions; `constantCoeff_iteratedPDeriv_mul` is the form a component
computation uses.

The truncation `truncation n` sets the Taylor coefficients of total degree above `n` to zero.

Finally the Euler operator `∑ x^ρ ∂_ρ` detects jets: a jet with vanishing constant coefficient
killed by the Euler operator is zero, and `coeff_eq_zero_of_coeff_pderiv_eq_zero` is the graded
form of that statement, where control of the first derivatives below degree `n` controls the
coefficients up to degree `n`.

## ii. Key results

- `SpaceTimeAlgebra.coeff_star`, `SpaceTimeAlgebra.star_X` : the star is coefficientwise, and
  the coordinates are self-adjoint.
- `SpaceTimeAlgebra.starConjEquiv` : the conjugate module of the jet ring is the jet ring.
- `SpaceTimeAlgebra.pderiv_star`, `SpaceTimeAlgebra.iteratedPDeriv_mul` : the derivative
  commutes with the star, and the Leibniz rule for iterated derivatives.
- `SpaceTimeAlgebra.truncation` : the truncation of a jet.
- `SpaceTimeAlgebra.eq_zero_of_sum_X_smul_pderiv_eq_zero` : the Euler operator detects jets.
- `SpaceTimeAlgebra.coeff_eq_zero_of_coeff_pderiv_eq_zero` : its graded form.

## iii. Table of contents

- A. The star structure on the jet ring
- B. The formal partial derivative
- C. Truncation of jets
- D. The Euler operator
  - D.1. The Euler vanishing principle by degree

## iv. References

The jet ring itself is in `Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic`.

-/

@[expose] public section

namespace SpaceTimeAlgebra

/-!

## A. The star structure on the jet ring

The star operation on the jet ring is coefficientwise complex conjugation, fixing
the formal variables. In particular the spacetime coordinates are self-adjoint.

-/

open MvPowerSeries

/-- **The real structure of the jet ring.** Coefficientwise conjugation is a `ℂ`-linear
equivalence from the conjugate module of the jet ring back to the jet ring itself. It is
honestly `ℂ`-linear, not merely semilinear, because the conjugate-linearity of `star`
cancels against the twisted scalar action of `ConjModule`.

This is what identifies the jets of a conjugate field with the conjugates of the jets:
`ConjModule (SpaceTimeAlgebra ⊗[ℂ] V)` and `SpaceTimeAlgebra ⊗[ℂ] ConjModule V` differ
exactly by this equivalence on the jet-ring factor. -/
noncomputable def starConjEquiv : ConjModule SpaceTimeAlgebra ≃ₗ[ℂ] SpaceTimeAlgebra :=
  (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra)).symm.trans (starLinearEquiv ℂ)

@[simp]
lemma starConjEquiv_apply (f : ConjModule SpaceTimeAlgebra) :
    starConjEquiv f = star ((conjEquiv (k := ℂ) (M := SpaceTimeAlgebra)).symm f) := rfl

@[simp]
lemma starConjEquiv_symm_apply (f : SpaceTimeAlgebra) :
    starConjEquiv.symm f = conjEquiv (k := ℂ) (M := SpaceTimeAlgebra) (star f) := rfl


/-- The first-order Leibniz rule: the degree-one Taylor coefficient, in the
  direction `μ`, of a product of jets. This is the coefficient-level statement
  that the first jet of a product is given by the product rule. -/
lemma coeff_single_one_mul (μ : Fin 1 ⊕ Fin 3) (f g : SpaceTimeAlgebra) :
    coeff (Finsupp.single μ 1) (f * g) =
      coeff (Finsupp.single μ 1) f * constantCoeff g +
        constantCoeff f * coeff (Finsupp.single μ 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single,
    show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} by decide, Finset.map_insert,
    Finset.map_singleton, Finset.sum_insert (by simp [Finsupp.single_eq_zero]),
    Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff]
  ring

/-- The constant-coefficient evaluation of a jet, as a `ℂ`-linear map. -/
noncomputable def constantCoeffₗ : SpaceTimeAlgebra →ₗ[ℂ] ℂ where
  toFun := constantCoeff
  map_add' f g := by simp
  map_smul' c f := by simp [smul_eq_C_mul]

@[simp]
lemma constantCoeffₗ_apply (f : SpaceTimeAlgebra) : constantCoeffₗ f = constantCoeff f := rfl

/-!

## B. The formal partial derivative

-/

/-- Iterated formal derivatives commute with a single formal partial derivative. -/
lemma iteratedPDeriv_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (pderiv μ f) = pderiv μ (iteratedPDeriv s f) := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp
  | cons ν s ih =>
      rw [iteratedPDeriv_cons, iteratedPDeriv_cons, pderiv_comm, ih]


/-- Iterated formal derivatives preserve complex scalar multiplication. -/
lemma iteratedPDeriv_smul (s : Multiset (Fin 1 ⊕ Fin 3)) (c : ℂ)
    (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (c • f) = c • iteratedPDeriv s f := by
  induction s using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons μ s ih => rw [iteratedPDeriv_cons, iteratedPDeriv_cons, Derivation.map_smul, ih]

/-- Iterated formal derivatives commute with negation. -/
lemma iteratedPDeriv_neg (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (-f) = -iteratedPDeriv s f := by
  induction s using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons μ s ih => rw [iteratedPDeriv_cons, iteratedPDeriv_cons, map_neg, ih]

/-- The iterated formal derivative of the zero jet vanishes. -/
@[simp]
lemma iteratedPDeriv_zero_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedPDeriv s (0 : SpaceTimeAlgebra) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons μ t ih => rw [iteratedPDeriv_cons, map_zero, ih]

/-- The iterated formal derivative of a finite sum. -/
lemma iteratedPDeriv_sum {κ : Type*} (s : Multiset (Fin 1 ⊕ Fin 3)) (t : Finset κ)
    (f : κ → SpaceTimeAlgebra) :
    iteratedPDeriv s (∑ k ∈ t, f k)
      = ∑ k ∈ t, iteratedPDeriv s (f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, iteratedPDeriv_add, ih,
      Finset.sum_insert ha]

/-- The iterated derivative of a constant jet vanishes for a nonempty multiset of
  directions. -/
lemma iteratedPDeriv_C_of_ne_zero {s : Multiset (Fin 1 ⊕ Fin 3)} (hs : s ≠ 0) (c : ℂ) :
    iteratedPDeriv s (C c : SpaceTimeAlgebra) = 0 := by
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hμ
  rw [iteratedPDeriv_cons, pderiv_C, iteratedPDeriv_zero_apply]

/-!

## C. Truncation of jets

-/
/-- The `n`-th truncation of a jet: the Taylor coefficients of total degree
  greater than `n` are set to zero. -/
noncomputable def truncation (n : ℕ) (f : SpaceTimeAlgebra) : SpaceTimeAlgebra :=
  fun m => if Finsupp.degree m ≤ n then f m else 0

@[simp]
lemma coeff_truncation_of_le {n : ℕ} {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (h : Finsupp.degree m ≤ n) (f : SpaceTimeAlgebra) :
    coeff m (truncation n f) = coeff m f := ite_eq_left h

@[simp]
lemma coeff_truncation_of_gt {n : ℕ} {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (h : n < Finsupp.degree m) (f : SpaceTimeAlgebra) :
    coeff m (truncation n f) = 0 := ite_eq_right (not_le.mpr h)

lemma truncation_add (n : ℕ) (f g : SpaceTimeAlgebra) :
    truncation n (f + g) = truncation n f + truncation n g := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm, map_add, map_add,
      coeff_truncation_of_le hm, coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), map_add,
      coeff_truncation_of_gt (not_le.mp hm), coeff_truncation_of_gt (not_le.mp hm), add_zero]

@[simp]
lemma truncation_zero (n : ℕ) : truncation n (0 : SpaceTimeAlgebra) = 0 := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), map_zero]

/-- Truncation fixes the identity: a constant series has its only nonzero Taylor
  coefficient in degree zero, which every truncation keeps. -/
@[simp]
lemma truncation_one (n : ℕ) : truncation n (1 : SpaceTimeAlgebra) = 1 := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), coeff_one,
      ite_eq_right (by rintro rfl; simp at hm)]

/-- A power series with value `1` and no coefficients in nonzero degree up to `n`
  truncates to `1`. -/
lemma truncation_eq_one_of_coeff {n : ℕ} {f : SpaceTimeAlgebra} (h0 : constantCoeff f = 1)
    (hf : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ, p ≠ 0 → Finsupp.degree p ≤ n → coeff p f = 0) :
    SpaceTimeAlgebra.truncation n f = SpaceTimeAlgebra.truncation n (1 : SpaceTimeAlgebra) := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [SpaceTimeAlgebra.coeff_truncation_of_le hm, SpaceTimeAlgebra.coeff_truncation_of_le hm]
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa [coeff_zero_eq_constantCoeff] using h0
    · rw [hf m hm0 hm, coeff_one, ite_eq_right hm0]
  · rw [SpaceTimeAlgebra.coeff_truncation_of_gt (not_le.mp hm),
      SpaceTimeAlgebra.coeff_truncation_of_gt (not_le.mp hm)]

/-!

## D. The Euler operator

-/

/-- The Taylor coefficients of a jet multiplied by a formal coordinate: the
  coefficient shifts down by one in that direction. -/
lemma coeff_X_smul (ρ : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p ((X ρ : SpaceTimeAlgebra) • f) =
      if Finsupp.single ρ 1 ≤ p then coeff (p - Finsupp.single ρ 1) f else 0 := by
  rw [smul_eq_mul, show (X ρ : SpaceTimeAlgebra) = monomial (Finsupp.single ρ 1) 1 from rfl,
    coeff_monomial_mul]
  split_ifs <;> simp

/-- The Euler (radial) operator acts on Taylor coefficients as multiplication by the
  total degree. -/
lemma coeff_sum_X_smul_pderiv (f : SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p (∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ f) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p f := by
  classical
  rw [map_sum]
  have ht : ∀ ρ, coeff p ((X ρ : SpaceTimeAlgebra) • pderiv ρ f) = (p ρ : ℂ) * coeff p f := by
    intro ρ
    rw [coeff_X_smul]
    by_cases h : Finsupp.single ρ 1 ≤ p
    · have hρ : 1 ≤ p ρ := by simpa using Finsupp.single_le_iff.mp h
      rw [ite_eq_left h, coeff_pderiv, tsub_add_cancel_of_le h, Finsupp.coe_tsub, Pi.sub_apply,
        Finsupp.single_eq_same, Nat.cast_sub hρ]
      push_cast
      ring
    · have hρ : p ρ = 0 := by
        by_contra hc
        exact h (Finsupp.single_le_iff.mpr (by omega))
      rw [ite_eq_right h, hρ]
      simp
  rw [Finset.sum_congr rfl fun ρ _ => ht ρ, ← Finset.sum_mul, ← Nat.cast_sum,
    ← Finsupp.degree_eq_sum]

/-- The scalar vanishing principle for the Euler operator: a jet vanishing at the base
  point that is killed by the Euler operator is zero. -/
lemma eq_zero_of_sum_X_smul_pderiv_eq_zero {f : SpaceTimeAlgebra} (h0 : constantCoeff f = 0)
    (hf : ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ f = 0) : f = 0 := by
  ext p
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [coeff_zero_eq_constantCoeff] using h0
  · have h := congrArg (coeff p) hf
    rw [coeff_sum_X_smul_pderiv, map_zero] at h
    have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
    simpa using (mul_eq_zero.mp h).resolve_left hne

/-!

### D.1. The Euler vanishing principle by degree

The graded form of `eq_zero_of_sum_X_smul_pderiv_eq_zero`: control of the first
derivatives below degree `n` controls the coefficients up to degree `n`.

-/

/-- A product with a factor whose coefficients vanish below degree `n` has coefficients
  vanishing below degree `n`. -/
lemma coeff_mul_eq_zero_of_lt {n : ℕ} {w : SpaceTimeAlgebra}
    (hw : ∀ q : (Fin 1 ⊕ Fin 3) →₀ ℕ, Finsupp.degree q < n → coeff q w = 0) (v : SpaceTimeAlgebra)
    {q : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hq : Finsupp.degree q < n) : coeff q (w * v) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpq : p.1 + p.2 = q := Finset.mem_antidiagonal.mp hp
  have hdeg : Finsupp.degree p.1 ≤ Finsupp.degree q := by
    rw [← hpq, map_add]
    exact Nat.le_add_right _ _
  rw [hw p.1 (lt_of_le_of_lt hdeg hq), zero_mul]

/-- The Euler vanishing principle: a power series all of whose first derivatives have
  coefficients vanishing below degree `n` has vanishing coefficients in every nonzero degree
  up to `n`, since `∑_ρ x_ρ ∂_ρ f` has the coefficient of `f` at `p` scaled by the degree
  of `p`. -/
lemma coeff_eq_zero_of_coeff_pderiv_eq_zero {n : ℕ} {f : SpaceTimeAlgebra}
    (hf : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      coeff q (pderiv ρ f) = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) : coeff p f = 0 := by
  have h1 := SpaceTimeAlgebra.coeff_sum_X_smul_pderiv f p
  have h2 : coeff p (∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ f) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [SpaceTimeAlgebra.coeff_X_smul]
    split_ifs with hle
    · refine hf ρ _ ?_
      have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.degree_single] at hd
      omega
    · rfl
  rw [h2] at h1
  have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
  exact (mul_eq_zero.mp h1.symm).resolve_left hne

/-- A power series satisfying a radial relation `∂_ρ f = x_ρ f`, with the `x_ρ` vanishing
  below degree `n`, has no coefficients in nonzero degree up to `n`. -/
lemma coeff_eq_zero_of_pderiv_eq_mul {n : ℕ} {f : SpaceTimeAlgebra}
    {x : (Fin 1 ⊕ Fin 3) → SpaceTimeAlgebra}
    (hd : ∀ ρ, pderiv ρ f = x ρ * f)
    (hx : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      coeff q (x ρ) = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) : coeff p f = 0 :=
  coeff_eq_zero_of_coeff_pderiv_eq_zero
    (fun ρ q hq => by rw [hd ρ]; exact coeff_mul_eq_zero_of_lt (hx ρ) f hq) hp hpn

lemma C_real_smul (r : ℝ) (x : ℂ) :
    (MvPowerSeries.C (r • x) : SpaceTimeAlgebra) = r • MvPowerSeries.C x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply]

/-- The constant coefficient commutes with real scalars. -/
lemma constantCoeff_real_smul (r : ℝ) (f : SpaceTimeAlgebra) :
    MvPowerSeries.constantCoeff (r • f) = r • MvPowerSeries.constantCoeff f := by
  rw [← algebraMap_smul ℂ r, MvPowerSeries.constantCoeff_smul, algebraMap_smul]

/-- The formal derivatives commute with real scalars. -/
lemma pderiv_real_smul (μ : Fin 1 ⊕ Fin 3) (r : ℝ) (f : SpaceTimeAlgebra) :
    MvPowerSeries.pderiv μ (r • f) = r • MvPowerSeries.pderiv μ f := by
  rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]


end SpaceTimeAlgebra
