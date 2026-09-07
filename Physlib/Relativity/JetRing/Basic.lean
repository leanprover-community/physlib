/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Mathematics.ConjModule
/-!
# The jet ring

The ring `JetRing` of formal power series in the four spacetime coordinates, in
which jets of fields and of gauge transformations at a spacetime point are valued.

This file contains the definition of `JetRing`, its star structure, first-order
coefficient identities, the formal partial derivative, and the truncation of jets.
Results about matrices over `JetRing` are in
`Physlib.Relativity.JetRing.Matrix`.
-/

@[expose] public section
/-!

## A. The Jet ring

-/

/-- The ring of formal power series in the four spacetime coordinates, with complex
  coefficients. Jets of fields and of gauge transformations at a spacetime point are
  valued in this ring. The star operation is coefficientwise complex conjugation, so
  the spacetime coordinates themselves are self-adjoint. -/
abbrev JetRing : Type := MvPowerSeries (Fin 1 ⊕ Fin 3) ℂ

/-!

### A.1. The star structure on the jet ring

The star operation on the jet ring is coefficientwise complex conjugation, fixing
the formal variables. In particular the spacetime coordinates are self-adjoint.

-/

namespace JetRing

open MvPowerSeries

instance : Star JetRing where
  star f := fun n => star (f n)

@[simp]
lemma coeff_star (n : (Fin 1 ⊕ Fin 3) →₀ ℕ) (f : JetRing) :
    coeff n (star f) = star (coeff n f) := rfl

instance : StarRing JetRing where
  star_involutive f := funext fun n => star_star (f n)
  star_add f g := funext fun n => star_add (f n) (g n)
  star_mul f g := by
    have h : ∀ a b : JetRing, star (a * b) = star a * star b := by
      intro a b
      ext n
      classical
      rw [coeff_star, coeff_mul, coeff_mul, star_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [star_mul', coeff_star, coeff_star]
    rw [h, mul_comm]

/-- Real scalars commute with the coefficientwise conjugation. -/
instance : StarModule ℝ JetRing where
  star_smul r f := funext fun n => star_smul r (f n)

/-- Complex scalars conjugate under the coefficientwise conjugation. -/
instance : StarModule ℂ JetRing where
  star_smul c f := funext fun n => star_smul c (f n)

@[simp]
lemma constantCoeff_star (f : JetRing) :
    constantCoeff (star f) = star (constantCoeff f) := rfl

@[simp]
lemma star_C (a : ℂ) :
    star (C a : JetRing) = C (star a) := by
  ext n
  classical
  rw [coeff_star, coeff_C, coeff_C]
  split_ifs <;> simp

/-- **The real structure of the jet ring.** Coefficientwise conjugation is a `ℂ`-linear
equivalence from the conjugate module of the jet ring back to the jet ring itself. It is
honestly `ℂ`-linear, not merely semilinear, because the conjugate-linearity of `star`
cancels against the twisted scalar action of `ConjModule`.

This is what identifies the jets of a conjugate field with the conjugates of the jets:
`ConjModule (JetRing ⊗[ℂ] V)` and `JetRing ⊗[ℂ] ConjModule V` differ exactly by this
equivalence on the jet-ring factor. -/
noncomputable def starConjEquiv : ConjModule JetRing ≃ₗ[ℂ] JetRing :=
  (conjEquiv (k := ℂ) (M := JetRing)).symm.trans (starLinearEquiv ℂ)

@[simp]
lemma starConjEquiv_apply (f : ConjModule JetRing) :
    starConjEquiv f = star ((conjEquiv (k := ℂ) (M := JetRing)).symm f) := rfl

@[simp]
lemma starConjEquiv_symm_apply (f : JetRing) :
    starConjEquiv.symm f = conjEquiv (k := ℂ) (M := JetRing) (star f) := rfl

/-- The first-order Leibniz rule: the degree-one Taylor coefficient, in the
  direction `μ`, of a product of jets. This is the coefficient-level statement
  that the first jet of a product is given by the product rule. -/
lemma coeff_single_one_mul (μ : Fin 1 ⊕ Fin 3) (f g : JetRing) :
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

/-- The first-order power rule: the degree-one Taylor coefficient, in the direction
  `μ`, of a power of a jet. -/
lemma coeff_single_one_pow (μ : Fin 1 ⊕ Fin 3) (f : JetRing) (n : ℕ) :
    coeff (Finsupp.single μ 1) (f ^ n) =
      (n : ℂ) * constantCoeff f ^ (n - 1) * coeff (Finsupp.single μ 1) f := by
  classical
  induction n with
  | zero =>
      simp [coeff_one, Finsupp.single_eq_zero]
  | succ n ih =>
      rw [pow_succ, coeff_single_one_mul, ih, map_pow, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hpow : constantCoeff f ^ (n - 1) * constantCoeff f = constantCoeff f ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        push_cast
        linear_combination ((n : ℂ) * coeff (Finsupp.single μ 1) f) * hpow

/-!

### A.2. The formal partial derivative on the jet ring

-/

/-- The formal partial derivative commutes with the coefficientwise star. -/
lemma pderiv_star (ν : Fin 1 ⊕ Fin 3) (f : JetRing) :
    pderiv ℂ ν (star f) = star (pderiv ℂ ν f) := by
  ext s
  rw [coeff_pderiv, coeff_star, coeff_star, coeff_pderiv, star_mul']
  congr 1
  simp

/-- Formal partial derivatives commute. -/
lemma pderiv_comm (μ ν : Fin 1 ⊕ Fin 3) (f : JetRing) :
    pderiv ℂ μ (pderiv ℂ ν f) = pderiv ℂ ν (pderiv ℂ μ f) := by
  classical
  ext s
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv,
    show s + Finsupp.single μ 1 + Finsupp.single ν 1 =
      s + Finsupp.single ν 1 + Finsupp.single μ 1 from by
      rw [add_assoc, add_assoc, add_comm (Finsupp.single μ 1)]]
  rcases eq_or_ne μ ν with rfl | h
  · rfl
  · rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne h.symm,
      Finsupp.single_eq_of_ne h]
    push_cast
    ring

/-- Application of `pderiv` is right-commutative, since formal partial derivatives
  commute (`JetRing.pderiv_comm`). This allows iterating them over a `Multiset` of
  directions. -/
instance : RightCommutative (fun (f : JetRing) (μ : Fin 1 ⊕ Fin 3) => pderiv ℂ μ f) where
  right_comm f μ ν := JetRing.pderiv_comm ν μ f

/-- Iterated formal derivatives over a multiset commute with a single derivative. -/
lemma foldl_pderiv_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (f : JetRing) :
    s.foldl (fun f ρ => pderiv ℂ ρ f) (pderiv ℂ μ f) =
      pderiv ℂ μ (s.foldl (fun f ρ => pderiv ℂ ρ f) f) := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.foldl_cons, Multiset.foldl_cons, JetRing.pderiv_comm, ih]

/-!

### The all-orders Leibniz rule for iterated derivatives

-/

/-- The iterated formal derivative is additive. -/
lemma foldl_pderiv_add (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : JetRing) :
    s.foldl (fun h ρ => pderiv ℂ ρ h) (f + g)
      = s.foldl (fun h ρ => pderiv ℂ ρ h) f + s.foldl (fun h ρ => pderiv ℂ ρ h) g := by
  induction s using Multiset.induction_on generalizing f g with
  | empty => rfl
  | cons μ t ih => rw [Multiset.foldl_cons, Multiset.foldl_cons, Multiset.foldl_cons,
      map_add, ih]

/-- The iterated formal derivative of the zero jet vanishes. -/
@[simp]
lemma foldl_pderiv_zero (s : Multiset (Fin 1 ⊕ Fin 3)) :
    s.foldl (fun h ρ => pderiv ℂ ρ h) (0 : JetRing) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons μ t ih => rw [Multiset.foldl_cons, map_zero, ih]

/-- The iterated formal derivative of a finite sum. -/
lemma foldl_pderiv_sum {κ : Type*} (s : Multiset (Fin 1 ⊕ Fin 3)) (t : Finset κ)
    (f : κ → JetRing) :
    s.foldl (fun h ρ => pderiv ℂ ρ h) (∑ k ∈ t, f k)
      = ∑ k ∈ t, s.foldl (fun h ρ => pderiv ℂ ρ h) (f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, foldl_pderiv_add, ih,
      Finset.sum_insert ha]

/-- The all-orders Leibniz rule for the iterated formal derivative on the jet ring:
  the derivative of a product distributes over the antidiagonal of the multiset of
  directions. -/
lemma foldl_pderiv_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : JetRing) :
    s.foldl (fun h ρ => pderiv ℂ ρ h) (f * g)
      = (s.antidiagonal.map fun p =>
          p.1.foldl (fun h ρ => pderiv ℂ ρ h) f *
            p.2.foldl (fun h ρ => pderiv ℂ ρ h) g).sum := by
  induction s using Multiset.induction_on generalizing f g with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons μ t ih =>
    rw [Multiset.foldl_cons,
      show pderiv ℂ μ (f * g) = pderiv ℂ μ f * g + f * pderiv ℂ μ g from by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm g],
      foldl_pderiv_add, ih, ih,
      Multiset.map_congr rfl (fun p hp => by
        rw [show p.1.foldl (fun h ρ => pderiv ℂ ρ h) (pderiv ℂ μ f)
            = (μ ::ₘ p.1).foldl (fun h ρ => pderiv ℂ ρ h) f from
          (Multiset.foldl_cons _ _ _ _).symm]),
      show (t.antidiagonal.map fun p =>
          p.1.foldl (fun h ρ => pderiv ℂ ρ h) f *
            p.2.foldl (fun h ρ => pderiv ℂ ρ h) (pderiv ℂ μ g)).sum
        = (t.antidiagonal.map fun p =>
          p.1.foldl (fun h ρ => pderiv ℂ ρ h) f *
            (μ ::ₘ p.2).foldl (fun h ρ => pderiv ℂ ρ h) g).sum from
        congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
          rw [show (μ ::ₘ p.2).foldl (fun h ρ => pderiv ℂ ρ h) g
            = p.2.foldl (fun h ρ => pderiv ℂ ρ h) (pderiv ℂ μ g) from
            Multiset.foldl_cons _ _ _ _])]
    simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
      Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    exact add_comm _ _

/-- The base-point Taylor coefficient of a product: the convolution of the base-point
  Taylor coefficients. -/
lemma constantCoeff_foldl_pderiv_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : JetRing) :
    constantCoeff (s.foldl (fun h ρ => pderiv ℂ ρ h) (f * g))
      = (s.antidiagonal.map fun p =>
          constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h) f) *
            constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) g)).sum := by
  rw [foldl_pderiv_mul, map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => map_mul _ _ _)

/-- The iterated derivative of a constant jet vanishes for a nonempty multiset of
  directions. -/
lemma foldl_pderiv_C_of_ne_zero {s : Multiset (Fin 1 ⊕ Fin 3)} (hs : s ≠ 0) (c : ℂ) :
    s.foldl (fun h ρ => pderiv ℂ ρ h) (C c : JetRing) = 0 := by
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hμ
  rw [Multiset.foldl_cons, pderiv_C, foldl_pderiv_zero]

/-!

### Truncation of jets

-/
/-- The `n`-th truncation of a jet: the Taylor coefficients of total degree
  greater than `n` are set to zero. -/
noncomputable def truncation (n : ℕ) (f : JetRing) : JetRing :=
  fun m => if Finsupp.degree m ≤ n then f m else 0

@[simp]
lemma coeff_truncation_of_le {n : ℕ} {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (h : Finsupp.degree m ≤ n) (f : JetRing) :
    coeff m (truncation n f) = coeff m f := if_pos h

@[simp]
lemma coeff_truncation_of_gt {n : ℕ} {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (h : n < Finsupp.degree m) (f : JetRing) :
    coeff m (truncation n f) = 0 := if_neg (not_le.mpr h)

lemma truncation_add (n : ℕ) (f g : JetRing) :
    truncation n (f + g) = truncation n f + truncation n g := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm, map_add, map_add,
      coeff_truncation_of_le hm, coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), map_add,
      coeff_truncation_of_gt (not_le.mp hm), coeff_truncation_of_gt (not_le.mp hm), add_zero]

lemma truncation_sum {ι : Type} (n : ℕ) (s : Finset ι) (f : ι → JetRing) :
    truncation n (∑ i ∈ s, f i) = ∑ i ∈ s, truncation n (f i) :=
  map_sum (AddMonoidHom.mk' (truncation n) (truncation_add n)) f s

/-- Truncation of a product only sees the factors through their truncations: the
  coefficients of `f * g` in degree at most `n` involve only coefficients of `f`
  and `g` in degree at most `n`. -/
lemma truncation_mul (n : ℕ) (f g : JetRing) :
    truncation n (f * g) = truncation n (truncation n f * truncation n g) := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm, coeff_truncation_of_le hm, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpq : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    have h1 : Finsupp.degree p.1 ≤ n := by
      refine le_trans ?_ hm
      rw [← hpq, map_add]
      exact Nat.le_add_right _ _
    have h2 : Finsupp.degree p.2 ≤ n := by
      refine le_trans ?_ hm
      rw [← hpq, map_add]
      exact Nat.le_add_left _ _
    rw [coeff_truncation_of_le h1, coeff_truncation_of_le h2]
  · rw [coeff_truncation_of_gt (not_le.mp hm), coeff_truncation_of_gt (not_le.mp hm)]

/-- The congruence principle for truncated products. -/
lemma truncation_mul_congr {n : ℕ} {f f' g g' : JetRing}
    (hf : truncation n f = truncation n f') (hg : truncation n g = truncation n g') :
    truncation n (f * g) = truncation n (f' * g') := by
  rw [truncation_mul, hf, hg, ← truncation_mul]

lemma truncation_star (n : ℕ) (f : JetRing) :
    truncation n (star f) = star (truncation n f) := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm, coeff_star, coeff_star, coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), coeff_star,
      coeff_truncation_of_gt (not_le.mp hm), star_zero]
@[simp]
lemma truncation_zero (n : ℕ) : truncation n (0 : JetRing) = 0 := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), map_zero]

/-- Truncation fixes the identity: a constant series has its only nonzero Taylor
  coefficient in degree zero, which every truncation keeps. -/
@[simp]
lemma truncation_one (n : ℕ) : truncation n (1 : JetRing) = 1 := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), coeff_one,
      if_neg (by rintro rfl; simp at hm)]

/-- Two jets have the same zeroth truncation exactly when they have the same
  value at the base point. -/
lemma truncation_zero_eq_iff {f g : JetRing} :
    truncation 0 f = truncation 0 g ↔ constantCoeff f = constantCoeff g := by
  constructor
  · intro h
    simpa using congrArg (coeff (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ)) h
  · intro h
    ext m
    by_cases hm : Finsupp.degree m ≤ 0
    · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (Nat.le_zero.mp hm)
      subst hm0
      simpa using h
    · rw [coeff_truncation_of_gt (not_le.mp hm), coeff_truncation_of_gt (not_le.mp hm)]


/-!

## The Euler operator toolkit

-/

/-- The formal coordinates of the jet ring are self-adjoint. -/
lemma star_X (ρ : Fin 1 ⊕ Fin 3) : star (X ρ : JetRing) = X ρ := by
  ext m
  rw [JetRing.coeff_star, show (X ρ : JetRing) = monomial (Finsupp.single ρ 1) 1 from rfl,
    coeff_monomial]
  split_ifs <;> simp

/-- The Taylor coefficients of a jet multiplied by a formal coordinate: the
  coefficient shifts down by one in that direction. -/
lemma coeff_X_smul (ρ : Fin 1 ⊕ Fin 3) (f : JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p ((X ρ : JetRing) • f) =
      if Finsupp.single ρ 1 ≤ p then coeff (p - Finsupp.single ρ 1) f else 0 := by
  rw [smul_eq_mul, show (X ρ : JetRing) = monomial (Finsupp.single ρ 1) 1 from rfl,
    coeff_monomial_mul]
  split_ifs <;> simp

/-- The Euler (radial) operator acts on Taylor coefficients as multiplication by the
  total degree. -/
lemma coeff_sum_X_smul_pderiv (f : JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p (∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ f) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p f := by
  classical
  rw [map_sum]
  have ht : ∀ ρ, coeff p ((X ρ : JetRing) • pderiv ℂ ρ f) = (p ρ : ℂ) * coeff p f := by
    intro ρ
    rw [coeff_X_smul]
    by_cases h : Finsupp.single ρ 1 ≤ p
    · have hρ : 1 ≤ p ρ := by simpa using Finsupp.single_le_iff.mp h
      rw [if_pos h, coeff_pderiv, tsub_add_cancel_of_le h, Finsupp.coe_tsub, Pi.sub_apply,
        Finsupp.single_eq_same, Nat.cast_sub hρ]
      push_cast
      ring
    · have hρ : p ρ = 0 := by
        by_contra hc
        exact h (Finsupp.single_le_iff.mpr (by omega))
      rw [if_neg h, hρ]
      simp
  rw [Finset.sum_congr rfl fun ρ _ => ht ρ, ← Finset.sum_mul, ← Nat.cast_sum,
    ← Finsupp.degree_eq_sum]

/-- The scalar vanishing principle for the Euler operator: a jet vanishing at the base
  point that is killed by the Euler operator is zero. -/
lemma eq_zero_of_sum_X_smul_pderiv_eq_zero {f : JetRing} (h0 : constantCoeff f = 0)
    (hf : ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ f = 0) : f = 0 := by
  ext p
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [coeff_zero_eq_constantCoeff] using h0
  · have h := congrArg (coeff p) hf
    rw [coeff_sum_X_smul_pderiv, map_zero] at h
    have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
    simpa using (mul_eq_zero.mp h).resolve_left hne

/-!

## Multiset derivative bookkeeping

-/

/-- The base-point value of an iterated formal derivative is the corresponding Taylor
  coefficient with the factorial normalization. -/
lemma constantCoeff_foldl_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    constantCoeff (s.foldl (fun f ρ => pderiv ℂ ρ f) f) =
      ((∏ ν, Nat.factorial (s.count ν) : ℕ) : ℂ) * coeff s.toFinsupp f := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp [coeff_zero_eq_constantCoeff]
  | cons a t ih =>
      rw [Multiset.foldl_cons, ih, coeff_pderiv]
      have hfin : (a ::ₘ t).toFinsupp = t.toFinsupp + Finsupp.single a 1 := by
        rw [show (a ::ₘ t : Multiset (Fin 1 ⊕ Fin 3)) = {a} + t from
          (Multiset.singleton_add a t).symm, map_add, Multiset.toFinsupp_singleton, add_comm]
      have hfac : (∏ ν, Nat.factorial ((a ::ₘ t).count ν) : ℕ) =
          (t.count a + 1) * ∏ ν, Nat.factorial (t.count ν) := by
        rw [show (∏ ν, Nat.factorial ((a ::ₘ t).count ν) : ℕ) =
            ∏ ν, ((if ν = a then t.count a + 1 else 1) * Nat.factorial (t.count ν)) from
          Finset.prod_congr rfl fun ν _ => by
            rcases eq_or_ne ν a with rfl | h
            · rw [Multiset.count_cons_self, Nat.factorial_succ, if_pos rfl]
            · rw [Multiset.count_cons_of_ne h, if_neg h, one_mul],
          Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ a]
        simp
      rw [hfin, hfac, Multiset.toFinsupp_apply]
      push_cast
      ring

/-- The key combinatorial identity behind the symmetrized Maurer–Cartan data: the sum
  over a multiset `r` of base-point values of iterated derivatives of `g` in the
  complementary directions is, up to factorials, the Taylor coefficient at `r` of the
  radial contraction `∑ μ x_μ g_μ`. -/
lemma sum_constantCoeff_foldl_erase (g : (Fin 1 ⊕ Fin 3) → JetRing)
    (r : Multiset (Fin 1 ⊕ Fin 3)) :
    (r.map fun μ => constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f) (g μ))).sum =
      ((∏ ν, Nat.factorial (r.count ν) : ℕ) : ℂ) *
        coeff r.toFinsupp (∑ μ, (X μ : JetRing) • g μ) := by
  classical
  rw [Finset.sum_multiset_map_count,
    Finset.sum_subset (Finset.subset_univ r.toFinset) (fun x _ hx => by
      rw [Multiset.count_eq_zero.mpr fun hmem => hx (Multiset.mem_toFinset.mpr hmem),
        zero_smul]),
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_X_smul, constantCoeff_foldl_pderiv]
  by_cases hμ : μ ∈ r
  · rw [if_pos (Finsupp.single_le_iff.mpr (by
      rw [Multiset.toFinsupp_apply]
      exact Multiset.one_le_count_iff_mem.mpr hμ))]
    have herase : (r.erase μ).toFinsupp = r.toFinsupp - Finsupp.single μ 1 := by
      ext ν
      rw [Multiset.toFinsupp_apply, Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply,
        Finsupp.single_apply]
      rcases eq_or_ne μ ν with rfl | h
      · rw [Multiset.count_erase_self, if_pos rfl]
      · rw [Multiset.count_erase_of_ne h.symm, if_neg h, Nat.sub_zero]
    have hfac : r.count μ * ∏ ν, Nat.factorial ((r.erase μ).count ν) =
        ∏ ν, Nat.factorial (r.count ν) := by
      rw [← Finset.mul_prod_erase Finset.univ
          (fun ν => Nat.factorial ((r.erase μ).count ν)) (Finset.mem_univ μ),
        ← Finset.mul_prod_erase Finset.univ
          (fun ν => Nat.factorial (r.count ν)) (Finset.mem_univ μ),
        Multiset.count_erase_self,
        Finset.prod_congr rfl fun ν hν =>
          congrArg Nat.factorial
            (Multiset.count_erase_of_ne (Finset.mem_erase.mp hν).1 r),
        ← mul_assoc, Nat.mul_factorial_pred (Multiset.count_pos.mpr hμ).ne']
    rw [herase, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hfac]
  · rw [if_neg fun hle => hμ (Multiset.one_le_count_iff_mem.mp (by
        simpa [Multiset.toFinsupp_apply] using Finsupp.single_le_iff.mp hle)),
      mul_zero, Multiset.count_eq_zero.mpr hμ, zero_smul]

lemma degree_toFinsupp_eq_card (r : Multiset (Fin 1 ⊕ Fin 3)) :
    Finsupp.degree (Multiset.toFinsupp r) = Multiset.card r := by
  rw [Finsupp.degree_eq_sum, Finset.sum_congr rfl fun ν _ => Multiset.toFinsupp_apply r ν,
    ← Finset.sum_subset (Finset.subset_univ r.toFinset) (fun x _ hx =>
      Multiset.count_eq_zero.mpr fun hmem => hx (Multiset.mem_toFinset.mpr hmem)),
    Multiset.toFinset_sum_count_eq]

end JetRing
