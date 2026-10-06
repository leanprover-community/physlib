/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Physlib.ProbabilisticTheory.Effect.Sharp
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Algebra.Module.Torsion.Free

/-!

# Projections are sharp

An idempotent effect of a C⋆-algebra is not a proper mixture of two different effects.

## i. Overview

A projection `p` is a sharp effect: it is not a proper mixture of two different effects. If `p = t
y₁ + s y₂`, conjugating by `1 - p` kills both `y₁` and `y₂`, so by the C⋆-identity both commute with
`p` and lie below it, which forces `y₁ = y₂ = p`.

## ii. Key results

- `IsIdempotentElem.isSharp` : idempotent effects are sharp.
- `ProbabilisticTheory.eq_of_mem_openSegment_of_isIdempotentElem` : the algebraic heart of the
  proof, stated on bare elements.

## iii. Table of contents

- A. Consequences of the C⋆-identity
- B. Projections are sharp

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-!

## A. Consequences of the C⋆-identity

-/

/-- In a partially ordered additive group, two nonnegative terms summing to zero vanish. -/
lemma nonneg_add_eq_zero {x y : A} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 0) :
    x = 0 := by
  apply le_antisymm
  · rw [← hxy]
    exact le_add_of_nonneg_right hy
  · exact hx

/-- If `b * x * b = 0` for `b` self-adjoint and `x ≥ 0`, then `√x * b = 0`: the C⋆-identity
`‖z⋆z‖ = ‖z‖²`, applied to `z := √x * b`, since `z⋆z = b * √x * √x * b = b * x * b`. -/
lemma sandwich_eq_zero {b x : A} (hb : IsSelfAdjoint b) (hx : 0 ≤ x)
    (h : b * x * b = 0) : CFC.sqrt x * b = 0 := by
  refine (CStarRing.star_mul_self_eq_zero_iff (CFC.sqrt x * b)).mp ?_
  have hstar : star (CFC.sqrt x * b) = b * CFC.sqrt x := by
    rw [star_mul, hb.star_eq, (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq]
  rw [hstar]
  calc b * CFC.sqrt x * (CFC.sqrt x * b) = b * (CFC.sqrt x * CFC.sqrt x) * b := by noncomm_ring
    _ = b * x * b := by rw [CFC.sqrt_mul_sqrt_self x hx]
    _ = 0 := h

/-- The algebraic heart of `IsIdempotentElem.isSharp`, stated on bare elements of `A`: an
idempotent `a` between `0` and `1` cannot be written as a nontrivial mixture of two different
effects. -/
lemma eq_of_mem_openSegment_of_isIdempotentElem {a y₁ y₂ : A} (ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (hidem : a * a = a) (hy₁0 : 0 ≤ y₁) (hy₁1 : y₁ ≤ 1) (hy₂0 : 0 ≤ y₂) (hy₂1 : y₂ ≤ 1)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hts : t + s = 1) (heq : t • y₁ + s • y₂ = a) :
    y₁ = a := by
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  have hone : IsSelfAdjoint (1 : A) := IsSelfAdjoint.one A
  have hb : IsSelfAdjoint (1 - a) := hone.sub ha
  have hy₁ : IsSelfAdjoint y₁ := IsSelfAdjoint.of_nonneg hy₁0
  have hy₂ : IsSelfAdjoint y₂ := IsSelfAdjoint.of_nonneg hy₂0
  -- Conjugating the mixture by `1 - a` kills it, since `(1 - a) * a = 0`.
  have hba : (1 - a) * a * (1 - a) = 0 := by
    have : (1 - a) * a = 0 := by rw [sub_mul, one_mul, hidem, sub_self]
    rw [this, zero_mul]
  have hsplit : t • ((1 - a) * y₁ * (1 - a)) + s • ((1 - a) * y₂ * (1 - a)) = 0 := by
    have heq2 : (1 - a) * (t • y₁ + s • y₂) * (1 - a) = (1 - a) * a * (1 - a) := by rw [heq]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc] at heq2
    rwa [hba] at heq2
  -- Both conjugated terms are nonnegative, so each vanishes.
  have hb1 : 0 ≤ (1 - a) * y₁ * (1 - a) := hb.conjugate_nonneg hy₁0
  have hb2 : 0 ≤ (1 - a) * y₂ * (1 - a) := hb.conjugate_nonneg hy₂0
  have hz1 : t • ((1 - a) * y₁ * (1 - a)) = 0 :=
    nonneg_add_eq_zero (smul_nonneg ht.le hb1) (smul_nonneg hs.le hb2) hsplit
  have h1 : (1 - a) * y₁ * (1 - a) = 0 :=
    (smul_eq_zero.mp hz1).resolve_left ht.ne'
  -- Hence `y₁` commutes with `1 - a`, i.e. with `a`, and is fixed by conjugating with `a`.
  have hsq := sandwich_eq_zero hb hy₁0 h1
  have hcomm1 : y₁ * (1 - a) = 0 := by
    have : CFC.sqrt y₁ * (CFC.sqrt y₁ * (1 - a)) = CFC.sqrt y₁ * 0 := by rw [hsq]
    rwa [← mul_assoc, CFC.sqrt_mul_sqrt_self y₁ hy₁0, mul_zero] at this
  have hcomm2 : (1 - a) * y₁ = 0 := by
    have := congrArg star hcomm1
    rwa [star_mul, hb.star_eq, hy₁.star_eq, star_zero] at this
  have hay₁ : a * y₁ = y₁ := by
    have := hcomm2
    rw [sub_mul, one_mul, sub_eq_zero] at this
    exact this.symm
  have hy₁a : y₁ * a = y₁ := by
    have := hcomm1
    rw [mul_sub, mul_one, sub_eq_zero] at this
    exact this.symm
  have hfix : a * y₁ * a = y₁ := by rw [hay₁, hy₁a]
  -- `y₁ ≤ 1` conjugated by `a` gives `y₁ ≤ a`; the same argument gives `y₂ ≤ a`.
  have hle1 : y₁ ≤ a := by
    have := ha.conjugate_le_conjugate hy₁1
    rwa [mul_one, hidem, hfix] at this
  have hz2 : s • ((1 - a) * y₂ * (1 - a)) = 0 :=
    nonneg_add_eq_zero (smul_nonneg hs.le hb2) (smul_nonneg ht.le hb1)
      (by rwa [add_comm] at hsplit)
  have h2 : (1 - a) * y₂ * (1 - a) = 0 :=
    (smul_eq_zero.mp hz2).resolve_left hs.ne'
  have hsq2 := sandwich_eq_zero hb hy₂0 h2
  have hcomm1' : y₂ * (1 - a) = 0 := by
    have : CFC.sqrt y₂ * (CFC.sqrt y₂ * (1 - a)) = CFC.sqrt y₂ * 0 := by rw [hsq2]
    rwa [← mul_assoc, CFC.sqrt_mul_sqrt_self y₂ hy₂0, mul_zero] at this
  have hcomm2' : (1 - a) * y₂ = 0 := by
    have := congrArg star hcomm1'
    rwa [star_mul, hb.star_eq, hy₂.star_eq, star_zero] at this
  have hay₂ : a * y₂ = y₂ := by
    have := hcomm2'; rw [sub_mul, one_mul, sub_eq_zero] at this; exact this.symm
  have hy₂a : y₂ * a = y₂ := by
    have := hcomm1'; rw [mul_sub, mul_one, sub_eq_zero] at this; exact this.symm
  have hfix2 : a * y₂ * a = y₂ := by rw [hay₂, hy₂a]
  have hle2 : y₂ ≤ a := by
    have := ha.conjugate_le_conjugate hy₂1
    rwa [mul_one, hidem, hfix2] at this
  -- Averaging `a - y₁ ≥ 0` and `a - y₂ ≥ 0` back against `a = t • y₁ + s • y₂` forces both to `0`.
  have hfin : t • (a - y₁) + s • (a - y₂) = 0 := by
    have h1 : t • a + s • a = a := by rw [← add_smul, hts, one_smul]
    rw [smul_sub, smul_sub, show t • a - t • y₁ + (s • a - s • y₂) =
      (t • a + s • a) - (t • y₁ + s • y₂) from by abel, h1, heq, sub_self]
  have hz3 : t • (a - y₁) = 0 := nonneg_add_eq_zero (smul_nonneg ht.le (sub_nonneg.mpr hle1))
    (smul_nonneg hs.le (sub_nonneg.mpr hle2)) hfin
  have h3 : a - y₁ = 0 := (smul_eq_zero.mp hz3).resolve_left ht.ne'
  exact (sub_eq_zero.mp h3).symm

/-!

## B. Projections are sharp

-/

/-- **Projections are sharp**: an idempotent effect is not a proper mixture of two different
effects. -/
lemma _root_.IsIdempotentElem.isSharp {e : Effect (selfAdjoint A)}
    (h : IsIdempotentElem ((e : selfAdjoint A) : A)) : Effect.IsSharp e := by
  refine ⟨e.2, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩
  obtain ⟨t, s, ht, hs, hts, hz⟩ := hseg
  apply Subtype.ext
  have heq : t • (x₁ : A) + s • (x₂ : A) = ((e : selfAdjoint A) : A) := by
    have hz' := congrArg Subtype.val hz
    simpa using hz'
  exact eq_of_mem_openSegment_of_isIdempotentElem e.2.1 e.2.2 h hx₁.1 hx₁.2 hx₂.1 hx₂.2 ht hs hts
    heq

end ProbabilisticTheory
