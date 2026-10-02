/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.Star.Unitary
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric

/-!

# The candidate generator of a unitary group

## i. Overview

For a strongly continuous one-parameter unitary group `U`, the candidate generator is defined on the
vectors whose orbit `t ↦ U t ψ` is differentiable at `0`, and sends such a vector to `-i` times the
derivative. It is a symmetric operator.

## ii. Key results

- `stoneCandidateDomain` : the vectors whose orbit is differentiable at `0`.
- `stoneCandidateGenerator` : the candidate generator.
- `stoneCandidateGenerator_isSymmetric` : the candidate generator is symmetric.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hU0 : U 0 = 1) (hUmul : ∀ s t, U (s + t) = U s * U t)
  (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))

/-- A vector is in the domain of the candidate generator when its orbit is differentiable at `0`. -/
def stoneCandidateDomainPred (ψ : H) : Prop := ∃ φ : H, HasDerivAt (fun t : ℝ => U t ψ) φ 0

omit [CompleteSpace H] in
/-- The candidate domain is closed under addition. The group law is an argument so that the
domain is attached to a unitary group. -/
lemma stoneCandidateDomainPred_add (_hUmul : ∀ s t, U (s + t) = U s * U t) {ψ₁ ψ₂ : H}
    (h₁ : stoneCandidateDomainPred (U := U) ψ₁) (h₂ : stoneCandidateDomainPred (U := U) ψ₂) :
    stoneCandidateDomainPred (U := U) (ψ₁ + ψ₂) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  refine ⟨φ₁ + φ₂, ?_⟩
  have hsum : HasDerivAt (fun t : ℝ => U t ψ₁ + U t ψ₂) (φ₁ + φ₂) 0 := hφ₁.add hφ₂
  simpa [map_add] using hsum

omit [CompleteSpace H] in
/-- The candidate domain is closed under scalar multiplication, by the same linearity argument. -/
lemma stoneCandidateDomainPred_smul {ψ : H} (c : ℂ)
    (h : stoneCandidateDomainPred (U := U) ψ) :
    stoneCandidateDomainPred (U := U) (c • ψ) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨c • φ, ?_⟩
  have hsmul : HasDerivAt (fun t : ℝ => c • U t ψ) (c • φ) 0 := hφ.const_smul c
  simpa [map_smul] using hsmul

omit [CompleteSpace H] in
lemma stoneCandidateDomainPred_zero : stoneCandidateDomainPred (U := U) (0 : H) :=
  ⟨0, by simpa using (hasDerivAt_const (0 : ℝ) (0 : H))⟩

variable (U) in
/-- The domain of the candidate generator of the unitary group `U`, as a submodule. -/
def stoneCandidateDomain : Submodule ℂ H where
  carrier := {ψ | stoneCandidateDomainPred (U := U) ψ}
  zero_mem' := stoneCandidateDomainPred_zero
  add_mem' h₁ h₂ := stoneCandidateDomainPred_add hUmul h₁ h₂
  smul_mem' c _ h := stoneCandidateDomainPred_smul c h

/-- The derivative witness for a vector in the candidate domain, chosen once and for all via
choice; `-Complex.I` times this is the candidate generator's action. -/
def stoneCandidateDeriv (ψ : stoneCandidateDomain (U := U) hUmul) : H :=
  ψ.property.choose

omit [CompleteSpace H] in
lemma stoneCandidateDeriv_spec (ψ : stoneCandidateDomain (U := U) hUmul) :
    HasDerivAt (fun t : ℝ => U t (ψ : H)) (stoneCandidateDeriv hUmul ψ) 0 :=
  ψ.property.choose_spec

omit [CompleteSpace H] in
lemma stoneCandidateDeriv_add (ψ₁ ψ₂ : stoneCandidateDomain (U := U) hUmul) :
    stoneCandidateDeriv hUmul (ψ₁ + ψ₂) =
      stoneCandidateDeriv hUmul ψ₁ + stoneCandidateDeriv hUmul ψ₂ := by
  apply HasDerivAt.unique (stoneCandidateDeriv_spec hUmul (ψ₁ + ψ₂))
  have hsum : HasDerivAt (fun t : ℝ => U t (ψ₁ : H) + U t (ψ₂ : H))
      (stoneCandidateDeriv hUmul ψ₁ + stoneCandidateDeriv hUmul ψ₂) 0 :=
    (stoneCandidateDeriv_spec hUmul ψ₁).add (stoneCandidateDeriv_spec hUmul ψ₂)
  have hco : ((ψ₁ + ψ₂ : stoneCandidateDomain (U := U) hUmul) : H) = (ψ₁ : H) + (ψ₂ : H) := rfl
  simpa [hco, map_add] using hsum

omit [CompleteSpace H] in
lemma stoneCandidateDeriv_smul (c : ℂ) (ψ : stoneCandidateDomain (U := U) hUmul) :
    stoneCandidateDeriv hUmul (c • ψ) = c • stoneCandidateDeriv hUmul ψ := by
  apply HasDerivAt.unique (stoneCandidateDeriv_spec hUmul (c • ψ))
  have hsmul : HasDerivAt (fun t : ℝ => c • U t (ψ : H)) (c • stoneCandidateDeriv hUmul ψ) 0 :=
    (stoneCandidateDeriv_spec hUmul ψ).const_smul c
  have hco : ((c • ψ : stoneCandidateDomain (U := U) hUmul) : H) = c • (ψ : H) := rfl
  simpa [hco, map_smul] using hsmul

/-- The candidate generator as a linear map on its domain. -/
def stoneCandidateLinearMap :
    stoneCandidateDomain (U := U) hUmul →ₗ[ℂ] H where
  toFun ψ := (-Complex.I) • stoneCandidateDeriv hUmul ψ
  map_add' ψ₁ ψ₂ := by rw [stoneCandidateDeriv_add, smul_add]
  map_smul' c ψ := by
    simp only [RingHom.id_apply, stoneCandidateDeriv_smul, smul_comm (-Complex.I) c]

/-- The candidate Stone generator: a `LinearPMap` whose domain is exactly the vectors along which
`U`'s orbit is differentiable at `0`, sending such a vector to `-i` times that derivative. -/
def stoneCandidateGenerator : H →ₗ.[ℂ] H where
  domain := stoneCandidateDomain (U := U) hUmul
  toFun := stoneCandidateLinearMap hUmul

omit [CompleteSpace H] in
lemma stoneCandidateGenerator_apply (ψ : (stoneCandidateGenerator (U := U) hUmul).domain) :
    stoneCandidateGenerator (U := U) hUmul ψ = (-Complex.I) • stoneCandidateDeriv hUmul ψ := rfl

include hU0 hUunit in
/-- **The candidate generator is symmetric.** The inner product `⟪U t ψ₁, U t ψ₂⟫` is constant in
`t`; differentiating at `0` gives the symmetry. -/
lemma stoneCandidateGenerator_isSymmetric :
    (stoneCandidateGenerator (U := U) hUmul).IsSymmetric := by
  intro ψ₁ ψ₂
  set φ₁ := stoneCandidateDeriv hUmul ψ₁
  set φ₂ := stoneCandidateDeriv hUmul ψ₂
  have hconst : ∀ t : ℝ, ⟪U t (ψ₁ : H), U t (ψ₂ : H)⟫_ℂ = ⟪(ψ₁ : H), (ψ₂ : H)⟫_ℂ := by
    intro t
    exact ContinuousLinearMap.inner_map_map_of_mem_unitary (hUunit t) (ψ₁ : H) (ψ₂ : H)
  have hderiv0 : HasDerivAt (fun t : ℝ => ⟪U t (ψ₁ : H), U t (ψ₂ : H)⟫_ℂ)
      (⟪φ₁, (ψ₂ : H)⟫_ℂ + ⟪(ψ₁ : H), φ₂⟫_ℂ) 0 := by
    have hraw := (stoneCandidateDeriv_spec hUmul ψ₁).inner ℂ (stoneCandidateDeriv_spec hUmul ψ₂)
    simp only [hU0, one_apply_eq_self] at hraw
    rw [add_comm] at hraw
    exact hraw
  have hconstfun : HasDerivAt (fun t : ℝ => ⟪U t (ψ₁ : H), U t (ψ₂ : H)⟫_ℂ) 0 0 := by
    have hfun : (fun t : ℝ => ⟪U t (ψ₁ : H), U t (ψ₂ : H)⟫_ℂ) =
        fun _ : ℝ => ⟪(ψ₁ : H), (ψ₂ : H)⟫_ℂ := funext hconst
    rw [hfun]
    exact hasDerivAt_const 0 _
  have hzero : ⟪φ₁, (ψ₂ : H)⟫_ℂ + ⟪(ψ₁ : H), φ₂⟫_ℂ = 0 := hderiv0.unique hconstfun
  show ⟪(-Complex.I) • φ₁, (ψ₂ : H)⟫_ℂ = ⟪(ψ₁ : H), (-Complex.I) • φ₂⟫_ℂ
  rw [inner_smul_left, inner_smul_right]
  have hconjI : (starRingEnd ℂ) (-Complex.I) = Complex.I := by simp
  rw [hconjI]
  linear_combination Complex.I * hzero

end
end QuantumMechanics

end ProbabilisticTheory
