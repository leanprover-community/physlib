/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Physlib.Mathematics.Projection.Compress

/-!
# Effective quantum Zeno dynamics
Effective dynamics on the range of a fixed orthogonal projection.

## i. Overview

For a fixed orthogonal projection `P` and a self-adjoint Hamiltonian `H`, the effective
Hamiltonian is `Projection.compress P H`. Its exponential evolution on the measured subspace
extends to the ambient space by acting as zero on the orthogonal complement.

## ii. Key results

- `effective_add` gives the composition law for the projected evolution.
- `finite_dimensional_effective_dynamics` shows that the evolution is unitary on the
  measured subspace and satisfies the Schrödinger equation with the compressed Hamiltonian.

## iii. Table of contents

- A. Projected exponential flow
- B. Adjoint and differential equation
- C. Finite-dimensional effective dynamics

## iv. References

* Burgarth et al., *Quantum Zeno Dynamics from General Quantum Operations*,
  Quantum 4, 289 (2020). Section 2(i) and Corollary 2 give background on Zeno dynamics
  under frequent projective measurements. [ref: Burgarth2020quantumzenodynamics]
-/

@[expose] public section

noncomputable section
namespace QuantumZenoDynamics

open Projection

/-!
## A. Projected exponential flow
-/

section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The exponential flow of a bounded generator at real time `t`. -/
def flow (a : A) (t : ℝ) : A := NormedSpace.exp ((t : ℂ) • a)

/-- The compressed evolution acts on the measured subspace and vanishes on its complement. -/
def effective (P a : A) (t : ℝ) : A := flow (compress P a) t * P

/-- The Schrödinger generator of a Hamiltonian `H` with reduced Planck constant `hbar`. -/
def generator (H : A) (hbar : ℝ) : A := (-Complex.I / (hbar : ℂ)) • H

omit [CompleteSpace A] in
@[simp] lemma flow_zero (a : A) : flow a 0 = 1 := by
  simp [flow]

omit [CompleteSpace A] in
lemma commute_flow_compress (P a : A) (hP : IsIdempotentElem P) (t : ℝ) :
    Commute P (flow (compress P a) t) := by
  have h : Commute P (compress P a) := (hP.mul_compress a).trans (hP.compress_mul a).symm
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  exact (h.smul_right (t : ℂ)).exp_right

omit [CompleteSpace A] in
lemma effective_left (P a : A) (hP : IsIdempotentElem P) (t : ℝ) :
    P * effective P a t = effective P a t := by
  unfold effective
  rw [← mul_assoc, (commute_flow_compress P a hP t).eq, mul_assoc, hP.eq]

omit [CompleteSpace A] in
@[simp] lemma effective_zero (P a : A) : effective P a 0 = P := by
  simp [effective]

lemma flow_add (a : A) (s t : ℝ) : flow a (s + t) = flow a s * flow a t := by
  have hc : Commute ((s : ℂ) • a) ((t : ℂ) • a) :=
    ((Commute.refl a).smul_left (s : ℂ)).smul_right (t : ℂ)
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  simpa [flow, Complex.ofReal_add, add_smul] using
    (NormedSpace.exp_add_of_commute hc)

lemma effective_add (P a : A) (hP : IsIdempotentElem P) (s t : ℝ) :
    effective P a (s + t) = effective P a s * effective P a t := by
  change flow (compress P a) (s + t) * P = flow (compress P a) s * P * effective P a t
  rw [flow_add, mul_assoc, mul_assoc, effective_left P a hP t]
  rfl

end

/-!
## B. Adjoint and differential equation
-/

section

variable {A : Type*} [CStarAlgebra A]

lemma compress_skew (P a : A) (hP : IsSelfAdjoint P) (ha : star a = -a) :
    star (compress P a) = -compress P a := by
  rw [hP.star_compress, ha]
  simp only [compress_apply, mul_neg, neg_mul]

lemma generator_skew (H : A) (hH : IsSelfAdjoint H) (hbar : ℝ) :
    star (generator H hbar) = -generator H hbar := by
  simp [generator, star_smul, hH.star_eq, neg_smul, neg_div]

lemma star_flow (a : A) (ha : star a = -a) (t : ℝ) :
    star (flow a t) = flow a (-t) := by
  simp [flow, NormedSpace.star_exp, star_smul, ha, smul_neg, neg_smul]

lemma generator_compress (P H : A) (hbar : ℝ) :
    compress P (generator H hbar) = generator (compress P H) hbar := by
  simp [compress_apply, generator]

lemma flow_derivative (a : A) (t : ℝ) :
    HasDerivAt (flow a) (a * flow a t) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℂ) a (t : ℂ)).hasFDerivAt
  have hr := (h.restrictScalars ℝ).comp t Complex.ofRealCLM.hasFDerivAt
  have hd := hr.hasDerivAt
  change HasDerivAt (flow a) ((1 : ℂ) • (a * flow a t)) t at hd
  rw [one_smul] at hd
  exact hd

lemma effective_derivative (P a : A) (t : ℝ) :
    HasDerivAt (effective P a) (compress P a * effective P a t) t := by
  let rightMul := (ContinuousLinearMap.mul ℂ A).flip P
  have h := ((rightMul.restrictScalars ℝ).hasFDerivAt).comp t
    (flow_derivative (compress P a) t).hasFDerivAt
  change HasDerivAt (fun s => flow (compress P a) s * P)
    (compress P a * (flow (compress P a) t * P)) t
  simpa [rightMul, Function.comp_def, mul_assoc] using h.hasDerivAt

/-- The projected evolution satisfies the Schrödinger equation for the compressed Hamiltonian. -/
lemma effective_schrodinger (P H : A) (hbar : ℝ) (t : ℝ) :
    HasDerivAt (effective P (generator H hbar))
      ((-Complex.I / (hbar : ℂ)) •
        (compress P H * effective P (generator H hbar) t)) t := by
  have h := effective_derivative P (generator H hbar) t
  rw [generator_compress] at h
  simpa only [generator, smul_mul_assoc] using h

lemma effective_star (P a : A) (hP : IsStarProjection P)
    (ha : star a = -a) (t : ℝ) :
    star (effective P a t) = effective P a (-t) := by
  unfold effective
  rw [star_mul, hP.isSelfAdjoint.star_eq, star_flow _ (compress_skew P a hP.isSelfAdjoint ha) t]
  exact (commute_flow_compress P a hP.isIdempotentElem (-t)).eq

lemma effective_star_mul (P a : A) (hP : IsStarProjection P)
    (ha : star a = -a) (t : ℝ) :
    star (effective P a t) * effective P a t = P := by
  rw [effective_star P a hP ha t, ← effective_add P a hP.isIdempotentElem]
  simp

lemma effective_mul_star (P a : A) (hP : IsStarProjection P)
    (ha : star a = -a) (t : ℝ) :
    effective P a t * star (effective P a t) = P := by
  rw [effective_star P a hP ha t, ← effective_add P a hP.isIdempotentElem]
  simp

end

/-!
## C. Finite-dimensional effective dynamics
-/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance finiteDimensionalCompleteSpace : CompleteSpace E :=
  FiniteDimensional.completeSpace ℂ E

set_option linter.unusedVariables false in
/-- With a positive reduced Planck constant, the effective evolution starts at `P`,
composes in time, is unitary on the range of `P`, and satisfies the compressed
Schrödinger equation. -/
@[nolint unusedArguments]
lemma finite_dimensional_effective_dynamics
    (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hP : IsStarProjection P)
    (hbar : ℝ) (hh : 0 < hbar) :
    effective P (generator H hbar) 0 = P ∧
    (∀ t : ℝ, P * effective P (generator H hbar) t = effective P (generator H hbar) t) ∧
    (∀ s t : ℝ, effective P (generator H hbar) (s + t) =
      effective P (generator H hbar) s * effective P (generator H hbar) t) ∧
    (∀ t : ℝ, star (effective P (generator H hbar) t) * effective P (generator H hbar) t = P) ∧
    (∀ t : ℝ, effective P (generator H hbar) t * star (effective P (generator H hbar) t) = P) ∧
    (∀ t : ℝ, HasDerivAt (effective P (generator H hbar))
      ((-Complex.I / (hbar : ℂ)) • (compress P H * effective P (generator H hbar) t)) t) := by
  refine ⟨effective_zero _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact effective_left P _ hP.isIdempotentElem
  · exact effective_add P _ hP.isIdempotentElem
  · exact effective_star_mul P _ hP (generator_skew H hH hbar)
  · exact effective_mul_star P _ hP (generator_skew H hH hbar)
  · exact effective_schrodinger P H hbar

end

end QuantumZenoDynamics
