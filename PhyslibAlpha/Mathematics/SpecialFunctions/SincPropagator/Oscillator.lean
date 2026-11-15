/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Basic

/-!

# The harmonic oscillator

## i. Overview

The matrix exponential of the generator and the Duhamel formula for the oscillator with a source.

## ii. Key results

- `generator` : The generator `[[0, 1], [-ω², 0]]` of the free evolution of Cauchy data at frequency
  `ω`.
- `evolutionMatrix` : The evolution matrix of the Cauchy data at frequency `ω` over the time `t`.
- `duhamelOsc` : The retarded solution of `u'' + ω² u = G` with zero data at the time `a`.
- `duhamelOscCos` : The derivative of `duhamelOsc`: the same integral with the cosine kernel.

## iii. Table of contents

- A. The exponential of the Klein–Gordon generator
- B. Duhamel's formula for the harmonic oscillator

## iv. References

None.

## A. The exponential of the Klein–Gordon generator

- `generator` : The generator `[[0, 1], [-ω², 0]]` of the free evolution of Cauchy data at frequency
  `ω`.
- `evolutionMatrix` : The evolution matrix of the Cauchy data at frequency `ω` over the time `t`.

Lemmas: `generator_sq`, `generator_pow_even`, `generator_pow_odd`, `hasSum_sincPropagator`,
`hasSum_exp_generator`, `evolutionMatrix_eq`, `exp_generator`, `evolutionMatrix_add`,
`sincPropagator_add`, `cos_mul_add`.

## B. Duhamel's formula for the harmonic oscillator

- `duhamelOsc` : The retarded solution of `u'' + ω² u = G` with zero data at the time `a`.
- `duhamelOscCos` : The derivative of `duhamelOsc`: the same integral with the cosine kernel.

Lemmas: `sincPropagator_sub_split`, `cos_sub_split`, `cos_sq_add_sq_mul`,
`continuous_sincPropagator_smul`, `continuous_cos_smul`, `duhamelOsc_eq`, `duhamelOscCos_eq`,
`hasDerivAt_cosIntegral`, `hasDerivAt_sinIntegral`, `hasDerivAt_duhamelOsc` and more.

-/

@[expose] public section

noncomputable section

open scoped Nat Matrix
open NormedSpace intervalIntegral

namespace SincPropagator

open Real

/-- The generator `[[0, 1], [-ω², 0]]` of the free evolution of Cauchy data at frequency `ω`. -/
def generator (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -((ω ^ 2 : ℝ) : ℂ), 0]

lemma generator_sq (ω : ℝ) : generator ω ^ 2 = (-((ω ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2)
    ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generator, sq, Matrix.mul_apply, Fin.sum_univ_two]

lemma generator_pow_even (ω : ℝ) (n : ℕ) :
    generator ω ^ (2 * n) = (-((ω ^ 2 : ℝ) : ℂ)) ^ n • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pow_mul, generator_sq, smul_pow, one_pow]

lemma generator_pow_odd (ω : ℝ) (n : ℕ) :
    generator ω ^ (2 * n + 1) = (-((ω ^ 2 : ℝ) : ℂ)) ^ n • generator ω := by
  rw [pow_succ, generator_pow_even, smul_mul_assoc, one_mul]

/-- The series of `sincPropagator`, as a convergent sum. -/
lemma hasSum_sincPropagator (t ω : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * t ^ (2 * n + 1) * ω ^ (2 * n) / (2 * n + 1)!)
      (sincPropagator t ω) := by
  by_cases hω : ω = 0
  · subst hω
    rw [sincPropagator_zero_right]
    convert hasSum_single 0 (f := fun n : ℕ => (-1) ^ n * t ^ (2 * n + 1) * (0:ℝ) ^ (2 * n) / (2 * n
      + 1)!) ?_ using 1
    · simp
    · intro n hn; simp [hn]
  · rw [sincPropagator_eq_sin_div hω]
    have h := (Real.hasSum_sin (ω * t)).div_const ω
    convert h using 1
    funext n
    field_simp
    ring

lemma hasSum_exp_generator (t ω : ℝ) :
    HasSum (fun n : ℕ => ((n ! : ℂ)⁻¹) • ((t : ℂ) • generator ω) ^ n)
      (((cos (ω * t) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((sincPropagator t ω : ℝ) : ℂ) • generator ω) := by
  refine HasSum.even_add_odd ?_ ?_
  · have h := (Complex.hasSum_ofReal.2 (Real.hasSum_cos (ω * t))).smul_const
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
    convert h using 2 with k
    rw [smul_pow, generator_pow_even, smul_smul, smul_smul]
    congr 1
    rw [neg_pow]
    push_cast
    ring
  · have h := (Complex.hasSum_ofReal.2 (hasSum_sincPropagator t ω)).smul_const (generator ω)
    convert h using 2 with k
    rw [smul_pow, generator_pow_odd, smul_smul, smul_smul]
    congr 1
    rw [neg_pow]
    push_cast
    rw [pow_succ, ← pow_mul]
    ring_nf

/-- The evolution matrix of the Cauchy data at frequency `ω` over the time `t`. -/
def evolutionMatrix (t ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((cos (ω * t) : ℝ) : ℂ), ((sincPropagator t ω : ℝ) : ℂ);
    -((ω ^ 2 : ℝ) : ℂ) * ((sincPropagator t ω : ℝ) : ℂ), ((cos (ω * t) : ℝ) : ℂ)]

lemma evolutionMatrix_eq (t ω : ℝ) :
    evolutionMatrix t ω = ((cos (ω * t) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((sincPropagator t ω : ℝ) : ℂ) • generator ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evolutionMatrix, generator]
  ring

/-- The exponential of the generator is the evolution matrix. -/
lemma exp_generator (t ω : ℝ) :
    exp ((t : ℂ) • generator ω) = evolutionMatrix t ω := by
  let _ : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  rw [exp_eq_tsum (𝕂 := ℂ)]
  beta_reduce
  rw [(hasSum_exp_generator t ω).tsum_eq, evolutionMatrix_eq]

/-- The group law of the evolution matrix, from `exp (A + B) = exp A * exp B` for commuting
`A` and `B`. -/
lemma evolutionMatrix_add (s t ω : ℝ) :
    evolutionMatrix (s + t) ω = evolutionMatrix s ω * evolutionMatrix t ω := by
  rw [← exp_generator, ← exp_generator, ← exp_generator, Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl _).smul_left _ |>.smul_right _)

end SincPropagator

namespace Real

open SincPropagator

/-- The addition law of `sincPropagator`, read off from the entry `(0, 1)` of the group law. -/
lemma sincPropagator_add (s t ω : ℝ) :
    sincPropagator (s + t) ω =
      cos (ω * s) * sincPropagator t ω + sincPropagator s ω * cos (ω * t) := by
  have h := congrFun (congrFun (evolutionMatrix_add s t ω) 0) 1
  simp [evolutionMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
  exact_mod_cast h

/-- The addition law of the cosine, read off from the entry `(0, 0)` of the group law. -/
lemma cos_mul_add (s t ω : ℝ) :
    cos (ω * (s + t)) =
      cos (ω * s) * cos (ω * t) - ω ^ 2 * sincPropagator s ω * sincPropagator t ω := by
  have h := congrFun (congrFun (evolutionMatrix_add s t ω) 0) 0
  simp [evolutionMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h
  have : ((cos (ω * (s + t)) : ℝ) : ℂ) = ((cos (ω * s) * cos (ω * t) -
      ω ^ 2 * sincPropagator s ω * sincPropagator t ω : ℝ) : ℂ) := by
    push_cast at h ⊢
    linear_combination h
  exact_mod_cast this

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The retarded solution of `u'' + ω² u = G` with zero data at the time `a`. -/
def duhamelOsc (ω a : ℝ) (G : ℝ → V) (t : ℝ) : V :=
  ∫ s in a..t, sincPropagator (t - s) ω • G s

/-- The derivative of `duhamelOsc`: the same integral with the cosine kernel. -/
def duhamelOscCos (ω a : ℝ) (G : ℝ → V) (t : ℝ) : V :=
  ∫ s in a..t, cos (ω * (t - s)) • G s

lemma sincPropagator_sub_split (ω t s : ℝ) :
    sincPropagator (t - s) ω =
      sincPropagator t ω * cos (ω * s) - cos (ω * t) * sincPropagator s ω := by
  have h := sincPropagator_add t (-s) ω
  rw [← sub_eq_add_neg] at h
  rw [h, sincPropagator_neg_left, mul_neg, mul_neg, cos_neg]
  ring

lemma cos_sub_split (ω t s : ℝ) :
    cos (ω * (t - s)) =
      cos (ω * t) * cos (ω * s) + ω ^ 2 * sincPropagator t ω * sincPropagator s ω := by
  have h := cos_mul_add t (-s) ω
  rw [← sub_eq_add_neg] at h
  rw [h, sincPropagator_neg_left, mul_neg, cos_neg]
  ring

lemma cos_sq_add_sq_mul (ω t : ℝ) :
    cos (ω * t) ^ 2 + ω ^ 2 * sincPropagator t ω ^ 2 = 1 := by
  have := cos_sub_split ω t t
  simp only [sub_self, mul_zero, cos_zero] at this
  rw [sq, sq]
  linarith
end

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {G : ℝ → V} (hG : Continuous G) (ω a : ℝ)
include hG

omit [CompleteSpace V] in
lemma continuous_sincPropagator_smul : Continuous fun s => sincPropagator s ω • G s :=
  (continuous_sincPropagator.comp (continuous_id.prodMk continuous_const)).smul hG

omit [CompleteSpace V] in
lemma continuous_cos_smul : Continuous fun s => cos (ω * s) • G s := by fun_prop

omit [CompleteSpace V] in
lemma duhamelOsc_eq (t : ℝ) :
    duhamelOsc ω a G t =
      sincPropagator t ω • (∫ s in a..t, cos (ω * s) • G s) -
        cos (ω * t) • (∫ s in a..t, sincPropagator s ω • G s) := by
  have h1 := continuous_cos_smul hG ω
  have h2 := continuous_sincPropagator_smul hG ω
  have key : duhamelOsc ω a G t = ∫ s in a..t,
      (sincPropagator t ω • (cos (ω * s) • G s) - cos (ω * t) • (sincPropagator s ω • G s)) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [sincPropagator_sub_split, sub_smul, mul_smul]
  have hi1 : IntervalIntegrable (fun s => sincPropagator t ω • (cos (ω * s) • G s))
      MeasureTheory.volume a t := (h1.const_smul _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => cos (ω * t) • (sincPropagator s ω • G s))
      MeasureTheory.volume a t := (h2.const_smul _).intervalIntegrable _ _
  rw [key, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_smul,
    intervalIntegral.integral_smul]

omit [CompleteSpace V] in
lemma duhamelOscCos_eq (t : ℝ) :
    duhamelOscCos ω a G t =
      cos (ω * t) • (∫ s in a..t, cos (ω * s) • G s) +
        (ω ^ 2 * sincPropagator t ω) • (∫ s in a..t, sincPropagator s ω • G s) := by
  have h1 := continuous_cos_smul hG ω
  have h2 := continuous_sincPropagator_smul hG ω
  have key : duhamelOscCos ω a G t = ∫ s in a..t,
      (cos (ω * t) • (cos (ω * s) • G s) +
        (ω ^ 2 * sincPropagator t ω) • (sincPropagator s ω • G s)) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [cos_sub_split, add_smul, mul_smul]
  have hi1 : IntervalIntegrable (fun s => cos (ω * t) • (cos (ω * s) • G s))
      MeasureTheory.volume a t := (h1.const_smul _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => (ω ^ 2 * sincPropagator t ω) • (sincPropagator s ω • G s))
      MeasureTheory.volume a t := (h2.const_smul _).intervalIntegrable _ _
  rw [key, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_smul,
    intervalIntegral.integral_smul]

lemma hasDerivAt_cosIntegral (t : ℝ) :
    HasDerivAt (fun u => ∫ s in a..u, cos (ω * s) • G s) (cos (ω * t) • G t) t :=
  (continuous_cos_smul hG ω).integral_hasStrictDerivAt a t |>.hasDerivAt

lemma hasDerivAt_sinIntegral (t : ℝ) :
    HasDerivAt (fun u => ∫ s in a..u, sincPropagator s ω • G s) (sincPropagator t ω • G t) t :=
  (continuous_sincPropagator_smul hG ω).integral_hasStrictDerivAt a t |>.hasDerivAt

/-- The derivative of the retarded oscillator solution is the cosine Duhamel integral. -/
lemma hasDerivAt_duhamelOsc (t : ℝ) :
    HasDerivAt (duhamelOsc ω a G) (duhamelOscCos ω a G t) t := by
  have h := ((hasDerivAt_sincPropagator ω t).smul (hasDerivAt_cosIntegral hG ω a t)).sub
    ((hasDerivAt_cos_mul ω t).smul (hasDerivAt_sinIntegral hG ω a t))
  have e : duhamelOsc ω a G = fun u =>
      sincPropagator u ω • (∫ s in a..u, cos (ω * s) • G s) -
        cos (ω * u) • (∫ s in a..u, sincPropagator s ω • G s) :=
    funext (duhamelOsc_eq hG ω a)
  rw [e]
  refine h.congr_deriv ?_
  rw [duhamelOscCos_eq hG ω a t]
  simp only [smul_smul, neg_mul, neg_smul]
  rw [mul_comm (sincPropagator t ω) (cos (ω * t))]
  abel

/-- The second derivative: the force minus `ω²` times the solution. -/
lemma hasDerivAt_duhamelOscCos (t : ℝ) :
    HasDerivAt (duhamelOscCos ω a G) (G t - ω ^ 2 • duhamelOsc ω a G t) t := by
  have h := ((hasDerivAt_cos_mul ω t).smul (hasDerivAt_cosIntegral hG ω a t)).add
    ((((hasDerivAt_sincPropagator ω t).const_mul (ω ^ 2))).smul (hasDerivAt_sinIntegral hG ω a t))
  have e : duhamelOscCos ω a G = fun u =>
      cos (ω * u) • (∫ s in a..u, cos (ω * s) • G s) +
        (ω ^ 2 * sincPropagator u ω) • (∫ s in a..u, sincPropagator s ω • G s) :=
    funext (duhamelOscCos_eq hG ω a)
  rw [e]
  refine ((hasDerivAt_cos_mul ω t).smul (hasDerivAt_cosIntegral hG ω a t)).add
    (((hasDerivAt_sincPropagator ω t).const_mul (ω ^ 2)).smul
      (hasDerivAt_sinIntegral hG ω a t)) |>.congr_deriv ?_
  rw [duhamelOsc_eq hG ω a t]
  have hid := cos_sq_add_sq_mul ω t
  match_scalars <;> first | linear_combination hid | ring
end

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The oscillator Green kernel recovers a twice differentiable field up to its initial data. -/
lemma duhamelOsc_operator {g g' g'' : ℝ → V}
    (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : ∀ s, HasDerivAt g' (g'' s) s)
    (hg'' : Continuous g'') (ω a t : ℝ) :
    duhamelOsc ω a (fun s => g'' s + ω ^ 2 • g s) t =
      g t - (cos (ω * (t - a)) • g a + sincPropagator (t - a) ω • g' a) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s => (hg s).continuousAt
  have hd : ∀ s, HasDerivAt
      (fun s => cos (ω * (t - s)) • g s + sincPropagator (t - s) ω • g' s)
      (sincPropagator (t - s) ω • (g'' s + ω ^ 2 • g s)) s := by
    intro s
    have hcos := (hasDerivAt_cos_mul ω (t - s)).comp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have hsin := (hasDerivAt_sincPropagator ω (t - s)).comp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    convert (hcos.smul (hg s)).add (hsin.smul (hg' s)) using 1
    · rfl
    · dsimp only [Function.comp_apply]
      module
  have hi : IntervalIntegrable
      (fun s => sincPropagator (t - s) ω • (g'' s + ω ^ 2 • g s))
      MeasureTheory.volume a t := by
    apply Continuous.intervalIntegrable
    exact (continuous_sincPropagator.comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)).smul
      (hg''.add (hgc.const_smul _))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  simpa [duhamelOsc] using h

/-- The retarded oscillator Green operator is a left inverse on fields with zero initial data. -/
lemma duhamelOsc_operator_of_initial_zero {g g' g'' : ℝ → V}
    (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : ∀ s, HasDerivAt g' (g'' s) s)
    (hg'' : Continuous g'') (ω a t : ℝ) (hga : g a = 0) (hg'a : g' a = 0) :
    duhamelOsc ω a (fun s => g'' s + ω ^ 2 • g s) t = g t := by
  simp [duhamelOsc_operator hg hg' hg'' ω a t, hga, hg'a]
end

end Real
