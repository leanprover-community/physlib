/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.QuantumMechanics.FreeParticle.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Fourier
public import Physlib.QuantumMechanics.Semiclassical.Quadratic
public import Physlib.QuantumMechanics.Semiclassical.QuadraticPhase
public import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Exact free propagation of quadratic Weyl symbols

Construct the unitary free propagator and prove its exact quadratic Egorov correspondence.

## i. Overview

For a free particle of mass `m`, the classical flow is `(x, p) -> (x + t p / m, p)`.
The quantum propagator is the Fourier multiplier with phase
`exp (-i (2 pi)^2 h t |xi|^2 / (2 m))`, using Mathlib's Fourier normalization. It
preserves Schwartz maps and extends to a strongly continuous unitary group on
`SpaceDHilbertSpace d`. The Fourier-coordinate Schrodinger equation connects this
propagator to `sum_i p_i^2 / (2 m)`.

Conjugation transforms position to `x + t p / m` and fixes momentum. Since conjugation
is an algebra equivalence, this proves exact transport of every Weyl-ordered quadratic
expression. The Hilbert-space identity is evaluated on the invariant Schwartz domain.
General potentials, general symbol classes, and semiclassical remainder estimates are
outside the scope of this file.

## ii. Key results

- `freeEvolution` : the Hilbert-space unitary propagator
- `freeEvolution_continuous` : strong continuity in time
- `freeEvolutionCLM_fourier_schrodinger` : the Fourier-coordinate Schrodinger equation
- `freeEgorov_quadratic` : the exact correspondence on Schwartz maps
- `freeEgorov_quadratic_hilbert` : the identity on the Hilbert-space Schwartz domain

## iii. Table of contents

- A. The classical flow
- B. The semiclassical Hamiltonian
- C. Propagation on Schwartz maps
- D. The Hilbert-space propagator
- E. Strong continuity
- F. The Schrodinger equation in Fourier coordinates
- G. Exact quadratic Egorov correspondence

## iv. References

* S. Dyatlov, Notes on fractal uncertainty principle (2017), Proposition 1.1.3
  for the general Egorov correspondence,
  https://math.mit.edu/~dyatlov/files/2017/fupnotes.pdf.
* J. E. Moyal, Quantum mechanics as a statistical theory (1949),
  https://doi.org/10.1017/S0305004100000487.
-/

@[expose] public section

namespace QuantumMechanics.Semiclassical

noncomputable section

open Complex Real MeasureTheory SchwartzMap ContinuousLinearMap
open SpaceDHilbertSpace
open scoped FourierTransform InnerProductSpace

variable {d : ℕ}

/-! ## A. The classical flow -/

/-- The classical free-particle flow `(x, p) -> (x + t p / m, p)`. -/
def freeFlow (Q : FreeParticle d) (t : ℝ) (z : Space d × Space d) : Space d × Space d :=
  (z.1 + (t / Q.m) • z.2, z.2)

/-- Pulling back a quadratic symbol along the free flow substitutes `x + t p / m` for `x`. -/
lemma quadraticSymbol_freeFlow (Q : FreeParticle d) (t : ℝ) (c : ℂ)
    (a b : Fin d → ℂ) (A B C : Matrix (Fin d) (Fin d) ℂ) (z : Space d × Space d) :
    quadraticSymbol c a b A B C (freeFlow Q t z) = quadraticPolynomial c a b A B C
      (fun i => (z.1 i : ℂ) + (t / Q.m : ℂ) * z.2 i) (fun i => z.2 i) := by
  simp [quadraticSymbol, freeFlow, Space.add_apply, Space.smul_apply]

/-! ## B. The semiclassical Hamiltonian -/

/-- The semiclassical free Hamiltonian `sum_i p_i^2 / (2 m)` on Schwartz maps. -/
def freeHamiltonianCLM (Q : FreeParticle d) (h : ℝ) :
    𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (1 / (2 * Q.m) : ℂ) • ∑ i, momentumCLM h i ∘L momentumCLM h i

/-- The semiclassical free Hamiltonian is symmetric on Schwartz maps. -/
lemma freeHamiltonianCLM_inner (Q : FreeParticle d) (h : ℝ) (f g : 𝓢(Space d, ℂ)) :
    ⟪schwartzIncl volume (freeHamiltonianCLM Q h f), schwartzIncl volume g⟫_ℂ =
      ⟪schwartzIncl volume f, schwartzIncl volume (freeHamiltonianCLM Q h g)⟫_ℂ := by
  simp only [freeHamiltonianCLM, smul_apply, sum_apply, comp_apply, map_smul, map_sum,
    inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp only [map_div₀, map_one, map_mul, map_ofNat, conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [momentumCLM_inner, momentumCLM_inner]

/-- In Fourier coordinates the free Hamiltonian multiplies by `(2 pi h)^2 |xi|^2 / (2 m)`. -/
lemma fourier_freeHamiltonianCLM (Q : FreeParticle d) (h : ℝ)
    (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 (freeHamiltonianCLM Q h f) ξ =
      ((2 * π * h) ^ 2 / (2 * Q.m) : ℂ) * (‖ξ‖ ^ 2 : ℝ) * 𝓕 f ξ := by
  simp only [freeHamiltonianCLM, smul_apply, sum_apply, comp_apply,
    FourierTransform.fourier_smul, FourierTransform.fourier_sum, fourier_momentumCLM,
    map_smul, smul_eq_mul, QuantumMechanics.positionCLM_apply]
  rw [Space.norm_sq_eq]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## C. Propagation on Schwartz maps -/

/-- The free propagator on Schwartz maps, as a Fourier multiplier.
Mathlib uses `exp (-2 pi i x . xi)`, so its multiplier is
`exp (-i (2 pi)^2 h t |xi|^2 / (2 m))`. -/
def freeEvolutionCLM (Q : FreeParticle d) (h t : ℝ) :
    𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (quadraticPhase (-(2 * π) ^ 2 * h * t / (2 * Q.m)))

/-- The Fourier-multiplier formula for the free propagator. -/
lemma freeEvolutionCLM_apply (Q : FreeParticle d) (h t : ℝ) (f : 𝓢(Space d, ℂ)) :
    freeEvolutionCLM Q h t f =
      𝓕⁻ (quadraticPhaseCLM (-(2 * π) ^ 2 * h * t / (2 * Q.m)) (𝓕 f)) := rfl

/-- Propagation for time zero is the identity. -/
@[simp]
lemma freeEvolutionCLM_zero (Q : FreeParticle d) (h : ℝ) :
    freeEvolutionCLM Q h 0 = .id ℂ _ := by
  ext f x
  simp [freeEvolutionCLM_apply]

/-- The free propagators on Schwartz maps satisfy the time-addition law. -/
lemma freeEvolutionCLM_add (Q : FreeParticle d) (h s t : ℝ) :
    freeEvolutionCLM Q h (s + t) = freeEvolutionCLM Q h s ∘L freeEvolutionCLM Q h t := by
  ext f
  simp only [comp_apply, freeEvolutionCLM_apply]
  rw [FourierTransform.fourier_fourierInv_eq,
    show -(2 * π) ^ 2 * h * (s + t) / (2 * Q.m) =
      -(2 * π) ^ 2 * h * s / (2 * Q.m) + -(2 * π) ^ 2 * h * t / (2 * Q.m) by ring,
    quadraticPhaseCLM_add, comp_apply]

/-- The free propagator preserves the Hilbert-space norm of a Schwartz map. -/
lemma freeEvolutionCLM_norm (Q : FreeParticle d) (h t : ℝ) (f : 𝓢(Space d, ℂ)) :
    ‖schwartzIncl volume (freeEvolutionCLM Q h t f)‖ = ‖schwartzIncl volume f‖ := by
  rw [freeEvolutionCLM_apply, ← schwartzIncl_fourierInv_eq]
  change ‖(fourierUnitary d).symm _‖ = _
  rw [LinearIsometryEquiv.norm_map, quadraticPhaseCLM_norm, ← schwartzIncl_fourier_eq]
  exact (fourierUnitary d).norm_map _

/-- The free propagator as a continuous linear equivalence of the Schwartz space. -/
def freeEvolutionCLE (Q : FreeParticle d) (h t : ℝ) :
    𝓢(Space d, ℂ) ≃L[ℂ] 𝓢(Space d, ℂ) where
  toLinearMap := (freeEvolutionCLM Q h t).toLinearMap
  invFun := freeEvolutionCLM Q h (-t)
  left_inv f := by
    change (freeEvolutionCLM Q h (-t) ∘L freeEvolutionCLM Q h t) f = f
    rw [← freeEvolutionCLM_add, neg_add_cancel, freeEvolutionCLM_zero, id_apply]
  right_inv f := by
    change (freeEvolutionCLM Q h t ∘L freeEvolutionCLM Q h (-t)) f = f
    rw [← freeEvolutionCLM_add, add_neg_cancel, freeEvolutionCLM_zero, id_apply]
  continuous_toFun := (freeEvolutionCLM Q h t).continuous
  continuous_invFun := (freeEvolutionCLM Q h (-t)).continuous

/-! ## D. The Hilbert-space propagator -/

/-- The free propagator as a unitary on the full Hilbert space, extended from the dense
Schwartz space by norm preservation. -/
def freeEvolution (Q : FreeParticle d) (h t : ℝ) :
    SpaceDHilbertSpace d ≃ₗᵢ[ℂ] SpaceDHilbertSpace d :=
  (freeEvolutionCLE Q h t).toLinearEquiv.extendOfIsometry
    (schwartzIncl volume).toLinearMap (schwartzIncl volume).toLinearMap
    (SchwartzSubmodule.dense d volume) (SchwartzSubmodule.dense d volume)
    (freeEvolutionCLM_norm Q h t)

/-- The Hilbert-space propagator agrees with the Schwartz-space propagator. -/
@[simp]
lemma freeEvolution_schwartzIncl (Q : FreeParticle d) (h t : ℝ) (f : 𝓢(Space d, ℂ)) :
    freeEvolution Q h t (schwartzIncl volume f) =
      schwartzIncl volume (freeEvolutionCLM Q h t f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

/-- The inverse Hilbert-space propagator acts by negative time on Schwartz maps. -/
@[simp]
lemma freeEvolution_symm_schwartzIncl (Q : FreeParticle d) (h t : ℝ)
    (f : 𝓢(Space d, ℂ)) :
    (freeEvolution Q h t).symm (schwartzIncl volume f) =
      schwartzIncl volume (freeEvolutionCLM Q h (-t) f) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ _

/-- The Hilbert-space propagator is the identity at time zero. -/
lemma freeEvolution_zero (Q : FreeParticle d) (h : ℝ) (ψ : SpaceDHilbertSpace d) :
    freeEvolution Q h 0 ψ = ψ := by
  refine (SchwartzSubmodule.dense d volume).induction ?_
    (isClosed_eq (freeEvolution Q h 0).continuous continuous_id) ψ
  rintro _ ⟨f, rfl⟩
  simp [freeEvolution_schwartzIncl, freeEvolutionCLM_zero]

/-- The time-addition law holds on the full Hilbert space. -/
lemma freeEvolution_add (Q : FreeParticle d) (h s t : ℝ) (ψ : SpaceDHilbertSpace d) :
    freeEvolution Q h (s + t) ψ = freeEvolution Q h s (freeEvolution Q h t ψ) := by
  refine (SchwartzSubmodule.dense d volume).induction ?_
    (isClosed_eq (freeEvolution Q h (s + t)).continuous
      ((freeEvolution Q h s).continuous.comp (freeEvolution Q h t).continuous)) ψ
  rintro _ ⟨f, rfl⟩
  change freeEvolution Q h (s + t) (schwartzIncl volume f) =
    freeEvolution Q h s (freeEvolution Q h t (schwartzIncl volume f))
  simp only [freeEvolution_schwartzIncl, freeEvolutionCLM_add, comp_apply]

/-- The Hilbert-space propagator preserves the common Schwartz domain. -/
lemma freeEvolution_mem_schwartzSubmodule (Q : FreeParticle d) (h t : ℝ)
    (ψ : SchwartzSubmodule d) : freeEvolution Q h t ψ ∈ SchwartzSubmodule d := by
  obtain ⟨f, hf⟩ := ψ.property
  rw [← hf]
  change freeEvolution Q h t (schwartzIncl volume f) ∈ SchwartzSubmodule d
  rw [freeEvolution_schwartzIncl]
  exact ⟨freeEvolutionCLM Q h t f, rfl⟩

/-! ## E. Strong continuity -/

/-- A propagated Schwartz map depends continuously on time in the Hilbert-space norm. -/
lemma freeEvolution_continuous_schwartz (Q : FreeParticle d) (h : ℝ)
    (f : 𝓢(Space d, ℂ)) :
    Continuous fun t : ℝ => schwartzIncl volume (freeEvolutionCLM Q h t f) := by
  have hc := (quadraticPhaseCLM_lipschitz (𝓕 f)).continuous.comp
    (show Continuous (fun t : ℝ => -(2 * π) ^ 2 * h * t / (2 * Q.m)) by fun_prop)
  have hu := (fourierUnitary d).symm.continuous.comp hc
  convert hu using 1
  funext t
  exact (schwartzIncl_fourierInv_eq
    (quadraticPhaseCLM (-(2 * π) ^ 2 * h * t / (2 * Q.m)) (𝓕 f))).symm

/-- The unitary free propagators form a strongly continuous group. -/
lemma freeEvolution_continuous (Q : FreeParticle d) (h : ℝ) (ψ : SpaceDHilbertSpace d) :
    Continuous fun t : ℝ => freeEvolution Q h t ψ := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨φ, ⟨f, rfl⟩, hf⟩ := (SchwartzSubmodule.dense d volume).exists_dist_lt ψ
    (show 0 < ε / 3 by positivity)
  change dist ψ (schwartzIncl volume f) < ε / 3 at hf
  have hc : ContinuousAt (fun t => freeEvolution Q h t (schwartzIncl volume f)) t₀ := by
    simpa only [freeEvolution_schwartzIncl] using
      (freeEvolution_continuous_schwartz Q h f).continuousAt (x := t₀)
  obtain ⟨δ, hδ, ht⟩ := Metric.continuousAt_iff.mp hc (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun t htδ => ?_⟩
  calc
    _ ≤ dist (freeEvolution Q h t ψ) (freeEvolution Q h t (schwartzIncl volume f)) +
        dist (freeEvolution Q h t (schwartzIncl volume f)) (freeEvolution Q h t₀ ψ) :=
      dist_triangle _ _ _
    _ ≤ dist (freeEvolution Q h t ψ) (freeEvolution Q h t (schwartzIncl volume f)) +
        (dist (freeEvolution Q h t (schwartzIncl volume f))
          (freeEvolution Q h t₀ (schwartzIncl volume f)) +
        dist (freeEvolution Q h t₀ (schwartzIncl volume f)) (freeEvolution Q h t₀ ψ)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by
      rw [(freeEvolution Q h t).dist_map, (freeEvolution Q h t₀).dist_map]
      rw [dist_comm (schwartzIncl volume f) ψ]
      linarith [ht htδ]

/-! ## F. The Schrodinger equation in Fourier coordinates -/

/-- The time derivative of a propagated Schwartz map at each Fourier coordinate. -/
lemma freeEvolutionCLM_fourier_hasDerivAt (Q : FreeParticle d) (h t : ℝ)
    (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    HasDerivAt (fun s : ℝ => 𝓕 (freeEvolutionCLM Q h s f) ξ)
      (-I * h * (2 * π) ^ 2 / (2 * Q.m) * (‖ξ‖ ^ 2 : ℝ) *
        𝓕 (freeEvolutionCLM Q h t f) ξ) t := by
  have h₁ := ((hasDerivAt_id t).const_mul (-(2 * π) ^ 2 * h)).div_const (2 * Q.m)
  have h₂ := ((quadraticPhase_hasDerivAt
    (-(2 * π) ^ 2 * h * t / (2 * Q.m)) ξ).scomp t h₁).mul_const (𝓕 f ξ)
  convert h₂ using 1
  · funext s
    simp [freeEvolutionCLM_apply, quadraticPhaseCLM_apply]
  · simp only [freeEvolutionCLM_apply, FourierTransform.fourier_fourierInv_eq,
      quadraticPhaseCLM_apply, Complex.real_smul, ofReal_div, ofReal_mul, ofReal_neg, ofReal_pow,
      ofReal_ofNat, ofReal_one]
    ring

/-- The free propagator satisfies the Schrodinger equation pointwise in Fourier coordinates.
This statement concerns the scalar derivative at each Fourier coordinate. -/
lemma freeEvolutionCLM_fourier_schrodinger (Q : FreeParticle d) (h t : ℝ)
    (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    I * h * deriv (fun s : ℝ => 𝓕 (freeEvolutionCLM Q h s f) ξ) t =
      𝓕 (freeHamiltonianCLM Q h (freeEvolutionCLM Q h t f)) ξ := by
  rw [(freeEvolutionCLM_fourier_hasDerivAt Q h t f ξ).deriv, fourier_freeHamiltonianCLM]
  simp only [ofReal_pow]
  ring_nf
  simp [I_sq]

/-! ## G. Exact quadratic Egorov correspondence -/

/-- Momentum commutes with free propagation on the common Schwartz domain. -/
lemma freeEvolutionCLM_momentum (Q : FreeParticle d) (h t : ℝ) (i : Fin d)
    (f : 𝓢(Space d, ℂ)) :
    momentumCLM h i (freeEvolutionCLM Q h t f) =
      freeEvolutionCLM Q h t (momentumCLM h i f) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(Space d, ℂ)).injective
  change 𝓕 (momentumCLM h i (freeEvolutionCLM Q h t f)) =
    𝓕 (freeEvolutionCLM Q h t (momentumCLM h i f))
  simp only [fourier_momentumCLM, freeEvolutionCLM_apply,
    FourierTransform.fourier_fourierInv_eq, map_smul]
  ext ξ
  simp only [quadraticPhaseCLM_apply, QuantumMechanics.positionCLM_apply, smul_apply,
    smul_eq_mul]
  ring

/-- Position after free propagation is the propagation of `x + t p / m`. -/
lemma freeEvolutionCLM_position (Q : FreeParticle d) (h : ℝ) (hh : h ≠ 0) (t : ℝ)
    (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    𝐱 i (freeEvolutionCLM Q h t f) =
      freeEvolutionCLM Q h t (𝐱 i f + (t / Q.m : ℂ) • momentumCLM h i f) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(Space d, ℂ)).injective
  change 𝓕 (𝐱 i (freeEvolutionCLM Q h t f)) =
    𝓕 (freeEvolutionCLM Q h t (𝐱 i f + (t / Q.m : ℂ) • momentumCLM h i f))
  simp only [freeEvolutionCLM_apply, fourier_positionCLM h hh,
    FourierTransform.fourier_fourierInv_eq, quadraticPhaseCLM_momentum,
    FourierTransform.fourier_add, FourierTransform.fourier_smul, fourier_momentumCLM,
    map_add, map_smul]
  ext ξ
  simp only [smul_apply, smul_eq_mul, add_apply, quadraticPhaseCLM_apply,
    QuantumMechanics.positionCLM_apply, ofReal_div, ofReal_mul, ofReal_neg, ofReal_pow,
    ofReal_ofNat]
  field_simp
  ring

/-- Exact free Egorov correspondence for a momentum coordinate. -/
lemma freeEgorov_momentum (Q : FreeParticle d) (h t : ℝ) (i : Fin d) :
    (freeEvolutionCLE Q h t).symm.conjContinuousAlgEquiv (momentumCLM h i) =
      momentumCLM h i := by
  ext1 f
  change freeEvolutionCLM Q h (-t) (momentumCLM h i (freeEvolutionCLM Q h t f)) = _
  rw [freeEvolutionCLM_momentum]
  exact (freeEvolutionCLE Q h t).left_inv _

/-- Exact free Egorov correspondence for a position coordinate. -/
lemma freeEgorov_position (Q : FreeParticle d) (h : ℝ) (hh : h ≠ 0) (t : ℝ) (i : Fin d) :
    (freeEvolutionCLE Q h t).symm.conjContinuousAlgEquiv (𝐱 i) =
      𝐱 i + (t / Q.m : ℂ) • momentumCLM h i := by
  ext1 f
  change freeEvolutionCLM Q h (-t) (𝐱 i (freeEvolutionCLM Q h t f)) = _
  rw [freeEvolutionCLM_position Q h hh]
  exact (freeEvolutionCLE Q h t).left_inv _

/-- Exact Egorov correspondence for all coefficient presentations of Weyl-ordered
quadratic symbols under free propagation. The transformed expression uses the same
substitution as `quadraticSymbol_freeFlow`. -/
theorem freeEgorov_quadratic (Q : FreeParticle d) (h : ℝ) (hh : h ≠ 0) (t : ℝ)
    (c : ℂ) (a b : Fin d → ℂ) (A B C : Matrix (Fin d) (Fin d) ℂ) :
    (freeEvolutionCLE Q h t).symm.conjContinuousAlgEquiv (weylQuadraticCLM h c a b A B C) =
      quadraticPolynomial c a b A B C
        (fun i => 𝐱 i + (t / Q.m : ℂ) • momentumCLM h i) (momentumCLM h) := by
  change (freeEvolutionCLE Q h t).symm.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
    (quadraticPolynomial c a b A B C QuantumMechanics.positionCLM (momentumCLM h)) = _
  rw [map_quadraticPolynomial]
  simp only [ContinuousAlgEquiv.coe_toAlgEquiv, AlgEquiv.coe_toAlgHom,
    freeEgorov_position Q h hh, freeEgorov_momentum]

/-- The exact quadratic Egorov identity in the Hilbert space, evaluated on its invariant
Schwartz domain. No equality of maximal unbounded-operator domains is asserted. -/
lemma freeEgorov_quadratic_hilbert (Q : FreeParticle d) (h : ℝ) (hh : h ≠ 0) (t : ℝ)
    (c : ℂ) (a b : Fin d → ℂ) (A B C : Matrix (Fin d) (Fin d) ℂ)
    (f : 𝓢(Space d, ℂ)) :
    (freeEvolution Q h t).symm
      (schwartzIncl volume (weylQuadraticCLM h c a b A B C (freeEvolutionCLM Q h t f))) =
      schwartzIncl volume (quadraticPolynomial c a b A B C
        (fun i => 𝐱 i + (t / Q.m : ℂ) • momentumCLM h i) (momentumCLM h) f) := by
  rw [freeEvolution_symm_schwartzIncl]
  exact congrArg (schwartzIncl volume)
    (congrArg (fun T : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) => T f)
      (freeEgorov_quadratic Q h hh t c a b A B C))

end

end QuantumMechanics.Semiclassical
