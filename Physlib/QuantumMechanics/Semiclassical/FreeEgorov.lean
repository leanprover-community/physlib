/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.QuantumMechanics.Semiclassical.FreeParticle
public import Physlib.QuantumMechanics.Semiclassical.Weyl

/-!
# Exact free Egorov correspondence for Schwartz symbols

Transport bounded Weyl operators along the classical free flow on the full Hilbert space.

## i. Overview

The free flow is the shear `(q, p) -> (q + t p / m, p)`. Its transpose acts on the
Fourier frequencies by `(u, v) -> (u, v + t u / m)`. Both shears preserve phase-space
volume and the Schwartz class. An explicit quadratic-phase identity shows that free
quantum propagation conjugates each Weyl displacement by the transpose shear.

Integrating this identity against the Fourier transform of a Schwartz symbol proves
`U(t)⁻¹ Op_h(a) U(t) = Op_h(a ∘ Phi(t))` for every Hilbert-space vector. The identity is
exact for the free Hamiltonian; it has no semiclassical remainder. It extends the
quadratic-symbol result using bounded Fourier synthesis, so no operator-domain
restriction on the initial vector is necessary.

## ii. Key results

- `fourier_freeSymbol` : the Fourier transform of the transported symbol
- `weyl_freeEvolution` : covariance of Weyl displacements under free propagation
- `freeEgorov` : exact free Egorov correspondence for every Schwartz symbol
- `freeEgorov_expectation` : the corresponding equality of quantum expectation values

## iii. Table of contents

- A. Covariance on Schwartz vectors
- B. Transport of phase-space symbols
- C. Exact Egorov correspondence on the Hilbert space

## iv. References

* J. Keller and C. Lasser, Propagation of Quantum Expectations with Husimi Functions,
  arXiv:1207.7211v2 (2013), introduction for the Egorov correspondence,
  https://arxiv.org/abs/1207.7211.
-/

@[expose] public section

namespace QuantumMechanics.Semiclassical

noncomputable section

open Complex Real MeasureTheory SchwartzMap ContinuousLinearMap
open SpaceDHilbertSpace
open scoped FourierTransform InnerProductSpace

variable {d : ℕ}

/-! ## A. Covariance on Schwartz vectors -/

/-- Free propagation multiplies the Fourier transform by its quadratic phase. -/
lemma fourier_freeEvolutionCLM (Q : FreeParticle d) (h t : ℝ)
    (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 (freeEvolutionCLM Q h t f) ξ =
      quadraticPhase (-(2 * π) ^ 2 * h * t / (2 * Q.m)) ξ * 𝓕 f ξ := by
  rw [freeEvolutionCLM_apply, FourierTransform.fourier_fourierInv_eq, quadraticPhaseCLM_apply]

/-- The quadratic free phase intertwines a Weyl displacement with the transpose shear. -/
lemma weyl_free_phase (s h : ℝ) (u v ξ : Space d) :
    (𝐞 (π * h * ⟪u, v⟫_ℝ) : ℂ) *
      (𝐞 (-⟪-(2 * π * h) • v, ξ - u⟫_ℝ) : ℂ) *
        quadraticPhase (-(2 * π) ^ 2 * h * s / 2) (ξ - u) =
    quadraticPhase (-(2 * π) ^ 2 * h * s / 2) ξ *
      ((𝐞 (π * h * ⟪u, v + s • u⟫_ℝ) : ℂ) *
        (𝐞 (-⟪-(2 * π * h) • (v + s • u), ξ - u⟫_ℝ) : ℂ)) := by
  simp only [Real.fourierChar_apply, quadraticPhase, ← Complex.exp_add]
  congr 1
  simp only [inner_smul_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm u ξ,
    starRingEnd_apply, star_trivial]
  push_cast
  ring

/-- Free propagation intertwines Weyl displacements with the classical transpose shear. -/
lemma weylCLM_freeEvolutionCLM (Q : FreeParticle d) (h t : ℝ)
    (z : Space d × Space d) (f : 𝓢(Space d, ℂ)) :
    weylCLM h z (freeEvolutionCLM Q h t f) =
      freeEvolutionCLM Q h t (weylCLM h (z.1, z.2 + (t / Q.m) • z.1) f) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(Space d, ℂ)).injective
  change 𝓕 (weylCLM h z (freeEvolutionCLM Q h t f)) =
    𝓕 (freeEvolutionCLM Q h t (weylCLM h (z.1, z.2 + (t / Q.m) • z.1) f))
  ext1 ξ
  simp only [fourier_weylCLM, fourier_freeEvolutionCLM]
  rw [show -(2 * π) ^ 2 * h * t / (2 * Q.m) =
    -(2 * π) ^ 2 * h * (t / Q.m) / 2 by ring]
  rw [← mul_assoc, weyl_free_phase (t / Q.m)]
  ring

/-! ## B. Transport of phase-space symbols -/

/-- The classical free flow as a continuous linear equivalence of Euclidean phase space. -/
def freeFlowCLE (Q : FreeParticle d) (t : ℝ) : PhaseSpace d ≃L[ℝ] PhaseSpace d :=
  let e : (Space d × Space d) ≃L[ℝ] (Space d × Space d) :=
    { toFun := freeFlow Q t
      invFun := freeFlow Q (-t)
      map_add' := by
        intro x y
        apply Prod.ext
        · change (x.1 + y.1) + (t / Q.m) • (x.2 + y.2) = _
          simp [freeFlow, smul_add, add_add_add_comm]
        · rfl
      map_smul' := by
        intro c z
        apply Prod.ext
        · change c • z.1 + (t / Q.m) • (c • z.2) = c • (z.1 + (t / Q.m) • z.2)
          module
        · rfl
      left_inv := by
        intro z
        apply Prod.ext
        · change z.1 + (t / Q.m) • z.2 + (-t / Q.m) • z.2 = z.1
          rw [neg_div, neg_smul]
          abel
        · rfl
      right_inv := by
        intro z
        apply Prod.ext
        · change z.1 + (-t / Q.m) • z.2 + (t / Q.m) • z.2 = z.1
          rw [neg_div, neg_smul]
          abel
        · rfl
      continuous_toFun := by unfold freeFlow; fun_prop
      continuous_invFun := by unfold freeFlow; fun_prop }
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).trans
    (e.trans (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm)

/-- The phase-space equivalence agrees with the existing classical free flow. -/
lemma freeFlowCLE_apply (Q : FreeParticle d) (t : ℝ) (z : PhaseSpace d) :
    freeFlowCLE Q t z = WithLp.toLp 2 (freeFlow Q t z.ofLp) := rfl

/-- Reversing the time gives the inverse classical free flow. -/
lemma freeFlowCLE_symm_apply (Q : FreeParticle d) (t : ℝ) (z : PhaseSpace d) :
    (freeFlowCLE Q t).symm z = freeFlowCLE Q (-t) z := rfl

/-- The transpose of the classical free flow, acting on Fourier frequencies. -/
def freeDualFlowCLE (Q : FreeParticle d) (t : ℝ) : PhaseSpace d ≃L[ℝ] PhaseSpace d :=
  let e := (LinearIsometryEquiv.withLpProdComm 2 ℝ (Space d) (Space d)).toContinuousLinearEquiv
  e.trans ((freeFlowCLE Q t).trans e)

/-- The transpose flow fixes the position frequency and shears the momentum frequency. -/
lemma freeDualFlowCLE_apply (Q : FreeParticle d) (t : ℝ) (z : PhaseSpace d) :
    freeDualFlowCLE Q t z = WithLp.toLp 2 (z.fst, z.snd + (t / Q.m) • z.fst) := rfl

/-- The classical free flow preserves Euclidean phase-space volume. -/
lemma freeFlowCLE_measurePreserving (Q : FreeParticle d) (t : ℝ) :
    MeasurePreserving (freeFlowCLE Q t) := by
  have hs : MeasurePreserving
      (fun z : Space d × Space d => (z.1, z.2 + (t / Q.m) • z.1)) :=
    (MeasurePreserving.id volume).skew_product
      (by fun_prop) (Filter.Eventually.of_forall fun x =>
        (measurePreserving_add_right volume ((t / Q.m) • x)).map_eq)
  exact (WithLp.volume_preserving_toLp (Space d) (Space d)).comp
    ((Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
      (hs.comp ((Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
      (WithLp.volume_preserving_ofLp (Space d) (Space d)))))

/-- The transpose free flow preserves phase-space volume. -/
lemma freeDualFlowCLE_measurePreserving (Q : FreeParticle d) (t : ℝ) :
    MeasurePreserving (freeDualFlowCLE Q t) := by
  let e := LinearIsometryEquiv.withLpProdComm 2 ℝ (Space d) (Space d)
  exact e.measurePreserving.comp ((freeFlowCLE_measurePreserving Q t).comp e.measurePreserving)

/-- The classical and transpose flows satisfy the defining transpose pairing identity. -/
lemma freeFlowCLE_inner (Q : FreeParticle d) (t : ℝ) (z w : PhaseSpace d) :
    ⟪freeFlowCLE Q t z, w⟫_ℝ = ⟪z, freeDualFlowCLE Q t w⟫_ℝ := by
  simp only [freeFlowCLE_apply, freeDualFlowCLE_apply, WithLp.prod_inner_apply,
    freeFlow, WithLp.fst, WithLp.snd, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial]
  ring

/-- Pullback of a Schwartz symbol along the classical free flow. -/
def freeSymbol (Q : FreeParticle d) (t : ℝ) (a : 𝓢(PhaseSpace d, ℂ)) :
    𝓢(PhaseSpace d, ℂ) :=
  compCLMOfContinuousLinearEquiv ℂ (freeFlowCLE Q t) a

/-- The transported symbol is evaluated along the classical free flow. -/
lemma freeSymbol_apply (Q : FreeParticle d) (t : ℝ) (a : 𝓢(PhaseSpace d, ℂ))
    (z : PhaseSpace d) :
    freeSymbol Q t a z = a (freeFlowCLE Q t z) := rfl

/-- The Fourier transform of a transported symbol is pulled back by the inverse transpose flow. -/
lemma fourier_freeSymbol (Q : FreeParticle d) (t : ℝ) (a : 𝓢(PhaseSpace d, ℂ))
    (z : PhaseSpace d) :
    𝓕 (freeSymbol Q t a) z = 𝓕 a (freeDualFlowCLE Q (-t) z) := by
  rw [fourier_coe, Real.fourier_eq]
  have hi := (freeFlowCLE_measurePreserving Q t).integral_comp
    (freeFlowCLE Q t).toHomeomorph.measurableEmbedding
    (fun w => 𝐞 (-⟪(freeFlowCLE Q t).symm w, z⟫_ℝ) • a w)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hi
  simp only [freeSymbol_apply]
  rw [hi, fourier_coe, Real.fourier_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp only
    rw [freeFlowCLE_symm_apply, freeFlowCLE_inner]

/-- Reversing time gives the inverse transpose flow. -/
lemma freeDualFlowCLE_symm_apply (Q : FreeParticle d) (t : ℝ) (z : PhaseSpace d) :
    (freeDualFlowCLE Q t).symm z = freeDualFlowCLE Q (-t) z := rfl

/-! ## C. Exact Egorov correspondence on the Hilbert space -/

/-- Free propagation intertwines Weyl displacements on the full Hilbert space. -/
lemma weyl_freeEvolution (Q : FreeParticle d) (h t : ℝ)
    (z : Space d × Space d) (ψ : SpaceDHilbertSpace d) :
    weyl h z (freeEvolution Q h t ψ) =
      freeEvolution Q h t (weyl h (z.1, z.2 + (t / Q.m) • z.1) ψ) := by
  refine (SchwartzSubmodule.dense d volume).induction ?_
    (isClosed_eq ((weyl h z).continuous.comp (freeEvolution Q h t).continuous)
      ((freeEvolution Q h t).continuous.comp (weyl h _).continuous)) ψ
  rintro _ ⟨f, rfl⟩
  change weyl h z (freeEvolution Q h t (schwartzIncl volume f)) =
    freeEvolution Q h t
      (weyl h (z.1, z.2 + (t / Q.m) • z.1) (schwartzIncl volume f))
  simp only [freeEvolution_schwartzIncl, weyl_schwartzIncl, weylCLM_freeEvolutionCLM]

/-- Weyl quantization of a transported symbol uses the transpose-sheared displacements. -/
lemma weylQuantization_freeSymbol (Q : FreeParticle d) (h t : ℝ)
    (a : 𝓢(PhaseSpace d, ℂ)) (ψ : SpaceDHilbertSpace d) :
    weylQuantization h (freeSymbol Q t a) ψ =
      ∫ z, 𝓕 a z • weyl h (WithLp.ofLp (freeDualFlowCLE Q t z)) ψ := by
  rw [weylQuantization_apply]
  simp_rw [fourier_freeSymbol]
  have hi := (freeDualFlowCLE_measurePreserving Q t).integral_comp
    (freeDualFlowCLE Q t).toHomeomorph.measurableEmbedding
    (fun z => 𝓕 a (freeDualFlowCLE Q (-t) z) • weyl h (WithLp.ofLp z) ψ)
  simpa only [← freeDualFlowCLE_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using hi.symm

/-- Exact free Egorov correspondence for every Schwartz symbol and every Hilbert-space vector. -/
theorem freeEgorov (Q : FreeParticle d) (h t : ℝ)
    (a : 𝓢(PhaseSpace d, ℂ)) (ψ : SpaceDHilbertSpace d) :
    (freeEvolution Q h t).symm (weylQuantization h a (freeEvolution Q h t ψ)) =
      weylQuantization h (freeSymbol Q t a) ψ := by
  rw [weylQuantization_apply, weylQuantization_freeSymbol]
  change (freeEvolution Q h t).symm.toLinearIsometry
    (∫ z, 𝓕 a z • weyl h (WithLp.ofLp z) (freeEvolution Q h t ψ)) = _
  rw [← (freeEvolution Q h t).symm.toLinearIsometry.integral_comp_comm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [map_smul, weyl_freeEvolution]
    change 𝓕 a z • (freeEvolution Q h t).symm
      (freeEvolution Q h t (weyl h (z.fst, z.snd + (t / Q.m) • z.fst) ψ)) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl

/-- Quantum expectations under free propagation equal expectations of the classically
transported symbol. -/
lemma freeEgorov_expectation (Q : FreeParticle d) (h t : ℝ)
    (a : 𝓢(PhaseSpace d, ℂ)) (ψ : SpaceDHilbertSpace d) :
    ⟪freeEvolution Q h t ψ, weylQuantization h a (freeEvolution Q h t ψ)⟫_ℂ =
      ⟪ψ, weylQuantization h (freeSymbol Q t a) ψ⟫_ℂ := by
  rw [← freeEgorov Q h t a ψ]
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    ((freeEvolution Q h t).symm.inner_map_map (freeEvolution Q h t ψ)
      (weylQuantization h a (freeEvolution Q h t ψ))).symm

end

end QuantumMechanics.Semiclassical
