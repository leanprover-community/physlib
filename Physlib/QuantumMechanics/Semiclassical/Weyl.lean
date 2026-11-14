/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Fourier

/-!
# Weyl quantization of Schwartz symbols

Construct bounded Weyl operators by Fourier synthesis of unitary phase-space displacements.

## i. Overview

The phase space uses the Euclidean product norm, so Mathlib's Fourier transform applies
to Schwartz symbols. For the phase-space frequency `(u, v)`, the Weyl displacement acts by
`exp (2 pi i (u . x + pi h u . v)) f (x + 2 pi h v)`. It preserves the Schwartz space and
the Hilbert-space norm, and depends strongly continuously on its frequency.

For a Schwartz symbol `a`, `weylQuantization h a` is the integral of its Fourier
coefficients against these displacements, taken after application to a Hilbert-space
vector. Integrability is proved before constructing the operator. Its operator norm is
bounded by the `L¹` norm of the Fourier transform of the symbol, uniformly in `h`.
Real-valued symbols give symmetric bounded operators. Fourier synthesis is the definition
used here; identifying it with the coordinate-kernel formula requires a separate argument.

## ii. Key results

- `weyl_norm` : Weyl displacements preserve the Hilbert-space norm
- `weyl_inner` : reversing a displacement gives its adjoint inner-product identity
- `weylQuantization` : the bounded Weyl quantization of a Schwartz symbol
- `weylQuantization_norm_le` : a bound independent of the Planck parameter
- `weylQuantization_inner` : symmetry for real-valued symbols

## iii. Table of contents

- A. Phase space, translation and modulation
- B. Weyl displacements
- C. Fourier synthesis of Schwartz symbols
- D. Real symbols

## iv. References

* V. Guillemin and S. Sternberg, Semi-classical analysis (2010), Section 15.11.2
  for Fourier synthesis of Weyl operators,
  https://math.mit.edu/~vwg/semiclassGuilleminSternberg.pdf.
* J. E. Moyal, Quantum mechanics as a statistical theory (1949),
  https://doi.org/10.1017/S0305004100000487.
* J. Keller and C. Lasser, Propagation of Quantum Expectations with Husimi Functions,
  arXiv:1207.7211v2 (2013), Section 2.1 for the Weyl convention,
  https://arxiv.org/abs/1207.7211.
-/

@[expose] public section

namespace QuantumMechanics.Semiclassical

noncomputable section

open Complex Real MeasureTheory SchwartzMap ContinuousLinearMap
open SpaceDHilbertSpace
open scoped FourierTransform InnerProductSpace

variable {d : ℕ}

/-! ## A. Phase space, translation and modulation -/

/-- Classical phase space with the Euclidean product norm, used for Fourier analysis. -/
abbrev PhaseSpace (d : ℕ) := WithLp 2 (Space d × Space d)

/-- Translation `f(x) -> f(x + a)` as a Hilbert-space linear isometry. -/
def translation (a : Space d) : SpaceDHilbertSpace d →ₗᵢ[ℂ] SpaceDHilbertSpace d :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + a) (measurePreserving_add_right volume a)

/-- Translation agrees with Schwartz translation on the dense Schwartz subspace. -/
lemma translation_schwartzIncl (a : Space d) (f : 𝓢(Space d, ℂ)) :
    translation a (schwartzIncl volume f) =
      schwartzIncl volume (compSubConstCLM ℂ (-a) f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (schwartzIncl volume f)
    (measurePreserving_add_right volume a),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
      (coeFn_toLp f 2 volume),
    coeFn_toLp (compSubConstCLM ℂ (-a) f) 2 volume] with x h₁ h₂ h₃
  calc
    _ = (schwartzIncl volume f) (x + a) := h₁
    _ = f (x + a) := h₂
    _ = _ := by
      change f (x + a) = ((compSubConstCLM ℂ (-a) f).toLp 2 volume) x
      simpa using h₃.symm

/-- Translations depend strongly continuously on the displacement. -/
lemma translation_continuous (ψ : SpaceDHilbertSpace d) :
    Continuous (fun a : Space d => translation a ψ) := by
  let g : Space d → C(Space d, Space d) := fun a => ⟨fun x => x + a, by fun_prop⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (by exact continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_add_right volume a) (by norm_num)

/-- Translation is jointly continuous in displacement and Hilbert-space vector. -/
lemma translation_joint_continuous :
    Continuous (fun aψ : Space d × SpaceDHilbertSpace d => translation aψ.1 aψ.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun a => (translation a).isometry.lipschitzWith) translation_continuous

/-- The Fourier transform converts translation into multiplication by a character. -/
lemma fourier_compSubConst (a : Space d) (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 (compSubConstCLM ℂ a f) ξ = (𝐞 (-⟪a, ξ⟫_ℝ) : ℂ) * 𝓕 f ξ := by
  have hf : (compSubConstCLM ℂ a f : Space d → ℂ) = f ∘ (fun x => x + (-a)) := by
    ext x
    simp [sub_eq_add_neg]
  rw [fourier_coe, hf]
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume
    (innerₗ (Space d)) (f : Space d → ℂ) (-a)) ξ
  change 𝓕 (f ∘ (fun x => x + (-a))) ξ =
    (𝐞 ⟪-a, ξ⟫_ℝ : ℂ) * (𝓕 (f : Space d → ℂ)) ξ at ht
  simpa only [inner_neg_left, fourier_coe] using ht

/-- The inverse Fourier transform converts translation into the opposite character. -/
lemma fourierInv_compSubConst (a : Space d) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    𝓕⁻ (compSubConstCLM ℂ a f) x = (𝐞 ⟪a, x⟫_ℝ : ℂ) * 𝓕⁻ f x := by
  rw [fourierInv_coe, fourierInv_eq_fourier_neg, ← fourier_coe, fourier_compSubConst,
    inner_neg_right, neg_neg, fourierInv_coe, fourierInv_eq_fourier_neg]
  rfl

/-- Multiplication by `exp (2 pi i u . x)` on Schwartz maps, defined by Fourier conjugation. -/
def modulationCLM (u : Space d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (FourierTransform.fourierCLE ℂ 𝓢(Space d, ℂ)).symm.toContinuousLinearMap ∘L
    compSubConstCLM ℂ u ∘L
      (FourierTransform.fourierCLE ℂ 𝓢(Space d, ℂ)).toContinuousLinearMap

/-- The pointwise character formula for modulation. -/
lemma modulationCLM_apply (u : Space d) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    modulationCLM u f x = (𝐞 ⟪u, x⟫_ℝ : ℂ) * f x := by
  change 𝓕⁻ (compSubConstCLM ℂ u (𝓕 f)) x = _
  rw [fourierInv_compSubConst, FourierTransform.fourierInv_fourier_eq]

/-- The Fourier transform converts modulation into translation. -/
lemma fourier_modulationCLM (u : Space d) (f : 𝓢(Space d, ℂ)) :
    𝓕 (modulationCLM u f) = compSubConstCLM ℂ u (𝓕 f) := by
  change 𝓕 (𝓕⁻ (compSubConstCLM ℂ u (𝓕 f))) = _
  exact FourierTransform.fourier_fourierInv_eq _

/-- Modulation as a Hilbert-space linear isometry, obtained by Fourier conjugation. -/
def modulation (u : Space d) : SpaceDHilbertSpace d →ₗᵢ[ℂ] SpaceDHilbertSpace d :=
  (fourierUnitary d).symm.toLinearIsometry.comp
    ((translation (-u)).comp (fourierUnitary d).toLinearIsometry)

/-- Hilbert-space modulation agrees with modulation of a Schwartz representative. -/
lemma modulation_schwartzIncl (u : Space d) (f : 𝓢(Space d, ℂ)) :
    modulation u (schwartzIncl volume f) = schwartzIncl volume (modulationCLM u f) := by
  change 𝓕⁻ (translation (-u) (𝓕 (schwartzIncl volume f))) = _
  rw [schwartzIncl_fourier_eq, translation_schwartzIncl, neg_neg, schwartzIncl_fourierInv_eq]
  rfl

/-- Modulations depend strongly continuously on their frequency. -/
lemma modulation_continuous (ψ : SpaceDHilbertSpace d) :
    Continuous (fun u : Space d => modulation u ψ) := by
  exact (fourierUnitary d).symm.continuous.comp
    ((translation_continuous (fourierUnitary d ψ)).comp continuous_neg)

/-- Modulation is jointly continuous in frequency and Hilbert-space vector. -/
lemma modulation_joint_continuous :
    Continuous (fun uψ : Space d × SpaceDHilbertSpace d => modulation uψ.1 uψ.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun u => (modulation u).isometry.lipschitzWith) modulation_continuous

/-! ## B. Weyl displacements -/

/-- The Weyl displacement associated to the frequency `(u, v)`, on Schwartz maps. -/
def weylCLM (h : ℝ) (z : Space d × Space d) :
    𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) •
    (modulationCLM z.1 ∘L compSubConstCLM ℂ (-(2 * π * h) • z.2))

/-- The Weyl displacement is a translation with the symmetric midpoint phase. -/
lemma weylCLM_apply (h : ℝ) (z : Space d × Space d)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    weylCLM h z f x = (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) *
      (𝐞 ⟪z.1, x⟫_ℝ : ℂ) * f (x + (2 * π * h) • z.2) := by
  simp [weylCLM, modulationCLM_apply, sub_eq_add_neg, mul_assoc]

/-- The Fourier-coordinate formula for a Weyl displacement. -/
lemma fourier_weylCLM (h : ℝ) (z : Space d × Space d)
    (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 (weylCLM h z f) ξ = (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) *
      (𝐞 (-⟪-(2 * π * h) • z.2, ξ - z.1⟫_ℝ) : ℂ) * 𝓕 f (ξ - z.1) := by
  simp only [weylCLM, smul_apply, comp_apply, FourierTransform.fourier_smul,
    fourier_modulationCLM, compSubConstCLM_apply, fourier_compSubConst, smul_eq_mul,
    mul_assoc]

/-- The Weyl displacement on the full Hilbert space, with Mathlib Fourier normalization. -/
def weyl (h : ℝ) (z : Space d × Space d) :
    SpaceDHilbertSpace d →L[ℂ] SpaceDHilbertSpace d :=
  (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) •
    ((modulation z.1).toContinuousLinearMap ∘L
      (translation ((2 * π * h) • z.2)).toContinuousLinearMap)

/-- Weyl displacements preserve the Hilbert-space norm for every real Planck parameter. -/
lemma weyl_norm (h : ℝ) (z : Space d × Space d) (ψ : SpaceDHilbertSpace d) :
    ‖weyl h z ψ‖ = ‖ψ‖ := by
  change ‖(𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) •
    modulation z.1 (translation ((2 * π * h) • z.2) ψ)‖ = _
  simp [norm_smul, (modulation z.1).norm_map, (translation _).norm_map]

/-- Weyl displacements preserve and agree with their action on the Schwartz subspace. -/
lemma weyl_schwartzIncl (h : ℝ) (z : Space d × Space d) (f : 𝓢(Space d, ℂ)) :
    weyl h z (schwartzIncl volume f) = schwartzIncl volume (weylCLM h z f) := by
  change (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) •
    modulation z.1 (translation ((2 * π * h) • z.2) (schwartzIncl volume f)) = _
  rw [translation_schwartzIncl, modulation_schwartzIncl, ← map_smul]
  simp only [weylCLM, smul_apply, comp_apply, neg_smul]

/-- For a fixed vector, the Weyl displacement depends continuously on its frequency. -/
lemma weyl_continuous (h : ℝ) (ψ : SpaceDHilbertSpace d) :
    Continuous (fun z : Space d × Space d => weyl h z ψ) := by
  change Continuous (fun z : Space d × Space d =>
    (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) •
      modulation z.1 (translation ((2 * π * h) • z.2) ψ))
  have hp : Continuous (fun z : Space d × Space d => π * h * ⟪z.1, z.2⟫_ℝ) :=
    continuous_const.mul (continuous_fst.inner continuous_snd)
  have hc : Continuous (fun z : Space d × Space d =>
      (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ)) :=
    (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).comp
      (continuous_fourierChar.comp hp)
  have ht : Continuous (fun z : Space d × Space d =>
      translation ((2 * π * h) • z.2) ψ) :=
    (translation_continuous ψ).comp (continuous_snd.const_smul (2 * π * h))
  have hm : Continuous (fun z : Space d × Space d =>
      modulation z.1 (translation ((2 * π * h) • z.2) ψ)) :=
    (modulation_joint_continuous (d := d)).comp
      (f := fun z : Space d × Space d =>
        (z.1, translation ((2 * π * h) • z.2) ψ)) (continuous_fst.prodMk ht)
  exact hc.smul hm

/-- Opposite Weyl displacements cancel on Schwartz maps. -/
lemma weylCLM_neg_apply (h : ℝ) (z : Space d × Space d) (f : 𝓢(Space d, ℂ)) :
    weylCLM h (-z) (weylCLM h z f) = f := by
  ext1 x
  simp only [weylCLM_apply, Prod.fst_neg, Prod.snd_neg]
  have hx : x + (2 * π * h) • -z.2 + (2 * π * h) • z.2 = x := by module
  rw [hx]
  simp only [mul_assoc]
  have hp : (𝐞 (π * h * ⟪-z.1, -z.2⟫_ℝ) : ℂ) *
      (𝐞 ⟪-z.1, x⟫_ℝ : ℂ) *
        (𝐞 (π * h * ⟪z.1, z.2⟫_ℝ) : ℂ) *
          (𝐞 ⟪z.1, x + (2 * π * h) • -z.2⟫_ℝ : ℂ) = 1 := by
    have hs : π * h * ⟪-z.1, -z.2⟫_ℝ + ⟪-z.1, x⟫_ℝ +
        π * h * ⟪z.1, z.2⟫_ℝ + ⟪z.1, x + (2 * π * h) • -z.2⟫_ℝ = 0 := by
      simp only [inner_neg_left, inner_neg_right, inner_add_right, inner_smul_right]
      ring
    simp only [← Circle.coe_mul, ← AddChar.map_add_eq_mul, hs]
    simp
  simpa only [mul_assoc, one_mul] using congrArg (fun c : ℂ => c * f x) hp

/-- Opposite Weyl displacements cancel on the full Hilbert space. -/
lemma weyl_neg_apply (h : ℝ) (z : Space d × Space d) (ψ : SpaceDHilbertSpace d) :
    weyl h (-z) (weyl h z ψ) = ψ := by
  refine (SchwartzSubmodule.dense d volume).induction ?_
    (isClosed_eq ((weyl h (-z)).continuous.comp (weyl h z).continuous) continuous_id) ψ
  rintro _ ⟨f, rfl⟩
  change weyl h (-z) (weyl h z (schwartzIncl volume f)) = schwartzIncl volume f
  rw [weyl_schwartzIncl, weyl_schwartzIncl, weylCLM_neg_apply]

/-- The adjoint inner-product identity for Weyl displacements. -/
lemma weyl_inner (h : ℝ) (z : Space d × Space d) (ψ φ : SpaceDHilbertSpace d) :
    ⟪weyl h z ψ, φ⟫_ℂ = ⟪ψ, weyl h (-z) φ⟫_ℂ := by
  let W : SpaceDHilbertSpace d →ₗᵢ[ℂ] SpaceDHilbertSpace d :=
    { (weyl h z).toLinearMap with norm_map' := weyl_norm h z }
  have hW := W.inner_map_map ψ (weyl h (-z) φ)
  change ⟪weyl h z ψ, weyl h z (weyl h (-z) φ)⟫_ℂ = _ at hW
  have hinv := weyl_neg_apply h (-z) φ
  simp only [neg_neg] at hinv
  rwa [hinv] at hW

/-! ## C. Fourier synthesis of Schwartz symbols -/

/-- Fourier synthesis of a Schwartz symbol is integrable after application to a vector. -/
lemma weyl_integrable (h : ℝ) (a : 𝓢(PhaseSpace d, ℂ))
    (ψ : SpaceDHilbertSpace d) :
    Integrable (fun z => 𝓕 a z • weyl h (WithLp.ofLp z) ψ) := by
  refine Integrable.mono' ((𝓕 a).integrable.norm.mul_const ‖ψ‖)
    (((𝓕 a).continuous).smul
      ((weyl_continuous h ψ).comp
        (WithLp.prod_continuous_ofLp 2 _ _))).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z => by rw [norm_smul, weyl_norm]

/-- The norm of the synthesized vector is bounded by the Fourier `L¹` norm of the symbol. -/
lemma weyl_integral_norm_le (h : ℝ) (a : 𝓢(PhaseSpace d, ℂ))
    (ψ : SpaceDHilbertSpace d) :
    ‖∫ z, 𝓕 a z • weyl h (WithLp.ofLp z) ψ‖ ≤ (∫ z, ‖𝓕 a z‖) * ‖ψ‖ := by
  calc
    _ ≤ ∫ z, ‖𝓕 a z • weyl h (WithLp.ofLp z) ψ‖ := norm_integral_le_integral_norm _
    _ = _ := by simp_rw [norm_smul, weyl_norm, integral_mul_const]

/-- Weyl quantization of a Schwartz symbol, as a bounded operator on the full Hilbert space.
The Bochner integral is taken after applying each displacement to the input vector. -/
def weylQuantization (h : ℝ) (a : 𝓢(PhaseSpace d, ℂ)) :
    SpaceDHilbertSpace d →L[ℂ] SpaceDHilbertSpace d :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ∫ z, 𝓕 a z • weyl h (WithLp.ofLp z) ψ
      map_add' := fun ψ φ => by
        simp_rw [map_add, smul_add]
        exact integral_add (weyl_integrable h a ψ) (weyl_integrable h a φ)
      map_smul' := fun c ψ => by
        simp_rw [map_smul, smul_comm (𝓕 a _)]
        exact integral_smul c _ }
    (∫ z, ‖𝓕 a z‖) (weyl_integral_norm_le h a)

/-- The convergent Fourier synthesis formula for Weyl quantization. -/
lemma weylQuantization_apply (h : ℝ) (a : 𝓢(PhaseSpace d, ℂ))
    (ψ : SpaceDHilbertSpace d) :
    weylQuantization h a ψ = ∫ z, 𝓕 a z • weyl h (WithLp.ofLp z) ψ := rfl

/-- The Weyl operator norm is bounded uniformly in `h` by the Fourier `L¹` norm. -/
lemma weylQuantization_norm_le (h : ℝ) (a : 𝓢(PhaseSpace d, ℂ)) :
    ‖weylQuantization h a‖ ≤ ∫ z, ‖𝓕 a z‖ :=
  opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) (weyl_integral_norm_le h a)

/-- Weyl quantization is additive in its symbol. -/
lemma weylQuantization_add (h : ℝ) (a b : 𝓢(PhaseSpace d, ℂ)) :
    weylQuantization h (a + b) = weylQuantization h a + weylQuantization h b := by
  ext1 ψ
  simp only [weylQuantization_apply, FourierTransform.fourier_add, add_apply, add_smul]
  exact integral_add (weyl_integrable h a ψ) (weyl_integrable h b ψ)

/-- Weyl quantization is complex linear in its symbol. -/
lemma weylQuantization_smul (h : ℝ) (c : ℂ) (a : 𝓢(PhaseSpace d, ℂ)) :
    weylQuantization h (c • a) = c • weylQuantization h a := by
  ext1 ψ
  simp only [weylQuantization_apply, FourierTransform.fourier_smul, smul_apply, smul_assoc,
    integral_smul]

/-! ## D. Real symbols -/

/-- The Fourier transform of a real-valued symbol has conjugate symmetry. -/
lemma fourier_realSymbol_neg (a : 𝓢(PhaseSpace d, ℂ))
    (ha : ∀ z, starRingEnd ℂ (a z) = a z) (z : PhaseSpace d) :
    starRingEnd ℂ (𝓕 a z) = 𝓕 a (-z) := by
  simp only [fourier_coe, Real.fourier_eq, ← integral_conj, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp only
    simp only [map_mul, ha, inner_neg_right, neg_neg, Real.fourierChar_apply,
      ← Complex.exp_conj]
    congr 2
    simp only [conj_ofReal, conj_I]
    push_cast
    ring

/-- A real-valued Schwartz symbol quantizes to a symmetric bounded operator. -/
lemma weylQuantization_inner (h : ℝ) (a : 𝓢(PhaseSpace d, ℂ))
    (ha : ∀ z, starRingEnd ℂ (a z) = a z) (ψ φ : SpaceDHilbertSpace d) :
    ⟪weylQuantization h a ψ, φ⟫_ℂ = ⟪ψ, weylQuantization h a φ⟫_ℂ := by
  rw [weylQuantization_apply, weylQuantization_apply]
  calc
    _ = starRingEnd ℂ (∫ z, ⟪φ, 𝓕 a z • weyl h (WithLp.ofLp z) ψ⟫_ℂ) := by
      rw [integral_inner (weyl_integrable h a ψ)]
      exact (inner_conj_symm _ _).symm
    _ = ∫ z, 𝓕 a (-z) * ⟪ψ, weyl h (-WithLp.ofLp z) φ⟫_ℂ := by
      rw [← integral_conj]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [inner_smul_right, map_mul, fourier_realSymbol_neg a ha,
          inner_conj_symm, weyl_inner]
    _ = ∫ z : PhaseSpace d, 𝓕 a z * ⟪ψ, weyl h (WithLp.ofLp z) φ⟫_ℂ := by
      exact integral_neg_eq_self (fun z : PhaseSpace d =>
        𝓕 a z * ⟪ψ, weyl h (WithLp.ofLp z) φ⟫_ℂ) volume
    _ = _ := by
      simpa only [inner_smul_right] using integral_inner (𝕜 := ℂ) (weyl_integrable h a φ) ψ

end

end QuantumMechanics.Semiclassical
