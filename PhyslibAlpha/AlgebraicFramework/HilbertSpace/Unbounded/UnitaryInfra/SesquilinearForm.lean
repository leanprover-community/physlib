/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.WeakIntegral
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.RCLike.ContinuousMap
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Infrastructure for the bounded-unitary spectral theorem: the sesquilinear form

Builds, from a bounded unitary `U`'s continuous functional calculus, the real-valued spectral
scalar measures `cfcScalarMeasure`/`polarizedCfcScalarMeasure` via the Riesz-Markov-Kakutani
theorem and polarization, proves their (sesqui)linearity and boundedness, and assembles them into
`cfcSesquilinearForm`. Continued in `UnitaryInfra/SpectralMeasure.lean`, which turns this
form into the projection-valued `cfcSpectralMeasure`.

This file proves, for any bounded normal operator `U` on a complex Hilbert space, the
continuous-functional-calculus construction of its weak-operator spectral measure
(`WOTSpectralMeasure.cfcSpectralMeasure` and friends, completed in `SpectralMeasure.lean`) — the
existence half of the bounded spectral theorem that `Cayley/Certificate.lean`'s
`BoundedNormalSpectralData` and `BoundedUnitarySpectralData` interfaces record the shape of.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]

/-- A positive scalar functional on a compact spectrum. -/
structure CompactPositiveFunctional where
  /-- The underlying positive linear functional. -/
  functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ

namespace CompactPositiveFunctional

variable (Λ : CompactPositiveFunctional (X := X))

/-- The regular Borel measure represented by the scalar functional. -/
noncomputable def measure : Measure X := RealRMK.rieszMeasure Λ.functional

instance regular : (Λ.measure).Regular := by
  dsimp [measure]
  infer_instance

lemma integral (f : CompactlySupportedContinuousMap X ℝ) :
    ∫ x, f x ∂Λ.measure = Λ.functional f := by
  exact RealRMK.integral_rieszMeasure Λ.functional f

lemma integral_eq_zero_of_support_disjoint {f : CompactlySupportedContinuousMap X ℝ}
    {S : Set X} (hS_meas : MeasurableSet S) (hS : ∀ x ∈ S, f x = 0) :
    ∫ x, f x ∂(Λ.measure.restrict S) = 0 := by
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hS_meas] with x hx
  exact hS x hx

lemma measure_ext {Λ₁ Λ₂ : CompactPositiveFunctional (X := X)}
    (hΛ : ∀ f, Λ₁.functional f = Λ₂.functional f) :
    Λ₁.measure = Λ₂.measure := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [Λ₁.integral, Λ₂.integral, hΛ]

end CompactPositiveFunctional

/-! ## Range-map/vector-integral bridge -/

section VectorMeasureBridge

variable {X E F G K : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

/-- Pull a bilinear pairing back along a continuous linear map in its second argument. -/
def pullbackPairing (L : F →L[ℝ] G) (B : E →L[ℝ] G →L[ℝ] K) :
    E →L[ℝ] F →L[ℝ] K :=
  (B.flip.comp L).flip

omit [CompleteSpace K] in
@[nolint unusedArguments]
lemma transpose_mapRange_pullback (μ : VectorMeasure X F) (L : F →L[ℝ] G)
    (B : E →L[ℝ] G →L[ℝ] K) :
    (μ.mapRange L.toAddMonoidHom L.continuous).transpose B =
      μ.transpose (pullbackPairing L B) := by
  ext s hs
  simp [VectorMeasure.transpose, pullbackPairing, ContinuousLinearMap.flip_apply]
  rfl

omit [CompleteSpace K] in
lemma integral_mapRange_pullback (μ : VectorMeasure X F) (L : F →L[ℝ] G)
    (B : E →L[ℝ] G →L[ℝ] K) (f : X → E)
    (hfμ : μ.Integrable f) (hfL : (μ.mapRange L.toAddMonoidHom L.continuous).Integrable f) :
    ∫ᵛ x, f x ∂[B; μ.mapRange L.toAddMonoidHom L.continuous] =
      ∫ᵛ x, f x ∂[pullbackPairing L B; μ] := by
  have hL := MeasureTheory.VectorMeasure.integral_eq_setToFun_transpose
    (μ := μ.mapRange L.toAddMonoidHom L.continuous) (B := B) (f := f) hfL
  have hμ := MeasureTheory.VectorMeasure.integral_eq_setToFun_transpose
    (μ := μ) (B := pullbackPairing L B) (f := f) hfμ
  have htranspose := transpose_mapRange_pullback (μ := μ) (L := L) (B := B)
  calc
    _ = _ := hL
    _ = _ := by simp only [htranspose]
    _ = _ := hμ.symm

end VectorMeasureBridge

/-! ## Complexification of finite signed measures -/

section Complexification

/-- The pairing used for a complex-valued function against a real signed measure. -/
def complexSignedPairing : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip

/-- Postcompose a pairing `E →L[ℝ] F →L[ℝ] G` with a continuous linear map `G →L[ℝ] K`, giving a
pairing `E →L[ℝ] F →L[ℝ] K`. -/
def postcomposePairing {E F G K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (C : G →L[ℝ] K) (B : E →L[ℝ] F →L[ℝ] G) :
    E →L[ℝ] F →L[ℝ] K :=
  { toFun := fun e => C.comp (B e)
    map_add' := by
      intro x y
      ext z
      simp
    map_smul' := by
      intro c x
      ext z
      simp
    cont := by fun_prop }

lemma transpose_postcomposePairing_apply {X E F G K : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (μ : VectorMeasure X F) (C : G →L[ℝ] K) (B : E →L[ℝ] F →L[ℝ] G)
    (s : Set X) (x : E) :
    μ.transpose (postcomposePairing C B) s x = C (μ.transpose B s x) := by
  simp [VectorMeasure.transpose, postcomposePairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, VectorMeasure.mapRange_apply]
  rw [VectorMeasure.mapRange_apply (v := μ) (f := B.flip.toAddMonoidHom)
    B.flip.continuous]
  change C (B x (μ s)) = C (B x (μ s))
  rfl

lemma setToL1S_compContinuousLinearMap {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : Set X → E →L[ℝ] F) (T' : Set X → E →L[ℝ] G) (C : F →L[ℝ] G)
    {μ : Measure X}
    (h : ∀ s, MeasurableSet s → ∀ x, T' s x = C (T s x))
    (f : X →₁ₛ[μ] E) :
    L1.SimpleFunc.setToL1S T' f = C (L1.SimpleFunc.setToL1S T f) := by
  rw [L1.SimpleFunc.setToL1S_eq_setToSimpleFunc,
    L1.SimpleFunc.setToL1S_eq_setToSimpleFunc]
  simp only [SimpleFunc.setToSimpleFunc]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [h _ (SimpleFunc.measurableSet_fiber (Lp.simpleFunc.toSimpleFunc f) x)]

lemma setToL1_compContinuousLinearMap {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure X} {T : Set X → E →L[ℝ] F} {T' : Set X → E →L[ℝ] G}
    {C₀ C₁ : ℝ} (hT : DominatedFinMeasAdditive μ T C₀)
    (hT' : DominatedFinMeasAdditive μ T' C₁) (C : F →L[ℝ] G)
    (h : ∀ s, MeasurableSet s → ∀ x, T' s x = C (T s x))
    (f : X →₁[μ] E) :
    L1.setToL1 hT' f = C (L1.setToL1 hT f) := by
  apply L1.setToL1_unique hT' (A := C.comp (L1.setToL1 hT))
  intro g
  change L1.SimpleFunc.setToL1SCLM X E μ hT' g =
    C (L1.setToL1 hT (Lp.simpleFunc.coeToLp X E ℝ g))
  rw [L1.setToL1_apply_coeToLp]
  change L1.SimpleFunc.setToL1S T' g = C (L1.SimpleFunc.setToL1S T g)
  exact setToL1S_compContinuousLinearMap T T' C h g

lemma setToFun_compContinuousLinearMap {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure X} {T : Set X → E →L[ℝ] F} {T' : Set X → E →L[ℝ] G}
    {C₀ C₁ : ℝ} (hT : DominatedFinMeasAdditive μ T C₀)
    (hT' : DominatedFinMeasAdditive μ T' C₁) (C : F →L[ℝ] G)
    (h : ∀ s, MeasurableSet s → ∀ x, T' s x = C (T s x))
    {f : X → E} (hf : Integrable f μ) :
    MeasureTheory.setToFun μ T' hT' f = C (MeasureTheory.setToFun μ T hT f) := by
  rw [MeasureTheory.setToFun_eq hT' hf, MeasureTheory.setToFun_eq hT hf]
  exact setToL1_compContinuousLinearMap hT hT' C h (hf.toL1 f)

lemma integral_postcomposePairing {X E F G K : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (C : G →L[ℝ] K)
    (f : X → E) (hf : μ.Integrable f) :
    C (∫ᵛ x, f x ∂[B; μ]) =
      ∫ᵛ x, f x ∂[postcomposePairing C B; μ] := by
  rw [MeasureTheory.VectorMeasure.integral_eq_setToFun,
    MeasureTheory.VectorMeasure.integral_eq_setToFun]
  symm
  exact setToFun_compContinuousLinearMap
    (μ := μ.variation) (T := μ.transpose B)
    (T' := μ.transpose (postcomposePairing C B))
    (hT := MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure μ B)
    (hT' := MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure μ
      (postcomposePairing C B)) C
    (fun s hs x => transpose_postcomposePairing_apply μ C B s x) hf

/-- Multiplication by `I`, followed by the canonical embedding of a real signed measure into a
complex vector measure. -/
def imaginaryOfRealCLM : ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ) Complex.I).comp Complex.ofRealCLM

@[simp]
lemma imaginaryOfRealCLM_apply (r : ℝ) : imaginaryOfRealCLM r = Complex.I * r := by
  simp [imaginaryOfRealCLM, ContinuousLinearMap.comp_apply]

lemma signedMeasure_toComplexMeasure_eq_add_mapRange
    {Y : Type*} [MeasurableSpace Y] (s t : SignedMeasure Y) :
    s.toComplexMeasure t =
      s.mapRange Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous +
        t.mapRange imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous := by
  ext S hS
  simp only [SignedMeasure.toComplexMeasure_apply,
    add_apply, VectorMeasure.mapRange_apply
      (v := s) (f := Complex.ofRealCLM.toAddMonoidHom) Complex.ofRealCLM.continuous,
    VectorMeasure.mapRange_apply (v := t) (f := imaginaryOfRealCLM.toAddMonoidHom)
      imaginaryOfRealCLM.continuous]
  change (⟨s S, t S⟩ : ℂ) = (s S : ℂ) + Complex.I * (t S : ℂ)
  apply Complex.ext <;> simp

lemma integral_toComplexMeasure_eq_add_mapRange
    {X : Type*} [MeasurableSpace X] (s t : SignedMeasure X) (f : X → ℂ)
    (hs : (s.mapRange Complex.ofRealCLM.toAddMonoidHom
      Complex.ofRealCLM.continuous).Integrable f)
    (ht : (t.mapRange imaginaryOfRealCLM.toAddMonoidHom
      imaginaryOfRealCLM.continuous).Integrable f) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); s.toComplexMeasure t] =
      (∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        s.mapRange Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous]) +
      ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        t.mapRange imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous] := by
  rw [signedMeasure_toComplexMeasure_eq_add_mapRange]
  exact MeasureTheory.VectorMeasure.integral_add_vectorMeasure hs ht

lemma pullbackPairing_ofReal_lsmul :
    pullbackPairing Complex.ofRealCLM
      (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)) = complexSignedPairing := by
  ext z
  simp [pullbackPairing, complexSignedPairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply]

lemma integral_mapRange_ofReal_signedMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      μ.toSignedMeasure.mapRange Complex.ofRealCLM.toAddMonoidHom
        Complex.ofRealCLM.continuous] =
      ∫ᵛ x, f x ∂<•μ.toSignedMeasure := by
  let μs := μ.toSignedMeasure
  have hμ : μs.Integrable f := by
    change Integrable f μs.variation
    rw [MeasureTheory.Measure.variation_toSignedMeasure]
    exact hf
  have hvar : (μs.mapRange Complex.ofRealCLM.toAddMonoidHom
      Complex.ofRealCLM.continuous).variation ≤ μs.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    rw [VectorMeasure.mapRange_apply (v := μs)
      (f := Complex.ofRealCLM.toAddMonoidHom) Complex.ofRealCLM.continuous]
    change ‖(μs s : ℂ)‖ₑ ≤ _
    have hn : ‖(μs s : ℂ)‖ₑ = ‖μs s‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      apply congrArg ENNReal.ofNNReal
      apply NNReal.eq
      exact Complex.norm_real _
    rw [hn]
    exact VectorMeasure.enorm_measure_le_variation μs s
  have hmap : (μs.mapRange Complex.ofRealCLM.toAddMonoidHom
      Complex.ofRealCLM.continuous).Integrable f := by
    exact hf.mono_measure (hvar.trans_eq
      (MeasureTheory.Measure.variation_toSignedMeasure (μ := μ)))
  rw [integral_mapRange_pullback μs Complex.ofRealCLM
    (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)) f hμ hmap]
  rw [pullbackPairing_ofReal_lsmul]
  change ∫ᵛ x, f x ∂<•μs = ∫ᵛ x, f x ∂<•μs
  rfl

lemma integrable_mapRange_toSignedMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (L : ℝ →L[ℝ] ℂ) (hL : ∀ r : ℝ, ‖L r‖ = ‖r‖)
    (f : X → ℂ) (hf : Integrable f μ) :
    (μ.toSignedMeasure.mapRange L.toAddMonoidHom L.continuous).Integrable f := by
  let μs := μ.toSignedMeasure
  have hμ : μs.Integrable f := by
    change Integrable f μs.variation
    rw [MeasureTheory.Measure.variation_toSignedMeasure]
    exact hf
  have hvar : (μs.mapRange L.toAddMonoidHom L.continuous).variation ≤ μs.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    rw [VectorMeasure.mapRange_apply (v := μs) (f := L.toAddMonoidHom) L.continuous]
    change ‖L (μs s)‖ₑ ≤ _
    have hn : ‖L (μs s)‖ₑ = ‖μs s‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      apply congrArg ENNReal.ofNNReal
      apply NNReal.eq
      exact hL _
    rw [hn]
    exact VectorMeasure.enorm_measure_le_variation μs s
  exact hf.mono_measure (hvar.trans_eq
    (MeasureTheory.Measure.variation_toSignedMeasure (μ := μ)))

lemma integrable_mapRange_ofReal_signedMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ) :
    (μ.toSignedMeasure.mapRange Complex.ofRealCLM.toAddMonoidHom
      Complex.ofRealCLM.continuous).Integrable f := by
  apply integrable_mapRange_toSignedMeasure μ Complex.ofRealCLM (by
    intro r
    exact Complex.norm_real r) f hf

lemma integrable_mapRange_imaginaryOfReal_signedMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ) :
    (μ.toSignedMeasure.mapRange imaginaryOfRealCLM.toAddMonoidHom
      imaginaryOfRealCLM.continuous).Integrable f := by
  apply integrable_mapRange_toSignedMeasure μ imaginaryOfRealCLM (by
    intro r
    rw [imaginaryOfRealCLM_apply]
    simp) f hf

lemma mapRange_sub_toSignedMeasure
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (L : ℝ →L[ℝ] ℂ) :
    (μ.toSignedMeasure - ν.toSignedMeasure).mapRange L.toAddMonoidHom L.continuous =
      μ.toSignedMeasure.mapRange L.toAddMonoidHom L.continuous -
        ν.toSignedMeasure.mapRange L.toAddMonoidHom L.continuous := by
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change L ((μ.toSignedMeasure - ν.toSignedMeasure) S) =
    L (μ.toSignedMeasure S) - L (ν.toSignedMeasure S)
  rw [sub_apply]
  simp

lemma integral_mapRange_ofReal_signedDifference
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ) (f : X → ℂ) (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      (c • (μ.toSignedMeasure - ν.toSignedMeasure)).mapRange
        Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous] =
      c • ((∫ x, f x ∂μ) - ∫ x, f x ∂ν) := by
  have hμ' := integrable_mapRange_ofReal_signedMeasure μ f hμ
  have hν' := integrable_mapRange_ofReal_signedMeasure ν f hν
  rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure μ ν]
  rw [MeasureTheory.VectorMeasure.integral_smul_vectorMeasure,
    MeasureTheory.VectorMeasure.integral_sub_vectorMeasure hμ' hν']
  rw [integral_mapRange_ofReal_signedMeasure μ f hμ,
    integral_mapRange_ofReal_signedMeasure ν f hν]
  rw [MeasureTheory.VectorMeasure.integral_toSignedMeasure,
    MeasureTheory.VectorMeasure.integral_toSignedMeasure]

/-- Multiplication by `I`, as a continuous ℝ-linear map on `ℂ`. -/
def imaginaryMulCLM : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ) Complex.I

@[simp]
lemma imaginaryMulCLM_apply (z : ℂ) : imaginaryMulCLM z = Complex.I * z := by
  rfl

/-- The `ℂ →L[ℝ] ℝ →L[ℝ] ℂ` pairing post-composed with multiplication by `I`. -/
def imaginarySignedPairing : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  postcomposePairing imaginaryMulCLM complexSignedPairing

lemma pullbackPairing_imaginaryOfReal_lsmul :
    pullbackPairing imaginaryOfRealCLM
      (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)) = imaginarySignedPairing := by
  ext z
  simp [pullbackPairing, imaginarySignedPairing, imaginaryMulCLM,
    complexSignedPairing, postcomposePairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply]
  ring

lemma integral_mapRange_imaginaryOfReal_signedMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      μ.toSignedMeasure.mapRange imaginaryOfRealCLM.toAddMonoidHom
        imaginaryOfRealCLM.continuous] =
      Complex.I * (∫ x, f x ∂μ) := by
  let μs := μ.toSignedMeasure
  have hμ : μs.Integrable f := by
    change Integrable f μs.variation
    rw [MeasureTheory.Measure.variation_toSignedMeasure]
    exact hf
  have hvar : (μs.mapRange imaginaryOfRealCLM.toAddMonoidHom
      imaginaryOfRealCLM.continuous).variation ≤ μs.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    rw [VectorMeasure.mapRange_apply (v := μs)
      (f := imaginaryOfRealCLM.toAddMonoidHom) imaginaryOfRealCLM.continuous]
    change ‖imaginaryOfRealCLM (μs s)‖ₑ ≤ _
    rw [imaginaryOfRealCLM_apply]
    have hn : ‖Complex.I * (μs s : ℂ)‖ₑ = ‖μs s‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      apply congrArg ENNReal.ofNNReal
      apply NNReal.eq
      simp
    rw [hn]
    exact VectorMeasure.enorm_measure_le_variation μs s
  have hmap : (μs.mapRange imaginaryOfRealCLM.toAddMonoidHom
      imaginaryOfRealCLM.continuous).Integrable f := by
    exact hf.mono_measure (hvar.trans_eq
      (MeasureTheory.Measure.variation_toSignedMeasure (μ := μ)))
  rw [integral_mapRange_pullback μs imaginaryOfRealCLM
    (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)) f hμ hmap]
  rw [pullbackPairing_imaginaryOfReal_lsmul]
  change (∫ᵛ x, f x ∂[postcomposePairing imaginaryMulCLM complexSignedPairing; μs]) = _
  rw [← integral_postcomposePairing μs complexSignedPairing imaginaryMulCLM f hμ]
  change imaginaryMulCLM (∫ᵛ x, f x ∂<•μs) = _
  rw [MeasureTheory.VectorMeasure.integral_toSignedMeasure]
  simp [imaginaryMulCLM]

lemma integral_mapRange_imaginaryOfReal_signedDifference
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ) (f : X → ℂ) (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      (c • (μ.toSignedMeasure - ν.toSignedMeasure)).mapRange
        imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous] =
      c • (Complex.I * ((∫ x, f x ∂μ) - ∫ x, f x ∂ν)) := by
  have hμ' := integrable_mapRange_imaginaryOfReal_signedMeasure μ f hμ
  have hν' := integrable_mapRange_imaginaryOfReal_signedMeasure ν f hν
  rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure μ ν]
  rw [MeasureTheory.VectorMeasure.integral_smul_vectorMeasure,
    MeasureTheory.VectorMeasure.integral_sub_vectorMeasure hμ' hν']
  rw [integral_mapRange_imaginaryOfReal_signedMeasure μ f hμ,
    integral_mapRange_imaginaryOfReal_signedMeasure ν f hν]
  simp [sub_eq_add_neg]
  ring

end Complexification

/-! ## Finiteness of the polarized scalar measures -/

set_option maxHeartbeats 3000000 in
lemma isFiniteMeasure_toComplexMeasure
    {X : Type*} [MeasurableSpace X] (s t : MeasureTheory.SignedMeasure X)
    [IsFiniteMeasure s.variation] [IsFiniteMeasure t.variation] :
    IsFiniteMeasure (s.toComplexMeasure t).variation := by
  apply isFiniteMeasure_of_le (s.variation + t.variation)
  apply MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le
  intro A hA
  calc
    ‖(s.toComplexMeasure t) A‖ₑ = ‖(⟨s A, t A⟩ : ℂ)‖ₑ := rfl
    _ = ‖(s A : ℂ) + (t A : ℂ) * Complex.I‖ₑ := by
      congr 1
      apply Complex.ext <;> simp
    _ ≤ ‖(s A : ℂ)‖ₑ + ‖(t A : ℂ) * Complex.I‖ₑ := enorm_add_le _ _
    _ = ‖s A‖ₑ + ‖t A‖ₑ := by
      simp [enorm_eq_nnnorm]
    _ ≤ s.variation A + t.variation A :=
      add_le_add (MeasureTheory.VectorMeasure.enorm_measure_le_variation s A)
        (MeasureTheory.VectorMeasure.enorm_measure_le_variation t A)

/-! ## A general positive-contraction norm estimate

This is a standalone fact about `H →L[ℂ] H` for any complex Hilbert space `H`, not specific to the
continuous functional calculus of a fixed normal operator: it is Step 2 of the idempotency
argument below, quantifying `0 ≤ A ≤ 1 ⟹ A ^ 2 ≤ A` into a norm bound. -/

section PositiveContraction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The positive-contraction norm estimate.** If `0 ≤ A ≤ 1` in the Loewner order on
`H →L[ℂ] H`, then `‖A x‖ ^ 2 ≤ re ⟪x, A x⟫` for every `x`.  Proved from `A ^ 2 ≤ A`
(`CStarAlgebra.pow_antitone`, using the `CStarAlgebra (H →L[ℂ] H)` instance) and self-adjointness
of `A` to identify `⟪x, A ^ 2 x⟫` with `⟪A x, A x⟫ = ‖A x‖ ^ 2`. -/
lemma norm_sq_le_inner_of_isPositive_of_le_one {A : H →L[ℂ] H}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (x : H) :
    ‖A x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_ℂ := by
  have hApos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA0
  have hAsa : IsSelfAdjoint A := hApos.isSelfAdjoint
  have hanti : Antitone (A ^ · : ℕ → H →L[ℂ] H) := CStarAlgebra.pow_antitone hA0 hA1
  have hsq_le : A ^ 2 ≤ A ^ 1 := hanti (by norm_num)
  rw [pow_one] at hsq_le
  have hpos_diff : ContinuousLinearMap.IsPositive (A - A ^ 2) :=
    (ContinuousLinearMap.le_def _ _).mp hsq_le
  have hre : 0 ≤ RCLike.re ⟪x, (A - A ^ 2) x⟫_ℂ := hpos_diff.re_inner_nonneg_right x
  have hexpand : ⟪x, (A - A ^ 2) x⟫_ℂ = ⟪x, A x⟫_ℂ - ⟪x, (A ^ 2) x⟫_ℂ := by
    rw [sub_apply, inner_sub_right]
  have hAsq : (A ^ 2) x = A (A x) := by
    rw [sq, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have hsym : ⟪A x, A x⟫_ℂ = ⟪x, A (A x)⟫_ℂ := hAsa.isSymmetric x (A x)
  have hnormsq : ⟪A x, A x⟫_ℂ = ((‖A x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hexpand, hAsq, ← hsym, hnormsq, map_sub] at hre
  simp only [Complex.ofReal_re, show ∀ z : ℂ, RCLike.re z = z.re from fun _ => rfl] at hre
  show ‖A x‖ ^ 2 ≤ (⟪x, A x⟫_ℂ).re
  linarith [hre]

end PositiveContraction

/-! ## Positive scalar functionals from the continuous functional calculus -/

section CFCScalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : H →L[ℂ] H) (hU : IsStarNormal U)

/-- Regard a real-valued continuous function on the spectrum of a normal operator as a complex
valued one.  Keeping this map explicit prevents the real/complex scalar changes in the Riesz
construction from being hidden in coercions. -/
noncomputable def realToComplexContinuousMap
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    C(spectrum ℂ U, ℂ) :=
  ContinuousMap.compStarAlgHom (spectrum ℂ U) (RCLike.ofRealStarAlgHom ℂ)
    RCLike.continuous_ofReal f.toContinuousMap

omit [CompleteSpace H] in
@[nolint unusedArguments, simp]
lemma realToComplexContinuousMap_apply
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (z : spectrum ℂ U) :
    realToComplexContinuousMap U f z = f z := by
  rfl

omit [CompleteSpace H] in
lemma realToComplexContinuousMap_add
    (f g : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    realToComplexContinuousMap U (f + g) =
      realToComplexContinuousMap U f + realToComplexContinuousMap U g := by
  ext z
  simp

omit [CompleteSpace H] in
lemma realToComplexContinuousMap_smul (r : ℝ)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    realToComplexContinuousMap U (r • f) =
      (r : ℂ) • realToComplexContinuousMap U f := by
  ext z
  simp

/-- The operator obtained by applying the complex continuous functional calculus to a real test
function. -/
noncomputable def cfcRealOperator
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) : H →L[ℂ] H :=
  cfcHom hU (realToComplexContinuousMap U f)

lemma cfcRealOperator_isSelfAdjoint
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    IsSelfAdjoint (cfcRealOperator U hU f) := by
  have hfstar : star (realToComplexContinuousMap U f) =
      realToComplexContinuousMap U f := by
    ext z
    change starRingEnd ℂ (f z : ℂ) = f z
    simp
  change star (cfcHom hU (realToComplexContinuousMap U f)) = _
  rw [← map_star, hfstar]
  rfl

lemma cfcRealOperator_nonneg
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    ContinuousLinearMap.IsPositive (cfcRealOperator U hU f) := by
  let gR : C(spectrum ℂ U, ℝ) :=
    ⟨fun z ↦ Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩
  let g : C(spectrum ℂ U, ℂ) :=
    ContinuousMap.compStarAlgHom (spectrum ℂ U) (RCLike.ofRealStarAlgHom ℂ)
      RCLike.continuous_ofReal gR
  have hsq : realToComplexContinuousMap U f = star g * g := by
    ext z
    change (f z : ℂ) = starRingEnd ℂ (Real.sqrt (f z) : ℂ) * Real.sqrt (f z)
    simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hf z)]
  change ContinuousLinearMap.IsPositive (cfcHom hU (realToComplexContinuousMap U f))
  rw [hsq, map_mul, map_star]
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using
    ContinuousLinearMap.isPositive_adjoint_comp_self (cfcHom hU g)

/-- The vector state of the continuous functional calculus, restricted to real test functions.
The positivity proof is the square-root argument above; this is the exact input required by
Riesz--Markov. -/
noncomputable def cfcScalarFunctional (x : H) :
    CompactPositiveFunctional (X := spectrum ℂ U) where
  functional := PositiveLinearMap.mk₀
    { toFun := fun f ↦ RCLike.re ⟪x, cfcRealOperator U hU f x⟫_ℂ
      map_add' := by
        intro f g
        change RCLike.re ⟪x, cfcRealOperator U hU (f + g) x⟫_ℂ = _
        rw [cfcRealOperator, realToComplexContinuousMap_add, map_add,
          add_apply, inner_add_right]
        simp [cfcRealOperator]
      map_smul' := by
        intro r f
        change RCLike.re ⟪x, cfcRealOperator U hU (r • f) x⟫_ℂ = _
        rw [cfcRealOperator, realToComplexContinuousMap_smul, map_smul,
          smul_apply, inner_smul_right]
        simp [cfcRealOperator] }
    (fun f hf ↦ (cfcRealOperator_nonneg U hU f hf).re_inner_nonneg_right x)

lemma cfcScalarFunctional_apply (x : H)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    (cfcScalarFunctional (hU := hU) U x).functional f =
      RCLike.re ⟪x, cfcRealOperator U hU f x⟫_ℂ := by
  rfl

/-- The scalar spectral measure supplied by Riesz--Markov for the vector state at `x`. -/
noncomputable def cfcScalarMeasure (x : H) : Measure (spectrum ℂ U) :=
  (cfcScalarFunctional (hU := hU) U x).measure

instance cfcScalarMeasure_isFinite (x : H) : IsFiniteMeasure (cfcScalarMeasure U hU x) := by
  dsimp [cfcScalarMeasure, CompactPositiveFunctional.measure]
  infer_instance

lemma cfcScalarMeasure_integral (x : H)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    ∫ z, f z ∂cfcScalarMeasure U hU x =
      RCLike.re ⟪x, cfcRealOperator U hU f x⟫_ℂ := by
  exact CompactPositiveFunctional.integral (cfcScalarFunctional (hU := hU) U x) f

lemma cfcScalarMeasure_integral_complex (x : H)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    ((∫ z, f z ∂cfcScalarMeasure U hU x : ℝ) : ℂ) =
      ⟪cfcRealOperator U hU f x, x⟫_ℂ := by
  rw [cfcScalarMeasure_integral]
  let A := cfcRealOperator U hU f
  have hA : IsSelfAdjoint A := cfcRealOperator_isSelfAdjoint U hU f
  have hreal :
      (RCLike.re ⟪x, A x⟫_ℂ : ℂ) = ⟪A x, x⟫_ℂ := by
    calc
      (RCLike.re ⟪x, A x⟫_ℂ : ℂ) =
          (RCLike.re ⟪A x, x⟫_ℂ : ℂ) := by
            rw [inner_re_symm]
      _ = ⟪A x, x⟫_ℂ :=
        Complex.conj_eq_iff_re.mp (hA.isSymmetric.conj_inner_sym x x)
  exact hreal

/-- The scalar integral of a real test function against the polarized candidate.  This is written
explicitly while the general vector-measure integral bridge is being proved. -/
noncomputable def polarizedCfcRealIntegral
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (x y : H) : ℂ :=
  ((1 / 4 : ℝ) *
      ((∫ z, f z ∂cfcScalarMeasure U hU (x + y)) -
        ∫ z, f z ∂cfcScalarMeasure U hU (x - y)) : ℂ) +
    Complex.I * ((1 / 4 : ℝ) *
      ((∫ z, f z ∂cfcScalarMeasure U hU (x + Complex.I • y)) -
        ∫ z, f z ∂cfcScalarMeasure U hU (x - Complex.I • y)) : ℂ)

lemma polarizedCfcRealIntegral_eq_inner
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (x y : H) :
    polarizedCfcRealIntegral U hU f x y =
      ⟪y, cfcRealOperator U hU f x⟫_ℂ := by
  let A := cfcRealOperator U hU f
  have hdiag (v : H) :
      ((∫ z, f z ∂cfcScalarMeasure U hU v : ℝ) : ℂ) = ⟪A v, v⟫_ℂ := by
    exact cfcScalarMeasure_integral_complex U hU v f
  have hpolar := inner_map_polarization (A : H →ₗ[ℂ] H) x y
  have hsym : ⟪A y, x⟫_ℂ = ⟪y, A x⟫_ℂ :=
    (cfcRealOperator_isSelfAdjoint U hU f).isSymmetric y x
  rw [← hsym]
  simp only [polarizedCfcRealIntegral, hdiag (x + y), hdiag (x - y),
    hdiag (x + Complex.I • y), hdiag (x - Complex.I • y)]
  calc
    _ = (⟪A (x + y), x + y⟫_ℂ - ⟪A (x - y), x - y⟫_ℂ +
      Complex.I * ⟪A (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
      Complex.I * ⟪A (x - Complex.I • y), x - Complex.I • y⟫_ℂ) / 4 := by
      norm_num
      ring
    _ = _ := hpolar.symm

/-- The scalar half of the normal-operator spectral construction.  The operator-valued assembly
below uses this data to build the actual weak-operator spectral measure. -/
structure VectorStateSpectralData where
  /-- The scalar measure attached to each vector `x`. -/
  measure : H → Measure (spectrum ℂ U)
  integral_identity : ∀ x f,
    ∫ z, f z ∂measure x = RCLike.re ⟪x, cfcRealOperator U hU f x⟫_ℂ

/-- The scalar spectral data of `U`'s continuous functional calculus. -/
noncomputable def cfcVectorStateSpectralData : VectorStateSpectralData U hU where
  measure := cfcScalarMeasure U hU
  integral_identity := cfcScalarMeasure_integral U hU

lemma cfcScalarMeasure_parallelogram (x y : H) :
    cfcScalarMeasure U hU (x + y) + cfcScalarMeasure U hU (x - y) =
      (cfcScalarMeasure U hU x + cfcScalarMeasure U hU x) +
        (cfcScalarMeasure U hU y + cfcScalarMeasure U hU y) := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf : ∀ v : H, Integrable (f : spectrum ℂ U → ℝ) (cfcScalarMeasure U hU v) := by
    intro v
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  have hxx : Integrable (f : spectrum ℂ U → ℝ)
      (cfcScalarMeasure U hU x + cfcScalarMeasure U hU x) :=
    integrable_add_measure.mpr ⟨hf x, hf x⟩
  have hyy : Integrable (f : spectrum ℂ U → ℝ)
      (cfcScalarMeasure U hU y + cfcScalarMeasure U hU y) :=
    integrable_add_measure.mpr ⟨hf y, hf y⟩
  rw [integral_add_measure (hf (x + y)) (hf (x - y)),
    integral_add_measure hxx hyy,
    integral_add_measure (hf x) (hf x), integral_add_measure (hf y) (hf y)]
  simp only [cfcScalarMeasure_integral]
  let A := cfcRealOperator U hU f
  have hA : IsSelfAdjoint A := cfcRealOperator_isSelfAdjoint U hU f
  change RCLike.re ⟪x + y, A (x + y)⟫_ℂ +
      RCLike.re ⟪x - y, A (x - y)⟫_ℂ =
    (RCLike.re ⟪x, A x⟫_ℂ + RCLike.re ⟪x, A x⟫_ℂ) +
      (RCLike.re ⟪y, A y⟫_ℂ + RCLike.re ⟪y, A y⟫_ℂ)
  simp only [map_add, map_neg, inner_add_left, inner_add_right, sub_eq_add_neg,
    inner_neg_left, inner_neg_right]
  ring

lemma cfcScalarMeasure_neg (x : H) :
    cfcScalarMeasure U hU (-x) = cfcScalarMeasure U hU x := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfx : Integrable (f : spectrum ℂ U → ℝ) (cfcScalarMeasure U hU x) := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  simp only [cfcScalarMeasure_integral]
  simp [inner_neg_left, inner_neg_right]

lemma cfcScalarMeasure_I_smul (x : H) :
    cfcScalarMeasure U hU (Complex.I • x) = cfcScalarMeasure U hU x := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfx : Integrable (f : spectrum ℂ U → ℝ) (cfcScalarMeasure U hU x) := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  have hix : Integrable (f : spectrum ℂ U → ℝ)
      (cfcScalarMeasure U hU (Complex.I • x)) := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  simp only [cfcScalarMeasure_integral]
  simp [inner_smul_left, inner_smul_right]

/-- The complex scalar measure obtained by polarizing the four diagonal Riesz measures.  This is
the canonical candidate for `⟪y, E(·) x⟫`; the next assembly theorem must prove that these
candidates are sesquilinear and have the required weak σ-additivity. -/
noncomputable def polarizedCfcScalarMeasure (x y : H) : ComplexMeasure (spectrum ℂ U) :=
  let muPlus := (cfcScalarMeasure U hU (x + y)).toSignedMeasure
  let muMinus := (cfcScalarMeasure U hU (x - y)).toSignedMeasure
  let nuPlus := (cfcScalarMeasure U hU (x + Complex.I • y)).toSignedMeasure
  let nuMinus := (cfcScalarMeasure U hU (x - Complex.I • y)).toSignedMeasure
  ((1 / 4 : ℝ) • (muPlus - muMinus)).toComplexMeasure
  ((1 / 4 : ℝ) • (nuPlus - nuMinus))

set_option maxHeartbeats 1000000 in
lemma polarizedCfcScalarMeasure_isFiniteMeasure (x y : H) :
    IsFiniteMeasure
      (polarizedCfcScalarMeasure (hU := hU) U x y).variation := by
  unfold polarizedCfcScalarMeasure
  have hsub (a b : H) : IsFiniteMeasure
      (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU a).toSignedMeasure -
        (cfcScalarMeasure U hU b).toSignedMeasure)).variation) := by
    let : IsFiniteMeasure (cfcScalarMeasure U hU a).toSignedMeasure.variation := by
      rw [Measure.variation_toSignedMeasure]
      infer_instance
    let : IsFiniteMeasure (cfcScalarMeasure U hU b).toSignedMeasure.variation := by
      rw [Measure.variation_toSignedMeasure]
      infer_instance
    apply isFiniteMeasure_of_le (cfcScalarMeasure U hU a + cfcScalarMeasure U hU b)
    rw [MeasureTheory.VectorMeasure.variation_smul]
    have hv : ((cfcScalarMeasure U hU a).toSignedMeasure -
        (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
        cfcScalarMeasure U hU a + cfcScalarMeasure U hU b := by
      simpa only [Measure.variation_toSignedMeasure] using
        (MeasureTheory.VectorMeasure.variation_sub_le
          (μ := (cfcScalarMeasure U hU a).toSignedMeasure)
          (ν := (cfcScalarMeasure U hU b).toSignedMeasure))
    calc
      ‖(1 / 4 : ℝ)‖₊ •
          ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
          (1 : ENNReal) • ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure).variation := by
        change ((‖(1 / 4 : ℝ)‖₊ : NNReal) : ENNReal) •
          ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
          (1 : ENNReal) • ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure).variation
        gcongr
        norm_num
      _ ≤ (1 : ENNReal) • (cfcScalarMeasure U hU a + cfcScalarMeasure U hU b) := by
        simpa only [one_smul] using hv
      _ = cfcScalarMeasure U hU a + cfcScalarMeasure U hU b := by simp
  let hplus : IsFiniteMeasure
      (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU (x + y)).toSignedMeasure -
        (cfcScalarMeasure U hU (x - y)).toSignedMeasure)).variation) :=
    hsub (x + y) (x - y)
  let hminus : IsFiniteMeasure
      (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU (x + Complex.I • y)).toSignedMeasure -
        (cfcScalarMeasure U hU (x - Complex.I • y)).toSignedMeasure)).variation) :=
    hsub (x + Complex.I • y) (x - Complex.I • y)
  exact isFiniteMeasure_toComplexMeasure
    (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU (x + y)).toSignedMeasure -
      (cfcScalarMeasure U hU (x - y)).toSignedMeasure)))
    (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU (x + Complex.I • y)).toSignedMeasure -
      (cfcScalarMeasure U hU (x - Complex.I • y)).toSignedMeasure)))

lemma polarizedCfcScalarMeasure_complexIntegral
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (x y : H) :
    ∫ᵛ z, (f z : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      polarizedCfcScalarMeasure (hU := hU) U x y] =
      polarizedCfcRealIntegral U hU f x y := by
  let fC : spectrum ℂ U → ℂ := fun z ↦ f z
  have hfC : Continuous fC := by
    fun_prop
  have hplus : Integrable fC (cfcScalarMeasure U hU (x + y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hminus : Integrable fC (cfcScalarMeasure U hU (x - y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hip : Integrable fC
      (cfcScalarMeasure U hU (x + Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have him : Integrable fC
      (cfcScalarMeasure U hU (x - Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  let μplus := cfcScalarMeasure U hU (x + y)
  let μminus := cfcScalarMeasure U hU (x - y)
  let νplus := cfcScalarMeasure U hU (x + Complex.I • y)
  let νminus := cfcScalarMeasure U hU (x - Complex.I • y)
  change ∫ᵛ z, fC z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      ((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).toComplexMeasure
        ((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure))] = _
  have hreal :
      (((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).mapRange
        Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure μplus μminus]
    exact (integrable_mapRange_ofReal_signedMeasure μplus fC hplus).sub_vectorMeasure
      (integrable_mapRange_ofReal_signedMeasure μminus fC hminus) |>.smul_vectorMeasure _
  have himag :
      (((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure)).mapRange
        imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure νplus νminus]
    exact (integrable_mapRange_imaginaryOfReal_signedMeasure νplus fC hip).sub_vectorMeasure
      (integrable_mapRange_imaginaryOfReal_signedMeasure νminus fC him) |>.smul_vectorMeasure _
  rw [integral_toComplexMeasure_eq_add_mapRange _ _ fC hreal himag]
  rw [integral_mapRange_ofReal_signedDifference μplus μminus (1 / 4 : ℝ) fC hplus hminus,
    integral_mapRange_imaginaryOfReal_signedDifference νplus νminus (1 / 4 : ℝ) fC hip him]
  dsimp [fC]
  simp only [integral_complex_ofReal]
  simp [polarizedCfcRealIntegral, μplus, μminus, νplus, νminus]
  ring

lemma polarizedCfcScalarMeasure_complexIntegral_eq_inner
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (x y : H) :
    ∫ᵛ z, (f z : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      polarizedCfcScalarMeasure (hU := hU) U x y] =
      ⟪y, cfcRealOperator U hU f x⟫_ℂ := by
  rw [polarizedCfcScalarMeasure_complexIntegral]
  exact polarizedCfcRealIntegral_eq_inner U hU f x y

lemma polarizedCfcScalarMeasure_apply {x y : H}
    {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U x y S =
      ((1 / 4 : ℝ) *
          ((cfcScalarMeasure U hU (x + y)).real S -
            (cfcScalarMeasure U hU (x - y)).real S) : ℂ) +
        Complex.I * ((1 / 4 : ℝ) *
          ((cfcScalarMeasure U hU (x + Complex.I • y)).real S -
            (cfcScalarMeasure U hU (x - Complex.I • y)).real S) : ℂ) := by
  simp [polarizedCfcScalarMeasure, MeasureTheory.SignedMeasure.toComplexMeasure_apply,
    MeasureTheory.Measure.toSignedMeasure_apply_measurable hS]
  apply Complex.ext <;> simp

/-! ## Sesquilinearity of the polarized measure -/

/-- The real-valued version of the parallelogram law, at a fixed (not necessarily measurable)
set `S`.  This is the algebraic engine behind the sesquilinearity proofs below. -/
lemma cfcScalarMeasure_real_parallelogram (a b : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU (a + b)).real S + (cfcScalarMeasure U hU (a - b)).real S =
      2 * (cfcScalarMeasure U hU a).real S + 2 * (cfcScalarMeasure U hU b).real S := by
  have hS : cfcScalarMeasure U hU (a + b) S + cfcScalarMeasure U hU (a - b) S =
      cfcScalarMeasure U hU a S + cfcScalarMeasure U hU a S +
        (cfcScalarMeasure U hU b S + cfcScalarMeasure U hU b S) :=
    congrArg (fun μ : Measure (spectrum ℂ U) => μ S) (cfcScalarMeasure_parallelogram U hU a b)
  have hne : ∀ v : H, cfcScalarMeasure U hU v S ≠ ⊤ := fun v => measure_ne_top _ S
  have hreal := congrArg ENNReal.toReal hS
  rw [ENNReal.toReal_add (hne _) (hne _)] at hreal
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hne _, hne _⟩)
      (ENNReal.add_ne_top.mpr ⟨hne _, hne _⟩)] at hreal
  rw [ENNReal.toReal_add (hne _) (hne _), ENNReal.toReal_add (hne _) (hne _)] at hreal
  simpa [measureReal_def, two_mul] using hreal

lemma cfcScalarMeasure_real_neg (a : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU (-a)).real S = (cfcScalarMeasure U hU a).real S := by
  rw [cfcScalarMeasure_neg]

lemma cfcScalarMeasure_real_I_smul (a : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU (Complex.I • a)).real S = (cfcScalarMeasure U hU a).real S := by
  rw [cfcScalarMeasure_I_smul]

lemma cfcScalarMeasure_real_nonneg (a : H) (S : Set (spectrum ℂ U)) :
    0 ≤ (cfcScalarMeasure U hU a).real S := ENNReal.toReal_nonneg

/-- The Riesz measure for the vector state at `x` has total mass `‖x‖ ^ 2`: the vector-state
counterpart of `cfcHom hU 1 = 1`. -/
lemma cfcScalarMeasure_real_univ (x : H) :
    (cfcScalarMeasure U hU x).real Set.univ = ‖x‖ ^ 2 := by
  let f1 : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ :=
    { toFun := fun _ => 1
      continuous_toFun := continuous_const
      hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  have hf1val : ∀ z, f1 z = 1 := fun _ => rfl
  have hop : cfcRealOperator U hU f1 = 1 := by
    have hone : realToComplexContinuousMap U f1 = 1 := by
      ext z
      simp [realToComplexContinuousMap_apply, hf1val]
    unfold cfcRealOperator
    rw [hone, map_one]
  have hint := cfcScalarMeasure_integral U hU x f1
  rw [hop] at hint
  have hint2 : ∫ z, f1 z ∂cfcScalarMeasure U hU x = (cfcScalarMeasure U hU x).real Set.univ := by
    simp only [hf1val]
    rw [MeasureTheory.integral_const]
    simp [measureReal_def]
  rw [hint2] at hint
  rw [hint, one_apply_eq_self, inner_self_eq_norm_sq]

lemma cfcScalarMeasure_real_le_univ (a : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU a).real S ≤ ‖a‖ ^ 2 := by
  rw [← cfcScalarMeasure_real_univ U hU a]
  apply MeasureTheory.measureReal_mono (Set.subset_univ S)

/-- The real polarization `Q(a+b) - Q(a-b)` is symmetric in `a b`, where
`Q v := (cfcScalarMeasure U hU v).real S`.  This is where `cfcScalarMeasure_neg` enters: it turns
the parallelogram law into a genuine (conjugate-)symmetric pairing. -/
lemma cfcScalarMeasure_real_polar_symm (a b : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU (a + b)).real S - (cfcScalarMeasure U hU (a - b)).real S =
      (cfcScalarMeasure U hU (b + a)).real S - (cfcScalarMeasure U hU (b - a)).real S := by
  have hba : b - a = -(a - b) := by abel
  rw [add_comm b a, hba, cfcScalarMeasure_real_neg]

/-- First-argument additivity of the real polarization `Q(a+b) - Q(a-b)`, established by pure
algebra from the parallelogram law (`cfcScalarMeasure_real_parallelogram`); no continuity is
needed for this step, matching the classical Jordan--von Neumann polarization argument
(`Mathlib.Analysis.InnerProductSpace.OfNorm`). -/
lemma cfcScalarMeasure_real_polar_add_left (x y z : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU (x + y + z)).real S - (cfcScalarMeasure U hU (x + y - z)).real S =
      ((cfcScalarMeasure U hU (x + z)).real S - (cfcScalarMeasure U hU (x - z)).real S) +
        ((cfcScalarMeasure U hU (y + z)).real S - (cfcScalarMeasure U hU (y - z)).real S) := by
  have h1 := cfcScalarMeasure_real_parallelogram U hU (x + y + z) (x - z) S
  have h2 := cfcScalarMeasure_real_parallelogram U hU (x + y - z) (x + z) S
  have h3 := cfcScalarMeasure_real_parallelogram U hU (y + z) z S
  have h4 := cfcScalarMeasure_real_parallelogram U hU (y - z) z S
  have e1 : x + y + z + (x - z) = 2 • x + y := by abel
  have e2 : x + y + z - (x - z) = y + 2 • z := by abel
  have e3 : x + y - z + (x + z) = 2 • x + y := by abel
  have e4 : x + y - z - (x + z) = y - 2 • z := by abel
  have e5 : y + z + z = y + 2 • z := by abel
  have e6 : y + z - z = y := by abel
  have e7 : y - z + z = y := by abel
  have e8 : y - z - z = y - 2 • z := by abel
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [e5, e6] at h3
  rw [e7, e8] at h4
  linarith [h1, h2, h3, h4]

/-- Second-argument additivity of the real polarization, obtained from first-argument additivity
(`cfcScalarMeasure_real_polar_add_left`) via the symmetry `cfcScalarMeasure_real_polar_symm`. -/
lemma cfcScalarMeasure_real_polar_add_right (a b c : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU (a + (b + c))).real S -
        (cfcScalarMeasure U hU (a - (b + c))).real S =
      ((cfcScalarMeasure U hU (a + b)).real S - (cfcScalarMeasure U hU (a - b)).real S) +
        ((cfcScalarMeasure U hU (a + c)).real S - (cfcScalarMeasure U hU (a - c)).real S) := by
  have hadd := cfcScalarMeasure_real_polar_add_left U hU b c a S
  have e1 : a + (b + c) = b + c + a := by abel
  have e2 : b + c - a = -(a - (b + c)) := by abel
  have e3 : b + a = a + b := by abel
  have e4 : b - a = -(a - b) := by abel
  have e5 : c + a = a + c := by abel
  have e6 : c - a = -(a - c) := by abel
  rw [← e1, e2, e3, e4, e5, e6, cfcScalarMeasure_real_neg, cfcScalarMeasure_real_neg,
    cfcScalarMeasure_real_neg] at hadd
  linarith [hadd]

/-- Additivity of the polarized measure in its second (right) vector argument, for a fixed
measurable set `S`.  This is the sesquilinearity step promised in the module docstring: it
follows from the parallelogram law by pure algebra, with no continuity or Riesz-representation
machinery required. -/
lemma polarizedCfcScalarMeasure_add_right (x y₁ y₂ : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U x (y₁ + y₂) S =
      polarizedCfcScalarMeasure (hU := hU) U x y₁ S +
        polarizedCfcScalarMeasure (hU := hU) U x y₂ S := by
  rw [polarizedCfcScalarMeasure_apply U hU hS, polarizedCfcScalarMeasure_apply U hU hS,
    polarizedCfcScalarMeasure_apply U hU hS]
  have hR := cfcScalarMeasure_real_polar_add_right U hU x y₁ y₂ S
  have hI : (cfcScalarMeasure U hU (x + Complex.I • (y₁ + y₂))).real S -
      (cfcScalarMeasure U hU (x - Complex.I • (y₁ + y₂))).real S =
      ((cfcScalarMeasure U hU (x + Complex.I • y₁)).real S -
          (cfcScalarMeasure U hU (x - Complex.I • y₁)).real S) +
        ((cfcScalarMeasure U hU (x + Complex.I • y₂)).real S -
          (cfcScalarMeasure U hU (x - Complex.I • y₂)).real S) := by
    have h := cfcScalarMeasure_real_polar_add_right U hU x (Complex.I • y₁) (Complex.I • y₂) S
    rwa [← smul_add] at h
  have hRc := congrArg (fun r : ℝ => (r : ℂ)) hR
  have hIc := congrArg (fun r : ℝ => (r : ℂ)) hI
  push_cast at hRc hIc
  rw [hRc, hIc]
  ring

/-- Additivity of the polarized measure in its first (left) vector argument, for a fixed
measurable set `S`. -/
lemma polarizedCfcScalarMeasure_add_left (x₁ x₂ y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U (x₁ + x₂) y S =
      polarizedCfcScalarMeasure (hU := hU) U x₁ y S +
        polarizedCfcScalarMeasure (hU := hU) U x₂ y S := by
  rw [polarizedCfcScalarMeasure_apply U hU hS, polarizedCfcScalarMeasure_apply U hU hS,
    polarizedCfcScalarMeasure_apply U hU hS]
  have hR := cfcScalarMeasure_real_polar_add_left U hU x₁ x₂ y S
  have hI : (cfcScalarMeasure U hU (x₁ + x₂ + Complex.I • y)).real S -
      (cfcScalarMeasure U hU (x₁ + x₂ - Complex.I • y)).real S =
      ((cfcScalarMeasure U hU (x₁ + Complex.I • y)).real S -
          (cfcScalarMeasure U hU (x₁ - Complex.I • y)).real S) +
        ((cfcScalarMeasure U hU (x₂ + Complex.I • y)).real S -
          (cfcScalarMeasure U hU (x₂ - Complex.I • y)).real S) :=
    cfcScalarMeasure_real_polar_add_left U hU x₁ x₂ (Complex.I • y) S
  have hRc := congrArg (fun r : ℝ => (r : ℂ)) hR
  have hIc := congrArg (fun r : ℝ => (r : ℂ)) hI
  push_cast at hRc hIc
  rw [hRc, hIc]
  ring

/-- `Complex.I`-homogeneity in the right (second) argument.  Because the second slot of the
target inner product `⟪y, cfcRealOperator U hU f x⟫_ℂ` is conjugate-linear (Mathlib's inner
product is conjugate-linear in its *first* argument), the correct identity has a `conj I = -I`
factor, not `I`; `polarizedCfcScalarMeasure_I_smul_left` below is the linear (non-conjugated)
counterpart in the first argument. -/
lemma polarizedCfcScalarMeasure_I_smul_right (x y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U x (Complex.I • y) S =
      -Complex.I * polarizedCfcScalarMeasure (hU := hU) U x y S := by
  rw [polarizedCfcScalarMeasure_apply U hU hS, polarizedCfcScalarMeasure_apply U hU hS]
  have e1 : Complex.I • (Complex.I • y) = -y := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [e1]
  have e2 : x + -y = x - y := by abel
  have e3 : x - -y = x + y := by abel
  rw [e2, e3]
  push_cast
  linear_combination ((1 : ℂ) / 4) *
    (((cfcScalarMeasure U hU (x + Complex.I • y)).real S : ℂ) -
      ((cfcScalarMeasure U hU (x - Complex.I • y)).real S : ℂ)) * Complex.I_sq

/-- `Complex.I`-homogeneity in the left (first) argument: this slot is genuinely `ℂ`-linear. -/
lemma polarizedCfcScalarMeasure_I_smul_left (x y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U (Complex.I • x) y S =
      Complex.I * polarizedCfcScalarMeasure (hU := hU) U x y S := by
  rw [polarizedCfcScalarMeasure_apply U hU hS, polarizedCfcScalarMeasure_apply U hU hS]
  have e1 : Complex.I • x + y = Complex.I • (x - Complex.I • y) := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have e2 : Complex.I • x - y = Complex.I • (x + Complex.I • y) := by
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have e3 : Complex.I • x + Complex.I • y = Complex.I • (x + y) := by rw [smul_add]
  have e4 : Complex.I • x - Complex.I • y = Complex.I • (x - y) := by rw [smul_sub]
  rw [e1, e2, e3, e4, cfcScalarMeasure_real_I_smul, cfcScalarMeasure_real_I_smul,
    cfcScalarMeasure_real_I_smul, cfcScalarMeasure_real_I_smul]
  push_cast
  linear_combination ((1 : ℂ) / 4) *
    (((cfcScalarMeasure U hU (x - Complex.I • y)).real S : ℂ) -
      ((cfcScalarMeasure U hU (x + Complex.I • y)).real S : ℂ)) * Complex.I_sq

/-- A crude but sufficient bound on the polarized measure, from the parallelogram law and
`cfcScalarMeasure_real_le_univ`.  This is enough to see `(x, y) ↦ polarizedCfcScalarMeasure U hU
x y S` is jointly bounded, the input a Riesz-representation argument needs. -/
lemma polarizedCfcScalarMeasure_norm_le (x y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    ‖polarizedCfcScalarMeasure (hU := hU) U x y S‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [polarizedCfcScalarMeasure_apply U hU hS]
  have hbound : ∀ a b : H, |(cfcScalarMeasure U hU (a + b)).real S -
      (cfcScalarMeasure U hU (a - b)).real S| ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have hpar := cfcScalarMeasure_real_parallelogram U hU a b S
    have hnn1 := cfcScalarMeasure_real_nonneg U hU (a + b) S
    have hnn2 := cfcScalarMeasure_real_nonneg U hU (a - b) S
    have hle1 := cfcScalarMeasure_real_le_univ U hU a S
    have hle2 := cfcScalarMeasure_real_le_univ U hU b S
    rw [abs_le]
    constructor <;> linarith
  have h1 := hbound x y
  have h2 := hbound x (Complex.I • y)
  rw [norm_smul] at h2
  simp only [Complex.norm_I, one_mul] at h2
  calc ‖((1 / 4 : ℝ) * ((cfcScalarMeasure U hU (x + y)).real S -
        (cfcScalarMeasure U hU (x - y)).real S) : ℂ) +
      Complex.I * ((1 / 4 : ℝ) * ((cfcScalarMeasure U hU (x + Complex.I • y)).real S -
        (cfcScalarMeasure U hU (x - Complex.I • y)).real S) : ℂ)‖
      ≤ ‖((1 / 4 : ℝ) * ((cfcScalarMeasure U hU (x + y)).real S -
          (cfcScalarMeasure U hU (x - y)).real S) : ℂ)‖ +
        ‖Complex.I * ((1 / 4 : ℝ) * ((cfcScalarMeasure U hU (x + Complex.I • y)).real S -
          (cfcScalarMeasure U hU (x - Complex.I • y)).real S) : ℂ)‖ := norm_add_le _ _
    _ = (1 / 4) * |(cfcScalarMeasure U hU (x + y)).real S -
          (cfcScalarMeasure U hU (x - y)).real S| +
        (1 / 4) * |(cfcScalarMeasure U hU (x + Complex.I • y)).real S -
          (cfcScalarMeasure U hU (x - Complex.I • y)).real S| := by
      simp [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / 4) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) + (1 / 4) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := by
      gcongr
    _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by ring

/-- An additive `ℝ → ℂ` function that is bounded on `[-1, 1]` is automatically `ℝ`-linear.  This
packages the classical "Cauchy's functional equation" regularity argument (additive + locally
bounded ⟹ continuous, then continuous additive between real topological vector spaces ⟹
`ℝ`-linear via `map_real_smul`) that both real-scalar-homogeneity lemmas below reduce to. -/
lemma real_linear_of_additive_bounded {φ : ℝ → ℂ}
    (hadd : ∀ a b : ℝ, φ (a + b) = φ a + φ b)
    {C : ℝ} (hbound : ∀ t : ℝ, |t| ≤ 1 → ‖φ t‖ ≤ C) (r : ℝ) :
    φ r = (r : ℂ) * φ 1 := by
  let φHom : ℝ →+ ℂ := AddMonoidHom.mk' φ hadd
  have hφHom : ∀ t : ℝ, φHom t = φ t := fun _ => rfl
  have hCnonneg : 0 ≤ C := (norm_nonneg (φ 0)).trans (hbound 0 (by norm_num))
  have hcont0 : ContinuousAt φHom 0 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.cast_zero] at hn
        exact absurd hn (not_lt.mpr (div_nonneg hCnonneg hε.le))
      · exact h0
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    refine ⟨1 / n, by positivity, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero] at ht
    have habs : (n : ℝ) * t ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [abs_lt] at ht
      have h1 : (n : ℝ) * t < (n : ℝ) * (1 / (n : ℝ)) := mul_lt_mul_of_pos_left ht.2 hnpos
      have h2 : (n : ℝ) * (-(1 / (n : ℝ))) < (n : ℝ) * t := mul_lt_mul_of_pos_left ht.1 hnpos
      have h1' : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
      have h2' : (n : ℝ) * (-(1 / (n : ℝ))) = -1 := by field_simp
      constructor <;> linarith
    have hnt_le : |(n : ℝ) * t| ≤ 1 := abs_le.mpr habs
    have hval : φHom ((n : ℝ) * t) = (n : ℂ) * φHom t := by
      have h' := map_nsmul φHom n t
      rwa [nsmul_eq_mul, nsmul_eq_mul] at h'
    have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hφt : φHom t = φHom ((n : ℝ) * t) / (n : ℂ) := by
      rw [hval, mul_div_cancel_left₀ _ hne]
    have hφnt_bound : ‖φHom ((n : ℝ) * t)‖ ≤ C := hbound _ hnt_le
    have hCn : C / n < ε := by
      rw [div_lt_iff₀ hnpos, mul_comm]
      exact (div_lt_iff₀ hε).mp hn
    rw [map_zero, Complex.dist_eq, sub_zero, hφt, norm_div, Complex.norm_natCast]
    calc ‖φHom ((n : ℝ) * t)‖ / (n : ℝ) ≤ C / (n : ℝ) := by gcongr
      _ < ε := hCn
  have hcont : Continuous φHom := continuous_of_continuousAt_zero φHom hcont0
  have hmap := map_real_smul φHom hcont r (1 : ℝ)
  rw [smul_eq_mul, mul_one, Complex.real_smul] at hmap
  rw [hφHom r, hφHom 1] at hmap
  exact hmap

/-- Real-scalar homogeneity in the right (second) argument: `B(x, r • y) = r * B(x, y)` for
`r : ℝ`.  Unlike additivity and `Complex.I`-homogeneity above (pure algebra from the
parallelogram law, see `polarizedCfcScalarMeasure_add_right` and
`polarizedCfcScalarMeasure_I_smul_right`), this reduces to the continuity argument packaged in
`real_linear_of_additive_bounded`. -/
theorem polarizedCfcScalarMeasure_real_smul_right (x y : H) (r : ℝ) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U x (r • y) S =
      (r : ℂ) * polarizedCfcScalarMeasure (hU := hU) U x y S := by
  have hadd : ∀ a b : ℝ, polarizedCfcScalarMeasure (hU := hU) U x ((a + b) • y) S =
      polarizedCfcScalarMeasure (hU := hU) U x (a • y) S +
        polarizedCfcScalarMeasure (hU := hU) U x (b • y) S := by
    intro a b
    rw [add_smul]
    exact polarizedCfcScalarMeasure_add_right U hU x (a • y) (b • y) hS
  have hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖polarizedCfcScalarMeasure (hU := hU) U x (t • y) S‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro t ht
    have h := polarizedCfcScalarMeasure_norm_le (hU := hU) U x (t • y) hS
    have h2 : ‖t • y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hty : |t| * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg y]
      gcongr
    linarith
  have h := real_linear_of_additive_bounded hadd hbound r
  rwa [one_smul] at h

/-- Real-scalar homogeneity in the left (first) argument, the counterpart of
`polarizedCfcScalarMeasure_real_smul_right` needed for conjugate-linearity in `x` (real scalars
are self-conjugate, so the same statement serves both roles). -/
theorem polarizedCfcScalarMeasure_real_smul_left (x y : H) (r : ℝ) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U (r • x) y S =
      (r : ℂ) * polarizedCfcScalarMeasure (hU := hU) U x y S := by
  have hadd : ∀ a b : ℝ, polarizedCfcScalarMeasure (hU := hU) U ((a + b) • x) y S =
      polarizedCfcScalarMeasure (hU := hU) U (a • x) y S +
        polarizedCfcScalarMeasure (hU := hU) U (b • x) y S := by
    intro a b
    rw [add_smul]
    exact polarizedCfcScalarMeasure_add_left U hU (a • x) (b • x) y hS
  have hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖polarizedCfcScalarMeasure (hU := hU) U (t • x) y S‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro t ht
    have h := polarizedCfcScalarMeasure_norm_le (hU := hU) U (t • x) y hS
    have h2 : ‖t • x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have htx : |t| * ‖x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x]
      gcongr
    linarith
  have h := real_linear_of_additive_bounded hadd hbound r
  rwa [one_smul] at h

/-! ## Polarization boundary -/

omit [CompleteSpace H] in
/-- The standard complex polarization identity, exposed at the continuous-operator level for the
assembly proof.  The scalar measures obtained above will be polarized with precisely these four
diagonal terms. -/
@[nolint unusedArguments]
lemma inner_map_polarization_continuous (A : H →L[ℂ] H) (x y : H) :
    ⟪A y, x⟫_ℂ =
      (⟪A (x + y), x + y⟫_ℂ - ⟪A (x - y), x - y⟫_ℂ +
          Complex.I * ⟪A (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
        Complex.I * ⟪A (x - Complex.I • y), x - Complex.I • y⟫_ℂ) / 4 := by
  exact inner_map_polarization (A : H →ₗ[ℂ] H) x y

/-! ## Full complex sesquilinearity of the polarized measure

The homogeneity lemmas above only cover real scalars and `Complex.I`.  Combining them via the
decomposition `c = c.re + c.im * I` upgrades them to genuine `ℂ`-linearity in the first argument
and conjugate-`ℂ`-linearity in the second, which is exactly the shape Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin` (Fréchet--Riesz for bounded sesquilinear forms)
consumes. -/

/-- Full `ℂ`-linearity of the polarized measure in its first (left) argument. -/
lemma polarizedCfcScalarMeasure_smul_left (c : ℂ) (x y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U (c • x) y S =
      c * polarizedCfcScalarMeasure (hU := hU) U x y S := by
  have hc : (c.re : ℝ) • x + (c.im : ℝ) • (Complex.I • x) = c • x := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul, ← add_smul]
    congr 1
    exact_mod_cast Complex.re_add_im c
  rw [← hc, polarizedCfcScalarMeasure_add_left U hU _ _ y hS,
    polarizedCfcScalarMeasure_real_smul_left U hU x y c.re hS,
    polarizedCfcScalarMeasure_real_smul_left U hU (Complex.I • x) y c.im hS,
    polarizedCfcScalarMeasure_I_smul_left U hU x y hS]
  have hcre : (c.re : ℂ) + (c.im : ℂ) * Complex.I = c := Complex.re_add_im c
  linear_combination (polarizedCfcScalarMeasure (hU := hU) U x y S) * hcre

/-- Full conjugate-`ℂ`-linearity of the polarized measure in its second (right) argument. -/
lemma polarizedCfcScalarMeasure_smul_right (c : ℂ) (x y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    polarizedCfcScalarMeasure (hU := hU) U x (c • y) S =
      (starRingEnd ℂ c) * polarizedCfcScalarMeasure (hU := hU) U x y S := by
  have hc : (c.re : ℝ) • y + (c.im : ℝ) • (Complex.I • y) = c • y := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul, ← add_smul]
    congr 1
    exact_mod_cast Complex.re_add_im c
  rw [← hc, polarizedCfcScalarMeasure_add_right U hU x _ _ hS,
    polarizedCfcScalarMeasure_real_smul_right U hU x y c.re hS,
    polarizedCfcScalarMeasure_real_smul_right U hU x (Complex.I • y) c.im hS,
    polarizedCfcScalarMeasure_I_smul_right U hU x y hS]
  have hcc : (c.re : ℂ) - (c.im : ℂ) * Complex.I = starRingEnd ℂ c := by
    have h := Complex.re_add_im (starRingEnd ℂ c)
    rw [Complex.conj_re, Complex.conj_im] at h
    push_cast at h
    linear_combination h
  linear_combination (polarizedCfcScalarMeasure (hU := hU) U x y S) * hcc

lemma polarizedCfcScalarMeasure_zero_left (y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) : polarizedCfcScalarMeasure (hU := hU) U 0 y S = 0 := by
  have h := polarizedCfcScalarMeasure_smul_left U hU 0 0 y hS
  simpa using h

lemma polarizedCfcScalarMeasure_zero_right (x : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) : polarizedCfcScalarMeasure (hU := hU) U x 0 S = 0 := by
  have h := polarizedCfcScalarMeasure_smul_right U hU 0 x 0 hS
  simpa using h

/-- A product (rather than sum-of-squares) bound on the polarized measure, obtained from
`polarizedCfcScalarMeasure_norm_le` by a homogeneity-rescaling trick: apply the sum bound to
`(t • x, t⁻¹ • y)` for the real `t` minimizing `t ^ 2 ‖x‖ ^ 2 + t⁻² ‖y‖ ^ 2`.  This is the bound a
Riesz-representation argument needs (`LinearMap.mkContinuous₂`). -/
lemma polarizedCfcScalarMeasure_norm_le_mul (x y : H) {S : Set (spectrum ℂ U)}
    (hS : MeasurableSet S) :
    ‖polarizedCfcScalarMeasure (hU := hU) U x y S‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0, polarizedCfcScalarMeasure_zero_left U hU y hS]
  rcases eq_or_ne y 0 with hy0 | hy0
  · simp [hy0, polarizedCfcScalarMeasure_zero_right U hU x hS]
  set t : ℝ := Real.sqrt (‖y‖ / ‖x‖) with ht_def
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hypos hxpos)
  have htsq : t ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (div_pos hypos hxpos).le
  have hkey : polarizedCfcScalarMeasure (hU := hU) U x y S =
      polarizedCfcScalarMeasure (hU := hU) U (t • x) (t⁻¹ • y) S := by
    rw [polarizedCfcScalarMeasure_real_smul_left U hU x (t⁻¹ • y) t hS,
      polarizedCfcScalarMeasure_real_smul_right U hU x y t⁻¹ hS]
    have ht1 : (t : ℂ) * ((t⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one]
    rw [← mul_assoc, ht1, one_mul]
  rw [hkey]
  have hbound := polarizedCfcScalarMeasure_norm_le (hU := hU) U (t • x) (t⁻¹ • y) hS
  have h1 : ‖t • x‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; ring
  have h2 : ‖t⁻¹ • y‖ ^ 2 = t⁻¹ ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]; ring
  rw [h1, h2, htsq] at hbound
  have h3 : t⁻¹ ^ 2 = ‖x‖ / ‖y‖ := by
    rw [inv_pow, htsq, inv_div]
  rw [h3] at hbound
  have e1 : ‖y‖ / ‖x‖ * ‖x‖ ^ 2 = ‖x‖ * ‖y‖ := by field_simp
  have e2 : ‖x‖ / ‖y‖ * ‖y‖ ^ 2 = ‖x‖ * ‖y‖ := by field_simp
  rw [e1, e2] at hbound
  linarith [hbound]

/-! ## Step B: Riesz representation of the polarized measure -/

/-- The algebraic (not-yet-continuous) sesquilinear form representing `S`, conjugate-linear in the
first argument and linear in the second — the convention Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin` expects. -/
noncomputable def cfcSesquilinearFormAux (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    H →ₛₗ[starRingEnd ℂ] H →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => starRingEnd ℂ (polarizedCfcScalarMeasure (hU := hU) U x y S))
    (fun x₁ x₂ y => by
      rw [polarizedCfcScalarMeasure_add_left U hU x₁ x₂ y hS, map_add])
    (fun c x y => by
      simp only [smul_eq_mul]
      rw [polarizedCfcScalarMeasure_smul_left U hU c x y hS, map_mul])
    (fun x y₁ y₂ => by
      rw [polarizedCfcScalarMeasure_add_right U hU x y₁ y₂ hS, map_add])
    (fun c x y => by
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [polarizedCfcScalarMeasure_smul_right U hU c x y hS, map_mul, Complex.conj_conj])

lemma cfcSesquilinearFormAux_apply (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) (x y : H) :
    cfcSesquilinearFormAux U hU S hS x y =
      starRingEnd ℂ (polarizedCfcScalarMeasure (hU := hU) U x y S) := rfl

/-- The continuous sesquilinear form, in the shape `InnerProductSpace.continuousLinearMapOfBilin`
consumes. -/
noncomputable def cfcSesquilinearForm (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ (cfcSesquilinearFormAux U hU S hS) 2 (fun x y => by
    rw [cfcSesquilinearFormAux_apply, RCLike.norm_conj]
    exact polarizedCfcScalarMeasure_norm_le_mul U hU x y hS)

@[simp]
lemma cfcSesquilinearForm_apply (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) (x y : H) :
    cfcSesquilinearForm U hU S hS x y =
      starRingEnd ℂ (polarizedCfcScalarMeasure (hU := hU) U x y S) := rfl

end CFCScalar

end QuantumMechanics

end
