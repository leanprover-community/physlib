/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.JBW.Basic
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.ProjectionResolution
public import PhyslibAlpha.AlgebraicFramework.Measurement.ProbabilityLaw
public import PhyslibAlpha.AlgebraicFramework.Measurement.MeasurableOutcome
public import PhyslibAlpha.AlgebraicFramework.Measurement.BoundedScalarization

/-!

# Projection resolutions in JBW-algebras

`MeasurableProjectionResolution` is defined at the weaker Jordan order-unit level and reuses the
entire effect-valued-measure API.  This JBW file adds the two genuinely JBW ingredients: normal
states produce ordinary probability laws, and the separating normal-state family detects equality
of projection resolutions.

It is deliberately only the bounded spectral-measure boundary.  An unbounded Hilbert-space
spectral integral carries an additional square-moment domain and remains a represented/affiliated
construction above this intrinsic JBW layer.

-/

@[expose] public section

open MeasureTheory

namespace MeasurableProjectionResolution

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedJordanAlgebra E] [PartialOrder E]
  [IsOrderedAddMonoid E] [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [JBAlgebra E]
  [IsJBOrderUnit E] [JBWAlgebra E]

/-- The identity order isomorphism into the explicit order-unit-norm copy, bundled as a normal
channel.  It changes topology only through the codomain type synonym; algebraic and order data
remain literally the same. -/
noncomputable def toWithOrderUnitNormChannel : E →ₚ₁[ℝ] WithOrderUnitNorm E :=
  UnitalPositiveLinearMap.ofLinearMap (WithOrderUnitNorm.linearEquiv (E := E)).toLinearMap
    (fun _ hx => hx) rfl

omit [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [JBAlgebra E] [IsJBOrderUnit E] [JBWAlgebra E] in
/-- The norm-copy channel is normal because it is the identity on the underlying ordered set. -/
theorem toWithOrderUnitNormChannel_isNormal :
    (toWithOrderUnitNormChannel (E := E)).IsNormal := by
  intro D x hD hdir hLUB
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    change y ≤ x
    exact hLUB.1 hy
  · intro y hy
    change x ≤ (show E from y)
    apply hLUB.2
    intro z hz
    have hzy := hy ⟨z, hz, rfl⟩
    change z ≤ (show E from y) at hzy
    exact hzy

/-- The inverse identity order isomorphism from the norm copy back to the ambient ordered space,
again packaged as a channel rather than by changing any global instances. -/
noncomputable def fromWithOrderUnitNormChannel :
    WithOrderUnitNorm E →ₚ₁[ℝ] E :=
  UnitalPositiveLinearMap.ofLinearMap (WithOrderUnitNorm.linearEquiv (E := E)).symm.toLinearMap
    (fun _ hx => hx) rfl

omit [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [JBAlgebra E] [IsJBOrderUnit E] [JBWAlgebra E] in
/-- The inverse norm-copy channel is normal for the same order-theoretic reason. -/
theorem fromWithOrderUnitNormChannel_isNormal :
    (fromWithOrderUnitNormChannel (E := E)).IsNormal := by
  intro D x hD hdir hLUB
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    change (show E from y) ≤ (show E from x)
    exact hLUB.1 hy
  · intro y hy
    change (show E from x) ≤ y
    apply hLUB.2
    intro z hz
    have hzy := hy ⟨z, hz, rfl⟩
    change (show E from z) ≤ y at hzy
    exact hzy

/-- The scalar identity channel into its explicit order-unit-norm copy.  This is stated directly:
the generic JB-copy channel is deliberately not invoked here, since `ℝ` need not carry the
ambient `NormedJordanAlgebra` structure used by the JB layer. -/
noncomputable def realToWithOrderUnitNormChannel :
    ℝ →ₚ₁[ℝ] WithOrderUnitNorm ℝ :=
  UnitalPositiveLinearMap.ofLinearMap (WithOrderUnitNorm.linearEquiv (E := ℝ)).toLinearMap
    (fun _ hx => hx) rfl

/-- The scalar norm-copy channel is normal because it is the identity on the ordered carrier. -/
theorem realToWithOrderUnitNormChannel_isNormal :
    realToWithOrderUnitNormChannel.IsNormal := by
  intro D x hD hdir hLUB
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    change y ≤ x
    exact hLUB.1 hy
  · intro y hy
    change x ≤ (show ℝ from y)
    apply hLUB.2
    intro z hz
    have hzy := hy ⟨z, hz, rfl⟩
    change z ≤ (show ℝ from y) at hzy
    exact hzy

/-- A normal state, regarded between explicit order-unit-norm copies.  This is the coherent
channel used to scalarize the copied bounded Borel calculus. -/
noncomputable def normalStateToWithOrderUnitNormChannel (ω : 𝓢[ℝ, E]) :
    WithOrderUnitNorm E →ₚ₁[ℝ] WithOrderUnitNorm ℝ :=
  realToWithOrderUnitNormChannel.comp
    (ω.comp (fromWithOrderUnitNormChannel (E := E)))

omit [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [JBAlgebra E] [IsJBOrderUnit E] [JBWAlgebra E] in
/-- Normality of a state is preserved by the two explicit order-unit-copy transports. -/
theorem normalStateToWithOrderUnitNormChannel_isNormal (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    (normalStateToWithOrderUnitNormChannel ω).IsNormal := by
  exact (fromWithOrderUnitNormChannel_isNormal (E := E)).comp
    (hω.comp realToWithOrderUnitNormChannel_isNormal)

/-- Bounded Borel integration of a projection resolution in the explicit order-unit-norm copy.
The input measure is transported through the normal identity channel, and completeness is supplied
by `JBAlgebra.completeWithOrderUnitNorm`; the ambient JB norm on `E` is never replaced. -/
noncomputable def boundedBorelWithOrderUnitNorm (P : MeasurableProjectionResolution Ω E)
    (f : Ω → ℝ) (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : WithOrderUnitNorm E := by
  let _ : NormedAddCommGroup (WithOrderUnitNorm E) :=
    IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup
  let e : WithOrderUnitNorm E ≃ₗᵢ[ℝ] E :=
    { __ := (WithOrderUnitNorm.linearEquiv (E := E)).symm
      norm_map' := fun x => by
        change ‖(show E from x)‖ = ‖x‖
        rw [show ‖x‖ = IsArchimedeanOrderUnit.orderUnitNorm (show E from x) by rfl]
        exact JBAlgebra.norm_eq_orderUnitNorm (show E from x) }
  let _ : CompleteSpace (WithOrderUnitNorm E) :=
    (completeSpace_congr (e := e.toLinearEquiv.toEquiv) e.isometry.isUniformEmbedding).mpr
      JBAlgebra.toCompleteSpace
  exact EffectValuedMeasure.integral hf hM
    (P.toEffectValuedMeasure.map (toWithOrderUnitNormChannel (E := E))
      (toWithOrderUnitNormChannel_isNormal (E := E)))

omit [JBWAlgebra E] in
/-- On an indicator, the copied bounded Borel calculus recovers the corresponding event
projection, transported through the norm-copy channel. -/
theorem boundedBorelWithOrderUnitNorm_indicator (P : MeasurableProjectionResolution Ω E)
    {s : Set Ω} (hs : MeasurableSet s) :
    P.boundedBorelWithOrderUnitNorm (s.indicator fun _ : Ω => (1 : ℝ))
        (measurable_const.indicator hs) (M := 1) (by intro x; by_cases hx : x ∈ s <;> simp [hx]) =
      toWithOrderUnitNormChannel (E := E) (P s hs : E) := by
  let : NormedAddCommGroup (WithOrderUnitNorm E) :=
    IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup
  let e : WithOrderUnitNorm E ≃ₗᵢ[ℝ] E :=
    { __ := (WithOrderUnitNorm.linearEquiv (E := E)).symm
      norm_map' := fun x => by
        change ‖(show E from x)‖ = ‖x‖
        rw [show ‖x‖ = IsArchimedeanOrderUnit.orderUnitNorm (show E from x) by rfl]
        exact JBAlgebra.norm_eq_orderUnitNorm (show E from x) }
  let : CompleteSpace (WithOrderUnitNorm E) :=
    (completeSpace_congr (e := e.toLinearEquiv.toEquiv) e.isometry.isUniformEmbedding).mpr
      JBAlgebra.toCompleteSpace
  let c : Bool → ℝ := fun b => if b then 1 else 0
  let pieces : Bool → Set Ω := fun b => if b then s else sᶜ
  have hpieces : EffectValuedMeasure.IsPartition pieces :=
    { measurable := by intro b; cases b <;> simp [pieces, hs]
      disjoint := by
        intro b b' hne
        cases b <;> cases b'
        · exact (hne rfl).elim
        · exact disjoint_compl_left
        · exact disjoint_compl_right
        · exact (hne rfl).elim
      cover := by
        apply Set.Subset.antisymm
        · exact Set.subset_univ _
        · intro x _
          by_cases hx : x ∈ s
          · exact Set.mem_iUnion.2 ⟨true, by simp [pieces, hx]⟩
          · exact Set.mem_iUnion.2 ⟨false, by simp [pieces, hx]⟩ }
  have hvalue : ∀ x, EffectValuedMeasure.simpleValue c pieces x =
      s.indicator (fun _ : Ω => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [EffectValuedMeasure.simpleValue_apply_of_mem hpieces (i := true)]
      · simp [c, hx]
      · simp [pieces, hx]
    · rw [EffectValuedMeasure.simpleValue_apply_of_mem hpieces (i := false)]
      · simp [c, hx]
      · simp [pieces, hx]
  rw [boundedBorelWithOrderUnitNorm, EffectValuedMeasure.integral_eq_simpleIntegral
    (measurable_const.indicator hs) (by intro x; by_cases hx : x ∈ s <;> simp [hx])
    hpieces hvalue]
  unfold EffectValuedMeasure.simpleIntegral
  simp [c, pieces]

/-- Scalarization of the copied bounded Borel calculus, still in the explicit order-unit-norm
copy of `ℝ`.  The final conversion to ordinary scalars is the separately proved isometry
`WithOrderUnitNorm.realLinearIsometryEquiv`. -/
noncomputable def scalarBoundedBorelWithOrderUnitNorm (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) (f : Ω → ℝ) (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) : WithOrderUnitNorm ℝ :=
  EffectValuedMeasure.scalarCopyIntegral f hf hM
    ((P.toEffectValuedMeasure.map (toWithOrderUnitNormChannel (E := E))
      (toWithOrderUnitNormChannel_isNormal (E := E))).map
        (normalStateToWithOrderUnitNormChannel ω)
        (normalStateToWithOrderUnitNormChannel_isNormal ω hω))

/-- The ordinary real scalar bounded Borel calculus of a normal JBW state.  The integral is first
taken in `WithOrderUnitNorm ℝ`; only then is it transported through the canonical real-line
isometry.  Thus this endpoint cannot silently inherit or replace the JB norm on `E`. -/
noncomputable def scalarBoundedBorel (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) (f : Ω → ℝ) (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) : ℝ :=
  WithOrderUnitNorm.realLinearIsometryEquiv
    (P.scalarBoundedBorelWithOrderUnitNorm ω hω f hf hM)

/-- A normal JBW state turns a projection resolution into its ordinary scalar probability law.
This is the existing effect-valued-measure scalarization, applied to the inherited measure rather
than reconstructed in the JBW layer. -/
noncomputable def probabilityLaw (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) : ProbabilityMeasure Ω :=
  P.toEffectValuedMeasure.probabilityLaw ω hω

omit [JBAlgebra E] [IsJBOrderUnit E] [JBWAlgebra E] in
/-- Evaluation of the normal-state probability law on a measurable event is the state evaluated
at the corresponding spectral projection. -/
theorem probabilityLaw_apply (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) (s : Set Ω) (hs : MeasurableSet s) :
    (P.probabilityLaw ω hω : Measure Ω) s = ENNReal.ofReal (ω (P s hs : E)) :=
  EffectValuedMeasure.probabilityLaw_apply P.toEffectValuedMeasure ω hω s hs

/-- A JBW projection resolution is determined by the ordinary probability laws it induces in all
normal states.  This is the operational form of normal-state separation: it lets clients compare
spectral resolutions through measurable probabilities rather than their ambient observables. -/
theorem eq_of_forall_normal_probabilityLaw_eq {P Q : MeasurableProjectionResolution Ω E}
    (h : ∀ ω : 𝓢[ℝ, E], ∀ hω : ω.IsNormal,
      P.probabilityLaw ω hω = Q.probabilityLaw ω hω) : P = Q := by
  apply MeasurableProjectionResolution.ext
  intro s hs
  apply JBWAlgebra.eq_of_forall_normal_state_eq
  intro ω hω
  have hmeasure : (P.probabilityLaw ω hω : Measure Ω) s =
      (Q.probabilityLaw ω hω : Measure Ω) s := by
    rw [h ω hω]
  rw [P.probabilityLaw_apply ω hω s hs, Q.probabilityLaw_apply ω hω s hs] at hmeasure
  exact (ENNReal.ofReal_eq_ofReal_iff
    (ω.map_nonneg (P s hs).2.1) (ω.map_nonneg (Q s hs).2.1)).mp hmeasure

/-- Normal states separate measurable projection resolutions pointwise. -/
theorem eq_of_forall_normal_state_eq {P Q : MeasurableProjectionResolution Ω E}
    (h : ∀ ω : 𝓢[ℝ, E], ω.IsNormal → ∀ s hs,
      ω (P s hs : E) = ω (Q s hs : E)) : P = Q := by
  apply MeasurableProjectionResolution.ext
  intro s hs
  apply JBWAlgebra.eq_of_forall_normal_state_eq
  intro ω hω
  exact h ω hω s hs

end MeasurableProjectionResolution
