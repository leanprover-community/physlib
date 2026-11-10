/-
Copyright (c) 2026 Cameron Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Lee
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.Continuous

open Function Set TopologicalSpace UniformSpace

/-- Given normed spaces `E` and `E'` and a map between them `g : E → E'`, define a map
between the spaces of test functions `𝓓(Ω', F)` and `𝓓(Ω, F)`. -/
noncomputable def testFunctionMap {E E'} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedSpace ℝ E] [NormedSpace ℝ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E} {Ω' : Opens E'} (g : E ≃L[ℝ] E')
    (h : g.invFun '' Ω' ⊆ ↑Ω) :
    TestFunction Ω' F ⊤ →L[ℝ] TestFunction Ω F ⊤ := by
  let pullback (φ : TestFunction Ω' F ⊤) : TestFunction Ω F ⊤ := {
    toFun := φ ∘ g
    contDiff' := φ.contDiff.comp g.contDiff
    hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph g.toHomeomorph
    tsupport_subset' := by
      trans g.invFun '' Ω'
      · intro x hx
        have hx' : g x ∈ tsupport φ :=
          (Set.ext_iff.mp (tsupport_comp_eq_preimage φ g.toHomeomorph) x).mp hx
        exact ⟨g x, φ.tsupport_subset hx', by simp⟩
      · exact h
  }
  refine TestFunction.limitCLM ℝ pullback (fun K hK => ?_) (fun K hK f => ?_)
  · let L : Compacts E := K.map g.symm g.symm.continuous
    have hL : (L : Set E) ⊆ Ω := by
      rintro x ⟨y, hy, rfl⟩
      exact h ⟨y, hK hy, by simp⟩
    let Pₗ : ContDiffMapSupportedIn E' F ⊤ K →ₗ[ℝ]
        ContDiffMapSupportedIn E F ⊤ L :=
      { toFun f := ⟨f ∘ g, f.contDiff.comp g.contDiff, by
          intro x hx
          apply f.zero_on_compl
          intro hgx
          apply hx
          exact ⟨g x, hgx, by simp⟩⟩
        map_add' := by intro f f'; ext x; rfl
        map_smul' := by intro a f; ext x; rfl }
    have hP : Continuous Pₗ := by
      apply (ContDiffMapSupportedIn.continuous_iff_comp Pₗ).2
      intro i
      let u : E →L[ℝ] E' := g
      let Rₗ : (E' [×i]→L[ℝ] F) →ₗ[ℝ] (E [×i]→L[ℝ] F) :=
        { toFun d := d.compContinuousLinearMap (fun _ : Fin i => u)
          map_add' := by intro d d'; ext1 v; simp
          map_smul' := by intro a d; ext1 v; simp }
      let R : (E' [×i]→L[ℝ] F) →L[ℝ] (E [×i]→L[ℝ] F) :=
        Rₗ.mkContinuous (‖u‖ ^ i) (fun d => by
          calc
            ‖Rₗ d‖ ≤ ‖d‖ * ∏ _ : Fin i, ‖u‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
            _ = ‖u‖ ^ i * ‖d‖ := by simp [mul_comm])
      let gC : ContinuousMap E E' := ⟨g, g.continuous⟩
      let Q : BoundedContinuousFunction E' (E' [×i]→L[ℝ] F) →L[ℝ]
          BoundedContinuousFunction E (E [×i]→L[ℝ] F) :=
        (R.compLeftContinuousBounded E).comp
          (BoundedContinuousFunction.compContinuousCLM _ ℝ gC)
      have hQ :
          (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i :
            ContDiffMapSupportedIn E F ⊤ L →L[ℝ]
              BoundedContinuousFunction E (E [×i]→L[ℝ] F)) ∘ Pₗ =
          Q ∘ (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i :
            ContDiffMapSupportedIn E' F ⊤ K →L[ℝ]
              BoundedContinuousFunction E' (E' [×i]→L[ℝ] F)) := by
        funext f
        ext x v
        change iteratedFDeriv ℝ i (fun z : E => f (g z)) x v =
          (iteratedFDeriv ℝ i f (g x)) (fun j => g (v j))
        exact congrArg (fun d => d v)
          (u.iteratedFDeriv_comp_right f.contDiff x (by simp))
      rw [hQ]
      exact Q.continuous.comp
        (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i : _ →L[ℝ] _).continuous
    let P : ContDiffMapSupportedIn E' F ⊤ K →L[ℝ]
        ContDiffMapSupportedIn E F ⊤ L :=
      { toLinearMap := Pₗ, cont := hP }
    exact TestFunction.ofSupportedInCLM ℝ hL ∘L P
  · ext x
    rfl

/--Having defined a CLM between test functions, we now define a map between spaces of
distributions `𝓓'(Ω, F)` and `𝓓'(Ω', F)`. -/
noncomputable def DistributionMap {E E'} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedSpace ℝ E] [NormedSpace ℝ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E} {Ω' : Opens E'} (g : E ≃L[ℝ] E')
    (h : g.invFun '' Ω' ⊆ ↑Ω) :
    Distribution Ω F ⊤ →L[ℝ] Distribution Ω' F ⊤ := {
    toFun f := f ∘ testFunctionMap g h
    map_add' := by sorry
    map_smul' := by sorry
    cont := by sorry
    }
