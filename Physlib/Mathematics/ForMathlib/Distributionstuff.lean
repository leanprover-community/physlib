/-
Copyright (c) 2026 Cameron Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Lee
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

open Function Set TopologicalSpace UniformSpace

/-- Given normed spaces `E` and `E'` and a map between them `g : E → E'`, define a map
between the spaces of test functions `𝓓(Ω, F)` and `𝓓(Ω', F)`. -/
def testFunctionMap {E E'} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedSpace ℝ E] [NormedSpace ℝ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E} {Ω' : Opens E'} (g : E ≃L[ℝ] E')
    (h : g.invFun '' Ω' ⊆ ↑Ω) :
     TestFunction Ω' F ⊤ → TestFunction Ω F ⊤ := fun φ =>
  {
  toFun := φ ∘ g
  contDiff' := φ.contDiff.comp g.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph g.toHomeomorph
  tsupport_subset' := by
    trans  g.invFun '' Ω'
    · sorry

    sorry
  }
