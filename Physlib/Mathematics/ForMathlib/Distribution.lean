/-
Copyright (c) 2026 Cameron Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Lee
-/
module

public import Physlib.Mathematics.ForMathlib.TestFunction
/-!

# Distribution

## i. Overview

In this module, we define continuous linear maps between spaces of distributions `𝓓'(Ω, F)`
and `𝓓'(Ω', F)`, using `TestFunction.compCLMofContinuousLinearEquiv`.

## ii. Key results

- `compContinuousLinearEquiv` : A continuous linear map between spaces of distributions `𝓓'(Ω, F)`
  and `𝓓'(Ω', F)`.

## iii. Table of contents

- A. Continuous linear maps

## iv. References

* None.
-/

@[expose] public section

/-!
## A. Continuous linear maps
-/

namespace Distribution

open Function Set TopologicalSpace UniformSpace
open TestFunction

/--Having defined a CLM between test functions, we now define a continuous linear map between spaces
of distributions `𝓓'(Ω, F)` and `𝓓'(Ω', F)`. -/
noncomputable def compContinuousLinearEquiv {E E'} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E] [NormedSpace ℝ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E} {Ω' : Opens E'} (g : E ≃L[ℝ] E')
    (h : g.invFun '' Ω' ⊆ ↑Ω) :
    Distribution Ω F ⊤ →L[ℝ] Distribution Ω' F ⊤ :=
    (compCLMofContinuousLinearEquiv (F := ℝ) g h).precompCompactConvergenceCLM F

end Distribution
