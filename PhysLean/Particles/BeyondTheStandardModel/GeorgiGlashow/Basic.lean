/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.Basic
/-!

# The Georgi-Glashow Model

The Georgi-Glashow model is a grand unified theory that unifies the Standard Model gauge group into
`SU(5)`.

This file currently contains informal-results about the Georgi-Glashow group.

-/

@[expose] public section

namespace GeorgiGlashow

/-- The gauge group of the Georgi-Glashow model, i.e., `SU(5)`. -/
informal_definition GaugeGroupI where
  deps := []
  tag := "6V2WM"

/-- The homomorphism of the Standard Model gauge group into the Georgi-Glashow gauge group, i.e.,
the group homomorphism `SU(3) × SU(2) × U(1) → SU(5)` taking `(h, g, α)` to
`blockdiag (α ^ 3 g, α ^ (-2) h)`.

See page 34 of https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition inclSM where
  deps := [``GaugeGroupI, ``StandardModel.GaugeGroupI]
  tag := "6V2WS"

/-- The kernel of the map `inclSM` is equal to the subgroup `StandardModel.gaugeGroupℤ₆SubGroup`.

See page 34 of https://math.ucr.edu/home/baez/guts.pdf
-/
informal_lemma inclSM_ker where
  deps := [``inclSM]
  tag := "6V2W2"

/-- The group embedding from `StandardModel.GaugeGroupℤ₆` to `GaugeGroupI` induced by `inclSM` by
quotienting by the kernel `inclSM_ker`.
-/
informal_definition embedSMℤ₆ where
  deps := [``inclSM, ``GaugeGroupI, ``inclSM_ker]
  tag := "6V2XA"

end GeorgiGlashow
