/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
/-!

# The Pati-Salam Model

The Pati-Salam model is a petite unified theory that unifies the Standard Model gauge group into
`SU(4) x SU(2) x SU(2)`.

This file currently contains informal-results about the Pati-Salam group.

## References

* Baez's Grand Unified Theories notes, cited throughout below. [ref: baez_guts_notes]
* A reference for the kernel of `inclSM`, cited below. [ref: arxiv_2201_07245]

-/

@[expose] public section

namespace PatiSalam
/-!

## The Pati-Salam gauge group.

-/

/-- The gauge group of the Pati-Salam model (unquotiented by ℤ₂), i.e., `SU(4) × SU(2) × SU(2)`. -/
informal_definition GaugeGroupI where
  deps := []
  tag := "6V2Q2"

/-- The homomorphism of the Standard Model gauge group into the Pati-Salam gauge group, i.e., the
group homomorphism `SU(3) × SU(2) × U(1) → SU(4) × SU(2) × SU(2)` taking `(h, g, α)` to
`(blockdiag (α h, α ^ (-3)), g, diag (α ^ 3, α ^(-3))`.

See page 54 of https://math.ucr.edu/home/baez/guts.pdf [ref: baez_guts_notes]
-/
informal_definition inclSM where
  deps := [``GaugeGroupI, ``StandardModel.GaugeGroupI]
  tag := "6V2RH"

/-- The kernel of the map `inclSM` is equal to the subgroup `StandardModel.gaugeGroupℤ₃SubGroup`.

See footnote 10 of https://arxiv.org/pdf/2201.07245 [ref: arxiv_2201_07245]
-/
informal_lemma inclSM_ker where
  deps := [``inclSM, ``StandardModel.gaugeGroupℤ₃SubGroup]
  tag := "6V2RQ"

/-- The group embedding from `StandardModel.GaugeGroupℤ₃` to `GaugeGroupI` induced by `inclSM` by
quotienting by the kernel `inclSM_ker`.
-/
informal_definition embedSMℤ₃ where
  deps := [``inclSM, ``StandardModel.GaugeGroupℤ₃, ``GaugeGroupI, ``inclSM_ker]
  tag := "6V2RY"

/-- The equivalence between `GaugeGroupI` and `Spin(6) × Spin(4)`. -/
informal_definition gaugeGroupISpinEquiv where
  deps := [``GaugeGroupI]
  tag := "6V2R7"

/-- The ℤ₂-subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₂-subgroup of `GaugeGroupI` with the non-trivial element `(-1, -1, -1)`.

See https://math.ucr.edu/home/baez/guts.pdf [ref: baez_guts_notes]
-/
informal_definition gaugeGroupℤ₂SubGroup where
  deps := [``GaugeGroupI]
  tag := "6V2SG"

/-- The gauge group of the Pati-Salam model with a ℤ₂ quotient, i.e., the quotient of `GaugeGroupI`
by the ℤ₂-subgroup `gaugeGroupℤ₂SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf [ref: baez_guts_notes]
-/
informal_definition GaugeGroupℤ₂ where
  deps := [``GaugeGroupI, ``gaugeGroupℤ₂SubGroup]
  tag := "6V2SM"

/-- The group `StandardModel.gaugeGroupℤ₆SubGroup` under the homomorphism `embedSM` factors through
the subgroup `gaugeGroupℤ₂SubGroup`.
-/
informal_lemma sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup where
  deps := [``inclSM, ``gaugeGroupℤ₂SubGroup]
  tag := "6V2SV"

/-- The group homomorphism from `StandardModel.GaugeGroupℤ₆` to `GaugeGroupℤ₂` induced by `embedSM`.
-/
informal_definition embedSMℤ₆Toℤ₂ where
  deps := [``inclSM, ``GaugeGroupℤ₂,
    ``sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup]
  tag := "6V2S4"

end PatiSalam
