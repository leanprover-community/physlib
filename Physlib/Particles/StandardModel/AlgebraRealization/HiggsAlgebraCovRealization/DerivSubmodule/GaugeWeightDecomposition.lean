/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.DerivSubmodule.Basic
/-!
# The gauge weight decomposition of the Higgs sector

The Higgs and conjugate-Higgs submodules carrying `n` derivatives each come with a gauge
weight decomposition, and the two join to one of `derivSubmodule n`.  The weights that
occur are the two Higgs weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights
`(0, 0, ±1, 3)`; they do not depend on the number of derivatives.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace HiggsAlgebraCovRealization

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)

/-- **The gauge weight decomposition of the Higgs derivative submodules**: the join of
  the decompositions of the Higgs and conjugate-Higgs submodules, whose weights are
  `(0, 0, ∓1, -3)` and `(0, 0, ±1, 3)` respectively.

  This is an instance: its statement mentions `h`, so unification against the goal
  recovers the sector and with it the rest of the structure's implicit data. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition rep (h.derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup (d := h.higgsSubmoduleGaugeWeight n)
      (d' := h.barHiggsSubmoduleGaugeWeight n))
    _ (by rw [derivSubmodule])

/-- The gauge weights occurring in the Higgs derivative submodules: the two Higgs
  weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights `(0, 0, ±1, 3)`. -/
lemma derivSubmoduleGaugeWeight_supp (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).supp
      = {((0, 0, -1, -3) : GaugeWeight), (0, 0, 1, -3), (0, 0, 1, 3), (0, 0, -1, 3)} :=
  rfl

end HiggsAlgebraCovRealization

end StandardModel
