/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.DerivSubmodule.Basic
/-!
# The gauge weight decomposition of the scalar sector

The gauge weight decomposition of the Higgs derivative submodules and the weights that occur.

## i. Overview

The Higgs and conjugate-Higgs submodules carrying `n` derivatives each come with a gauge
weight decomposition, and the two join to one of `derivSubmodule n`. The weights that
occur are the two Higgs weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights
`(0, 0, ±1, 3)`; they do not depend on the number of derivatives.

## ii. Key results

- `derivSubmoduleGaugeWeight` : the gauge weight decomposition of the Higgs derivative
  submodules.
- `derivSubmoduleGaugeWeight_supp` : the gauge weights occurring in the Higgs derivative
  submodules, the two Higgs weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights
  `(0, 0, ±1, 3)`.

## iii. Table of contents

- A. The gauge weight decomposition

## iv. References

* None.

-/

/-!

## A. The gauge weight decomposition

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz
open LocalCovFieldAlgebra (repGaugeGroupI repLorentzGroup massWeightPoly)

namespace ScalarSector

/-- The gauge weight decomposition of the Higgs derivative submodules, the join of
  the decompositions of the Higgs and conjugate-Higgs submodules, whose weights are
  `(0, 0, ∓1, -3)` and `(0, 0, ±1, 3)` respectively. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition repGaugeGroupI (derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup (d := higgsSubmoduleGaugeWeight n)
      (d' := barHiggsSubmoduleGaugeWeight n))
    _ (by rw [derivSubmodule])

/-- The gauge weights occurring in the Higgs derivative submodules are the two Higgs
  weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights `(0, 0, ±1, 3)`. -/
lemma derivSubmoduleGaugeWeight_supp (n : ℕ) :
    (derivSubmoduleGaugeWeight n).supp
      = {((0, 0, -1, -3) : GaugeWeight), (0, 0, 1, -3), (0, 0, 1, 3), (0, 0, -1, 3)} :=
  rfl

end ScalarSector

end StandardModel
