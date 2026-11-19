/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.DerivSubmodule.Basic
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.CentreEigenspace
/-!
# The centre of `SL(2,ℂ)` on the scalar sector

The centre of `SL(2,ℂ)` acts by `+1` on the Higgs derivative submodules.

## i. Overview

The Higgs is a Lorentz scalar, so the centre of `SL(2,ℂ)` acts on its derivative submodules by
`+1`. The covariant-derivative slots mix by the Lorentz matrix, which is the identity at the
centre, and the value index is inert because the value space carries the trivial
representation. The conjugate tower is the same, conjugation of the trivial representation
being trivial again.

This is the integer-spin half of the parity count the Yukawa classification runs. Paired with
`StandardModel.FermionSector.derivSubmodule_le_centreEigenspace`, which gives the fermions
`-1`, it makes a product with a single fermion factor carry `-1`, and a subspace of sign `-1`
carries no Lorentz invariant.

## ii. Key results

- `range_covH_le_centreEigenspace` : the Higgs symbols carry the sign `+1`, their value space
  being a Lorentz scalar.
- `range_covBarH_le_centreEigenspace` : the conjugate Higgs symbols carry the sign `+1`, for the
  same reason.
- `derivSubmodule_le_centreEigenspace` : the centre of `SL(2,ℂ)` acts on the Higgs derivative
  submodules by `+1`, for any number of covariant derivatives.

## iii. Table of contents

- A. The two towers
- B. The Higgs derivative submodules

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.Invariants
open LocalCovFieldAlgebra (repGaugeGroupI repLorentzGroup massWeightPoly)

namespace ScalarSector

/-!

## A. The two towers

Each tower feeds `range_le_centreEigenspace` with its own Lorentz law and the sign of its
value space, which is `+1` for both. The value space of the Higgs tower carries the trivial
representation and that of the conjugate tower its conjugate.

-/

/-- The Higgs symbols carry the sign `+1`, their value space being a Lorentz scalar. -/
lemma range_covH_le_centreEigenspace (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (covH n l) ≤ centreEigenspace repLorentzGroup 1 :=
  range_le_centreEigenspace repLorentz_H (by ext x; simp) l

/-- The conjugate Higgs symbols carry the sign `+1`, for the same reason. -/
lemma range_covBarH_le_centreEigenspace (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (covBarH n l) ≤ centreEigenspace repLorentzGroup 1 :=
  range_le_centreEigenspace repLorentz_barH (by ext x; simp) l

/-!

## B. The Higgs derivative submodules

The derivative submodule is the join of the two towers over the derivative slots, and an
eigenspace is closed under joins.

-/

/-- The centre of `SL(2,ℂ)` acts on the Higgs derivative submodules by `+1`, for any
  number of covariant derivatives. The Higgs is a Lorentz scalar and the derivative slots are
  inert at the centre. -/
lemma derivSubmodule_le_centreEigenspace (n : ℕ) :
    derivSubmodule n ≤ centreEigenspace repLorentzGroup 1 := by
  rw [derivSubmodule, higgsSubmodule, barHiggsSubmodule]
  exact sup_le (iSup_le fun l => range_covH_le_centreEigenspace n l)
    (iSup_le fun l => range_covBarH_le_centreEigenspace n l)

end ScalarSector

end StandardModel
