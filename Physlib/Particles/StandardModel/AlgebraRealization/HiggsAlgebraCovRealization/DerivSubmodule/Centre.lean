/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.DerivSubmodule.Basic
public import Physlib.Relativity.LorentzGroup.Invariants.Centre
/-!
# The centre of `SL(2,ℂ)` on the Higgs sector

The Higgs is a Lorentz scalar, so the centre of `SL(2,ℂ)` acts on its derivative submodules by
`+1`: the covariant-derivative slots mix by the Lorentz matrix, which is the identity at the
centre, and the value index is inert because the value space carries the trivial
representation. The conjugate tower is the same, conjugation of the trivial representation
being trivial again.

This is the integer-spin half of the parity count the Yukawa classification runs. Paired with
`IsFermionSector.derivSubmodule_le_centreEigenspace`, which gives the fermions `-1`, it makes
a product with a single fermion factor carry `-1`, and a subspace of sign `-1` carries no
Lorentz invariant.

- A. The two towers
- B. The Higgs derivative submodules

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.Invariants

namespace HiggsAlgebraCovRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)

/-!

## A. The two towers

Each tower feeds `range_le_centreEigenspace` with its own Lorentz law and the sign of its
value space, which is `+1` for both: the value space of the Higgs tower carries the trivial
representation and that of the conjugate tower its conjugate.

-/

include h in
/-- The Higgs symbols carry the sign `+1`: their value space is a Lorentz scalar. -/
lemma range_covH_le_centreEigenspace (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (h.covH n l) ≤ centreEigenspace repLorentz 1 :=
  range_le_centreEigenspace h.repLorentz_H (by ext x; simp) l

include h in
/-- The conjugate Higgs symbols carry the sign `+1`, for the same reason. -/
lemma range_covBarH_le_centreEigenspace (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (h.covBarH n l) ≤ centreEigenspace repLorentz 1 :=
  range_le_centreEigenspace h.repLorentz_barH (by ext x; simp) l

/-!

## B. The Higgs derivative submodules

The derivative submodule is the join of the two towers over the derivative slots, and an
eigenspace is closed under joins.

-/

include h in
/-- **The centre of `SL(2,ℂ)` acts on the Higgs derivative submodules by `+1`**, for any
  number of covariant derivatives: the Higgs is a Lorentz scalar and the derivative slots are
  inert at the centre. -/
theorem derivSubmodule_le_centreEigenspace (n : ℕ) :
    h.derivSubmodule n ≤ centreEigenspace repLorentz 1 := by
  rw [derivSubmodule, higgsSubmodule, barHiggsSubmodule]
  exact sup_le (iSup_le fun l => h.range_covH_le_centreEigenspace n l)
    (iSup_le fun l => h.range_covBarH_le_centreEigenspace n l)

end HiggsAlgebraCovRealization

end StandardModel
