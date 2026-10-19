/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import PhyslibAlpha.Mathematics.RepresentationDual
public import PhyslibAlpha.Relativity.SL2C.Basic
/-!
# The representation of `SL(2, ℂ)` on real Lorentz covectors

The covector representation pulled back along the covering map, and its dual.

## i. Overview

`Physlib.Relativity.Tensors.RealTensor.CoVector.Representation` carries the representation of
the Lorentz group on real Lorentz covectors. Composing it with the covering map
`SL(2, ℂ) →* LorentzGroup 3` gives `sl2Rep`, the representation of `SL(2, ℂ)` on the same
space, which is the form a spinor computation needs. Its dual acts on the dual basis
contravariantly: `sl2Rep_dual_dualBasis` says that `e^μ` goes to the combination given by the
column `μ` of the Lorentz matrix.

## ii. Key results

- `Lorentz.CoVector.sl2Rep` : the representation of `SL(2, ℂ)` on real Lorentz covectors.
- `Lorentz.CoVector.sl2Rep_dual_dualBasis` : dual covectors transform by the columns of the
  Lorentz matrix.

## iii. Table of contents

- A. The representation of `SL(2, ℂ)`

## iv. References

The Lorentz-group representation is in
`Physlib.Relativity.Tensors.RealTensor.CoVector.Representation`.

-/

@[expose] public section

open Module Matrix MatrixGroups Complex TensorProduct

namespace Lorentz

namespace CoVector

/-!

## A. The representation of `SL(2, ℂ)`

-/

/-- The representation of `SL(2,ℂ)` on real Lorentz covectors, obtained from the
  representation of the Lorentz group through the covering map
  `SL(2,ℂ) →* LorentzGroup 3`. -/
noncomputable def sl2Rep : Representation ℝ SL(2,ℂ) Lorentz.CoVector :=
  MonoidHom.comp Lorentz.CoVector.rep Lorentz.SL2C.toLorentzGroup

/-- The dual of the covector representation on the dual basis: dual covectors
  transform contravariantly, by the columns of the Lorentz matrix. -/
lemma sl2Rep_dual_dualBasis (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    Lorentz.CoVector.sl2Rep.dual Λ (Lorentz.CoVector.basis.dualBasis μ) =
      ∑ j, (Lorentz.SL2C.toLorentzGroup Λ).1 j μ •
        Lorentz.CoVector.basis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Lorentz.SL2C.toLorentzGroup Λ).1 j l) (fun j => ?_)
  rw [show Lorentz.CoVector.sl2Rep Λ⁻¹ =
      Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup Λ⁻¹) from rfl,
    Lorentz.CoVector.rep_apply_basis, ← LorentzGroup.coe_inv, map_inv, inv_inv]
  rfl

end CoVector

end Lorentz
