/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.Prod
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod
/-!
# The fermionic algebra of a direct sum

## i. Overview

Two matter fields, valued in `V` and `W`, are jointly a single matter field valued in
`V × W`; its fermionic algebra is the **exterior product** of the two individual fermionic
algebras. That is the content of `FermionicAlgebra.prodEquiv`: an algebra equivalence

`FermionicAlgebra (V × W) ≃ₐ[ℂ] (evenOdd V ᵍ⊗[ℂ] evenOdd W)`

onto the graded tensor product of the two algebras with respect to their Fermi-parity
gradings. The graded — as opposed to ordinary — tensor product is what makes generators of
*different* species anticommute, as fermions must.

The proof is two steps. First the component space of a direct sum is the direct sum of the
component spaces (`JetComponentSpace.prodEquiv`) — duals and conjugates both split. Then the
exterior algebra of a direct sum is the graded tensor product of the exterior algebras,
which is `CliffordAlgebra.prodEquiv` specialized to the zero quadratic form.

## ii. Key results

- `FermionicAlgebra.evenOdd` : the Fermi-parity grading.
- `FermionicAlgebra.prodEquiv` : the fermionic algebra of a direct sum is the exterior
  product of the fermionic algebras.

## iii. Table of contents

- A. The component space of a direct sum
- B. The Fermi-parity grading
- C. The exterior product decomposition

-/

@[expose] public section

open scoped TensorProduct

namespace StandardModel

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-!

## A. The component space of a direct sum

The splitting `JetComponentSpace.prodEquiv` of the component space of a direct sum lives
with the component space itself, in `Physlib.Particles.StandardModel.Matter.JetComponentSpace.Basic`.

-/

/-!

## B. The Fermi-parity grading

-/

/-- **The Fermi-parity grading** of the fermionic algebra: the `ZMod 2` grading of the
  exterior algebra by the number of component functions in a monomial. An even element
  commutes with everything; two odd elements anticommute. -/
abbrev FermionicAlgebra.evenOdd (V : Type) [AddCommGroup V] [Module ℂ V] :
    ZMod 2 → Submodule ℂ (FermionicAlgebra V) :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (JetComponentSpace V))

/-!

## C. The exterior product decomposition

-/

/-- **The fermionic algebra of a direct sum is the exterior product of the fermionic
  algebras.** Two matter fields taken together are one field valued in the direct sum of
  their target spaces, and its fermionic algebra is the graded tensor product of theirs.

  The tensor product must be the *graded* one `ᵍ⊗`: an ordinary `⊗[ℂ]` would make a
  generator of the first field commute with a generator of the second, whereas fermionic
  generators anticommute across species just as they do within one. -/
noncomputable def FermionicAlgebra.prodEquiv (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    FermionicAlgebra (V × W) ≃ₐ[ℂ]
      (FermionicAlgebra.evenOdd V ᵍ⊗[ℂ] FermionicAlgebra.evenOdd W) :=
  (ExteriorAlgebra.congr (JetComponentSpace.prodEquiv V W)).trans <|
    (CliffordAlgebra.equivOfIsometry
        (Q₁ := (0 : QuadraticForm ℂ (JetComponentSpace V × JetComponentSpace W)))
        (Q₂ := (0 : QuadraticForm ℂ (JetComponentSpace V)).prod
          (0 : QuadraticForm ℂ (JetComponentSpace W)))
        ⟨LinearEquiv.refl ℂ _, fun _ => by simp⟩).trans
      (CliffordAlgebra.prodEquiv _ _)

end StandardModel
