/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Prod
/-!
# The bosonic algebra of a direct sum

## i. Overview

Two bosonic matter fields, valued in `V` and `W`, are jointly a single matter field valued
in `V × W`; its bosonic algebra is the **tensor product** of the two individual bosonic
algebras. That is the content of `BosonicAlgebra.prodEquiv`: an algebra equivalence

`BosonicAlgebra (M.prod N h) ≃ₐ[ℂ] BosonicAlgebra M ⊗[ℂ] BosonicAlgebra N`.

Unlike the fermionic analogue `FermionicAlgebra.prodEquiv`, the *ordinary* tensor product
suffices: bosonic generators of different species commute, so no grading is needed.

The proof is two steps. First the component space of a direct sum is the direct sum of the
component spaces (`JetComponentSpace.prodEquiv`). Then the symmetric algebra of a direct
sum is the tensor product of the symmetric algebras, which is
`SymmetricAlgebra.prodEquiv`.

## ii. Key results

- `BosonicAlgebra.prodEquiv` : the bosonic algebra of a direct sum is the tensor product
  of the bosonic algebras.

## iii. Table of contents

- A. The tensor product decomposition

-/

@[expose] public section

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

open scoped TensorProduct

namespace StandardModel

/-!

## A. The tensor product decomposition

-/

/-- **The bosonic algebra of a direct sum is the tensor product of the bosonic algebras.**
  Two bosonic matter fields taken together are one field valued in the direct sum of their
  target spaces, and its bosonic algebra is the tensor product of theirs. The ordinary —
  rather than the graded — tensor product is correct here: bosonic generators commute
  across species just as they do within one. -/
noncomputable def BosonicAlgebra.prodEquiv (M N : MatterField jets)
    (h : M.massWeight = N.massWeight) :
    BosonicAlgebra (M.prod N h) ≃ₐ[ℂ] BosonicAlgebra M ⊗[ℂ] BosonicAlgebra N :=
  (SymmetricAlgebra.congr (JetComponentSpace.prodEquiv M N h)).trans
    SymmetricAlgebra.prodEquiv

end StandardModel
