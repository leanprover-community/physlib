/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.Statistics
/-!
# The field algebras of a direct sum

## i. Overview

Two matter fields, valued in `V` and `W`, are jointly a single matter field valued in
`V × W`. For bosonic fields its algebra is the ordinary tensor product of the two bosonic
algebras (`BosonicAlgebra.prodEquiv`); for fermionic fields it is the *graded* tensor
product of the two fermionic algebras with their Fermi-parity grading
(`FermionicAlgebra.prodEquiv`), which is what makes fermions of different species
anticommute.

## ii. Key results

- `BosonicAlgebra.prodEquiv` :
  `BosonicAlgebra (V × W) ≃ₐ[ℂ] BosonicAlgebra V ⊗[ℂ] BosonicAlgebra W`.
- `FermionicAlgebra.evenOdd` : the Fermi-parity grading.
- `FermionicAlgebra.prodEquiv` : the graded tensor product decomposition.

-/

@[expose] public section

section Bosonic

open scoped TensorProduct


/-!

## A. The tensor product decomposition

-/

/-- **The bosonic algebra of a direct sum is the tensor product of the bosonic algebras.**
  Two bosonic matter fields taken together are one field valued in the direct sum of their
  target spaces, and its bosonic algebra is the tensor product of theirs. The ordinary —
  rather than the graded — tensor product is correct here: bosonic generators commute
  across species just as they do within one. -/
noncomputable def BosonicAlgebra.prodEquiv (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    BosonicAlgebra (V × W) ≃ₐ[ℂ] BosonicAlgebra V ⊗[ℂ] BosonicAlgebra W :=
  (SymmetricAlgebra.congr (JetComponentSpace.prodEquiv V W)).trans
    SymmetricAlgebra.prodEquiv

end Bosonic

section Fermionic

open scoped TensorProduct

/-- Transport of an exterior algebra along a linear equivalence of the underlying module. -/
noncomputable def ExteriorAlgebra.congr {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    ExteriorAlgebra R A ≃ₐ[R] ExteriorAlgebra R B :=
  CliffordAlgebra.equivOfIsometry ⟨e, fun _ => rfl⟩


variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-!

## A. The component space of a direct sum

The splitting `JetComponentSpace.prodEquiv` of the component space of a direct sum lives
with the component space itself, in
  `Physlib.ClassicalFieldTheory.JetAlgebra.JetComponentSpace.Basic`.

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

end Fermionic
