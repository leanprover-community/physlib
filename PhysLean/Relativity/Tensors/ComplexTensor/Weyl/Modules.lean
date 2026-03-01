/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
/-!

## Modules associated with Fermions

Weyl fermions live in the vector space `ℂ^2`, defined here as `Fin 2 → ℂ`.
However if we simply define the Module of Weyl fermions as `Fin 2 → ℂ` we get casting problems,
where e.g. left-handed fermions can be cast to right-handed fermions etc.
To overcome this, for each type of Weyl fermion we define a structure that wraps `Fin 2 → ℂ`,
and these structures we define the instance of a module. This prevents casting between different
types of fermions.

-/

namespace Fermion
noncomputable section

section LeftHanded

/-- The module in which left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure LeftHandedModule where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace LeftHandedModule

/-- The equivalence between `LeftHandedModule` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : LeftHandedModule ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `LeftHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid LeftHandedModule := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `LeftHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup LeftHandedModule := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `LeftHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ LeftHandedModule := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `LeftHandedModule` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : LeftHandedModule ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `LeftHandedModule` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : LeftHandedModule) := toFin2ℂEquiv ψ

end LeftHandedModule

end LeftHanded

section AltLeftHanded

/-- The module in which alt-left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure AltLeftHandedModule where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace AltLeftHandedModule

/-- The equivalence between `AltLeftHandedModule` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : AltLeftHandedModule ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `AltLeftHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid AltLeftHandedModule := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `AltLeftHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup AltLeftHandedModule := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `AltLeftHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ AltLeftHandedModule := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `AltLeftHandedModule` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : AltLeftHandedModule ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `AltLeftHandedModule` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : AltLeftHandedModule) := toFin2ℂEquiv ψ

end AltLeftHandedModule

end AltLeftHanded

section RightHanded

/-- The module in which right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure RightHandedModule where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace RightHandedModule

/-- The equivalence between `RightHandedModule` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : RightHandedModule ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `RightHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid RightHandedModule := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `RightHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup RightHandedModule := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `RightHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ RightHandedModule := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `RightHandedModule` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : RightHandedModule ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `RightHandedModule` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : RightHandedModule) := toFin2ℂEquiv ψ

end RightHandedModule

end RightHanded

section AltRightHanded

/-- The module in which alt-right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure AltRightHandedModule where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace AltRightHandedModule

/-- The equivalence between `AltRightHandedModule` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : AltRightHandedModule ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `AltRightHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid AltRightHandedModule := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `AltRightHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup AltRightHandedModule := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `AltRightHandedModule` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ AltRightHandedModule := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `AltRightHandedModule` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : AltRightHandedModule ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `AltRightHandedModule` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : AltRightHandedModule) := toFin2ℂEquiv ψ

end AltRightHandedModule

end AltRightHanded

end
end Fermion
