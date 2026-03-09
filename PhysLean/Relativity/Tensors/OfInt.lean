/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.Basic
/-!

# Basis for tensors in a tensor species

-/

@[expose] public section

open Module IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] (S : TensorSpecies k C G)

namespace Tensor

/-- A tensor with integer components with respect to the basis. -/
abbrev TensorInt {n : ℕ} (c : Fin n → C) := (ComponentIdx (S := S) c) → ℤ

namespace TensorInt

variable {k : Type} [CommRing k] {G : Type} [Group G] {S : TensorSpecies k C G}

/-- The element of `S.Tensor c` created from a tensor `TensorInt S c`. -/
noncomputable def toTensor {n : ℕ} {c : Fin n → C} (f : TensorInt S c) :
    S.Tensor c := (Tensor.basis c).repr.symm <|
  (Finsupp.linearEquivFunOnFinite k k ((j : Fin n) → Fin (S.repDim (c j)))).symm <|
  (fun j => Int.cast (f j))

lemma basis_repr_apply {n : ℕ} {c : Fin n → C}
    (f : TensorInt S c) (b : ComponentIdx c) :
    (Tensor.basis c).repr (toTensor f) b = Int.cast (f b) := by
  simp only [toTensor, Basis.repr_symm_apply, Basis.repr_linearCombination]
  rfl

end TensorInt

lemma basis_eq_tensorInt {n : ℕ} {c : Fin n → C}
    (b : ComponentIdx c) :
    Tensor.basis c b = TensorInt.toTensor (S := S) (fun b' => if b = b' then 1 else 0) := by
  apply (Tensor.basis c).repr.injective
  simp only [Basis.repr_self]
  ext b'
  simp only [TensorInt.basis_repr_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rw [Finsupp.single_apply]

end Tensor

end TensorSpecies
