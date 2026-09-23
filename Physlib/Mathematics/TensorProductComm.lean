/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Associator
/-!
# Commuting tensor-factor endomorphisms

An endomorphism of one tensor factor of `W ⊗ X` commutes with a map acting on another
factor, since the two act independently. `lTensor_map_id_comm` is that fact for two
factors, and `congr_assoc_map_id_comm` is its analogue after reassociating and recombining
a third factor into the second.

-/

@[expose] public section

open scoped TensorProduct

/-- An endomorphism of the second tensor factor commutes with one of the first. -/
lemma lTensor_map_id_comm {k : Type} [CommSemiring k] {W X : Type} [AddCommMonoid W]
    [Module k W] [AddCommMonoid X] [Module k X] (f : X →ₗ[k] X) (g : W →ₗ[k] W)
    (t : W ⊗[k] X) :
    (LinearMap.lTensor W f) (TensorProduct.map g LinearMap.id t) =
      TensorProduct.map g LinearMap.id ((LinearMap.lTensor W f) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

/-- Reassociating and recombining the last two tensor factors commutes with an
  endomorphism of the first. -/
lemma congr_assoc_map_id_comm {k : Type} [CommSemiring k] {W X Y Z : Type} [AddCommMonoid W]
    [Module k W] [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid Z] [Module k Z] (E : X ⊗[k] Y ≃ₗ[k] Z) (g : W →ₗ[k] W)
    (t : (W ⊗[k] X) ⊗[k] Y) :
    (TensorProduct.congr (LinearEquiv.refl k W) E) (TensorProduct.assoc k W X Y
        (TensorProduct.map (TensorProduct.map g LinearMap.id) LinearMap.id t)) =
      TensorProduct.map g LinearMap.id
        ((TensorProduct.congr (LinearEquiv.refl k W) E) (TensorProduct.assoc k W X Y t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]
