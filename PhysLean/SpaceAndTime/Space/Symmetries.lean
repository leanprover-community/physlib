/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone
-/
import PhysLean.SpaceAndTime.Space.Basic
/-!

# Coordinate symmetries on Space

We define isometric coordinate transformations on `Space d`:
- `Space.reflectCoord k` negates the `k`-th coordinate.
- `Space.swapCoord i j` swaps the `i`-th and `j`-th coordinates.

Both preserve the norm and are self-inverse, so they are linear isometric equivalences.

-/

namespace Space

variable {d : ℕ}

/-- A single-coordinate negation on `Space d` — negates the k-th coordinate. -/
noncomputable def reflectCoord (k : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toLinearEquiv := {
    toFun := fun x => ⟨fun i => if i = k then -(x i) else x i⟩
    map_add' := fun x y => by ext i; simp only [Space.add_apply]; split_ifs <;> ring
    map_smul' := fun c x => by
      ext i; simp only [Space.smul_apply, RingHom.id_apply]; split_ifs <;> ring
    invFun := fun x => ⟨fun i => if i = k then -(x i) else x i⟩
    left_inv := fun x => by ext i; simp only; split_ifs <;> simp
    right_inv := fun x => by ext i; simp only; split_ifs <;> simp
  }
  norm_map' := fun x => by
    simp only [LinearEquiv.coe_mk, Space.norm_eq]; congr 1
    apply Finset.sum_congr rfl; intro i _
    show (if i = k then -(x i) else x i) ^ 2 = x i ^ 2; split_ifs <;> ring

/-- A coordinate swap on `Space d` — swaps the i-th and j-th coordinates. -/
noncomputable def swapCoord (i j : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toLinearEquiv := {
    toFun := fun x => ⟨fun k => x (Equiv.swap i j k)⟩
    map_add' := fun x y => by ext k; simp [Space.add_apply]
    map_smul' := fun c x => by ext k; simp [Space.smul_apply]
    invFun := fun x => ⟨fun k => x (Equiv.swap i j k)⟩
    left_inv := fun x => by ext k; simp
    right_inv := fun x => by ext k; simp
  }
  norm_map' := fun x => by
    simp only [LinearEquiv.coe_mk, Space.norm_eq]; congr 1
    exact Finset.sum_equiv (Equiv.swap i j) (by simp) (by intro k _; rfl)

@[simp]
lemma reflectCoord_apply (k i : Fin d) (x : Space d) :
    (Space.reflectCoord k x) i = if i = k then -(x i) else x i := by
  simp [Space.reflectCoord]

@[simp]
lemma swapCoord_apply (i j k : Fin d) (x : Space d) :
    (Space.swapCoord i j x) k = x (Equiv.swap i j k) := by
  simp [Space.swapCoord]

end Space
