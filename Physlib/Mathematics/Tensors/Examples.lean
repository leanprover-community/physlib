/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.IndexMaps

/-!

# Examples of colored tensors

Tests of the colors of tensors and of the group action on tensors.

## i. Overview

Each test fails if its guarantee breaks. The tests are:
- A. A tensor or a vector of one color is rejected at another color.
- B. The group does not act on a product of tensors through one factor.
- C. `intertwiningMapAt` rejects a map that does not commute with the group.

## ii. Key results

- `toy` : a species with the same space `ℝ` at every color.
- `scale` : a species on which a unit acts differently at its two colors.
- `scaleCopy` : the copy of components from `up` to `down`, which does not commute with the group.

## iii. Table of contents

- A. Wrong colors
- B. The action on a product of tensors
- C. Maps that change a color

## iv. References

* None.

-/

@[expose] public section

namespace Tensor.Examples

open Species TensorProduct

/-!

## A. Wrong colors

The species `toy` has the space `ℝ` at both colors, so only the color tells them apart.

-/

/-- The species with the space `ℝ` at every color, the trivial action of `Unit` and the basis
`1`. -/
noncomputable def toy : Species ℝ Unit Unit (fun _ => Unit) where
  V _ := ℝ
  rep _ := Representation.trivial ℝ Unit ℝ
  basis _ := Module.Basis.singleton Unit ℝ
  invariant _ _ _ _ := rfl

/-- The color of variance `.up`. -/
abbrev up : Color Unit := ⟨(), .up⟩

/-- The color of variance `.down`. -/
abbrev down : Color Unit := ⟨(), .down⟩

/--
error: Type mismatch
  t
has type
  Tensor toy ![up]
but is expected to have type
  Tensor toy ![down]
-/
#guard_msgs in
example (t : Tensor toy ![up]) : Tensor toy ![down] := t

-- The colors differ also when all definitions unfold, and on a single vector.
example (t : Tensor toy ![up]) (v : toy.colored.V up) : Tensor toy ![up] × toy.colored.V up := by
  fail_if_success have : Tensor toy ![down] := by with_unfolding_all exact t
  fail_if_success have : toy.colored.V down := v
  exact (t, v)

/-!

## B. The action on a product of tensors

`SMulCommClass k G` is not an instance. So the group does not act on `T ⊗ₜ U` through `T`.

-/

/--
error: failed to synthesize instance of type class
  SMul G (Tensor S d ⊗[k] Tensor S d)
-/
#guard_msgs (substring := true) in
noncomputable example {k G : Type} [RCLike k] [Group G] (S : Species k G Unit fun _ => Unit)
    (d : Fin 1 → Color Unit) : SMul G (Tensor S d ⊗[k] Tensor S d) :=
  inferInstance

/-!

## C. Maps that change a color

On `scale` the copy of components from `up` to `down` is linear but does not commute with the
group. So `intertwiningMapAt` rejects it.

-/

/-- The species with the space `ℝ` at both colors and the basis `1`. A unit `r` acts by `r` at
`up` and by `r⁻¹` at `down`. -/
noncomputable def scale : Species ℝ ℝˣ Unit (fun _ => Unit) where
  V _ := ℝ
  rep c := cond c.variance.isUp (Representation.ofDistribMulAction ℝ ℝˣ ℝ)
    ((Representation.ofDistribMulAction ℝ ℝˣ ℝ).comp invMonoidHom)
  basis _ := Module.Basis.singleton Unit ℝ
  invariant := by
    rintro ⟨_, ⟨_ | _, _ | _, h⟩⟩ r x y <;> try exact absurd rfl h
    all_goals
      simp [Module.Basis.coordPairing_tmul, Units.smul_def]
      field_simp

/-- The copy `w := v` of components from `up` to `down`. It does not commute with the group,
since `2 • 1 ≠ 2⁻¹ • 1`. -/
noncomputable abbrev scaleCopy : scale.colored.V up →ₗ[ℝ] scale.colored.V down :=
  (scale.coloredEquiv down).toLinearMap ∘ₗ (scale.coloredEquiv up).symm.toLinearMap

noncomputable example (f : (scale.colored.rep up).IntertwiningMap (scale.colored.rep down)) :
    (scale.tensorRep fun _ : Fin 1 => up).IntertwiningMap
      (scale.tensorRep fun _ : Fin 1 => down) := by
  fail_if_success
    exact scale.intertwiningMapAt 0 scaleCopy fun x hx => absurd (Subsingleton.elim x 0) hx
  exact scale.intertwiningMapAt 0 f fun x hx => absurd (Subsingleton.elim x 0) hx

end Tensor.Examples
