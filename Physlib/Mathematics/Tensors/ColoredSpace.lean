/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Species
/-!

# The space of a color

`S.ColoredSpace c` is a copy of `S.V c`, a different type for each color `c` of the species `S`.

## i. Overview

A species `S` can give two colors spaces of the same type. The real Lorentz colors `⟨vec, up⟩` and
`⟨vec, down⟩` both have the space of vectors with one time and `d` space components. So Lean would
accept a covector `w_μ` where a vector `v^μ` is expected.

We give each color its own space (A). `S.ColoredSpace c` has the one field `toV : S.V c`, so it is a
different type for each color. We then build the species `S.colored` on these spaces (B), with the
addition, scalars, action and basis of `S` on `toV`. Tensors are built from `S.colored`, so a tensor
of one color is not accepted at another. Finally we go from `S.V c` to the space of `c` (C).
`coloredEquiv c` is the explicit map `ColoredSpace.ofV` as an equivalence of representations.

## ii. Key results

- `Species.ColoredSpace c` : the space of the color `c`, a different type for each color.
- `Species.colored` : the species on these spaces.
- `Species.coloredEquiv` : the equivalence of representations from `S.V c` to `S.colored.V c`.

## iii. Table of contents

- A. The space of a color
- B. The species on the spaces of the colors
- C. From `S.V c` to `S.colored.V c`

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

namespace Tensor

namespace Species

variable {k : Type} [RCLike k] {G : Type} [Group G] {K : Type} {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

/-!

## A. The space of a color

-/

variable (S) in
/-- The vector space `S.V c` with its color `c` attached, a different type for each color. A vector
`v^μ` lies in `S.ColoredSpace ⟨vec, up⟩` and a covector `w_μ` in `S.ColoredSpace ⟨vec, down⟩`. -/
@[ext]
structure ColoredSpace (c : Color K) : Type where
  /-- A vector of `S.V c` as a vector of the space of `c`. The retagging `ofV v.toV` of `v^μ` as
  `w_μ := v^μ` is explicit. It need not commute with the group. -/
  ofV ::
  /-- The vector of `S.V c` underlying a vector of the space of `c`. -/
  toV : S.V c

namespace ColoredSpace

variable {c : Color K}

/-- The zero vector of the space of `c`. -/
instance : Zero (S.ColoredSpace c) := ⟨⟨0⟩⟩

/-- The sum of two vectors of the space of `c`. -/
instance : Add (S.ColoredSpace c) := ⟨fun x y => ⟨x.toV + y.toV⟩⟩

/-- The negative of a vector of the space of `c`. -/
instance : Neg (S.ColoredSpace c) := ⟨fun x => ⟨-x.toV⟩⟩

/-- The difference of two vectors of the space of `c`. -/
instance : Sub (S.ColoredSpace c) := ⟨fun x y => ⟨x.toV - y.toV⟩⟩

/-- Natural multiples of a vector of the space of `c`. -/
instance : SMul ℕ (S.ColoredSpace c) := ⟨fun n x => ⟨n • x.toV⟩⟩

/-- Integer multiples of a vector of the space of `c`. -/
instance : SMul ℤ (S.ColoredSpace c) := ⟨fun n x => ⟨n • x.toV⟩⟩

/-- Scalar multiples of a vector of the space of `c`. -/
instance : SMul k (S.ColoredSpace c) := ⟨fun r x => ⟨r • x.toV⟩⟩

/-- Two vectors of `S.ColoredSpace c` with the same `toV` are equal. -/
lemma toV_injective : Function.Injective (ColoredSpace.toV (S := S) (c := c)) :=
  fun _ _ => ColoredSpace.ext

/-- The space of `c` is an additive group, as `S.V c` is. -/
instance : AddCommGroup (S.ColoredSpace c) := fast_instance%
  toV_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The space of `c` is a vector space over `k`, as `S.V c` is. -/
instance : Module k (S.ColoredSpace c) := fast_instance%
  toV_injective.module k ⟨⟨ColoredSpace.toV, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

/-! The `simp` lemmas below are on the spelling `S.ColoredSpace c`. Those on `S.colored.V c` are
in B. -/

@[simp] lemma toV_ofV (v : S.V c) : (ofV v : S.ColoredSpace c).toV = v := rfl

@[simp] lemma ofV_toV (v : S.ColoredSpace c) : ofV v.toV = v := rfl

@[simp] lemma toV_zero : (0 : S.ColoredSpace c).toV = 0 := rfl

@[simp] lemma toV_add (v w : S.ColoredSpace c) : (v + w).toV = v.toV + w.toV := rfl

@[simp] lemma toV_neg (v : S.ColoredSpace c) : (-v).toV = -v.toV := rfl

@[simp] lemma toV_sub (v w : S.ColoredSpace c) : (v - w).toV = v.toV - w.toV := rfl

@[simp] lemma toV_nsmul (n : ℕ) (v : S.ColoredSpace c) : (n • v).toV = n • v.toV := rfl

@[simp] lemma toV_zsmul (n : ℤ) (v : S.ColoredSpace c) : (n • v).toV = n • v.toV := rfl

@[simp] lemma toV_smul (r : k) (v : S.ColoredSpace c) : (r • v).toV = r • v.toV := rfl

end ColoredSpace

/-!

## B. The species on the spaces of the colors

The `simp` lemmas of this section are on the spelling `S.colored.V c`. Each is named after its left
side.

-/

variable (S)

-- `colored` is a `def`, so goals show `S.colored.V c`. It is `instance_reducible`, so the
-- instances on `S.colored.V c` are those of `S.ColoredSpace c`.
/-- The species with the space `S.ColoredSpace c` at each color `c`. Its action and basis are those
of `S` on the field `toV`. -/
@[instance_reducible] noncomputable def colored : Species k G K basisIdx where
  V := S.ColoredSpace
  rep c :=
    { toFun g :=
        { toFun v := ⟨S.rep c g v.toV⟩
          map_add' v w := congrArg ColoredSpace.ofV (map_add (S.rep c g) v.toV w.toV)
          map_smul' r v := congrArg ColoredSpace.ofV (map_smul (S.rep c g) r v.toV) }
      map_one' := LinearMap.ext fun v =>
        congrArg ColoredSpace.ofV (LinearMap.congr_fun (map_one (S.rep c)) v.toV)
      map_mul' g h := LinearMap.ext fun v =>
        congrArg ColoredSpace.ofV (LinearMap.congr_fun (map_mul (S.rep c) g h) v.toV) }
  basis c := (S.basis c).map
    { toFun := ColoredSpace.ofV, invFun := ColoredSpace.toV, left_inv _ := rfl, right_inv _ := rfl,
      map_add' _ _ := rfl, map_smul' _ _ := rfl }
  invariant c g x y := by
    have h := S.invariant c g x.toV y.toV
    simp only [Module.Basis.coordPairing_tmul, Module.Basis.equivFun_apply] at h ⊢
    exact h

variable {S}

section

variable {c : Color K}

open ColoredSpace

/-- Two vectors of `S.colored.V c` are equal when their fields `toV` are. -/
@[ext]
lemma colored_ext {v w : S.colored.V c} (h : v.toV = w.toV) : v = w := toV_injective h

@[simp] lemma toV_colored_ofV (v : S.V c) : (ofV v : S.colored.V c).toV = v := rfl

@[simp] lemma ofV_toV_colored (v : S.colored.V c) : ofV v.toV = v := rfl

@[simp] lemma toV_colored_zero : (0 : S.colored.V c).toV = 0 := rfl

@[simp] lemma toV_colored_add (v w : S.colored.V c) : (v + w).toV = v.toV + w.toV := rfl

@[simp] lemma toV_colored_neg (v : S.colored.V c) : (-v).toV = -v.toV := rfl

@[simp] lemma toV_colored_sub (v w : S.colored.V c) : (v - w).toV = v.toV - w.toV := rfl

@[simp] lemma toV_colored_nsmul (n : ℕ) (v : S.colored.V c) : (n • v).toV = n • v.toV := rfl

@[simp] lemma toV_colored_zsmul (n : ℤ) (v : S.colored.V c) : (n • v).toV = n • v.toV := rfl

@[simp] lemma toV_colored_smul (r : k) (v : S.colored.V c) : (r • v).toV = r • v.toV := rfl

end

/-- The action of `S.colored` is that of `S` on the field `toV`. -/
@[simp]
lemma toV_colored_rep (c : Color K) (g : G) (v : S.colored.V c) :
    (S.colored.rep c g v).toV = S.rep c g v.toV := rfl

/-- The action of `S.colored` on `ColoredSpace.ofV v` is that of `S` on `v`. -/
@[simp]
lemma colored_rep_ofV (c : Color K) (g : G) (v : S.V c) :
    S.colored.rep c g (ColoredSpace.ofV v) = ColoredSpace.ofV (S.rep c g v) := rfl

/-- The components of a vector of `S.colored.V c` are those of its field `toV`. -/
@[simp]
lemma colored_basis_repr (c : Color K) (v : S.colored.V c) :
    (S.colored.basis c).repr v = (S.basis c).repr v.toV := rfl

/-- The basis vector `e_μ` of `S.colored.V c` is `ColoredSpace.ofV e_μ`. -/
@[simp]
lemma colored_basis_apply (c : Color K) (μ : basisIdx c.kind) :
    S.colored.basis c μ = ColoredSpace.ofV (S.basis c μ) := rfl

/-- The contraction `u^μ α_μ` of `S.colored` is that of `S` on the fields `toV`. -/
@[simp]
lemma colored_contr_tmul (c : Color K) (x : S.colored.V c) (y : S.colored.V c.dual) :
    S.colored.contr c (x ⊗ₜ y) = S.contr c (x.toV ⊗ₜ y.toV) := by
  simp only [contr_tmul_eq_sum_basis, colored_basis_repr]

/-- Moving a vector of `S.colored` along an equality of colors `a = a'` moves its field `toV` by
`S.cast`. -/
-- `simp↓`, so that it fires before `cast_apply` rewrites `S.colored.cast p x` inside it.
@[simp↓]
lemma toV_colored_cast {a a' : Color K} (p : a = a') (x : S.colored.V a) :
    (S.colored.cast p x).toV = S.cast p x.toV := by
  subst p
  rfl

/-!

## C. From `S.V c` to `S.colored.V c`

A vector `v` of `S.V c` has no color in its type. `coloredEquiv c` sends it to the vector
`ColoredSpace.ofV v` of `S.colored.V c`, whose type records the color `c`. Its inverse `toV` sends
it back. The vector itself does not change, so the group acts on both in the same way. So
`coloredEquiv c` is an equivalence of representations. Tensors are made of vectors of
`S.colored.V c`, so a vector of `S.V c` enters a tensor through `coloredEquiv c`.

-/

variable (S) in
/-- The equivalence of representations `v ↦ ColoredSpace.ofV v` from `S.V c` to `S.colored.V c`. -/
def coloredEquiv (c : Color K) : (S.rep c).Equiv (S.colored.rep c) where
  toFun := ColoredSpace.ofV
  invFun := ColoredSpace.toV
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

/-- `coloredEquiv c` sends `v` to `ColoredSpace.ofV v`. -/
@[simp]
lemma coloredEquiv_apply (c : Color K) (v : S.V c) : S.coloredEquiv c v = ColoredSpace.ofV v :=
  rfl

/-- The inverse of `coloredEquiv c` sends `v` to its field `toV`. -/
@[simp]
lemma coloredEquiv_symm_apply (c : Color K) (v : S.colored.V c) :
    (S.coloredEquiv c).symm v = v.toV := rfl

end Species

end Tensor
