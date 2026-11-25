/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic

/-!

# The Poincaré group

The Poincaré group acts on spacetime by Lorentz transformations and translations.

## i. Overview

An element of the Poincaré group is a pair of a translation `a` and a Lorentz transformation `Λ`.
It acts on a point `x` by `x ↦ Λ x + a`. The group is built from the existing `LorentzGroup d`
and the vector group of `SpaceTime d`. The file also defines the action on functions of
spacetime by `(g • u) x = u (g⁻¹ x)`. A group element is orthochronous when its Lorentz part is.
The action on functions sends the support of a function to the image of the support.

## ii. Key results

- `PoincareGroup` : the group of translations and Lorentz transformations.
- `PoincareGroup.IsOrthochronous` : the Lorentz part preserves the direction of time.
- `PoincareGroup.act` : the action on functions of spacetime.
- `PoincareGroup.tsupport_act` : the support of `g • u` is the image of the support of `u`.

## iii. Table of contents

- A. The group
- B. The action on spacetime
- C. Orthochronous elements
- D. Point reflections
- E. The action on functions

## iv. References

None.

## A. The group

- `PoincareGroup` : the group of translations and Lorentz transformations.

## B. The action on spacetime

- `PoincareGroup.toHomeomorph` : each element is a homeomorphism of spacetime.

## C. Orthochronous elements

- `PoincareGroup.IsOrthochronous` : the Lorentz part preserves the direction of time.

## D. Point reflections

- `PoincareGroup.pointReflection` : the point reflection `x ↦ p - x`.
- `PoincareGroup.not_isOrthochronous_pointReflection` : it is not orthochronous.

## E. The action on functions

- `PoincareGroup.act` : the action `(g • u) x = u (g⁻¹ x)` on functions of spacetime.
-/

@[expose] public section

noncomputable section

open Lorentz
open scoped Pointwise

/-- The Poincaré group of `SpaceTime d`. An element `⟨a, Λ⟩` acts by `x ↦ Λ x + a`. -/
@[ext]
structure PoincareGroup (d : ℕ) where
  /-- The translation part. -/
  translation : SpaceTime d
  /-- The Lorentz part. -/
  lorentz : LorentzGroup d

namespace PoincareGroup

variable {d : ℕ}

section Group

instance : Group (PoincareGroup d) where
  mul g h := ⟨g.translation + g.lorentz • h.translation, g.lorentz * h.lorentz⟩
  one := ⟨0, 1⟩
  inv g := ⟨-(g.lorentz⁻¹ • g.translation), g.lorentz⁻¹⟩
  mul_assoc g h k := by
    ext1
    · change (g.translation + g.lorentz • h.translation) + (g.lorentz * h.lorentz) • k.translation =
        g.translation + g.lorentz • (h.translation + h.lorentz • k.translation)
      rw [smul_add, mul_smul, add_assoc]
    · exact mul_assoc _ _ _
  one_mul g := by
    ext1
    · change 0 + (1 : LorentzGroup d) • g.translation = g.translation
      rw [one_smul, zero_add]
    · exact one_mul _
  mul_one g := by
    ext1
    · change g.translation + g.lorentz • (0 : SpaceTime d) = g.translation
      rw [smul_zero, add_zero]
    · exact mul_one _
  inv_mul_cancel g := by
    ext1
    · change -(g.lorentz⁻¹ • g.translation) + g.lorentz⁻¹ • g.translation = 0
      rw [neg_add_cancel]
    · exact inv_mul_cancel _

/-- The translation part of a product. -/
lemma translation_mul (g h : PoincareGroup d) :
    (g * h).translation = g.translation + g.lorentz • h.translation := rfl

/-- The Lorentz part of a product. -/
lemma lorentz_mul (g h : PoincareGroup d) : (g * h).lorentz = g.lorentz * h.lorentz := rfl

/-- The translation part of an inverse. -/
lemma translation_inv (g : PoincareGroup d) :
    g⁻¹.translation = -(g.lorentz⁻¹ • g.translation) := rfl

/-- The Lorentz part of an inverse. -/
lemma lorentz_inv (g : PoincareGroup d) : g⁻¹.lorentz = g.lorentz⁻¹ := rfl

end Group

section Action

/-- The Poincaré group acts on spacetime by `x ↦ Λ x + a`. -/
instance : MulAction (PoincareGroup d) (SpaceTime d) where
  smul g x := g.lorentz • x + g.translation
  one_smul x := by
    change (1 : LorentzGroup d) • x + 0 = x
    rw [one_smul, add_zero]
  mul_smul g h x := by
    change (g.lorentz * h.lorentz) • x + (g.translation + g.lorentz • h.translation) =
      g.lorentz • (h.lorentz • x + h.translation) + g.translation
    rw [mul_smul, smul_add]
    abel

/-- The action on a point. -/
lemma smul_def (g : PoincareGroup d) (x : SpaceTime d) :
    g • x = g.lorentz • x + g.translation := rfl

/-- Each element is a homeomorphism of spacetime. -/
def toHomeomorph (g : PoincareGroup d) : SpaceTime d ≃ₜ SpaceTime d where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x
  continuous_toFun := by
    change Continuous fun x : SpaceTime d => g.lorentz • x + g.translation
    exact ((Vector.actionCLM g.lorentz).continuous).add continuous_const
  continuous_invFun := by
    change Continuous fun x : SpaceTime d => g⁻¹.lorentz • x + g⁻¹.translation
    exact ((Vector.actionCLM g⁻¹.lorentz).continuous).add continuous_const

/-- The homeomorphism acts as the point action. -/
lemma toHomeomorph_apply (g : PoincareGroup d) (x : SpaceTime d) : g.toHomeomorph x = g • x := rfl

/-- The inverse homeomorphism acts as the inverse point action. -/
lemma toHomeomorph_symm_apply (g : PoincareGroup d) (x : SpaceTime d) :
    g.toHomeomorph.symm x = g⁻¹ • x := rfl

/-- The image of a compact set under a Poincaré transformation is compact. -/
lemma isCompact_smul (g : PoincareGroup d) {K : Set (SpaceTime d)} (hK : IsCompact K) :
    IsCompact (g • K) := by
  have h : g • K = g.toHomeomorph '' K := (Set.image_smul (a := g) (t := K)).symm
  rw [h]
  exact hK.image g.toHomeomorph.continuous

end Action

section Orthochronous

/-- A Poincaré element is orthochronous when its Lorentz part preserves the direction of time. -/
def IsOrthochronous (g : PoincareGroup d) : Prop := LorentzGroup.IsOrthochronous g.lorentz

/-- The identity is orthochronous. -/
lemma isOrthochronous_one : IsOrthochronous (1 : PoincareGroup d) :=
  LorentzGroup.id_isOrthochronous

/-- Products of orthochronous elements are orthochronous. -/
lemma IsOrthochronous.mul {g h : PoincareGroup d} (hg : IsOrthochronous g)
    (hh : IsOrthochronous h) : IsOrthochronous (g * h) :=
  LorentzGroup.isOrthochronous_mul hg hh

/-- Inverses of orthochronous elements are orthochronous. -/
lemma IsOrthochronous.inv {g : PoincareGroup d} (hg : IsOrthochronous g) :
    IsOrthochronous g⁻¹ :=
  LorentzGroup.isOrthochronous_inv_iff.mpr hg

end Orthochronous

section Reflection

/-- The point reflection `x ↦ p - x` as a Poincaré transformation. -/
def pointReflection (p : SpaceTime d) : PoincareGroup d := ⟨p, -1⟩

/-- The point reflection sends `x` to `p - x`. -/
lemma pointReflection_smul (p x : SpaceTime d) : pointReflection p • x = p - x := by
  rw [smul_def]
  change (-1 : LorentzGroup d) • x + p = p - x
  rw [Lorentz.Vector.neg_smul, one_smul]
  abel

/-- The point reflection is not orthochronous. -/
lemma not_isOrthochronous_pointReflection (p : SpaceTime d) :
    ¬ (pointReflection p).IsOrthochronous := by
  have h : LorentzGroup.IsOrthochronous (-1 : LorentzGroup d) ↔
      ¬ LorentzGroup.IsOrthochronous (1 : LorentzGroup d) :=
    LorentzGroup.neg_isOrthochronous_iff_not
  exact fun hp => (h.mp hp) LorentzGroup.id_isOrthochronous

end Reflection

section Functions

variable {V : Type*}

/-- The action on functions of spacetime: `(g • u) x = u (g⁻¹ x)`. -/
def act (g : PoincareGroup d) (u : SpaceTime d → V) : SpaceTime d → V := fun x => u (g⁻¹ • x)

/-- The value of the transformed function. -/
lemma act_apply (g : PoincareGroup d) (u : SpaceTime d → V) (x : SpaceTime d) :
    act g u x = u (g⁻¹ • x) := rfl

/-- The identity acts trivially. -/
lemma act_one (u : SpaceTime d → V) : act (1 : PoincareGroup d) u = u := by
  funext x
  simp [act_apply]

/-- The action is a left action. -/
lemma act_mul (g h : PoincareGroup d) (u : SpaceTime d → V) :
    act (g * h) u = act g (act h u) := by
  funext x
  simp [act_apply, mul_smul]

/-- The action of an element and its inverse cancel. -/
lemma act_inv_act (g : PoincareGroup d) (u : SpaceTime d → V) : act g⁻¹ (act g u) = u := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- The action commutes with addition. -/
lemma act_add [AddCommGroup V] (g : PoincareGroup d) (u v : SpaceTime d → V) :
    act g (u + v) = act g u + act g v := rfl

/-- The action commutes with scalar multiplication. -/
lemma act_smul {R : Type*} [SMul R V] (g : PoincareGroup d) (c : R) (u : SpaceTime d → V) :
    act g (c • u) = c • act g u := rfl

variable [TopologicalSpace V]

omit [TopologicalSpace V] in
/-- The support of the transformed function is the image of the support. -/
lemma tsupport_act [Zero V] (g : PoincareGroup d) (u : SpaceTime d → V) :
    tsupport (act g u) = g • tsupport u := by
  have h : act g u = u ∘ g⁻¹.toHomeomorph := rfl
  rw [h, tsupport_comp_eq_preimage u g⁻¹.toHomeomorph]
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rfl

end Functions

end PoincareGroup
