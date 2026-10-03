/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.JetPoint
/-!
# Fiber directions on jet points

Affine fiber-direction structure on coordinate-level jet points.

## i. Overview

This module adds the affine fiber-direction structure on coordinate-level jet points.

At this stage, it introduces:

- fiber-coordinate data on jet points,
- affine translation and line maps in the jet fiber,
- and the jet-fiber direction determined by a field.

## ii. Key results

- `ClassicalFieldTheory.Local.JetFiberData`
- `ClassicalFieldTheory.Local.JetPoint.addFiber`
- `ClassicalFieldTheory.Local.JetPoint.lineMap`
- `ClassicalFieldTheory.Local.jetDirectionAt`

## iii. Table of contents

- A. Fiber-coordinate data
- B. Affine fiber structure on jet points
- C. Fiber directions determined by fields

## iv. References

* None.
-/

@[expose] public section

open Physlib
open scoped ContDiff

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Fiber-coordinate data

-/

/-- Fiber-coordinate data for jet points of order `k`. This records only the coordinates `u^a_I`,
not the base point in `Space d`. -/
structure JetFiberData (d m k : ℕ) where
  /-- The fiber coordinates indexed by all derivative indices of order at most `k`. -/
  coord : JetCoordinates d m k

namespace JetFiberData

variable {d m k : ℕ}

instance : CoeFun (JetFiberData d m k) (fun _ => DerivativeIndex d k → Fin m → ℝ) where
  coe V := V.coord

@[ext]
lemma ext (V W : JetFiberData d m k) (hcoord : ∀ I a, V.coord I a = W.coord I a) : V = W := by
  cases V with
  | mk coordV =>
  cases W with
  | mk coordW =>
  have h : coordV = coordW := by
    funext I
    funext a
    exact hcoord I a
  cases h
  rfl

/-- The zero-th order component of a jet-fiber direction, corresponding to the field value. -/
def value (V : JetFiberData d m k) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun a => V.coord 0 a

@[simp]
lemma value_apply (V : JetFiberData d m k) (a : Fin m) :
    V.value a = V.coord 0 a := by
  simp [value]

instance : Zero (JetFiberData d m k) where
  zero := { coord := fun _ _ => 0 }

instance : Add (JetFiberData d m k) where
  add V W := { coord := fun I a => V.coord I a + W.coord I a }

instance : SMul ℝ (JetFiberData d m k) where
  smul c V := { coord := fun I a => c * V.coord I a }

@[simp]
lemma zero_coord (I : DerivativeIndex d k) (a : Fin m) :
    (0 : JetFiberData d m k).coord I a = 0 := rfl

@[simp]
lemma add_coord (V W : JetFiberData d m k) (I : DerivativeIndex d k) (a : Fin m) :
    (V + W).coord I a = V.coord I a + W.coord I a := rfl

@[simp]
lemma smul_coord (c : ℝ) (V : JetFiberData d m k) (I : DerivativeIndex d k) (a : Fin m) :
    (c • V).coord I a = c * V.coord I a := rfl

end JetFiberData

/-!
## B. Affine fiber structure on jet points

-/

namespace JetPoint

variable {d m k : ℕ}

/-- Translate a jet point by a fiber-direction increment. -/
def addFiber (J : JetPoint d m k) (V : JetFiberData d m k) : JetPoint d m k where
  base := J.base
  fiber := fun I a => J.fiber I a + V.coord I a

/-- The affine line in jet space through `J` in the fiber direction `V`. -/
def lineMap (J : JetPoint d m k) (V : JetFiberData d m k) (s : ℝ) : JetPoint d m k :=
  J.addFiber (s • V)

@[simp]
lemma addFiber_base (J : JetPoint d m k) (V : JetFiberData d m k) :
    (J.addFiber V).base = J.base := rfl

@[simp]
lemma addFiber_value (J : JetPoint d m k) (V : JetFiberData d m k) :
    (J.addFiber V).value = J.value + V.value := by
  ext a
  rfl

@[simp]
lemma addFiber_coord (J : JetPoint d m k) (V : JetFiberData d m k)
    (I : DerivativeIndex d k) (a : Fin m) :
    (J.addFiber V).coord I a = J.coord I a + V.coord I a := rfl

@[simp]
lemma lineMap_base (J : JetPoint d m k) (V : JetFiberData d m k) (s : ℝ) :
    (J.lineMap V s).base = J.base := rfl

@[simp]
lemma lineMap_coord (J : JetPoint d m k) (V : JetFiberData d m k) (s : ℝ)
    (I : DerivativeIndex d k) (a : Fin m) :
    (J.lineMap V s).coord I a = J.coord I a + s * V.coord I a := rfl

end JetPoint

/-!
## C. Fiber directions determined by fields

-/

/-- The jet-fiber direction determined by a field `g` at a point `x`. -/
noncomputable def jetDirectionAt (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) :
    JetFiberData d m k where
  coord := jetCoordinatesAt k g x

@[simp]
lemma jetDirectionAt_coord (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d)
    (I : DerivativeIndex d k) (a : Fin m) :
    (jetDirectionAt k g x).coord I a = ∂^[I.1] (fun y => (g y) a) x := rfl

lemma jetDirectionAt_coord_zero (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (a : Fin m) :
    (jetDirectionAt k g x).coord 0 a = (g x) a := by
  simp [jetDirectionAt_coord]

lemma jetCoordinatesAt_add_smul (k : ℕ) (f g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (s : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    jetCoordinatesAt k (fun y => f y + s • g y) x =
      jetCoordinatesAt k f x + s • jetCoordinatesAt k g x := by
  funext I
  funext a
  have hfa : ContDiff ℝ ∞ (fun y => (f y) a) := by
    exact (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2)
      (E := fun _ : Fin m => ℝ) (i := a)).comp hf
  have hga : ContDiff ℝ ∞ (fun y => (g y) a) := by
    exact (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2)
      (E := fun _ : Fin m => ℝ) (i := a)).comp hg
  have hadd :
      (fun y => (f y + s • g y) a) = (fun y => (f y) a) + s • fun y => (g y) a := by
    funext y
    simp [smul_eq_mul]
  have hsg : ContDiff ℝ ∞ (s • fun y => (g y) a) := by
    exact hga.const_smul s
  simp [jetCoordinatesAt]
  have hsum := congrFun (Space.iteratedDeriv_add I.1 hfa hsg) x
  have hsmul := congrFun (Space.iteratedDeriv_const_smul I.1 s hga) x
  calc
    ∂^[I.1] ((fun y => (f y) a) + s • fun y => (g y) a) x
      = (∂^[I.1] (fun y => (f y) a) + ∂^[I.1] (s • fun y => (g y) a)) x := by
          simpa using hsum
    _ = ∂^[I.1] (fun y => (f y) a) x + s * ∂^[I.1] (fun y => (g y) a) x := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsmul]

lemma jetAt_add_smul (k : ℕ) (f g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (s : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    jetAt k (fun y => f y + s • g y) x = (jetAt k f x).lineMap (jetDirectionAt k g x) s := by
  apply JetPoint.ext
  · simp [JetPoint.lineMap]
  · intro I a
    have hfa : ContDiff ℝ ∞ (fun y => (f y) a) := by
      exact (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2)
        (E := fun _ : Fin m => ℝ) (i := a)).comp hf
    have hga : ContDiff ℝ ∞ (fun y => (g y) a) := by
      exact (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2)
        (E := fun _ : Fin m => ℝ) (i := a)).comp hg
    have hadd :
        (fun y => (f y + s • g y) a) = (fun y => (f y) a) + s • fun y => (g y) a := by
      funext y
      simp [smul_eq_mul]
    change ∂^[I.1] (fun y => (f y + s • g y) a) x =
      ((jetAt k f x).lineMap (jetDirectionAt k g x) s).coord I a
    rw [JetPoint.lineMap_coord, jetAt_coord, jetDirectionAt_coord]
    rw [hadd]
    have hsg : ContDiff ℝ ∞ (s • fun y => (g y) a) := by
      exact hga.const_smul s
    have hsum := congrFun (Space.iteratedDeriv_add I.1 hfa hsg) x
    have hsmul := congrFun (Space.iteratedDeriv_const_smul I.1 s hga) x
    calc
      ∂^[I.1] ((fun y => (f y) a) + s • fun y => (g y) a) x
        = (∂^[I.1] (fun y => (f y) a) + ∂^[I.1] (s • fun y => (g y) a)) x := hsum
      _ = ∂^[I.1] (fun y => (f y) a) x + s * ∂^[I.1] (fun y => (g y) a) x := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsmul]

end Local
end ClassicalFieldTheory
