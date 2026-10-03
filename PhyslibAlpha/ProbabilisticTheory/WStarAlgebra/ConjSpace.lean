/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!

# The complex conjugate of a normed space

The complex conjugate `ConjSpace X` of a complex normed space, with twisted scalar action.

## i. Overview

`ConjSpace X` is `X` with scalar multiplication twisted by complex conjugation: `c • x` in
`ConjSpace X` is `conj c • x` in `X`. It turns conjugate-linear maps on `X` into linear maps on
`ConjSpace X`.

## ii. Key results

- `ConjSpace` : the complex conjugate of a normed space.
- `ConjSpace.toConj`, `ConjSpace.ofConj` : the identity maps between `X` and `ConjSpace X`.
- `ConjSpace.instNormedSpace` : the conjugate normed space structure.

## iii. Table of contents

- A. The conjugate space and the identity maps
- B. The additive and normed group structure
- C. The conjugate scalar action

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexConjugate

/-!

## A. The conjugate space and the identity maps

-/

/-- The complex conjugate of `X`: the same type, with `c • x = conj c • x`. -/
def ConjSpace (X : Type*) : Type _ := X

namespace ConjSpace

variable {X : Type*}

/-- The identity, viewed as the map from `X` into `ConjSpace X`. Spelled out explicitly (instead
of relying on the bare definitional equality `ConjSpace X := X`) to keep instance search from
having to guess which scalar action a plain type ascription intends. -/
def toConj (x : X) : ConjSpace X := x

/-- The identity, viewed as the map from `ConjSpace X` back into `X`. -/
def ofConj (x : ConjSpace X) : X := x

@[simp] lemma ofConj_toConj (x : X) : ofConj (toConj x) = x := rfl
@[simp] lemma toConj_ofConj (x : ConjSpace X) : toConj (ofConj x) = x := rfl

/-!

## B. The additive and normed group structure

-/

instance instAddCommGroup [AddCommGroup X] : AddCommGroup (ConjSpace X) := ‹AddCommGroup X›

@[simp] lemma ofConj_add [AddCommGroup X] (x y : ConjSpace X) :
    ofConj (x + y) = ofConj x + ofConj y := rfl

@[simp] lemma ofConj_zero [AddCommGroup X] : ofConj (0 : ConjSpace X) = 0 := rfl

@[simp] lemma toConj_add [AddCommGroup X] (x y : X) :
    toConj (x + y) = toConj x + toConj y := rfl

@[simp] lemma toConj_zero [AddCommGroup X] : toConj (0 : X) = 0 := rfl

instance instNormedAddCommGroup [NormedAddCommGroup X] :
    NormedAddCommGroup (ConjSpace X) := ‹NormedAddCommGroup X›

@[simp] lemma norm_ofConj [NormedAddCommGroup X] (x : ConjSpace X) : ‖ofConj x‖ = ‖x‖ := rfl

@[simp] lemma norm_toConj [NormedAddCommGroup X] (x : X) : ‖toConj x‖ = ‖x‖ := rfl

/-!

## C. The conjugate scalar action

-/

variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The twisted scalar action: `c • x := (starRingEnd ℂ c) • ofConj x`, moved back into
`ConjSpace X` via `toConj`. -/
instance instSMul : SMul ℂ (ConjSpace X) :=
  ⟨fun c x => toConj ((starRingEnd ℂ c) • ofConj x)⟩

lemma smul_def (c : ℂ) (x : ConjSpace X) :
    c • x = toConj ((starRingEnd ℂ c) • ofConj x) := rfl

@[simp] lemma ofConj_smul (c : ℂ) (x : ConjSpace X) :
    ofConj (c • x) = (starRingEnd ℂ c) • ofConj x := rfl

/-- The conjugate module structure on `ConjSpace X`. -/
instance instModule : Module ℂ (ConjSpace X) where
  one_smul x := by rw [smul_def]; simp
  mul_smul c d x := by rw [smul_def, smul_def, smul_def]; simp [mul_smul]
  smul_zero c := by rw [smul_def]; simp
  smul_add c x y := by
    show toConj ((starRingEnd ℂ c) • ofConj (x + y)) =
        toConj ((starRingEnd ℂ c) • ofConj x) + toConj ((starRingEnd ℂ c) • ofConj y)
    rw [ofConj_add, smul_add, toConj_add]
  add_smul c d x := by rw [smul_def, smul_def, smul_def]; simp [add_smul]
  zero_smul x := by rw [smul_def]; simp

/-- The norm on `ConjSpace X` is literally `X`'s norm (via `ofConj`), so `norm_smul_le` reduces to
`‖conj c‖ = ‖c‖` (`Complex.norm_conj`) composed with `X`'s own `norm_smul_le`. -/
instance instNormedSpace : NormedSpace ℂ (ConjSpace X) where
  norm_smul_le c x := by
    show ‖ofConj (c • x)‖ ≤ ‖c‖ * ‖x‖
    rw [ofConj_smul, norm_smul, Complex.norm_conj, norm_ofConj]

/-- `ConjSpace X` is complete when `X` is. -/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (ConjSpace X) := ‹CompleteSpace X›

end ConjSpace

end ProbabilisticTheory
