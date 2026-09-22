/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The conjugate-scalar twist of a normed space

`ConjSpace X` is `X` again, as a type, but with its `ℂ`-scalar action twisted by complex
conjugation: `c • x` in `ConjSpace X` means `(starRingEnd ℂ c) • x` in `X`. This is the usual
device for turning a *linear* identification into a *conjugate-linear* one without inventing a
conjugate-linear self-map of `X` itself (there is none, canonically, for an arbitrary Banach
space): a functional `f : StrongDual ℂ X` is `X`-linear, but the same underlying function,
postcomposed with `starRingEnd ℂ` and reinterpreted as acting on `ConjSpace X`, becomes honestly
`ConjSpace X`-linear (`Phi` below). That reinterpretation is genuinely needed — postcomposing `f`
with `starRingEnd ℂ` and leaving the domain as plain `X` does *not* give another element of
`StrongDual ℂ X`, since `conj ∘ f` is conjugate-linear, not linear, as a function of `x : X`.

This file only builds the twisted space and its basic instances; the semilinear equivalence
`Phi`/`Psi` connecting `StrongDual ℂ X` and `StrongDual ℂ (ConjSpace X)` is
`WStarAlgebra/Mathlib.lean`'s job, since it is the part that actually uses this twist.

## Definitions

- `ConjSpace X` : the type synonym itself.
- `ConjSpace.toConj`, `ConjSpace.ofConj` : the underlying identity maps `X → ConjSpace X` and
  back, spelled out explicitly (rather than relying on the bare definitional equality) so that
  Lean's elaborator is never asked to guess, from a bare type ascription, which of the (defeq but
  distinct as far as instance search is concerned) scalar actions on `X` is intended.
- `ConjSpace.instModule`, `ConjSpace.instNormedSpace` : the twisted `ℂ`-module and normed-space
  structures, built by hand (rather than via `Module.compHom`) precisely so that the defining
  equation `ofConj (c • x) = (starRingEnd ℂ c) • ofConj x` is a genuine `rfl` lemma
  (`ofConj_smul`), usable directly, instead of being buried several `compHom`/`FunLike`-coercion
  layers deep.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

/-- The type synonym for `X` with the scalar action twisted by complex conjugation:
`c • x = (starRingEnd ℂ c) • x` for the original action on `X`. See the module docstring for
why this twist is exactly what turns a linear identification into a conjugate-linear one. -/
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

variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The twisted scalar action: `c • x := (starRingEnd ℂ c) • ofConj x`, moved back into
`ConjSpace X` via `toConj`. -/
instance instSMul : SMul ℂ (ConjSpace X) :=
  ⟨fun c x => toConj ((starRingEnd ℂ c) • ofConj x)⟩

lemma smul_def (c : ℂ) (x : ConjSpace X) :
    c • x = toConj ((starRingEnd ℂ c) • ofConj x) := rfl

@[simp] lemma ofConj_smul (c : ℂ) (x : ConjSpace X) :
    ofConj (c • x) = (starRingEnd ℂ c) • ofConj x := rfl

/-- The `ℂ`-module structure on `ConjSpace X`, with `c • x = (starRingEnd ℂ c) • x` for the
original action on `X`. Built by hand from `instSMul` rather than via `Module.compHom`, so that
`ofConj_smul` is a plain `rfl` usable by `rw`/`simp` without unfolding several layers of
`compHom`/`FunLike` machinery. -/
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

/-- The scalar twist changes neither the underlying points, the norm, nor the uniform structure
of `X`, so completeness transports across it for free. -/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (ConjSpace X) := ‹CompleteSpace X›

end ConjSpace
