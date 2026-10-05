/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.WStarAlgebra.Basic
public import PhyslibAlpha.ProbabilisticTheory.WStarAlgebra.ConjSpace
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!

# W⋆-algebra structures are W⋆-algebras

A W⋆-algebra structure with a chosen predual gives a W⋆-algebra in Mathlib's sense.

## i. Overview

Mathlib's `WStarAlgebra` asks for a conjugate-linear isometric isomorphism from the dual of a Banach
space onto `A`. For any Banach space `X`, `f ↦ conj ∘ f` is a conjugate-linear isometric isomorphism
from the dual of `X` to the dual of `ConjSpace X`. Composing with the inverse of the linear
identification of `A` with the dual of its predual shows that a W⋆-algebra structure gives a
W⋆-algebra in Mathlib's sense, when the predual lives in the same universe as `A`.

## ii. Key results

- `PhiEquiv` : the conjugate-linear isometric isomorphism between the duals of `X` and `ConjSpace
  X`.
- `WStarAlgebraStructure.toWStarAlgebra` : a W⋆-algebra structure gives a W⋆-algebra.

## iii. Table of contents

- A. The conjugate-linear self-duality `Phi` of the strong dual, via `ConjSpace`
- B. Closing the connection to Mathlib's `WStarAlgebra`

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexConjugate
open ConjSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ## A. The conjugate-linear self-duality `Phi` of the strong dual, via `ConjSpace` -/

/-- The map `f ↦ (x ↦ conj (f x))` from the dual of `X` to linear functionals on `ConjSpace X`. -/
def PhiLM (f : StrongDual ℂ X) : ConjSpace X →ₗ[ℂ] ℂ where
  toFun x := starRingEnd ℂ (f (ofConj x))
  map_add' _ _ := by simp
  map_smul' c x := by
    show starRingEnd ℂ (f (ofConj (c • x))) = c * starRingEnd ℂ (f (ofConj x))
    rw [ofConj_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]

/-- `Phi f`, as a continuous linear functional on `ConjSpace X`: the same bound `‖f‖` works, since
`conj` is an isometry of `ℂ`. -/
def Phi (f : StrongDual ℂ X) : StrongDual ℂ (ConjSpace X) :=
  LinearMap.mkContinuous (PhiLM f) ‖f‖ (fun x => by
    show ‖starRingEnd ℂ (f (ofConj x))‖ ≤ ‖f‖ * ‖x‖
    rw [Complex.norm_conj]
    simpa using f.le_opNorm (ofConj x))

@[simp] lemma Phi_apply (f : StrongDual ℂ X) (x : ConjSpace X) :
    Phi f x = starRingEnd ℂ (f (ofConj x)) := rfl

/-- The linear part of `Psi`, the same construction the other way around:
`g ↦ (x ↦ conj (g (toConj x)))`. -/
def PsiLM (g : StrongDual ℂ (ConjSpace X)) : X →ₗ[ℂ] ℂ where
  toFun x := starRingEnd ℂ (g (toConj x))
  map_add' _ _ := by simp
  map_smul' c x := by
    show starRingEnd ℂ (g (toConj (c • x))) = c * starRingEnd ℂ (g (toConj x))
    have hsmul : toConj (c • x) = (starRingEnd ℂ c) • (toConj x : ConjSpace X) := by
      show toConj (c • x) = toConj ((starRingEnd ℂ (starRingEnd ℂ c)) • ofConj (toConj x))
      simp
    rw [hsmul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]

/-- `Psi g`, as a continuous linear functional on `X`. -/
def Psi (g : StrongDual ℂ (ConjSpace X)) : StrongDual ℂ X :=
  LinearMap.mkContinuous (PsiLM g) ‖g‖ (fun x => by
    show ‖starRingEnd ℂ (g (toConj x))‖ ≤ ‖g‖ * ‖x‖
    rw [Complex.norm_conj]
    simpa using g.le_opNorm (toConj x))

@[simp] lemma Psi_apply (g : StrongDual ℂ (ConjSpace X)) (x : X) :
    Psi g x = starRingEnd ℂ (g (toConj x)) := rfl

/-- `Psi` undoes `Phi`: `conj (conj (f x)) = f x`. -/
lemma Psi_Phi (f : StrongDual ℂ X) : Psi (Phi f) = f := by
  ext x; simp

/-- `Phi` undoes `Psi`, the same computation run the other way. -/
lemma Phi_Psi (g : StrongDual ℂ (ConjSpace X)) : Phi (Psi g) = g := by
  ext x
  show starRingEnd ℂ (Psi g (ofConj x)) = g x
  rw [Psi_apply, Complex.conj_conj, toConj_ofConj]

/-- `Phi`, bundled as a (conjugate-)linear map `StrongDual ℂ X →ₛₗ[starRingEnd ℂ]
StrongDual ℂ (ConjSpace X)`: additive since `conj` and evaluation both are, and conjugate-linear
in `f` because `conj ((c • f) x) = conj (c * f x) = conj c * conj (f x)`. -/
def PhiLM' : StrongDual ℂ X →ₛₗ[starRingEnd ℂ] StrongDual ℂ (ConjSpace X) where
  toFun := Phi
  map_add' _ _ := by ext x; simp [map_add]
  map_smul' _ _ := by ext x; simp

/-- `‖Phi f‖ ≤ ‖f‖`, from the bound used to build `Phi f` via `LinearMap.mkContinuous`. -/
lemma norm_Phi_le (f : StrongDual ℂ X) : ‖Phi f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le (PhiLM f) (norm_nonneg f) _

/-- `‖Psi g‖ ≤ ‖g‖`, the mirror-image bound for `Psi`. -/
lemma norm_Psi_le (g : StrongDual ℂ (ConjSpace X)) : ‖Psi g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le (PsiLM g) (norm_nonneg g) _

/-- `Phi` is isometric: `≤` from `norm_Phi_le` directly, `≥` from applying `norm_Psi_le` to
`Phi f` and using that `Psi` undoes `Phi`. -/
lemma norm_Phi_eq (f : StrongDual ℂ X) : ‖Phi f‖ = ‖f‖ :=
  le_antisymm (norm_Phi_le f) (by
    have := norm_Psi_le (Phi f)
    rwa [Psi_Phi] at this)

/-- `Phi`, bundled as a conjugate-linear *isometric embedding*. -/
def PhiLI : StrongDual ℂ X →ₛₗᵢ[starRingEnd ℂ] StrongDual ℂ (ConjSpace X) :=
  { PhiLM' with norm_map' := norm_Phi_eq }

/-- **`Phi`, bundled as a conjugate-linear isometric equivalence.** Surjective because `Psi` is a
two-sided inverse (`Phi_Psi`); an isometric embedding is automatically injective, so this is
exactly `Phi`'s promotion to a `≃ₗᵢ⋆[ℂ]`. -/
def PhiEquiv : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] StrongDual ℂ (ConjSpace X) :=
  LinearIsometryEquiv.ofSurjective PhiLI (fun g => ⟨Psi g, Phi_Psi g⟩)

/-! ## B. Closing the connection to Mathlib's `WStarAlgebra` -/

universe u

/-- **A W⋆-algebra structure gives a W⋆-algebra** in Mathlib's sense, when the predual lives in the
universe of `A`. -/
lemma WStarAlgebraStructure.toWStarAlgebra
    {A : Type u} [WStarAlgebraStructure.{u, u} A] : WStarAlgebra A :=
  ⟨ConjSpace (WStarAlgebraStructure.Predual A), inferInstance, inferInstance, inferInstance,
    ⟨(PhiEquiv (X := WStarAlgebraStructure.Predual A)).symm.trans
      (WStarAlgebraStructure.toDual (A := A)).symm⟩⟩

end ProbabilisticTheory
