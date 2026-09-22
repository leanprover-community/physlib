/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.Basic
public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.ConjSpace
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# `WStarAlgebraStructure A` gives Mathlib's `WStarAlgebra A`

This file closes the connection `Basic.lean`'s module docstring flags as unattempted: every
`WStarAlgebraStructure A` (a *chosen* predual and identification, a `class`) gives a proof of
Mathlib's `WStarAlgebra A` (mere *existence* of a predual, a `Prop`,
`Mathlib.Analysis.VonNeumannAlgebra.Basic`).

There are exactly two mismatches between `toDual : A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)` and what
`WStarAlgebra`'s `exists_predual` wants (`StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A` for some `X`), and this file
closes each in turn.

* **Direction.** `toDual` points from `A` to the dual of its predual; `exists_predual` wants a map
  the other way, from the dual of some Banach space *to* `A`. This half is free: `toDual.symm :
  StrongDual ℂ (Predual A) ≃ₗᵢ[ℂ] A` is still linear, just reversed.

* **Linearity.** `toDual` (and hence `toDual.symm`) is linear (`≃ₗᵢ[ℂ]`); `exists_predual` wants a
  *conjugate*-linear identification (`≃ₗᵢ⋆[ℂ]`, notation for `LinearIsometryEquiv (starRingEnd ℂ)`).
  There is no canonical conjugate-linear self-map of an arbitrary Banach space, so this cannot be
  fixed by post- or pre-composing `toDual.symm` with some fixed conjugate-linear equivalence of
  `Predual A` or of `A`. Instead, `ConjSpace.lean`'s scalar-conjugation twist of the *type* of the
  predual supplies exactly the missing conjugate-linear step: `Phi : StrongDual ℂ X ≃ₗᵢ⋆[ℂ]
  StrongDual ℂ (ConjSpace X)`, `f ↦ (x ↦ conj (f (ofConj x)))`, for any Banach space `X`. This is
  well-defined precisely because reinterpreting `conj ∘ f` as a function on `ConjSpace X` (rather
  than on `X`) turns its conjugate-linearity in `x` into honest `ConjSpace X`-linearity — the
  twisted scalar action absorbs the extra conjugation. `Phi` is bijective (inverse `Psi`, the same
  construction run the other way) and isometric (postcomposing with `starRingEnd ℂ`, itself an
  isometry, does not change the operator norm).

Chaining `Phi.symm : StrongDual ℂ (ConjSpace (Predual A)) ≃ₗᵢ⋆[ℂ] StrongDual ℂ (Predual A)` with
`toDual.symm : StrongDual ℂ (Predual A) ≃ₗᵢ[ℂ] A` composes a conjugate-linear equivalence with a
linear one, giving a conjugate-linear equivalence overall (Mathlib's `RingHomCompTriple`/
`RingHomInvPair` instances for `starRingEnd ℂ` handle the bookkeeping); this is exactly the witness
`exists_predual` needs, with `X := ConjSpace (Predual A)`.

One further subtlety, purely about universes, is worth recording: `WStarAlgebraStructure A`'s
`Predual A` is universe-polymorphic *independently* of `A` (`WStarAlgebraStructure.{u, v}`), while
Mathlib's `WStarAlgebra (M : Type u)` demands its predual witness live in the *same* universe `u`
as `M` (`exists_predual : ∃ (X : Type u), ...`). `toWStarAlgebra` below is therefore stated for
`WStarAlgebraStructure.{u, u} A`, pinning the predual to `A`'s own universe. Every concrete instance
in this development (`WStarAlgebra/Concrete.lean`'s trace-class predual included) already satisfies
this, so it costs nothing in practice; it is only a genuine restriction for a hypothetical
`WStarAlgebraStructure A` whose chosen predual deliberately lives in a strictly larger universe than
`A`, which no construction here does.

## Main declarations

- `Phi`, `Psi` : the mutually inverse conjugate-linear maps `StrongDual ℂ X → StrongDual ℂ
  (ConjSpace X)` and back, for any Banach space `X`.
- `PhiEquiv : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] StrongDual ℂ (ConjSpace X)` : the bundled conjugate-linear
  isometric equivalence.
- `WStarAlgebraStructure.toWStarAlgebra` : the theorem closing the connection,
  `WStarAlgebraStructure A → WStarAlgebra A` (universe-pinned as above).
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open ConjSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ## The conjugate-linear self-duality `Phi` of the strong dual, via `ConjSpace` -/

/-- The linear part of `Phi`, before recording continuity: `f ↦ (x ↦ conj (f (ofConj x)))`, viewed
as a map into `ConjSpace X →ₗ[ℂ] ℂ`. Genuinely `ConjSpace X`-linear (not just conjugate-linear in
`x`): the twist in `ConjSpace X`'s scalar action exactly absorbs the extra conjugation, since
`f (c •[ConjSpace] x) = f ((starRingEnd ℂ c) • ofConj x) = (starRingEnd ℂ c) * f (ofConj x)`, and
applying `conj` once more turns this into `c * conj (f (ofConj x))`. -/
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

/-! ## Closing the connection to Mathlib's `WStarAlgebra` -/

universe u

/-- **Every `WStarAlgebraStructure A` gives Mathlib's `WStarAlgebra A`.** See the module docstring
for the two mismatches this closes (direction, via `toDual.symm`; linearity, via `PhiEquiv`) and
for why the predual's universe is pinned to `A`'s own (`WStarAlgebraStructure.{u, u}`) rather than
left fully independent. -/
theorem WStarAlgebraStructure.toWStarAlgebra
    {A : Type u} [WStarAlgebraStructure.{u, u} A] : WStarAlgebra A :=
  ⟨ConjSpace (WStarAlgebraStructure.Predual A), inferInstance, inferInstance, inferInstance,
    ⟨(PhiEquiv (X := WStarAlgebraStructure.Predual A)).symm.trans
      (WStarAlgebraStructure.toDual (A := A)).symm⟩⟩
