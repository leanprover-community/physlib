/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Physlib.Meta.TODO.Basic
/-!

# The Hilbert space of a finite target quantum mechanical system

A finite target quantum mechanical system is one whose states live in a finite
dimensional Hilbert space, with the basis states labelled by a finite type `d`
(for example the sites of a finite lattice, or the levels of a qudit).

This file contains
- the definition of `FiniteHilbertSpace d`, the Hilbert space of such a system,
  as a structure wrapping `EuclideanSpace ℂ d`, together with the notation `𝓗[d]`;
- its vector space structure (`AddCommGroup` and `Module ℂ`), transferred from
  `EuclideanSpace ℂ d` along the equivalence `equivEuclidean`;
- its Hilbert space structure (`NormedAddCommGroup`, `InnerProductSpace ℂ`,
  `FiniteDimensional ℂ` and `CompleteSpace`), induced along `linearEquivEuclidean`;
- the standard orthonormal basis `basisFun`, whose elements are the states
  localized at the points of `d`.

-/

@[expose] public section

namespace QuantumMechanics

TODO "To match this with the results currently in the `QuantumInfo` part of the library,
  we should:
  1. Define `FiniteHilbertSpace` as a structure with a single entry `val`, this
    should take as an input a finite and decidable type `d`. Below this type is
    taken as default to be `Fin n`.
  2. On this type we should then define the structure of an inner-product space, and a
    Hilbert space.
  3. We could then define the notation `𝓗[d]` to denote the Hilbert space corresponding
    to the type `d`.
  4. The results from `QuantumInfo/Finite/Braket.lean` can then be moved over
    to Physlib, and related to the definition of the Hilbert space here.
  Optional. Maybe it is worth moving these files to a directory called `States`, with
  the idea that it includes this definition of the Hilbert space, the
  definition of bras and kets, and the definition of mixed states. Maybe also
  parts of `./ResourceTheory/FreeState`."

/-- The Hilbert space of a finite target quantum mechanical system whose target is
  a finite type `d` with decidable equality.

  It is defined as a structure with a single field `val`, wrapping an element of
  `EuclideanSpace ℂ d` — the space of functions `d → ℂ` carrying the `L²` inner
  product `⟪ψ, φ⟫ = ∑ i, conj (ψ i) * φ i`. Using a structure in preference to
  `EuclideanSpace ℂ d` itself makes the Hilbert space of states a type of its own,
  with its own API and the notation `𝓗[d]`.

  Being finite dimensional, it is automatically a complete inner product space,
  that is, a genuine Hilbert space. -/
@[ext]
structure FiniteHilbertSpace (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying element of `EuclideanSpace ℂ d`. -/
  val : EuclideanSpace ℂ d

@[inherit_doc FiniteHilbertSpace]
scoped notation "𝓗[" d "]" => FiniteHilbertSpace d

namespace FiniteHilbertSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  given by `val`. -/
def equivEuclidean : FiniteHilbertSpace d ≃ EuclideanSpace ℂ d where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-!

## The vector space structure on `FiniteHilbertSpace d`

The vector space structure is transferred from `EuclideanSpace ℂ d`
along the equivalence `equivEuclidean`.

-/

noncomputable instance : AddCommGroup (FiniteHilbertSpace d) := equivEuclidean.addCommGroup

noncomputable instance : Module ℂ (FiniteHilbertSpace d) :=
  AddEquiv.module ℂ { equivEuclidean with map_add' := fun _ _ => rfl }

@[simp]
lemma val_add (ψ φ : FiniteHilbertSpace d) : (ψ + φ).val = ψ.val + φ.val := rfl

@[simp]
lemma val_smul (c : ℂ) (ψ : FiniteHilbertSpace d) : (c • ψ).val = c • ψ.val := rfl

@[simp]
lemma val_zero : (0 : FiniteHilbertSpace d).val = 0 := rfl

/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  as a `ℂ`-linear equivalence, upgrading `equivEuclidean`. -/
noncomputable def linearEquivEuclidean : FiniteHilbertSpace d ≃ₗ[ℂ] EuclideanSpace ℂ d :=
  { equivEuclidean with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-!

## The Hilbert space structure on `FiniteHilbertSpace d`

The norm and inner product are induced from `EuclideanSpace ℂ d` along
`linearEquivEuclidean`, making `FiniteHilbertSpace d` a finite dimensional
(and hence complete) inner product space, that is, a Hilbert space.

-/

noncomputable instance : NormedAddCommGroup (FiniteHilbertSpace d) :=
  NormedAddCommGroup.induced _ _ linearEquivEuclidean.toLinearMap linearEquivEuclidean.injective

@[simp]
lemma norm_eq_val (ψ : FiniteHilbertSpace d) : ‖ψ‖ = ‖ψ.val‖ := rfl

noncomputable instance : InnerProductSpace ℂ (FiniteHilbertSpace d) :=
  InnerProductSpace.induced linearEquivEuclidean.toLinearMap

@[simp]
lemma inner_eq_val (ψ φ : FiniteHilbertSpace d) : inner ℂ ψ φ = inner ℂ ψ.val φ.val := rfl

instance : FiniteDimensional ℂ (FiniteHilbertSpace d) :=
  Module.Finite.equiv linearEquivEuclidean.symm

instance : CompleteSpace (FiniteHilbertSpace d) := FiniteDimensional.complete ℂ _

/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  as a linear isometry equivalence, upgrading `linearEquivEuclidean`. -/
noncomputable def isometryEquivEuclidean : FiniteHilbertSpace d ≃ₗᵢ[ℂ] EuclideanSpace ℂ d where
  toLinearEquiv := linearEquivEuclidean
  norm_map' _ := rfl

/-!

## The standard orthonormal basis of `FiniteHilbertSpace d`

-/

/-- The standard orthonormal basis of `FiniteHilbertSpace d`, indexed by `d`. -/
noncomputable def basisFun (d : Type*) [Fintype d] [DecidableEq d] :
    OrthonormalBasis d ℂ (FiniteHilbertSpace d) :=
  (EuclideanSpace.basisFun d ℂ).map isometryEquivEuclidean.symm

lemma basisFun_apply (i : d) : basisFun d i = ⟨EuclideanSpace.single i 1⟩ := by
  rw [basisFun, OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply]; rfl

end FiniteHilbertSpace

end QuantumMechanics
