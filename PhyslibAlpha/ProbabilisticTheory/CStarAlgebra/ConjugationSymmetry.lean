/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Channel.Symmetry
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Mathlib.Algebra.Star.Unitary

/-!

# Unitary conjugation as a symmetry

## i. Overview

A symmetry of a quantum system is usually implemented as `a ↦ u a u⋆` for a unitary `u`. Conjugation
by a unitary maps self-adjoint elements to self-adjoint elements, preserves positivity and the unit,
and is inverted by conjugation by `u⋆`. So it is a symmetry of the observables, and `u ↦ u (·) u⋆`
is a group homomorphism from the unitaries to the symmetry group. Composing with a unitary
representation of a group `G` gives a symmetry action of `G`.

## ii. Key results

- `unitary.conjugationChannel` : conjugation by a unitary, as a channel.
- `unitary.conjugationSymmetry` : conjugation by a unitary, as a symmetry.
- `unitary.conjugationSymmetryHom` : the homomorphism from unitaries to symmetries.
- `Unitary.Representation.toSymmetryHom` : the symmetry action of a unitary representation.

## iii. Table of contents

- A. Conjugation as a linear map
- B. Conjugation as a unital positive linear map
- C. Conjugation as a symmetry
- D. Unitary representations induce symmetry actions

-/

@[expose] public section


namespace unitary
open ProbabilisticTheory
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## A. Conjugation as a linear map -/

/-- The underlying `ℝ`-linear map of conjugation by a unitary `u`, `a ↦ u a u*`, restricted to
self-adjoint elements. Lands back in `selfAdjoint A` by `IsSelfAdjoint.conjugate`. -/
def conjugationLinearMap (u : unitary A) : selfAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun a := ⟨(u : A) * (a : A) * star (u : A), a.2.conjugate (u : A)⟩
  map_add' a b := by
    ext
    show (u : A) * ((a : A) + (b : A)) * star (u : A) =
        (u : A) * (a : A) * star (u : A) + (u : A) * (b : A) * star (u : A)
    rw [mul_add, add_mul]
  map_smul' c a := by
    ext
    show (u : A) * (c • (a : A)) * star (u : A) = c • ((u : A) * (a : A) * star (u : A))
    rw [mul_smul_comm, smul_mul_assoc]

@[simp]
lemma coe_conjugationLinearMap (u : unitary A) (a : selfAdjoint A) :
    (conjugationLinearMap u a : A) = (u : A) * (a : A) * star (u : A) := rfl

/-- Conjugating by `v` and then by `u` is conjugating by `u * v`. -/
lemma conjugationLinearMap_conjugationLinearMap (u v : unitary A) (a : selfAdjoint A) :
    conjugationLinearMap u (conjugationLinearMap v a) = conjugationLinearMap (u * v) a := by
  ext
  show (u : A) * ((v : A) * (a : A) * star (v : A)) * star (u : A) =
      ((u * v : unitary A) : A) * (a : A) * star ((u * v : unitary A) : A)
  rw [Submonoid.coe_mul, star_mul]
  noncomm_ring

/-- Conjugation by `1` does nothing. -/
@[simp]
lemma conjugationLinearMap_one (a : selfAdjoint A) :
    conjugationLinearMap (1 : unitary A) a = a := by
  ext
  show (1 : A) * (a : A) * star (1 : A) = (a : A)
  simp

/-- Conjugating by `u` then by `star u` is the identity: this is
`conjugationLinearMap_conjugationLinearMap` specialized along `star u * u = 1`. -/
lemma conjugationLinearMap_star_conjugationLinearMap (u : unitary A) (a : selfAdjoint A) :
    conjugationLinearMap (star u) (conjugationLinearMap u a) = a := by
  rw [conjugationLinearMap_conjugationLinearMap, Unitary.star_mul_self, conjugationLinearMap_one]

/-- Conjugating by `star u` then by `u` is the identity: this is
`conjugationLinearMap_conjugationLinearMap` specialized along `u * star u = 1`. -/
lemma conjugationLinearMap_conjugationLinearMap_star (u : unitary A) (a : selfAdjoint A) :
    conjugationLinearMap u (conjugationLinearMap (star u) a) = a := by
  rw [conjugationLinearMap_conjugationLinearMap, Unitary.mul_star_self, conjugationLinearMap_one]

/-! ## B. Conjugation as a unital positive linear map -/

/-- Conjugation by a unitary `u`, `a ↦ u a u*`, as a unital positive linear map (channel) on
`selfAdjoint A`: positive by `star_right_conjugate_nonneg`, unital because `u * star u = 1`. -/
noncomputable def conjugationChannel (u : unitary A) : Channel (selfAdjoint A) (selfAdjoint A) :=
  .ofLinearMap (conjugationLinearMap u)
    (fun x hx => star_right_conjugate_nonneg hx (u : A))
    (by
      ext
      show (u : A) * (1 : A) * star (u : A) = (1 : A)
      rw [mul_one, Unitary.mul_star_self_of_mem u.2])

@[simp]
lemma coe_conjugationChannel (u : unitary A) (a : selfAdjoint A) :
    (conjugationChannel u a : A) = (u : A) * (a : A) * star (u : A) := rfl

lemma conjugationChannel_comp_conjugationChannel (u v : unitary A) :
    (conjugationChannel u).comp (conjugationChannel v) = conjugationChannel (u * v) :=
  UnitalPositiveLinearMap.ext fun a =>
    Subtype.ext (congrArg Subtype.val (conjugationLinearMap_conjugationLinearMap u v a))

lemma conjugationChannel_one : conjugationChannel (1 : unitary A) = .id ℝ (selfAdjoint A) :=
  UnitalPositiveLinearMap.ext fun a =>
    Subtype.ext (congrArg Subtype.val (conjugationLinearMap_one a))

/-! ## C. Conjugation as a symmetry -/

/-- Conjugation by a unitary `u`, as a symmetry of the observables, with inverse conjugation by
`u⋆`. -/
noncomputable def conjugationSymmetry (u : unitary A) : Symmetry (selfAdjoint A) :=
  ⟨conjugationChannel u, conjugationChannel (star u),
    UnitalPositiveLinearMap.ext fun a =>
      Subtype.ext (congrArg Subtype.val (conjugationLinearMap_star_conjugationLinearMap u a)),
    UnitalPositiveLinearMap.ext fun a =>
      Subtype.ext (congrArg Subtype.val (conjugationLinearMap_conjugationLinearMap_star u a))⟩

@[simp]
lemma val_conjugationSymmetry (u : unitary A) :
    (conjugationSymmetry u : Channel (selfAdjoint A) (selfAdjoint A)) = conjugationChannel u := rfl

/-- Conjugation as a group homomorphism from the unitaries to the symmetries of the observables. -/
noncomputable def conjugationSymmetryHom : unitary A →* Symmetry (selfAdjoint A) where
  toFun := conjugationSymmetry
  map_one' := Symmetry.ext fun a => by
    rw [val_conjugationSymmetry, conjugationChannel_one, Symmetry.val_one]
  map_mul' u v := Symmetry.ext fun a => by
    simp only [Symmetry.val_mul, val_conjugationSymmetry]
    rw [conjugationChannel_comp_conjugationChannel]

@[simp]
lemma conjugationSymmetryHom_apply (u : unitary A) :
    conjugationSymmetryHom u = conjugationSymmetry u := rfl

end unitary

namespace ProbabilisticTheory

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## D. Unitary representations induce symmetry actions -/

namespace Unitary

/-- The symmetry action `α_g(a) = U_g a U_g*` of a unitary representation `U : G →* unitary A`. -/
noncomputable def Representation.toSymmetryHom {G : Type*} [Group G] (U : G →* unitary A) :
    G →* Symmetry (selfAdjoint A) :=
  unitary.conjugationSymmetryHom.comp U

@[simp]
lemma Representation.toSymmetryHom_apply {G : Type*} [Group G] (U : G →* unitary A) (g : G) :
    Representation.toSymmetryHom U g = unitary.conjugationSymmetry (U g) := rfl

/-- Unwinding `Representation.toSymmetryHom` on an element `a` recovers `α_g(a) = U_g a U_g*`
literally. -/
lemma Representation.toSymmetryHom_apply_coe {G : Type*} [Group G] (U : G →* unitary A) (g : G)
    (a : selfAdjoint A) :
    ((Representation.toSymmetryHom U g).1 a : A) = (U g : A) * (a : A) * star (U g : A) := rfl

end Unitary

end ProbabilisticTheory
