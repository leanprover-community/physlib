/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Symmetry
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.OrderUnit
public import Mathlib.Algebra.Star.Unitary

/-!

# Conjugation by a unitary is a symmetry of the self-adjoint part

A symmetry of a quantum system is standardly modeled as `α_g(a) = U_g a U_g*` for `U` a unitary
representation of a group `G`. This file builds the purely algebraic core of that statement: for a
fixed unitary `u` of a unital C⋆-algebra `A`, conjugation `a ↦ u a u*` restricts to a genuine
order-automorphism of `selfAdjoint A` (`OrderUnit/Symmetry.lean`'s `Symmetry`), and this assignment
is a group homomorphism `unitary A →* Symmetry (selfAdjoint A)`. Composing with a homomorphism
`U : G →* unitary A` — the algebraic shadow of a (strongly continuous, projective) unitary
representation, minus any topology this layer does not carry — produces exactly such a homomorphism
`G →* Symmetry (selfAdjoint A)`.

Conjugation lands back in `selfAdjoint A` because `IsSelfAdjoint.conjugate` already gives
`IsSelfAdjoint (z * x * star z)` for self-adjoint `x`; it is positive because `A` is a
`StarOrderedRing` (`star_right_conjugate_nonneg`); it is unital because `u * star u = 1`
(`Unitary.mul_star_self_of_mem`); and the two-sided inverse is conjugation by `star u` (equivalently
`u⁻¹`, since `unitary A` is a group with `Inv := star`), because `u * star u = star u * u = 1`
collapses `conjugationLinearMap u` composed with `conjugationLinearMap (star u)` (in either order)
to the identity by pure associativity. None of this needs any topology or continuity hypothesis —
this is purely algebraic content, independent of the "strongly continuous" qualifier that a genuine
unitary representation would carry.

## Main definitions

- `unitary.conjugationLinearMap u`, `unitary.conjugationUPLM u` : the underlying `ℝ`-linear map
  and unital positive linear map of conjugation by `u`, `a ↦ u a u*`, on `selfAdjoint A`.
- `unitary.conjugationLinearMap_conjugationLinearMap` : the algebraic heart,
  `conjugationLinearMap u (conjugationLinearMap v a) = conjugationLinearMap (u * v) a`, with no
  unitarity of `u`, `v` needed — pure associativity.
- `unitary.conjugationSymmetry u : Symmetry (selfAdjoint A)` : conjugation by `u` as a genuine
  order-automorphism, with inverse conjugation by `star u`.
- `unitary.conjugationSymmetryHom : unitary A →* Symmetry (selfAdjoint A)` : the assignment
  `u ↦ conjugationSymmetry u` is a group homomorphism (not an anti-homomorphism — composition
  order works out because `Symmetry`'s multiplication is itself `.comp`, "apply the right factor
  first").
- `Unitary.Representation.toSymmetryHom (U : G →* unitary A) : G →* Symmetry (selfAdjoint A)` :
  composing with a homomorphism into the unitary group gives `α_g(a) = U_g a U_g*` directly, as a
  homomorphism into the automorphism group.

-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace unitary

/-! ## Conjugation as a linear map -/

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

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
lemma coe_conjugationLinearMap (u : unitary A) (a : selfAdjoint A) :
    (conjugationLinearMap u a : A) = (u : A) * (a : A) * star (u : A) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The algebraic heart of the whole file: composing conjugation by `v` then by `u` is
conjugation by `u * v`, by pure associativity of multiplication in `A` — no unitarity of `u` or
`v` is used here at all. Matches `Unitary.conjStarAlgAut_mul_apply` in mathlib, which is the same
identity for the full ⋆-algebra automorphism rather than its restriction to `selfAdjoint A`. -/
lemma conjugationLinearMap_conjugationLinearMap (u v : unitary A) (a : selfAdjoint A) :
    conjugationLinearMap u (conjugationLinearMap v a) = conjugationLinearMap (u * v) a := by
  ext
  show (u : A) * ((v : A) * (a : A) * star (v : A)) * star (u : A) =
      ((u * v : unitary A) : A) * (a : A) * star ((u * v : unitary A) : A)
  rw [Submonoid.coe_mul, star_mul]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
/-- Conjugation by `1` does nothing. -/
@[simp]
lemma conjugationLinearMap_one (a : selfAdjoint A) :
    conjugationLinearMap (1 : unitary A) a = a := by
  ext
  show (1 : A) * (a : A) * star (1 : A) = (a : A)
  simp

omit [PartialOrder A] [StarOrderedRing A] in
/-- Conjugating by `u` then by `star u` is the identity: this is
`conjugationLinearMap_conjugationLinearMap` specialized along `star u * u = 1`. -/
lemma conjugationLinearMap_star_conjugationLinearMap (u : unitary A) (a : selfAdjoint A) :
    conjugationLinearMap (star u) (conjugationLinearMap u a) = a := by
  rw [conjugationLinearMap_conjugationLinearMap, Unitary.star_mul_self, conjugationLinearMap_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Conjugating by `star u` then by `u` is the identity: this is
`conjugationLinearMap_conjugationLinearMap` specialized along `u * star u = 1`. -/
lemma conjugationLinearMap_conjugationLinearMap_star (u : unitary A) (a : selfAdjoint A) :
    conjugationLinearMap u (conjugationLinearMap (star u) a) = a := by
  rw [conjugationLinearMap_conjugationLinearMap, Unitary.mul_star_self, conjugationLinearMap_one]

/-! ## Conjugation as a unital positive linear map -/

/-- Conjugation by a unitary `u`, `a ↦ u a u*`, as a unital positive linear map (channel) on
`selfAdjoint A`: positive by `star_right_conjugate_nonneg`, unital because `u * star u = 1`. -/
noncomputable def conjugationUPLM (u : unitary A) : selfAdjoint A →ₚ₁[ℝ] selfAdjoint A :=
  .ofLinearMap (conjugationLinearMap u)
    (fun x hx => star_right_conjugate_nonneg hx (u : A))
    (by
      ext
      show (u : A) * (1 : A) * star (u : A) = (1 : A)
      rw [mul_one, Unitary.mul_star_self_of_mem u.2])

@[simp]
lemma coe_conjugationUPLM (u : unitary A) (a : selfAdjoint A) :
    (conjugationUPLM u a : A) = (u : A) * (a : A) * star (u : A) := rfl

lemma conjugationUPLM_comp_conjugationUPLM (u v : unitary A) :
    (conjugationUPLM u).comp (conjugationUPLM v) = conjugationUPLM (u * v) :=
  UnitalPositiveLinearMap.ext fun a =>
    Subtype.ext (congrArg Subtype.val (conjugationLinearMap_conjugationLinearMap u v a))

lemma conjugationUPLM_one : conjugationUPLM (1 : unitary A) = .id ℝ (selfAdjoint A) :=
  UnitalPositiveLinearMap.ext fun a =>
    Subtype.ext (congrArg Subtype.val (conjugationLinearMap_one a))

/-! ## Conjugation as a symmetry -/

/-- Conjugation by a unitary `u` is a genuine order-automorphism of `selfAdjoint A`: conjugation by
a fixed unitary realizes `α_g(a) = U_g a U_g*` for a single group element. Its two-sided inverse is
conjugation by `star u`. -/
noncomputable def conjugationSymmetry (u : unitary A) : Symmetry (selfAdjoint A) :=
  ⟨conjugationUPLM u, conjugationUPLM (star u),
    UnitalPositiveLinearMap.ext fun a =>
      Subtype.ext (congrArg Subtype.val (conjugationLinearMap_star_conjugationLinearMap u a)),
    UnitalPositiveLinearMap.ext fun a =>
      Subtype.ext (congrArg Subtype.val (conjugationLinearMap_conjugationLinearMap_star u a))⟩

@[simp]
lemma val_conjugationSymmetry (u : unitary A) :
    (conjugationSymmetry u : selfAdjoint A →ₚ₁[ℝ] selfAdjoint A) = conjugationUPLM u := rfl

/-- `u ↦ conjugationSymmetry u` is a genuine group homomorphism
`unitary A →* Symmetry (selfAdjoint A)`, not an anti-homomorphism — `Symmetry`'s multiplication is
`φ * ψ = φ.comp ψ` (apply `ψ` first), and `conjugationLinearMap_conjugationLinearMap` shows
conjugation composes the same way: conjugating by `v` then `u` is conjugation by `u * v`. -/
noncomputable def conjugationSymmetryHom : unitary A →* Symmetry (selfAdjoint A) where
  toFun := conjugationSymmetry
  map_one' := Symmetry.ext fun a => by
    rw [val_conjugationSymmetry, conjugationUPLM_one, Symmetry.val_one]
  map_mul' u v := Symmetry.ext fun a => by
    simp only [Symmetry.val_mul, val_conjugationSymmetry]
    rw [conjugationUPLM_comp_conjugationUPLM]

@[simp]
lemma conjugationSymmetryHom_apply (u : unitary A) :
    conjugationSymmetryHom u = conjugationSymmetry u := rfl

end unitary

/-! ## Unitary representations induce symmetry actions -/

namespace Unitary

/-- A group homomorphism `U : G →* unitary A` — the algebraic shadow of a unitary representation,
minus any strong-continuity hypothesis, which needs a topology this layer does not carry —
composes with `conjugationSymmetryHom` to give exactly `α_g(a) = U_g a U_g*` as a homomorphism
`G →* Symmetry (selfAdjoint A)`. A measurement covariant under such an action
(`UnitalPositiveLinearMap.IsCovariant` / `EffectValuedMeasure.IsCovariant`,
`Measurement/Covariance.lean`) is exactly one satisfying `M ∘ β_g = α_g ∘ M` for this `α`;
connecting the two is future work, not attempted here. -/
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
