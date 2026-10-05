/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RepresentationTheory.Basic
/-!
# Derivations and representations on the exterior algebra

## i. Overview

Mathlib's `ExteriorAlgebra` carries the universal property `ExteriorAlgebra.lift` and the
functorial map `ExteriorAlgebra.map`, but neither the derivation extending a linear
endomorphism of the generators nor the representation extending a representation on them.
This file provides both, as the exterior counterparts of the symmetric-algebra
constructions in `Physlib.Mathematics.SymmetricAlgebra`.

A linear endomorphism `d` of `M` extends uniquely to an *even* derivation of the exterior
algebra — the Leibniz rule with no Koszul signs — because the generator map
`ι x ↦ (ι x, ι (d x))` into the trivial square-zero extension squares to zero: degree-one
elements of an exterior algebra anticommute. A representation of a monoid `G` on `M`
extends to one on the exterior algebra by functoriality of `ExteriorAlgebra.map`, and every
element of `G` then acts by an algebra homomorphism.

## ii. Key results

- `ExteriorAlgebra.derivationOfLinear` : the even derivation extending a linear
  endomorphism of the generators.
- `ExteriorAlgebra.derivationOfLinear_mul` : the Leibniz rule.
- `ExteriorAlgebra.derivationOfLinear_comm_apply` : derivations extending commuting
  endomorphisms commute.
- `ExteriorAlgebra.algHom_derivationOfLinear` : an algebra map determined by an
  intertwining linear map carries one derivation to the other.
- `Representation.exteriorAlgebra` : the representation extending one on the generators.
- `Representation.exteriorAlgebra_apply_mul` : each element acts multiplicatively.
- `ExteriorAlgebra.exteriorAlgebra_derivationOfLinear` : covariance of the derivation
  under the representation.
- `ExteriorAlgebra.mapEquiv` : transport of the algebra along a linear equivalence of the
  generators.
- `ExteriorAlgebra.algHom_exteriorAlgebra` : an algebra map determined by an intertwining
  linear map carries one representation to the other.

## iii. Table of contents

- A. The derivation extending a linear endomorphism
- B. The representation extending a representation on the generators
- C. Transport along a linear equivalence

-/

@[expose] public section

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-!

## A. The derivation extending a linear endomorphism

-/

section Derivation

variable (d : M →ₗ[R] M)

/-- The generator map of the derivation extending `d`, into the trivial square-zero
  extension of the exterior algebra: `ι x ↦ (ι x, ι (d x))`. -/
noncomputable def derivationGen :
    M →ₗ[R] TrivSqZeroExt (ExteriorAlgebra R M) (ExteriorAlgebra R M) where
  toFun x := (ι R x, ι R (d x))
  map_add' x y := by simp only [map_add]; rfl
  map_smul' c x := by simp only [map_smul, RingHom.id_apply]; rfl

@[simp]
lemma derivationGen_fst (x : M) : (derivationGen d x).fst = ι R x := rfl

@[simp]
lemma derivationGen_snd (x : M) : (derivationGen d x).snd = ι R (d x) := rfl

/-- The generator map squares to zero: degree-one elements of the exterior algebra
  anticommute, which is exactly the square-zero condition on the pair. -/
lemma derivationGen_mul_self (x : M) : derivationGen d x * derivationGen d x = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, derivationGen_fst, ι_sq_zero, TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, derivationGen_fst, derivationGen_snd,
      TrivSqZeroExt.snd_zero, smul_eq_mul, op_smul_eq_mul]
    exact ι_add_mul_swap x (d x)

/-- The lift of the derivation extending `d` to the trivial square-zero extension of the
  exterior algebra: the algebra homomorphism `x ↦ (x, derivationOfLinear d x)`. -/
noncomputable def derivationHom :
    ExteriorAlgebra R M →ₐ[R]
      TrivSqZeroExt (ExteriorAlgebra R M) (ExteriorAlgebra R M) :=
  ExteriorAlgebra.lift R ⟨derivationGen d, derivationGen_mul_self d⟩

@[simp]
lemma derivationHom_ι (x : M) : derivationHom d (ι R x) = derivationGen d x := by
  rw [derivationHom, ExteriorAlgebra.lift_ι_apply]

/-- The first component of the square-zero lift is the identity. -/
@[simp]
lemma derivationHom_fst (x : ExteriorAlgebra R M) : (derivationHom d x).fst = x := by
  have h : (TrivSqZeroExt.fstHom R (ExteriorAlgebra R M) (ExteriorAlgebra R M)).comp
      (derivationHom d) = AlgHom.id R (ExteriorAlgebra R M) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, derivationHom_ι]
      rfl)
  exact DFunLike.congr_fun h x

/-- The even derivation of the exterior algebra extending a linear endomorphism `d` of
  `M`: the map obeying the Leibniz rule, with no Koszul signs, whose value on a generator
  `ι x` is `ι (d x)`. -/
noncomputable def derivationOfLinear : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M where
  toFun x := (derivationHom d x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (derivationHom d) x y)
  map_smul' c x := congrArg TrivSqZeroExt.snd (map_smul (derivationHom d) c x)

@[simp]
lemma derivationOfLinear_ι (x : M) : derivationOfLinear d (ι R x) = ι R (d x) := by
  rw [show derivationOfLinear d (ι R x) = (derivationHom d (ι R x)).snd from rfl,
    derivationHom_ι, derivationGen_snd]

@[simp]
lemma derivationOfLinear_one : derivationOfLinear d (1 : ExteriorAlgebra R M) = 0 :=
  congrArg TrivSqZeroExt.snd (map_one (derivationHom d))

@[simp]
lemma derivationOfLinear_algebraMap (r : R) :
    derivationOfLinear d (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, derivationOfLinear_one, smul_zero]

/-- The Leibniz rule for the derivation extending `d`, with no Koszul signs: the derivation
  is even even though the generators are odd. -/
lemma derivationOfLinear_mul (x y : ExteriorAlgebra R M) :
    derivationOfLinear d (x * y)
      = derivationOfLinear d x * y + x * derivationOfLinear d y := by
  have h : derivationOfLinear d (x * y) =
      (derivationHom d x).fst * derivationOfLinear d y
        + derivationOfLinear d x * (derivationHom d y).fst :=
    congrArg TrivSqZeroExt.snd (map_mul (derivationHom d) x y)
  rw [derivationHom_fst, derivationHom_fst] at h
  exact h.trans (add_comm _ _)

/-- Derivations extending commuting endomorphisms commute. -/
lemma derivationOfLinear_comm_apply {d₁ d₂ : M →ₗ[R] M} (h : d₁ ∘ₗ d₂ = d₂ ∘ₗ d₁)
    (x : ExteriorAlgebra R M) :
    derivationOfLinear d₁ (derivationOfLinear d₂ x)
      = derivationOfLinear d₂ (derivationOfLinear d₁ x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp only [derivationOfLinear_ι]
    exact congrArg (ι R) (DFunLike.congr_fun h v)
  | mul x y hx hy =>
    simp only [derivationOfLinear_mul, map_add, hx, hy]
    abel
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An algebra map carries one derivation to the other when the linear map it is
  determined by on the generators intertwines the two endomorphisms. The hypotheses are
  stated pointwise so that the lemma can be applied without rewriting inside a large
  algebra. -/
lemma algHom_derivationOfLinear {N : Type*} [AddCommGroup N] [Module R N]
    (F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N) {f : M →ₗ[R] N}
    (hF : ∀ x, F (ι R x) = ι R (f x)) {d : M →ₗ[R] M} {d' : N →ₗ[R] N}
    (h : ∀ x, f (d x) = d' (f x)) (y : ExteriorAlgebra R M) :
    F (derivationOfLinear d y) = derivationOfLinear d' (F y) := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [derivationOfLinear_algebraMap, map_zero, AlgHom.commutes,
      derivationOfLinear_algebraMap]
  | ι v => rw [derivationOfLinear_ι, hF, hF, derivationOfLinear_ι, h]
  | mul a b ha hb =>
    simp only [derivationOfLinear_mul, map_add, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end Derivation

end ExteriorAlgebra

/-!

## B. The representation extending a representation on the generators

-/

namespace Representation

variable {R G M : Type*} [CommRing R] [Monoid G] [AddCommGroup M] [Module R M]

/-- The representation on the exterior algebra extending a representation on the
  generators, by functoriality of `ExteriorAlgebra.map`. -/
noncomputable def exteriorAlgebra (ρ : Representation R G M) :
    Representation R G (ExteriorAlgebra R M) where
  toFun g := (ExteriorAlgebra.map (ρ g)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g h := by
    have hmap : ExteriorAlgebra.map (R := R) (ρ (g * h))
        = (ExteriorAlgebra.map (ρ g)).comp (ExteriorAlgebra.map (ρ h)) := by
      rw [map_mul, Module.End.mul_eq_comp, ExteriorAlgebra.map_comp_map]
    rw [hmap]
    rfl

lemma exteriorAlgebra_apply (ρ : Representation R G M) (g : G)
    (x : ExteriorAlgebra R M) :
    ρ.exteriorAlgebra g x = ExteriorAlgebra.map (ρ g) x := rfl

@[simp]
lemma exteriorAlgebra_ι (ρ : Representation R G M) (g : G) (x : M) :
    ρ.exteriorAlgebra g (ExteriorAlgebra.ι R x) = ExteriorAlgebra.ι R (ρ g x) :=
  ExteriorAlgebra.map_apply_ι _ x

@[simp]
lemma exteriorAlgebra_apply_one (ρ : Representation R G M) (g : G) :
    ρ.exteriorAlgebra g (1 : ExteriorAlgebra R M) = 1 :=
  map_one (ExteriorAlgebra.map (ρ g))

lemma exteriorAlgebra_apply_mul (ρ : Representation R G M) (g : G)
    (x y : ExteriorAlgebra R M) :
    ρ.exteriorAlgebra g (x * y) = ρ.exteriorAlgebra g x * ρ.exteriorAlgebra g y :=
  map_mul (ExteriorAlgebra.map (ρ g)) x y

lemma exteriorAlgebra_algebraMap (ρ : Representation R G M) (g : G) (r : R) :
    ρ.exteriorAlgebra g (algebraMap R (ExteriorAlgebra R M) r)
      = algebraMap R (ExteriorAlgebra R M) r :=
  AlgHom.commutes (ExteriorAlgebra.map (ρ g)) r

end Representation

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Covariance of the derivation under the representation. If the representation
  carries each endomorphism of a family into a combination of the others on the generators,
  then it carries the derivation extending one into the same combination of the derivations
  extending the others on the whole exterior algebra. This is the shape the statement that
  the total derivative is a Lorentz vector takes; it is proved by induction rather than by
  algebra-map extensionality, a derivation not being an algebra map. -/
lemma exteriorAlgebra_derivationOfLinear {G κ : Type*} [Monoid G] [Fintype κ]
    (ρ : Representation R G M) (g : G) (d : κ → M →ₗ[R] M) (μ : κ) (c : κ → R)
    (h : ∀ x, ρ g (d μ x) = ∑ a, c a • d a (ρ g x)) (y : ExteriorAlgebra R M) :
    ρ.exteriorAlgebra g (derivationOfLinear (d μ) y)
      = ∑ a, c a • derivationOfLinear (d a) (ρ.exteriorAlgebra g y) := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [derivationOfLinear_algebraMap, map_zero, Representation.exteriorAlgebra_algebraMap]
    exact ((Finset.sum_congr rfl fun a _ => by
      rw [derivationOfLinear_algebraMap, smul_zero]).trans Finset.sum_const_zero).symm
  | ι v =>
    rw [derivationOfLinear_ι, Representation.exteriorAlgebra_ι,
      Representation.exteriorAlgebra_ι, h, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, derivationOfLinear_ι]
  | mul a b ha hb =>
    rw [derivationOfLinear_mul, map_add]
    simp only [Representation.exteriorAlgebra_apply_mul]
    rw [ha, hb, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [derivationOfLinear_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [map_add, smul_add]

/-- An algebra map carries one representation to the other when the linear map it is
  determined by on the generators intertwines the two representations on them. Unlike the
  derivation statement this is pure extensionality of algebra maps, each group element
  acting by one; the hypotheses are stated pointwise so that the lemma can be applied
  without rewriting inside a large algebra. -/
lemma algHom_exteriorAlgebra {N G : Type*} [AddCommGroup N] [Module R N] [Monoid G]
    (F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N) {f : M →ₗ[R] N}
    (hF : ∀ x, F (ι R x) = ι R (f x))
    {ρ : Representation R G M} {σ : Representation R G N} (g : G)
    (h : ∀ x, f (ρ g x) = σ g (f x)) (y : ExteriorAlgebra R M) :
    F (ρ.exteriorAlgebra g y) = σ.exteriorAlgebra g (F y) := by
  have key : F.comp (ExteriorAlgebra.map (ρ g)) = (ExteriorAlgebra.map (σ g)).comp F :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.comp_apply,
        ExteriorAlgebra.map_apply_ι, hF, hF, ExteriorAlgebra.map_apply_ι, h])
  exact DFunLike.congr_fun key y

end ExteriorAlgebra


/-!

## C. Transport along a linear equivalence

Mathlib's `ExteriorAlgebra.congr` goes through `CliffordAlgebra.equivOfIsometry`, whose
quadratic-form layer the elaborator cannot see through cheaply once the underlying module is
a large direct sum. The version below is built from `ExteriorAlgebra.map` instead.

-/

namespace ExteriorAlgebra

/-- Transport of an exterior algebra along a linear equivalence, built from
  `ExteriorAlgebra.map` so that no `CliffordAlgebra` isometry has to be unfolded. -/
noncomputable def mapEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
    (ExteriorAlgebra.map e.symm.toLinearMap)
    ((ExteriorAlgebra.map_comp_map e.symm.toLinearMap e.toLinearMap).trans
      ((congrArg (fun f : N →ₗ[R] N => ExteriorAlgebra.map f)
          (LinearMap.ext fun x => e.apply_symm_apply x)).trans ExteriorAlgebra.map_id))
    ((ExteriorAlgebra.map_comp_map e.toLinearMap e.symm.toLinearMap).trans
      ((congrArg (fun f : M →ₗ[R] M => ExteriorAlgebra.map f)
          (LinearMap.ext fun x => e.symm_apply_apply x)).trans ExteriorAlgebra.map_id))

@[simp]
lemma mapEquiv_apply_ι {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (x : M) :
    mapEquiv e (ExteriorAlgebra.ι R x) = ExteriorAlgebra.ι R (e x) :=
  ExteriorAlgebra.map_apply_ι _ x

end ExteriorAlgebra
