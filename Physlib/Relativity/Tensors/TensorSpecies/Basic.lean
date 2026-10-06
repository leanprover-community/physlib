/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.TODO.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Intertwining
/-!

# Tensor species

- A tensor species is a structure including all of the ingredients needed to define a type of
  tensor.
- Examples of tensor species will include real Lorentz tensors, complex Lorentz tensors, and
  Einstein tensors.
- Tensor species are built upon symmetric monoidal categories.

-/

@[expose] public section

open Module
open scoped TensorProduct

TODO "Include in the condition of `TensorSpecies` a relationship between
  the metrics and the basis vectors."

/-- The structure `TensorSpecies` contains the necessary structure needed to define
  a system of tensors with index notation. Examples of `TensorSpecies` include real Lorentz tensors,
  complex Lorentz tensors, and ordinary Euclidean tensors. -/
structure TensorSpecies (k : Type) [CommRing k] (C : Type) (G : Type) [Group G]
    (V : C → Type) [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    (basisIdx : C → Type) [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    (rep : (c : C) → Representation k G (V c)) (basis : (c : C) → Basis (basisIdx c) k (V c)) where
  /-- A map from `C` to `C`. An involution. -/
  τ : C → C
  /-- The condition that `τ` is an involution. -/
  τ_involution : Function.Involutive τ
  /-- The contraction of vectors with dual colors. -/
  contr : (c : C) → ((rep c).tprod (rep (τ c))).IntertwiningMap (Representation.trivial k G k)
  /-- The invariant unit tensor for a given color. -/
  unit : (c : C) → ((Representation.trivial k G k)).IntertwiningMap ((rep (τ c)).tprod (rep c))
  /-- Contraction is symmetric with respect to duals. -/
  contr_tmul_symm : ∀ c (x : V c) (y : V (τ c)),
      contr c (x ⊗ₜ[k] y) = contr (τ c) (y ⊗ₜ Equiv.cast (congrArg V (τ_involution c).symm) x)
  /-- The unit is symmetric. -/
  unit_symm : ∀ c, unit c (1 : k) =
      LinearMap.lTensor _ (LinearEquiv.cast (τ_involution c)).toLinearMap
      (TensorProduct.comm k _ _ (unit (τ c) (1 : k)))
  /-- Contraction with unit leaves invariant. -/
  contr_unit : ∀ c (x : V c),
    (TensorProduct.lid k _ <|
    (contr c).toLinearMap.rTensor _ <|
    (TensorProduct.assoc k (V c) (V (τ c)) (V c)).symm <|
    x ⊗ₜ[k] (unit c (1 : k))) = x

noncomputable section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} [Group G]
  {basisIdx : C → Type}

/-!

## Properties of the basis

-/
/-- The casting between `basisIdx c` and `basisIdx c1`. -/
def basisIdxCongr {c c1 : C} (h : c = c1) :
    basisIdx c ≃ basisIdx c1 := Equiv.cast (by simp [h])

@[simp]
lemma basisIdxCongr_rfl (c : C) (i : basisIdx c) :
    basisIdxCongr (Eq.refl c) i = i := rfl

lemma basisIdxCongr_symm {c c1 : C} (h : c = c1) (i : basisIdx c1) :
    (basisIdxCongr h).symm i = basisIdxCongr h.symm i := by
  subst h
  rfl

@[simp]
lemma basisIdxCongr_apply_apply {c c1 c2 : C} (h1 : c = c1) (h2 : c1 = c2) (i : basisIdx c) :
    basisIdxCongr h2 (basisIdxCongr h1 i) = basisIdxCongr (by simp [h1, h2]) i := by
  simp [basisIdxCongr]

/-- `basisIdxCongr` only depends on its endpoints up to `HEq` of the arguments: equal target
colours and heterogeneously equal labels give equal casts. -/
lemma basisIdxCongr_heq_arg {c1 c2 d : C} (h1 : c1 = d) (h2 : c2 = d)
    {x : basisIdx c1} {y : basisIdx c2} (hxy : HEq x y) :
    basisIdxCongr h1 x = basisIdxCongr h2 y := by
  subst h1; subst h2; cases hxy; rfl

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {basis : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep basis)

@[simp]
lemma τ_τ_apply (c : C) : S.τ (S.τ c) = c := S.τ_involution c

omit [(c : C) → Fintype (basisIdx c)] [(c : C) → DecidableEq (basisIdx c)] in
lemma basis_congr {c c1 : C} (h : c = c1) (i : basisIdx c) :
    basis c i = LinearEquiv.cast (R := k) h.symm (basis c1 (basisIdxCongr h i)) := by
  subst h
  simp

omit [(c : C) → Fintype (basisIdx c)] [(c : C) → DecidableEq (basisIdx c)] in
lemma map_basis_eq {c c1 : C} (h : c = c1) (i : basisIdx c) :
    LinearEquiv.cast (R := k) h (basis c i) = basis c1 (basisIdxCongr h i) := by
  subst h
  simp

omit [(c : C) → Fintype (basisIdx c)] [(c : C) → DecidableEq (basisIdx c)] in
/-- `map_basis_eq` with the cast spelled `Equiv.cast`, the form `contr_tmul_symm` applies to its
  first vector. -/
lemma equivCast_basis {c c1 : C} (h : c = c1) (i : basisIdx c) :
    Equiv.cast (congrArg V h) (basis c i) = basis c1 (basisIdxCongr h i) :=
  map_basis_eq h i

set_option linter.unusedVariables false in
/-- The number of indices `n` from a tensor. -/
@[nolint unusedArguments]
def numIndices {S : TensorSpecies k C G V basisIdx rep basis} {n : ℕ} {c : Fin n → C}
    (_ : PiTensorProduct k (fun i => V (c i))) : ℕ := n

/-!

## Metric

-/

/-- Instance of a metric on a tensor species. For each color `c` an invariant tensor
  in `V c ⊗ V c`, whose contraction against the metric of the dual color `τ c` is the unit.
  Not every species has one: it requires every color to be self-dual,
  which fails for the fundamental of `SU(N)`, `3 ≤ N`. -/
class WithMetric {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {basis : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep basis) where
  /-- The invariant metric tensor for a given color. -/
  metric : (c : C) → ((Representation.trivial k G k)).IntertwiningMap ((rep c).tprod (rep c))
  /-- On contracting metrics we get the unit. -/
  contr_metric : ∀ c,
    (TensorProduct.comm k _ _ <|
      (TensorProduct.lid k _).lTensor _ <|
      ((S.contr c).toLinearMap.rTensor (V (S.τ c))).lTensor (V c) <|
      (TensorProduct.assoc k (V c) (V (S.τ c)) (V (S.τ c))).symm.toLinearMap.lTensor (V c) <|
      TensorProduct.assoc k (V c) (V c) (V (S.τ c) ⊗[k] V (S.τ c)) <|
      (metric c 1) ⊗ₜ[k] (metric (S.τ c) 1)) = S.unit c (1 : k)

/-- The metric of a species with a metric, at the color `c`. -/
abbrev metric [S.WithMetric] (c : C) :
    ((Representation.trivial k G k)).IntertwiningMap ((rep c).tprod (rep c)) :=
  WithMetric.metric (S := S) c

/-- On contracting metrics we get the unit. -/
lemma contr_metric [S.WithMetric] (c : C) :
    (TensorProduct.comm k _ _ <|
      (TensorProduct.lid k _).lTensor _ <|
      ((S.contr c).toLinearMap.rTensor (V (S.τ c))).lTensor (V c) <|
      (TensorProduct.assoc k (V c) (V (S.τ c)) (V (S.τ c))).symm.toLinearMap.lTensor (V c) <|
      TensorProduct.assoc k (V c) (V c) (V (S.τ c) ⊗[k] V (S.τ c)) <|
      (S.metric c 1) ⊗ₜ[k] (S.metric (S.τ c) 1)) = S.unit c (1 : k) :=
  WithMetric.contr_metric c

end TensorSpecies

end
