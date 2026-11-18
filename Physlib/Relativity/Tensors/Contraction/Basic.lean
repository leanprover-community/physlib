/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Pure
/-!

# Contractions on tensors

## i. Overview

This file defines tensor contraction for an arbitrary `TensorSpecies`.

The colors of a tensor record the type of each index. A pair of positions can be
contracted when their colors are dual, expressed by a proof
`S.τ (c i) = c j`, where `S.τ` is the color involution in the tensor species.
For a tensor with colors `c : Fin (n + 1 + 1) → C`, contraction at positions
`i` and `j` produces a tensor with two fewer indices and colors
`c ∘ Fin.succSuccAbove i j`.

The construction is first made on pure tensors in
`Physlib.Relativity.Tensors.Contraction.Pure`. There, `Pure.dropPair` removes the
two contracted factors from the remaining pure tensor, `Pure.contrPCoeff`
computes the scalar contraction of the two removed factors using `S.contr`, and
`Pure.contrP` multiplies that scalar by the dropped tensor. This file extends the
operation linearly to arbitrary tensors via `contrT`.

## ii. Key results

- `TensorSpecies.Tensor.contrT` is the linear contraction map on tensors.
- `TensorSpecies.Tensor.contrT_pure` identifies `contrT` on pure tensors with
  `Pure.contrP`.
- `TensorSpecies.Tensor.contrT_equivariant` says contraction commutes with the
  symmetry-group action.
- `TensorSpecies.Tensor.contrT_permT`, `TensorSpecies.Tensor.contrT_symm`, and
  `TensorSpecies.Tensor.contrT_comm` describe the interaction of contraction with
  reindexing, swapping the contracted pair, and performing two contractions.

## iii. Related files

- `Physlib.Relativity.Tensors.Contraction.SuccSuccAbove` contains the finite-index
  maps used to drop two positions.
- `Physlib.Relativity.Tensors.Contraction.Pure` defines `Pure.dropPair`,
  `Pure.contrPCoeff`, `Pure.contrP`, and the multilinear map used to define
  `contrT`.
- `Physlib.Relativity.Tensors.Contraction.Products` proves compatibility between
  contractions and tensor products.

## iv. Table of contents

- A. Tensor contraction

## v. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace TensorSpecies
open Module

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor
open Fin
/-!

## A. Tensor contraction

-/

open _root_.TensorSpecies.Tensor.Pure

lemma contrT_decide {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (hx : S.τ (c i) = c j) (hij : i ≠ j := by decide) :
    i ≠ j ∧ S.τ (c i) = c j := by
  apply And.intro hij hx

/-- For `c : Fin (n + 1 + 1) → C`, `i j : Fin (n + 1 + 1)` with dual color, and a tensor
  `t : Tensor S c`, `contrT i j _ t` is the tensor
  formed by contracting the `i`th index of `t`
  with the `j`th index. -/
noncomputable def contrT (n : ℕ) {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
      (hij : i ≠ j ∧ S.τ (c i) = c j) :
    Tensor S c →ₗ[k] Tensor S (c ∘ succSuccAbove i j) :=
  PiTensorProduct.lift
    { toFun p := Pure.contrP i j hij p
      map_update_add' p m x y := by
        change (Pure.update p m (x + y)).contrP i j hij = _
        simp only [Pure.contrP_update_add]
        rfl
      map_update_smul' p k r y := by
        change (Pure.update p k (r • y)).contrP i j hij = _
        rw [Pure.contrP_update_smul]
        rfl }

lemma contrT_congr {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j}
    (i' j' : Fin (n + 1 + 1)) (t : S.Tensor c)
    (hii' : i = i' := by decide)
    (hjj' : j = j' := by decide) :
    contrT n i j hij t = permT id (And.intro (Function.bijective_id) (by subst hii' hjj'; simp))
      (contrT n i' j' (by subst hii' hjj'; exact hij) t) := by
  subst hii' hjj'
  simp

@[simp]
lemma contrT_pure {n : ℕ} {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) :
    contrT n i j hij p.toTensor = p.contrP i j hij :=
  PiTensorProduct.lift.tprod p

@[simp]
lemma contrT_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (g : G)
    (t : Tensor S c) :
    contrT n i j hij (g • t) = g • contrT n i j hij t := by
  let P (t : Tensor S c) : Prop := contrT n i j hij (g • t) = g • contrT n i j hij t
  change P t
  apply induction_on_pure
  · intro p
    simp only [contrT_pure, P]
    rw [actionT_pure, contrT_pure]
    simp only [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_smul]
    congr 1
    exact Eq.symm actionT_pure
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr]

lemma contrT_permT {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j ∧ S.τ (c1 i) = (c1 j))
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1))
    (hσ : IsReindexing c c1 σ) (t : Tensor S c) :
    contrT n1 i j hij (permT σ hσ t) = permT _ (hσ.succSuccAbove i j hij.1)
      (contrT n (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t) := by
  let P (t : Tensor S c) : Prop := contrT n1 i j hij (permT σ hσ t) =
      permT _ (hσ.succSuccAbove i j hij.1)
        (contrT n (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t)
  change P t
  apply induction_on_pure
  · intro p
    simp only [contrT_pure, P]
    rw [permT_pure, contrT_pure]
    simp only [contrP, contrPCoeff_permP, dropPair_permP, map_smul]
    congr
    rw [permT_pure]
  · intro r t ht
    simp_all [P]
  · intro t1 t2 ht1 ht2
    simp_all [P]

lemma contrT_symm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j} (t : Tensor S c) :
    contrT n i j hij t = permT id (by simp)
      (contrT n j i ⟨hij.1.symm, by simp [← hij.2]⟩ t) := by
  let P (t : Tensor S c) : Prop := contrT n i j hij t = permT id (by simp)
      (contrT n j i ⟨hij.1.symm, by simp [← hij.2]⟩ t)
  change P t
  apply induction_on_pure
  · intro p
    simp only [contrT_pure, P]
    rw [contrP_symm]
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr]

lemma contrT_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ S.τ (c i1) = (c j1))
    (hij2 : i2 ≠ j2 ∧ S.τ (c (succSuccAbove i1 j1 i2)) = (c (succSuccAbove i1 j1 j2)))
    (t : Tensor S c) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    contrT n i2 j2 hij2 (contrT (n + 1 + 1) i1 j1 hij1 t) =
    permT id (IsReindexing.succSuccAbove_comm i1 j1 i2 j2 hij1.left hij2.left)
      (contrT n i1' j1' (by simp [i1', j1', i2', j2', hij1])
      (contrT (n + 1 + 1) i2' j2' (by simp [i2', j2', hij2]) t)) := by
  let i2' := (succSuccAbove i1 j1 i2);
  let j2' := (succSuccAbove i1 j1 j2);
  let i1' := (predPredAbove i2' j2' (by simp [i2', j2', hij2]) i1
    (by simp [i2', j2']));
  let j1' := (predPredAbove i2' j2' (by simp [i2', j2', hij2]) j1
    (by simp [i2', j2']));
  let P (t : Tensor S c) : Prop := contrT n i2 j2 hij2 (contrT (n + 1 + 1) i1 j1 hij1 t) =
      permT id (IsReindexing.succSuccAbove_comm i1 j1 i2 j2 hij1.left hij2.left)
        (contrT n i1' j1' (by simp [i1', j1', i2', j2', hij1])
        (contrT (n + 1 + 1) i2' j2' (by simp [i2', j2', hij2]) t))
  change P t
  apply induction_on_pure
  · intro p
    dsimp only [P]
    conv_lhs => enter [2]; rw [contrT_pure, contrP]
    conv_lhs => rw [map_smul, contrT_pure, contrP, smul_smul]
    conv_rhs => enter [2, 2]; rw [contrT_pure, contrP]
    conv_rhs => enter [2]; rw [map_smul]
    conv_rhs => rw [map_smul]
    conv_rhs => enter [2, 2]; rw [contrT_pure, contrP]
    conv_rhs => enter [2]; rw [map_smul, permT_pure]
    conv_rhs => rw [smul_smul]
    congr 1
    · exact contrPCoeff_mul_dropPair i1 j1 i2 j2 hij1 hij2 p
    · congr 1
      rw [dropPair_comm]
  · intro p q hp
    dsimp only [P] at hp ⊢
    conv_lhs => rw [map_smul, map_smul, hp]
    conv_rhs => enter [2, 2]; rw [map_smul]
    conv_rhs => enter [2]; rw [map_smul]
    conv_rhs => rw [map_smul]
  · intro p r hp hr
    dsimp only [P] at hp hr ⊢
    conv_lhs => rw [map_add, map_add, hp]
    conv_lhs => enter [2]; rw [hr]
    conv_rhs => enter [2, 2]; rw [map_add]
    conv_rhs => enter [2]; rw [map_add]
    conv_rhs => rw [map_add]

end Tensor

end TensorSpecies
