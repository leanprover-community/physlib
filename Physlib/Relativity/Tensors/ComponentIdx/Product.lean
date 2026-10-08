/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Basic
/-!

# Products of component indices

## i. Overview

This file contains the component-index API induced by appending two lists of tensor colors.

The main construction identifies component indices for appended color lists with pairs
of component indices for each side of the append.

## ii. Key results

- `TensorSpecies.Tensor.ComponentIdx.prod` is the equivalence between
  `ComponentIdx (Fin.append c c1)` and `ComponentIdx c × ComponentIdx c1`.

## iii. Table of contents

- A. Product equivalence

## iv. References

* None.
-/

@[expose] public section

namespace TensorSpecies

variable {k C G : Type} [CommRing k] [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)}
  {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-!

## A. Product equivalence

-/

/-- The equivalence between `ComponentIdx (Fin.append c c1)` and
  `ComponentIdx c × ComponentIdx c1` formed by products. -/
def ComponentIdx.prod {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C} :
    ComponentIdx (S := S) (Fin.append c c1) ≃
      ComponentIdx (S := S) c × ComponentIdx (S := S) c1 where
  toFun p := (fun i => basisIdxCongr (by simp) (p (Fin.castAdd n2 i)),
    fun i => basisIdxCongr (by simp) (p (Fin.natAdd n1 i)))
  invFun p := Fin.addCases (fun i => basisIdxCongr (by simp) (p.1 i))
    (fun i => basisIdxCongr (by simp) (p.2 i))
  left_inv p := by
    ext1 i
    revert i
    simp [Fin.forall_fin_add]
  right_inv p := by simp

lemma ComponentIdx.prod_apply_fst {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p : ComponentIdx (S := S) (Fin.append c c1)) (i : Fin n1) :
    p.prod.1 i =
      basisIdxCongr (by simp) (p (Fin.castAdd n2 i)) := rfl

lemma ComponentIdx.prod_apply_snd {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p : ComponentIdx (S := S) (Fin.append c c1)) (i : Fin n2) :
    p.prod.2 i =
      basisIdxCongr (by simp) (p (Fin.natAdd n1 i)) := rfl

@[simp]
lemma ComponentIdx.prod_symm_natAdd {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p : ComponentIdx (S := S) c) (q : ComponentIdx (S := S) c1) (i : Fin n2) :
    ComponentIdx.prod.symm (p, q) (Fin.natAdd n1 i) =
      basisIdxCongr (by simp) (q i) := by simp [ComponentIdx.prod]

@[simp]
lemma ComponentIdx.prod_symm_castAdd {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p : ComponentIdx (S := S) c) (q : ComponentIdx (S := S) c1) (i : Fin n1) :
    ComponentIdx.prod.symm (p, q) (Fin.castAdd n2 i) =
      basisIdxCongr (by simp) (p i) := by simp [ComponentIdx.prod]

/-- `ComponentIdx.prod_symm_castAdd` at a slot only propositionally equal to `Fin.castAdd n2 a`,
  up to `HEq`. -/
lemma ComponentIdx.prod_symm_heq_castAdd {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p : ComponentIdx (S := S) c) (q : ComponentIdx (S := S) c1) {x : Fin (n1 + n2)} {a : Fin n1}
    (hx : x = Fin.castAdd n2 a) : ComponentIdx.prod.symm (p, q) x ≍ p a := by
  subst hx
  rw [ComponentIdx.prod_symm_castAdd]
  exact basisIdxCongr_heq _ _

/-- `ComponentIdx.prod_symm_natAdd` at a slot only propositionally equal to `Fin.natAdd n1 a`,
  up to `HEq`. -/
lemma ComponentIdx.prod_symm_heq_natAdd {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p : ComponentIdx (S := S) c) (q : ComponentIdx (S := S) c1) {x : Fin (n1 + n2)} {a : Fin n2}
    (hx : x = Fin.natAdd n1 a) : ComponentIdx.prod.symm (p, q) x ≍ q a := by
  subst hx
  rw [ComponentIdx.prod_symm_natAdd]
  exact basisIdxCongr_heq _ _

end Tensor
end TensorSpecies
