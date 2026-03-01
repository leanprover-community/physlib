/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Basic
/-!

# Evaluation of tensor indices

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

namespace Tensor

namespace Pure

variable {n : ℕ} {c : Fin (n + 1) → C}

/-!

## The evaluation coefficient.

-/

/-- Given a `i : Fin (n + 1)`, a `b : Fin (S.repDim (c i))` and a pure tensor
  `p : Pure S c`, `evalPCoeff i b p` is the `b`th component of `p i`. -/
noncomputable def evalPCoeff (i : Fin (n + 1)) (b : Fin (S.repDim (c i))) (p : Pure S c) : k :=
  (S.basis (c i)).repr (p i) b

@[simp]
lemma evalPCoeff_update_self (i : Fin (n + 1)) [inst : DecidableEq (Fin (n + 1))]
    (b : Fin (S.repDim (c i))) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c i))) :
    evalPCoeff i b (p.update i x) = (S.basis (c i)).repr x b := by
  simp [evalPCoeff]

@[simp]
lemma evalPCoeff_update_succAbove (i : Fin (n + 1)) [inst : DecidableEq (Fin (n + 1))]
    (j : Fin n)
    (b : Fin (S.repDim (c i))) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c (i.succAbove j)))) :
    evalPCoeff i b (p.update (i.succAbove j) x) = evalPCoeff i b p := by
  simp [evalPCoeff]

/-!

## Evaluation for a pure tensor.

-/

/-- Given a `i : Fin (n + 1)`, a `b : Fin (S.repDim (c i))` and a pure tensor
  `p : Pure S c`, `evalP i b p` is the tensor formed by evaluating the `i`th index
  of `p` at `b`. -/
noncomputable def evalP (i : Fin (n + 1)) (b : Fin (S.repDim (c i))) (p : Pure S c) :
  Tensor S (c ∘ i.succAbove) := evalPCoeff i b p • (drop p i).toTensor

@[simp]
lemma evalP_update_add [inst : DecidableEq (Fin (n + 1))] (i j : Fin (n + 1))
    (b : Fin (S.repDim (c i))) (p : Pure S c)
    (x y: S.FD.obj (Discrete.mk (c j))) :
    evalP i b (p.update j (x + y)) =
    evalP i b (p.update j x) + evalP i b (p.update j y) := by
  simp only [evalP]
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [add_smul]
  · simp

@[simp]
lemma evalP_update_smul [inst : DecidableEq (Fin (n + 1))] (i j : Fin (n + 1))
    (b : Fin (S.repDim (c i))) (p : Pure S c)
    (r : k)
    (x : S.FD.obj (Discrete.mk (c j))) :
    evalP i b (p.update j (r • x)) =
    r • evalP i b (p.update j x) := by
  simp only [evalP]
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [smul_smul]
  · simp [smul_smul, mul_comm]

/-!

## Evaluation for a pure tensor as multilinear map.

-/

/-- The multi-linear map formed by evaluation of an index of pure tensors. -/
noncomputable def evalPMultilinear {n : ℕ} {c : Fin (n + 1)→ C}
    (i : Fin (n + 1)) (b : Fin (S.repDim (c i))) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i)))
      (S.Tensor (c ∘ i.succAbove)) where
  toFun p := evalP i b p
  map_update_add' p m x y := by
    change (update p m (x + y)).evalP i b = _
    simp only [evalP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).evalP i b = _
    rw [Pure.evalP_update_smul]
    rfl

end Pure

/-- Given a `i : Fin (n + 1)`, a `b : Fin (S.repDim (c i))` and a tensor
  `t : Tensor S c`, `evalT i b t` is the tensor formed by evaluating the `i`th index
  of `t` at `b`. -/
noncomputable def evalT {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
      (b : Fin (S.repDim (c i))) :
    Tensor S c →ₗ[k] Tensor S (c ∘ i.succAbove) :=
  PiTensorProduct.lift (Pure.evalPMultilinear i b)

@[simp]
lemma evalT_pure {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (b : Fin (S.repDim (c i))) (p : Pure S c) :
    evalT i b p.toTensor = Pure.evalP i b p := by
  simp only [evalT, Pure.toTensor]
  change _ = Pure.evalPMultilinear i b p
  conv_rhs => rw [← PiTensorProduct.lift.tprod]
  rfl

TODO "6VZ6G" "Add lemmas related to the interaction of evalT and permT, prodT and contrT."

end Tensor

end TensorSpecies
