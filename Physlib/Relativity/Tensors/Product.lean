/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
public import Physlib.Relativity.Tensors.ComponentIdx.Product
/-!

# The product of tensors

## i. Overview

In this module we define the tensor product of
- index components of tensors,
- pure tensors, and
- tensors.
We prove a number of properties about these products, for example,
permutation of the factors, equivariance, and associativity.

## ii. Key results

- `Pure.prodP` : The tensor product of two pure tensors.
- `prodT` : The tensor product of two tensors.

The following results exist for both `prodP` and `prodT` :
- `prodT_swap` : Swapping the order of the product of two tensors.
- `prodT_permT_left` : Permuting the indices of the left tensor commute with the product.
- `prodT_permT_right` : Permuting the indices of the right tensor commute with the product.
- `prodT_equivariant` : The product of two tensors is equivariant.
- `prodT_assoc` : The product of three tensors is associative.
- `prodT_assoc'` : The product of three tensors is associative in the other direction.

## iii. Table of contents

- A. Products of index components
  - A.1. The product of component indices as an equivalence
- B. Products of pure tensors
  - B.1. Indexing pure tensors by `Fin n1 ⊕ Fin n2` rather than `Fin (n1 + n2)`
  - B.2. The product of two pure tensors
  - B.3. The vectors making up product of two pure tensors
  - B.4. The product of two pure basis vectors
  - B.5. The basis components of the product of two pure tensors
  - B.6. Equivariance of the product of two pure tensors
  - B.7. Product with a tensor with no indices on the right
  - B.8. Swapping the order of the product of two pure tensors
  - B.9. Permuting the indices of the left tensor in a product
  - B.10. Permuting the indices of the right tensor in a product
  - B.11. Associativity of the product of three pure tensors in one direction
  - B.12. Associativity of the product of three pure tensors in the other direction
- C. Products of tensors
  - C.1. Indexing tensors by `Fin n1 ⊕ Fin n2` rather than `Fin (n1 + n2)`
  - C.2. The product of two tensors
  - C.3. The product of two pure tensors as a tensor
  - C.4. The product of basis vectors
  - C.5. The product as an equivalence
  - C.6. Rewriting the basis for the product in terms of the tensor product basis
  - C.7. Equivariance of the product of two tensors
  - C.8. The product with the default tensor with no indices on the right
  - C.9. Swapping the order of the product of two tensors
  - C.10. Permuting the indices of the left tensor in a product
  - C.11. Permuting the indices of the right tensor in a product
  - C.12. Associativity of the product of three tensors in one direction
  - C.13. Associativity of the product of three tensors in the other direction

## iv. References

* Tooby-Smith, Formalization of physics index notation in Lean 4, arXiv:2411.07667.
  [ref: tooby_smith_2024_index_notation]
-/

@[expose] public section

namespace TensorSpecies

namespace Tensor
open Module

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b} {n n' n2 : ℕ} {c : Fin n → C} {c' : Fin n' → C}
    {c2 : Fin n2 → C}

/-!

## B. Products of pure tensors

-/

/-!

### B.1. Indexing pure tensors by `Fin n1 ⊕ Fin n2` rather than `Fin (n1 + n2)`

-/

/-!

### B.2. The product of two pure tensors

-/

/-- Given two pure tensors `p1 : Pure S c` and `p2 : Pure S c`, `prodP p p2` is the tensor
  product of those tensors returning an element in
  `Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)`. -/
def Pure.prodP {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) : Pure S (Fin.append c c1) :=
  Fin.addCases (fun i => LinearEquiv.cast (R := k) (by simp) (p1 i))
  (fun i => LinearEquiv.cast (R := k) (by simp) (p2 i))

/-!

### B.3. The vectors making up product of two pure tensors

-/

@[simp]
lemma Pure.prodP_apply_castAdd {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1) :
    Pure.prodP p1 p2 (Fin.castAdd n2 i) =
    LinearEquiv.cast (R := k) (by simp) (p1 i) := by
  simp [Pure.prodP]

@[simp]
lemma Pure.prodP_apply_natAdd {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) :
    Pure.prodP p1 p2 (Fin.natAdd n1 i) =
    LinearEquiv.cast (R := k) (by simp) (p2 i) := by
  simp [Pure.prodP]

lemma Pure.prodP_apply_finSumFinEquiv {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1 ⊕ Fin n2) :
    Pure.prodP p1 p2 (finSumFinEquiv i) =
    match i with
    | Sum.inl i => LinearEquiv.cast (R := k) (by simp) (p1 i)
    | Sum.inr i => LinearEquiv.cast (R := k) (by simp) (p2 i) := by
  rw [Pure.prodP]
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, LinearEquiv.cast_apply, Fin.addCases_left]
    rfl
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, LinearEquiv.cast_apply, Fin.addCases_right]
    rfl

/-!

### B.4. The product of two pure basis vectors

-/

lemma Pure.prodP_basisVector {n n1 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C}
    (φ : ComponentIdx c) (φ1 : ComponentIdx (S := S) c1) :
    Pure.prodP (Pure.basisVector c φ) (Pure.basisVector c1 φ1) =
    Pure.basisVector _ (ComponentIdx.prod.symm (φ, φ1)) := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro i
    symm
    simp only [basisVector, ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.addCases_left,
      LinearEquiv.cast_apply]
    rw [basis_congr (c1 := (c i)) (by simp)]
    simp
  · intro i
    symm
    simp only [basisVector, ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.addCases_right,
      LinearEquiv.cast_apply]
    rw [basis_congr (c1 := (c1 i)) (by simp)]
    simp
/-!

### B.5. The basis components of the product of two pure tensors

-/

lemma Pure.prodP_component {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (p : Pure S c) (p1 : Pure S c1)
    (φ : ComponentIdx (Fin.append c c1)) :
    (p.prodP p1).component φ = p.component (ComponentIdx.prod φ).1 *
    p1.component (ComponentIdx.prod φ).2 := by
  simp [component]
  rw [← finSumFinEquiv.prod_comp]
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Fintype.prod_sum_type]
  congr
  · funext x
    simp only [prodP_apply_castAdd, LinearEquiv.cast_apply, ComponentIdx.prod, Equiv.coe_fn_mk]
    generalize_proofs h1 h2 h3
    generalize p x = p'
    generalize c x = c' at *
    subst h3
    rfl
  · funext x
    simp only [prodP_apply_natAdd, LinearEquiv.cast_apply, ComponentIdx.prod, Equiv.coe_fn_mk]
    generalize_proofs h1 h2 h3
    generalize p1 x = p1'
    generalize c1 x = c1' at *
    subst h3
    rfl

/-!

### B.6. Equivariance of the product of two pure tensors

-/

@[simp]
lemma Pure.prodP_equivariant {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (g : G) (p : Pure S c) (p1 : Pure S c1) :
    prodP (g • p) (g • p1) = g • prodP p p1 := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [actionP_eq, prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro j
    generalize_proofs h1 h2
    generalize p j = p'
    generalize c j = c' at *
    subst h2
    rfl
  · intro j
    generalize_proofs h1 h2
    generalize p1 j = p1'
    generalize c1 j = c1' at *
    subst h2
    rfl

/-!

### B.7. Product with a tensor with no indices on the right

-/


lemma Pure.prodP_zero_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} (p : Pure S c) (p0 : Pure S c1) :
    prodP p p0 = permP id IsReindexing.append_zero_right p := by
  ext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rw (transparency := .instances) [prodP_apply_finSumFinEquiv]
  match j with
  | Sum.inl j => rfl
  | Sum.inr j => exact Fin.elim0 j

/-!

### B.8. Swapping the order of the product of two pure tensors

-/

lemma Pure.prodP_swap {n n1} {c : Fin n → C} {c1 : Fin n1 → C} (p : Pure S c) (p1 : Pure S c1) :
    Pure.prodP p p1 = permP _ IsReindexing.append_swap (Pure.prodP p1 p) := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h0 : (i.castAdd n1).append (Fin.natAdd n1) (Fin.castAdd n) = i.natAdd n1 := by simp
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : (i.natAdd n).append (Fin.natAdd n1) (Fin.castAdd n) = i.castAdd n := by simp
    simp [permP, ← congr_right _ _ _ h0]

/-!

### B.9. Permuting the indices of the left tensor in a product

-/

@[simp]
lemma Pure.prodP_permP_left {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : IsReindexing c c' σ) (p : Pure S c) (p2 : Pure S c2) :
    Pure.prodP (permP σ h p) p2 = permP _ (h.append_congr_left c2) (Pure.prodP p p2) := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h0 : (i.castAdd n2).append (Fin.castAdd n2 ∘ σ) (Fin.natAdd n) = (σ i).castAdd n2 := by
      simp
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : (i.natAdd n').append (Fin.castAdd n2 ∘ σ) (Fin.natAdd n) = i.natAdd n := by simp
    simp [permP,  ← congr_right _ _ _ h0]

/-!

### B.10. Permuting the indices of the right tensor in a product

-/

@[simp]
lemma Pure.prodP_permP_right {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : IsReindexing c c' σ) (p : Pure S c) (p2 : Pure S c2) :
    prodP p2 (permP σ h p) = permP _ (h.append_congr_right c2) (Pure.prodP p2 p) := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h0 : (i.castAdd n').append (Fin.castAdd n) (Fin.natAdd n2 ∘ σ) = i.castAdd n := by simp
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : (i.natAdd n2).append (Fin.castAdd n) (Fin.natAdd n2 ∘ σ) = (σ i).natAdd n2 := by simp
    simp [permP,  ← congr_right _ _ _ h0]

/-!

### B.11. Associativity of the product of three pure tensors in one direction

-/

lemma Pure.prodP_assoc {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C}
    (p : Pure S c) (p1 : Pure S c1) (p2 : Pure S c2) :
    prodP (prodP p p1) p2 =
    permP _ IsReindexing.append_assoc_right (prodP p (prodP p1 p2)) := by
  ext i
  refine Fin.addCases (fun i => Fin.addCases (fun i => ?_) (fun i => ?_) i) (fun i => ?_) i
  · have h0 : (i.natAdd (n + n1)).cast (by grind) = (i.natAdd n1).natAdd n := by grind
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : ((i.castAdd n1).castAdd n2).cast (by grind) = i.castAdd (n1 + n2) := by grind
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : ((i.natAdd n).castAdd n2).cast (by grind) = (i.castAdd n2).natAdd n := by grind
    simp [permP, ← congr_right _ _ _ h0]

/-!

### B.12. Associativity of the product of three pure tensors in the other direction

-/

lemma Pure.prodP_assoc' {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C}
    (p : Pure S c) (p1 : Pure S c1) (p2 : Pure S c2) :
    prodP p (prodP p1 p2) = permP _ IsReindexing.append_assoc_left (prodP (prodP p p1) p2) := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => Fin.addCases (fun i => ?_) (fun i => ?_) i) i
  · have h0 : (i.castAdd (n1 + n2)).cast (by grind) = (i.castAdd n1).castAdd n2 := by grind
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : ((i.castAdd n2).natAdd n).cast (by grind) = (i.natAdd n).castAdd n2 := by grind
    simp [permP, ← congr_right _ _ _ h0]
  · have h0 : ((i.natAdd n1).natAdd n).cast (by grind) = i.natAdd (n + n1) := by grind
    simp [permP, ← congr_right _ _ _ h0]

/-!

### B.13. Linearity of the product

-/

attribute [-simp] LinearEquiv.cast_apply

@[simp]
lemma Pure.prodP_update_left {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1) (x : V (c i)) :
    Pure.prodP (Pure.update p1 i x) p2
    = Pure.update (Pure.prodP p1 p2) (Fin.castAdd n2 i)
      (LinearEquiv.cast (R := k) (by simp) x) := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro j
    generalize_proofs h1 h2 h3
    by_cases h : j = i
    · subst h
      simp
    · rw [update_diff _ _ _ _ (by grind), update_diff _ _ _ _ (by simp; grind)]
      simp
  · intro j
    generalize_proofs h1 h2 h3
    rw [update_diff]
    · simp
    · simp [Fin.ext_iff]
      grind

@[simp]
lemma Pure.prodP_update_right {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) (x : V (c1 i)) :
    Pure.prodP p1 (Pure.update p2 i x)
    = Pure.update (Pure.prodP p1 p2) (Fin.natAdd n1 i)
      (LinearEquiv.cast (R := k) (by simp) x) := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro j
    generalize_proofs h1 h2 h3
    rw [update_diff]
    · simp
    · simp [Fin.ext_iff]
      grind
  · intro j
    generalize_proofs h1 h2 h3
    by_cases h : j = i
    · subst h
      simp
    · rw [update_diff _ _ _ _ (by grind), update_diff _ _ _ _ (by simp; grind)]
      simp

lemma Pure.prodP_update_add_toTensor_left {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) (x y : V (c1 i)) :
    (Pure.prodP p1 (Pure.update p2 i (x + y))).toTensor
    = (Pure.prodP p1 (Pure.update p2 i x)).toTensor
    + (Pure.prodP p1 (Pure.update p2 i y)).toTensor := by simp
/-!

## C. Products of tensors

-/

/-!

### C.2. The product of two tensors

-/
open TensorProduct
/-- The tensor product of two tensors as a bi-linear map from
  `S.Tensor c` and `S.Tensor c1` to `S.Tensor (Fin.append c c1)`. -/
noncomputable def prodT {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C} :
    S.Tensor c →ₗ[k] S.Tensor c1 →ₗ[k] S.Tensor (Fin.append c c1) := by
  refine PiTensorProduct.lift (MultilinearMap.mk' (fun p1 => PiTensorProduct.lift
    (MultilinearMap.mk' (fun p2 => (Pure.prodP p1 p2).toTensor) ?_ ?_)) ?_ ?_)
  · intro p2 i x y
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp
  · intro p2 i r p2'
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp
  · intro p1 i x y
    ext p2
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp
  · intro p1 i r p1'
    ext p2
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp

/-!

### C.3. The product of two pure tensors as a tensor

-/

lemma prodT_pure {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (t : Pure S c) (t1 : Pure S c1) :
    (t.toTensor).prodT (t1.toTensor) = (Pure.prodP t t1).toTensor := by
  simp [prodT, Pure.toTensor]

/-!

### C.4. The product of basis vectors

-/

open TensorProduct

lemma prodT_basis {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (b : ComponentIdx c) (b1 : ComponentIdx (S := S) c1) :
    (basis c b).prodT (basis c1 b1) =
    (Pure.basisVector _ (ComponentIdx.prod.symm (b, b1))).toTensor := by
  rw [basis_apply, basis_apply, prodT_pure, Pure.prodP_basisVector]

lemma prodT_basis' {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (b : ComponentIdx c) (b1 : ComponentIdx (S := S) c1) :
    (basis c b).prodT (basis c1 b1) =
    basis (Fin.append c c1) (ComponentIdx.prod.symm (b, b1)) := by
  rw [prodT_basis]
  simp [basis_apply]
/-!

### C.5. The product as an equivalence

-/

set_option synthInstance.maxHeartbeats 0 in
/-- The linear equivalence between `S.Tensor c ⊗[k] S.Tensor c1` and
    `S.Tensor (Fin.append c c1)`. -/
noncomputable def tensorEquivProd {n n2 : ℕ} {c : Fin n → C} {c1 : Fin n2 → C} :
    S.Tensor c ⊗[k] S.Tensor c1 ≃ₗ[k] S.Tensor (Fin.append c c1) where
  toLinearMap := TensorProduct.lift prodT
  invFun := (Tensor.basis (Fin.append c c1)).constr k (fun b =>
    (Tensor.basis c) (ComponentIdx.prod b).1 ⊗ₜ[k]
    (Tensor.basis c1) (ComponentIdx.prod b).2)
  left_inv x := by
    let f : S.Tensor (Fin.append c c1) →ₗ[k]
      S.Tensor c ⊗[k] S.Tensor c1 :=
      (Tensor.basis (Fin.append c c1)).constr k (fun b =>
        (Tensor.basis c) (ComponentIdx.prod b).1 ⊗ₜ[k]
        (Tensor.basis c1) (ComponentIdx.prod b).2)
    let P (x : S.Tensor c ⊗[k] S.Tensor c1) := f (TensorProduct.lift prodT x) = x
    change P x
    apply TensorProduct.inductionOn
    · intro t1 t2
      apply induction_on_basis (t := t1)
      · intro b1
        · apply induction_on_basis (t := t2)
          intro b2
          dsimp [P]
          rw [prodT_basis]
          simp [f]
          · simp [P]
          · intro r t h
            simp [tmul_smul, P] at *
            rw [h]
          · intro t1 t2 h1 h2
            simp [tmul_add, P] at *
            rw [h1, h2]
      · simp [P]
      · intro r t h
        simp [smul_tmul, P] at *
        rw [h]
      · intro t1 t2 h1 h2
        simp [add_tmul, P] at *
        rw [h1, h2]
    · intro x y h1 h2
      simp [P] at *
      rw [h1, h2]
  right_inv x := by
    simp only [Basis.constr_apply_fintype, Basis.equivFun_apply, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, map_sum, map_smul, lift.tmul]
    conv_rhs => rw [← (basis (Fin.append c c1)).sum_repr x]
    congr
    funext φ
    congr 1
    simp only [prodT_basis, Prod.mk.eta, Equiv.symm_apply_apply]
    exact (basis_apply (Fin.append c c1) φ).symm

/-!

### C.6. Rewriting the basis for the product in terms of the tensor product basis

-/

/-- Rewriting basis for the product in terms of the tensor product basis. -/
lemma basis_prod_eq {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C} :
    basis (S := S) (Fin.append c c1) =
    (((Tensor.basis (S := S) c).tensorProduct (Tensor.basis (S := S) c1)).reindex
    (ComponentIdx.prod.symm)).map tensorEquivProd := by
  ext b
  simp [ComponentIdx.prod, tensorEquivProd]
  rw [prodT_basis]
  rw [← basis_apply]
  congr
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;> simp [ComponentIdx.prod]

lemma prodT_basis_repr_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (t : Tensor S c) (t1 : Tensor S c1)
    (b : ComponentIdx (Fin.append c c1)) :
    (basis (Fin.append c c1)).repr (prodT t t1) b =
    (basis c).repr t (ComponentIdx.prod b).1 *
    (basis c1).repr t1 (ComponentIdx.prod b).2 := by
  apply induction_on_pure (t := t)
  · apply induction_on_pure (t := t1)
    · intro p p1
      simp only [prodT_pure, basis_repr_pure, Pure.prodP_component]
    · intro r t hp p
      simp only [basis_repr_pure, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hp ⊢
      rw [hp]
      ring
    · intro t1 t2 hp1 hp2 p
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, hp1, basis_repr_pure, hp2]
      ring_nf
  · intro r t hp
    simp only [map_smul, LinearMap.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hp ⊢
    rw [hp]
    ring
  · intro t1 t2 hp1 hp2
    simp only [map_add, LinearMap.add_apply, Finsupp.coe_add, Pi.add_apply, hp1, hp2]
    ring_nf
/-!

### C.7. Equivariance of the product of two tensors

-/

@[simp]
lemma prodT_equivariant {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (g : G) (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT (g • t) (g • t1) = g • prodT t t1 := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · induction' t1 using induction_on_pure with q r t ht t1 t2 ht1 ht2
    · simp [prodT_pure, actionT_pure]
    · simp [actionT_smul, map_smul, ht]
    · simp [map_add, ht1, ht2]
  · simp [actionT_smul, map_smul, ht]
  · simp [map_add, ht1, ht2]

/-!

### C.8. The product with the default tensor with no indices on the right

-/

lemma prodT_default_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} (t : S.Tensor c) :
    prodT t (Pure.toTensor default : S.Tensor c1) =
    permT id (IsReindexing.append_zero_right) t := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · simp only [Nat.add_zero]
    rw (transparency := .instances) [prodT_pure]
    rw [Pure.prodP_zero_right, permT_pure]
  · simp [map_smul, ht]
  · simp [map_add, ht1, ht2]

lemma prodT_zero_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT t t1 = (toField t1) • permT id (IsReindexing.append_zero_right) t := by
  conv_lhs => rw [Tensor.eq_smul_toField t1]
  rw [map_smul]
  congr 1
  convert prodT_default_right _
  simp only [basis_apply]
  congr
  exact Unique.eq_default (Pure.basisVector c1 default)

/-!

### C.9. Swapping the order of the product of two tensors

-/

lemma prodT_swap {n n1} {c : Fin n → C} {c1 : Fin n1 → C} (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT t t1 = permT _ IsReindexing.append_swap (prodT t1 t) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · induction' t1 using induction_on_pure with q r t ht t1 t2 ht1 ht2
    · simp [prodT_pure, permT_pure, Pure.prodP_swap p q]
    · simp [map_smul, ht]
    · simp [map_add, ht1, ht2]
  · simp [ht]
  · simp [ht1, ht2]

/-!

### C.10. Permuting the indices of the left tensor in a product

-/

@[simp]
lemma prodT_permT_left {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : IsReindexing c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT (permT σ h t) t2 = permT _ (h.append_congr_left c2) (prodT t t2) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · induction' t2 using induction_on_pure with q r t ht t1 t2 ht1 ht2
    · simp [prodT_pure, permT_pure]
    · simp only [map_smul, ht]
    · simp only [map_add, ht1, ht2]
  · simp [ht]
  · simp [ht1, ht2]

/-!

### C.11. Permuting the indices of the right tensor in a product

-/

@[simp]
lemma prodT_permT_right {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : IsReindexing c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT t2 (permT σ h t) = permT _ (h.append_congr_right c2) (prodT t2 t) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · induction' t2 using induction_on_pure with q r t ht t1 t2 ht1 ht2
    · simp [prodT_pure, permT_pure]
    · simp [map_smul, ht]
    · simp [map_add, ht1, ht2]
  · simp [ht]
  · simp [ht1, ht2]

/-!

### C.12. Associativity of the product of three tensors in one direction

-/

lemma prodT_assoc {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C} (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) :
    prodT (prodT t t1) t2 = permT _ IsReindexing.append_assoc_right (prodT t (prodT t1 t2)) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · induction' t1 using induction_on_pure with q r t ht t1 t2 ht1 ht2
    · induction' t2 using induction_on_pure with q r t ht t1 t2 ht1 ht2
      · simp [prodT_pure, permT_pure, Pure.prodP_assoc]
      · simp [ht]
      · simp [ht1, ht2]
    · simp [ht]
    · simp [ht1, ht2]
  · simp [ht]
  · simp [ht1, ht2]

/-!

### C.13. Associativity of the product of three tensors in the other direction

-/

lemma prodT_assoc' {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C} (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) :
    prodT t (prodT t1 t2) = permT _ IsReindexing.append_assoc_left (prodT (prodT t t1) t2) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · induction' t1 using induction_on_pure with q r t ht t1 t2 ht1 ht2
    · induction' t2 using induction_on_pure with q r t ht t1 t2 ht1 ht2
      · simp [prodT_pure, permT_pure, Pure.prodP_assoc']
      · simp [ht]
      · simp [ht1, ht2]
    · simp [ht]
    · simp [ht1, ht2]
  · simp [ht]
  · simp [ht1, ht2]

open TensorProduct

end Tensor

end TensorSpecies
