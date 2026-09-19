/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Products
/-!

# Constructors of tensors.

There are a number of ways to construct explicit tensors.
-/

@[expose] public section

open Module

namespace TensorSpecies

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}
attribute [-simp] LinearEquiv.cast_apply

namespace Tensor

/-!

## Tensors with a single index.

-/

/-- The equivalence between `V c` and `Pure S ![c]`. -/
noncomputable def Pure.fromSingleP {c : C} : V c ≃ₗ[k] Pure S ![c] where
  toFun x := fun | 0 => x
  invFun x := x 0
  map_add' x y := by
    ext i
    fin_cases i
    rfl
  map_smul' r x := by
    ext i
    fin_cases i
    rfl
  left_inv x := by rfl
  right_inv x := by
    ext i
    fin_cases i
    rfl

/-- The equivalence between `V c` and `S.Tensor ![c]`. -/
noncomputable def fromSingleT {c : C} : V c ≃ₗ[k] S.Tensor ![c] :=
  (PiTensorProduct.subsingletonEquiv (s := fun i => V (![c] i)) 0).symm

lemma fromSingleT_symm_pure {c : C} (p : Pure S ![c]) :
    fromSingleT.symm p.toTensor = Pure.fromSingleP.symm p :=
  PiTensorProduct.subsingletonEquiv_apply_tprod 0 p

lemma fromSingleT_eq_pureT {c : C} (x : V c) :
    fromSingleT (S := S) x = Pure.toTensor (fun 0 => x : Pure S ![c]) := by
  change _ = Pure.toTensor (Pure.fromSingleP x)
  apply fromSingleT.symm.injective
  rw [fromSingleT_symm_pure]
  simp

lemma actionT_fromSingleT {c : C} (x : V c) (g : G) :
    g • fromSingleT (S := S) x = fromSingleT (rep c g x) := by
  rw [fromSingleT_eq_pureT, actionT_pure, fromSingleT_eq_pureT]
  congr
  funext x
  fin_cases x
  rfl

lemma fromSingleT_map {c c1 : C}
    (h : c = c1) (x : V c) :
    fromSingleT (LinearEquiv.cast (R := k) h x) =
    permT id (by simp [h]) (fromSingleT (S := S) x) := by
  rw [fromSingleT_eq_pureT, fromSingleT_eq_pureT, permT_pure]
  congr
  funext i
  fin_cases i
  rfl

lemma contrT_fromSingleT_fromSingleT {c : C} (x : V c)
    (y : V (S.τ c)) :
    contrT (S := S) 0 0 1 (by simp; rfl) (prodT (fromSingleT x) (fromSingleT y)) =
    (S.contr c) (x ⊗ₜ[k] y) • (Pure.toTensor default) := by
  rw [fromSingleT_eq_pureT, fromSingleT_eq_pureT, prodT_pure, contrT_pure, Pure.contrP,
    Pure.contrPCoeff]
  congr 1
  simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue]
  congr
  ext i
  fin_cases i

/-!

## Tensors with two indices.

-/
open TensorProduct

/-!

## fromPairT

-/

/-- The construction of a tensor with two indices from the tensor product
  `V c1 ⊗[k] V c2 ` defined
  categorically. -/
noncomputable def fromPairT {c1 c2 : C} :
    V c1 ⊗[k] V c2 →ₗ[k] S.Tensor ![c1, c2] where
  toFun x :=
    permT id (And.intro Function.bijective_id (fun i => by fin_cases i <;> rfl))
    (TensorProduct.lift prodT (TensorProduct.map (fromSingleT (S := S) (c := c1))
      (fromSingleT (S := S) (c := c2)).toLinearMap (x) : S.Tensor ![c1] ⊗[k] S.Tensor ![c2]))
  map_add' x y := by simp
  map_smul' r x := by simp

lemma fromPairT_tmul {c1 c2 : C} (x : V c1)
    (y : V c2) : fromPairT (x ⊗ₜ[k] y) =
    permT id (And.intro Function.bijective_id (fun i => by fin_cases i <;> rfl))
    (prodT (fromSingleT (S := S) x) (fromSingleT y)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma fromPairT_eq_pure {c1 c2 : C} (x : V c1) (y : V c2) :
    fromPairT (S := S) (x ⊗ₜ[k] y) = Pure.toTensor (fun | 0 => x | 1 => y) := by
  rw [fromPairT_tmul, fromSingleT_eq_pureT, fromSingleT_eq_pureT, prodT_pure, permT_pure]
  congr
  funext i
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
lemma actionT_fromPairT {c1 c2 : C}
    (x : V c1 ⊗[k]V c2)
    (g : G) :
    g • fromPairT (S := S) x = fromPairT (TensorProduct.map (rep c1 g)
      (rep c2 g) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_tmul]
    rw [fromPairT_tmul, ← permT_equivariant, ← prodT_equivariant,
      actionT_fromSingleT, actionT_fromSingleT]
    rfl
  | add x y hx hy => simp [hx, hy]

set_option backward.isDefEq.respectTransparency false in
lemma fromPairT_map_right {c1 c2 c2' : C} (h :c2 = c2')
    (x : V c1 ⊗[k] V c2) :
    fromPairT (TensorProduct.map LinearMap.id
      (LinearEquiv.cast (R := k) (M := V) h) x : _ ⊗[k] V c2') =
    permT id (by simp [h]) (fromPairT (S := S) x) := by
  induction' x using TensorProduct.inductionOn with x y x1 x2 h1 h2
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_tmul, LinearMap.id_coe, id_eq,
    LinearEquiv.coe_coe]
    rw [fromPairT_tmul, fromPairT_tmul]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, permT_permT, CompTriple.comp_eq]
    rw [fromSingleT_map, prodT_permT_right, permT_permT]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, CompTriple.comp_eq]
    congr
    exact List.ofFn_inj.mp rfl
  · simp [h1, h2]

set_option backward.isDefEq.respectTransparency false in
lemma fromPairT_comm {c1 c2 : C}
    (x : V c1 ⊗[k] V c2) :
    fromPairT (TensorProduct.comm k _ _ x) =
    permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
    (fromPairT (S := S) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, comm_tmul, Fin.isValue]
    rw [fromPairT_tmul, fromPairT_tmul, prodT_swap]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, permT_permT, CompTriple.comp_eq, Fin.isValue]
    congr
    ext i
    fin_cases i <;> rfl
  | add x y hx hy => simp [hx, hy]

/-!

### Contraction of fromPairT with fromSingleT

-/

/-- The contraction of tensors with one index with one with two indices defined categorically. -/
noncomputable def fromSingleTContrFromPairT {c c2 : C}
    (x : V c) (y : V (S.τ c) ⊗[k] V c2) : S.Tensor ![c2] :=
  let T1 : V c ⊗[k] (V (S.τ c) ⊗[k] (V c2)) := x ⊗ₜ[k] y
  let T3 : (V c ⊗[k] V (S.τ c)) ⊗[k] V c2 := (TensorProduct.assoc _ _ _ _).symm T1
  let T4 : k ⊗[k] V c2 := (S.contr c).toLinearMap.rTensor (V c2) T3
  let T5 : V c2 := TensorProduct.lid _ _ T4
  fromSingleT T5

lemma fromSingleTContrFromPairT_tmul {c c2 : C}
    (x : V c) (y1 : V (S.τ c)) (y2 : V c2) :
    fromSingleTContrFromPairT x (y1 ⊗ₜ[k] y2) =
    S.contr c (x ⊗ₜ[k] y1) • fromSingleT y2 := by
  simp [fromSingleTContrFromPairT]

set_option backward.isDefEq.respectTransparency false in
lemma fromSingleT_contr_fromPairT_tmul {c c2 : C}
    (x : V c) (y1 : V (S.τ c)) (y2 : V c2) :
    contrT 1 0 1 (by simp; rfl)
      (prodT (fromSingleT x) (fromPairT (y1 ⊗ₜ[k] y2))) =
    permT id (by simp; rfl) (fromSingleTContrFromPairT x (y1 ⊗ₜ[k] y2)) := by
  trans permT id (by simp; rfl)
    (prodT (contrT 0 0 1 (by simp; rfl) (prodT (fromSingleT x) (fromSingleT y1))) (fromSingleT y2))
  · conv_rhs =>
      enter [2]
      rw [prodT_swap]
      enter [2]
      rw [prodT_contrT_snd]
      change permT id _ (contrT 1 1 2 _ _)
    conv_rhs =>
      enter [2, 2, 2, 2]
      rw [prodT_swap]
    conv_rhs =>
      enter [2, 2, 2]
      rw [contrT_permT]
      enter [2]
      change contrT 1 0 1 _ _
    conv_rhs =>
      rw [permT_permT, permT_permT, permT_permT]
    rw [fromPairT_tmul]
    symm
    conv_rhs =>
      enter [2]
      rw [prodT_permT_right]
      enter [2]
      rw [prodT_assoc']
    conv_rhs =>
      enter [2]
      rw [permT_permT]
    conv_rhs =>
      rw [contrT_permT]
    refine permT_congr ?_ rfl
    ext i
    simp
  · rw [contrT_fromSingleT_fromSingleT]
    simp only [map_smul, LinearMap.smul_apply]
    rw [fromSingleTContrFromPairT_tmul]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, map_smul]
    congr 1
    rw [prodT_swap, permT_permT]
    simp only [Fin.isValue, Nat.add_zero, CompTriple.comp_eq, prodT_default_right, permT_permT]
    refine permT_congr ?_ rfl
    ext i
    simp

lemma contrT_fromSingleT_fromPairT {c c2 : C}
    (x : V c)
    (y : V (S.τ c) ⊗[k] V c2) :
    contrT 1 0 1 (by simp; rfl)
      (prodT (fromSingleT x) (fromPairT y)) =
    permT id (by simp; rfl) (fromSingleTContrFromPairT x y) := by
  induction y using TensorProduct.inductionOn with
  | tmul y1 y2 => exact fromSingleT_contr_fromPairT_tmul x y1 y2
  | add a b ha hb =>
    simp only [fromSingleTContrFromPairT] at ha hb ⊢
    simp only [tmul_add, map_add]
    rw [ha, hb]

/-!

### Contraction of fromPairT with fromPairT

-/

/-- The contraction of tensors with two indices defined categorically. -/
noncomputable def fromPairTContr {c c1 c2 : C}(x : V c1 ⊗[k] V c) (y : V (S.τ c) ⊗[k] V c2) :
    S.Tensor ![c1, c2] :=
  let V1 := (V c1)
  let V2 := (V c)
  let V2' := (V (S.τ c))
  let V3 := V c2
  let T1 : (V c1 ⊗[k] V c) ⊗[k] (V (S.τ c) ⊗[k] V c2) := x ⊗ₜ[k] y
  let T2 : V1 ⊗[k] (V2 ⊗[k] (V2' ⊗[k] V3)) := TensorProduct.assoc _ _ _ _ T1
  let T3 : V1 ⊗[k] ((V2 ⊗[k] V2') ⊗[k] V3) := (TensorProduct.assoc _ _ _ _).symm.lTensor _ T2
  let T4 : V1 ⊗[k] (k ⊗[k] V3) := ((S.contr c).toLinearMap.rTensor _).lTensor _ T3
  let T5 : V1 ⊗[k] V3 := (TensorProduct.lid _ _).lTensor _ T4
  fromPairT T5

lemma fromPairTContr_tmul_tmul {c c1 c2 : C} (x1 : V c1) (x2 : V c) (y1 : V (S.τ c))
    (y2 : V c2) : fromPairTContr (x1 ⊗ₜ[k] x2) (y1 ⊗ₜ[k] y2) =
    (S.contr c) (x2 ⊗ₜ[k] y1) • fromPairT (x1 ⊗ₜ[k] y2) := by
  simp [fromPairTContr, tmul_smul]

lemma fromPairT_contr_fromPairT_eq_fromPairTContr_tmul (c c1 c2 : C)
    (x1 : V c1) (x2 : V c) (y1 : V (S.τ c))
    (y2 : V c2) :
    contrT 2 1 2 (by simp; rfl) (prodT (fromPairT (x1 ⊗ₜ[k] x2)) (fromPairT (y1 ⊗ₜ[k] y2))) =
    permT id (by simp; exact ⟨rfl, rfl⟩)
    (fromPairTContr (x1 ⊗ₜ[k] x2) (y1 ⊗ₜ[k] y2)) := by
  simp only [map_smul, fromPairTContr_tmul_tmul, fromPairT_eq_pure, permT_pure,
    Pure.contrP, contrT_pure, prodT_pure]
  congr
  funext i
  fin_cases i <;> rfl

lemma fromPairT_contr_fromPairT_eq_fromPairTContr (c c1 c2 : C)
    (x : V c1 ⊗[k] V c)
    (y : V (S.τ c) ⊗[k] V c2) :
    contrT 2 1 2 (by simp; rfl)
      (prodT (fromPairT x) (fromPairT y)) =
    permT id (by simp; exact ⟨rfl, rfl⟩) (fromPairTContr x y) := by
  induction x using TensorProduct.inductionOn with
  | tmul x1 x2 =>
    induction y using TensorProduct.inductionOn with
    | tmul y1 y2 =>
      simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue]
      exact fromPairT_contr_fromPairT_eq_fromPairTContr_tmul c c1 c2 x1 x2 y1 y2
    | add a b ha hb =>
      simp only [fromPairTContr] at ha hb ⊢
      simp only [tmul_add, map_add]
      rw [← ha, ← hb]
  | add a b ha hb =>
    simp only [fromPairTContr] at ha hb ⊢
    simp only [add_tmul, map_add]
    rw [← ha, ← hb]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma fromPairT_basis_repr {c c1 : C}
    (x : V c ⊗[k] V c1)
    (φ : ComponentIdx ![c, c1]) :
    (basis ![c, c1]).repr (fromPairT (S := S) x) φ =
    (Basis.tensorProduct (b c) (b c1)).repr x (φ 0, φ 1) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Basis.tensorProduct_repr_tmul_apply,
      smul_eq_mul]
    conv_lhs =>
      left
      right
      rw [fromPairT_tmul]
    rw [fromSingleT_eq_pureT, fromSingleT_eq_pureT]
    rw [prodT_pure, permT_pure]
    rw [basis_repr_pure]
    simp [Pure.component]
    rw [mul_comm]
    rfl
  | add x y hx hy => simp_all

set_option backward.isDefEq.respectTransparency false in
lemma fromPairT_apply_basis_repr {c c1 : C}
    (b0 : basisIdx c) (b1 : basisIdx c1) :
    fromPairT (S := S) (b c b0 ⊗ₜ[k] b c1 b1) =
    Tensor.basis ![c, c1] (fun | 0 => b0 | 1 => b1) := by
  apply (Tensor.basis _).repr.injective
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Basis.repr_self]
  ext b
  rw [fromPairT_basis_repr]
  simp [Finsupp.single_apply]
  conv_rhs =>
    enter [1]
    rw [funext_iff]
    rw [Fin.forall_fin_two]
    simp
  split
  next h =>
    subst h
    simp_all only [Fin.isValue, true_and]
  next h => simp_all only [Fin.isValue, false_and, ↓reduceIte]

/-!

## fromConstPair

-/

/-- A constant two tensor (e.g. metric and unit). -/
noncomputable def fromConstPair {c1 c2 : C}
      (v : (Representation.trivial k G k).IntertwiningMap ((rep c1).tprod (rep c2))) :
    S.Tensor ![c1, c2] := fromPairT (v (1 : k))

/-- Tensors formed by `fromConstPair` are invariant under the group action. -/
@[simp]
lemma actionT_fromConstPair {c1 c2 : C}
    (v : (Representation.trivial k G k).IntertwiningMap ((rep c1).tprod (rep c2)))
    (g : G) : g • fromConstPair (S := S) v = fromConstPair v := by
  rw [fromConstPair, actionT_fromPairT]
  exact congrArg _ (LinearMap.congr_fun (v.isIntertwining' g) 1).symm

/-!

## fromTripleT

-/

/-- The construction of a tensor with two indices from the tensor product
  `V c1 ⊗[k] V c2 ` defined
  categorically. -/
noncomputable def fromTripleT {c1 c2 c3 : C} :
    V c1 ⊗[k] (V c2 ⊗[k] V c3) →ₗ[k] S.Tensor ![c1, c2, c3] where
  toFun x :=
    let x1 : S.Tensor ![c1] ⊗[k] (S.Tensor ![c2] ⊗[k] S.Tensor ![c3]) :=
      TensorProduct.map (fromSingleT (S := S) (c := c1))
        (TensorProduct.map (fromSingleT (S := S) (c := c2))
        (fromSingleT (S := S) (c := c3)).toLinearMap) x
    let x2 :=
      TensorProduct.lift prodT (TensorProduct.map LinearMap.id (TensorProduct.lift prodT) x1)
    permT id (And.intro Function.bijective_id (fun i => by fin_cases i <;> rfl)) x2
  map_add' x y := by
    simp
  map_smul' r x := by
    simp

lemma fromTripleT_tmul {c1 c2 c3 : C} (x : V c1)
    (y : V c2) (z : V c3) :
    fromTripleT (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
    permT id (And.intro Function.bijective_id (fun i => by fin_cases i <;> rfl))
      (prodT (fromSingleT (S := S) x) (prodT (fromSingleT y) (fromSingleT z))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma actionT_fromTripleT {c1 c2 c3 : C}
    (x : V c1 ⊗[k] (V c2 ⊗[k] V c3)) (g : G) :
    g • fromTripleT (S := S) x = fromTripleT (TensorProduct.map (rep c1 g)
      (TensorProduct.map (rep c2 g) (rep c3 g)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x yz =>
    induction yz using TensorProduct.inductionOn with
    | tmul y z =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_tmul]
      rw [fromTripleT_tmul, fromTripleT_tmul]
      rw [← permT_equivariant, ← prodT_equivariant, ← prodT_equivariant]
      simp [← actionT_fromSingleT]
    | add a b ha hb => simp [ha, hb, tmul_add]
  | add a b ha hb => simp [ha, hb]

set_option backward.isDefEq.respectTransparency false in
lemma fromTripleT_basis_repr {c c1 c2 : C}
    (x : V c ⊗[k] (V c1 ⊗[k] V c2))
    (φ : ComponentIdx ![c, c1, c2]) :
    (basis ![c, c1, c2]).repr (fromTripleT (S := S) x) φ =
    (Basis.tensorProduct (b c) (Basis.tensorProduct (b c1) (b c2))).repr x
    (φ 0, φ 1, φ 2) := by
  induction x using TensorProduct.inductionOn with
  | tmul x yz =>
    induction yz using TensorProduct.inductionOn with
    | tmul y z =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
      rw [fromTripleT_tmul]
      rw [fromSingleT_eq_pureT, fromSingleT_eq_pureT, fromSingleT_eq_pureT]
      rw [prodT_pure, prodT_pure, permT_pure]
      rw [basis_repr_pure]
      simp [Pure.component, Fin.prod_univ_three]
      conv_rhs =>
        rw [mul_assoc, mul_comm]
        enter [1]
        rw [mul_comm]
      rfl
    | add y1 y2 hx hy =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        Basis.tensorProduct_repr_tmul_apply, smul_eq_mul] at hx hy
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, tmul_add, map_add, Finsupp.coe_add,
        Pi.add_apply]
      rw [hx, hy]
  | add a b ha hb => simp_all

set_option backward.isDefEq.respectTransparency false in
lemma fromTripleT_apply_basis {c c1 c2 : C}
    (b0 : basisIdx c) (b1 : basisIdx c1)
    (b2 : basisIdx c2) :
    fromTripleT (S := S) (b c b0 ⊗ₜ[k] (b c1 b1 ⊗ₜ[k] b c2 b2)) =
    Tensor.basis ![c, c1, c2] (fun | 0 => b0 | 1 => b1 | 2 => b2) := by
  apply (Tensor.basis _).repr.injective
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Basis.repr_self]
  ext b
  rw [fromTripleT_basis_repr]
  simp [Finsupp.single_apply]
  conv_rhs =>
    enter [1]
    rw [funext_iff]
    rw [Fin.forall_fin_succ, Fin.forall_fin_two]
    simp
  split
  next h =>
    subst h
    simp_all only [Fin.isValue, true_and]
    split
    next h =>
      subst h
      simp_all only [Fin.isValue, true_and]
    next h => simp_all only [Fin.isValue, false_and, ↓reduceIte]
  next h => simp_all only [Fin.isValue, false_and, ↓reduceIte]

/-!

## fromConstTriple

-/

/-- A constant three tensor (e.g. the Pauli matrices). -/
noncomputable def fromConstTriple {c1 c2 c3 : C}
    (v : (Representation.trivial k G k).IntertwiningMap
      ((rep c1).tprod ((rep c2).tprod (rep c3)))) :
  S.Tensor ![c1, c2, c3] := fromTripleT (v (1 : k))

/-- Tensors formed by `fromConstPair` are invariant under the group action. -/
@[simp]
lemma actionT_fromConstTriple {c1 c2 c3 : C}
    (v : (Representation.trivial k G k).IntertwiningMap ((rep c1).tprod ((rep c2).tprod (rep c3))))
    (g : G) : g • fromConstTriple (S := S) v = fromConstTriple v := by
  rw [fromConstTriple, actionT_fromTripleT]
  exact congrArg _ (LinearMap.congr_fun (v.isIntertwining' g) 1).symm

end Tensor

end TensorSpecies
