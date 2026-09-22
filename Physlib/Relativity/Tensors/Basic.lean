/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Single
public import Physlib.Relativity.Tensors.Reindexing
public import Physlib.Relativity.Tensors.Contraction.SuccSuccAbove
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Tactic.Cases
/-!

# Tensors

This module sets up the tensors used for index notation in Physlib.

Physics picture:
- Choose a symmetry group `G` (for example, the Lorentz group).
- Give each index kind a name called a *color* (encoded by a type `C`).
  In Lorentzian notation, a typical choice is two colors: `up` and `down`.
- For each color, choose a representation of `G`.
- Fix a basis for each color. This determines which values that index can take and
  lets us speak about tensor components explicitly.
- Specify a dual color for each color, telling us which index pairs can contract.
- For dual pairs, provide the contraction/unit/metric data used for contraction and
  for raising/lowering indices.

All of this structure is packaged as a `TensorSpecies`.

For `S : TensorSpecies` and a list of index colors `c : Fin n → C`:
- `Tensor S c` is the type of tensors with those indices.
- `Pure S c` is the type of pure tensors, i.e. tensors of the form
  `v₀ ⊗ₜ v₁ ⊗ₜ v₂ …`.
- `ComponentIdx S c` is the type of allowed component labels for those indices.

This file realizes `Tensor S c` as a `PiTensorProduct`, relates pure tensors to
their components, constructs the component basis, and supplies the inherited
finite-dimensional and module-topology instances. It also defines the natural
action of `G` on pure tensors and tensors, the associated permutation maps, and
the map from rank-zero tensors to the base field.

From this setup we get the usual index-notation operations in a uniform way:
contraction, raising/lowering, and permutation of indices.
-/

@[expose] public section

open Module

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep b)

set_option linter.unusedVariables false in
/-- The tensors associated with a list of indices of a given color
  `c : Fin n → C`. -/
@[nolint unusedArguments]
noncomputable abbrev Tensor {n : ℕ} (S : TensorSpecies k C G V basisIdx rep b)
  (c : Fin n → C) : Type := PiTensorProduct k (fun i => V (c i))

namespace Tensor

variable {S : TensorSpecies k C G V basisIdx rep b} {n n' n2 : ℕ} {c : Fin n → C}
  {c' : Fin n' → C} {c2 : Fin n2 → C}

/-!

## Components of tensors

-/
/-!

## Pure tensors

-/

set_option linter.unusedVariables false in
/-- The type of pure tensors associated to a list of indices `c : OverColor C`.
  A pure tensor is a tensor which can be written in the form `v1 ⊗ₜ v2 ⊗ₜ v3 …`. -/
@[nolint unusedArguments]
abbrev Pure (S : TensorSpecies k C G V basisIdx rep b) (c : Fin n → C) : Type :=
    (i : Fin n) → V (c i)

namespace Pure

lemma congr_right {n : ℕ} {c : Fin n → C} (p : Pure S c)
    (i j : Fin n) (h : i = j) : LinearEquiv.cast (R := k) (by rw [h]) (p j) = p i := by
  subst h
  simp

lemma congr_mid {n : ℕ} {c : Fin n → C} (c' : C) (p : Pure S c)
    (i j : Fin n) (h : i = j) (hi : c i = c') (hj : c j = c') :
    LinearEquiv.cast (R := k) (by rw [hi] : c i = c') (p i) =
    LinearEquiv.cast (R := k) (by rw [hj] : c j = c') (p j) := by
  subst h hi
  simp

lemma map_mid_move_left {n n1 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C} (p : Pure S c)
    (p' : Pure S c1) {c' : C}
    (i : Fin n) (j : Fin n1) (hi : c i = c') (hj : c1 j = c') :
    LinearEquiv.cast (R := k) (by rw [hi] : c i = c') (p i) =
    LinearEquiv.cast (R := k) (by rw [hj] : c1 j = c') (p' j)
    ↔ LinearEquiv.cast (R := k) (by rw [hi, hj] : c i = c1 j) (p i) =
    (p' j) := by
  subst hj
  simp_all

/-- The tensor corresponding to a pure tensor. -/
noncomputable def toTensor {n : ℕ} {c : Fin n → C} (p : Pure S c) : S.Tensor c :=
  PiTensorProduct.tprod k p

lemma toTensor_apply {n : ℕ} (c : Fin n → C) (p : Pure S c) :
    toTensor p = PiTensorProduct.tprod k p := rfl

/-- Given a list of indices `c` of `n` indices, a pure tensor `p`, an element `i : Fin n` and
  a `x` in `V (c i)` then `update p i x` corresponds to `p` where
  the `i`th part of `p` is replaced with `x`.

  E.g. if `n = 2` and `p = v₀ ⊗ₜ v₁` then `update p 0 x = x ⊗ₜ v₁`. -/
def update {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c) (i : Fin n)
    (x : V (c i)) : Pure S c := Function.update p i x

lemma update_eq_function_update {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)]
    (p : Pure S c) (i : Fin n)
    (x : V (c i)) : update p i x = Function.update p i x := rfl

@[simp]
lemma update_same {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c) (i : Fin n)
    (x : V (c i)) : (update p i x) i = x := by
  simp [update]

lemma update_diff {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c) (i j : Fin n)
    (x : V (c i)) (hij : i ≠ j) : (update p i x) j = p j := by
  rw [update_eq_function_update, Function.update_of_ne hij.symm]

@[simp]
lemma update_succAbove_apply {n : ℕ} {c : Fin (n + 1) → C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (j : Fin n) (x : V (c (i.succAbove j))) :
    update p (i.succAbove j) x i = p i := by
  rw [update_eq_function_update, Function.update_of_ne (Fin.ne_succAbove i j)]

@[simp]
lemma toTensor_update_add {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c)
    (i : Fin n) (x y : V (c i)) :
    (update p i (x + y)).toTensor = (update p i x).toTensor + (update p i y).toTensor := by
  simp [toTensor, update]

@[simp]
lemma toTensor_update_smul {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c)
    (i : Fin n) (r : k) (y : V (c i)) :
    (update p i (r • y)).toTensor = r • (update p i y).toTensor := by
  simp [toTensor, update]

/-- Given a list of indices `c` of length `n + 1`, a pure tensor `p` and an `i : Fin (n + 1)`, then
  `drop p i` is the tensor `p` with it's `i`th part dropped.

  For example, if `n = 2` and `p = v₀ ⊗ₜ v₁ ⊗ₜ v₂` then `drop p 1 = v₀ ⊗ₜ v₂`. -/
def drop {n : ℕ} {c : Fin (n + 1) → C} (p : Pure S c) (i : Fin (n + 1)) :
    Pure S (c ∘ i.succAbove) :=
  fun j => p (i.succAbove j)

@[simp]
lemma update_succAbove_drop {n : ℕ} {c : Fin (n + 1) → C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (k : Fin n) (x : V (c (i.succAbove k))) :
    (update p (i.succAbove k) x).drop i = (p.drop i).update k x :=
  Function.update_comp_eq_of_injective' p Fin.succAbove_right_injective k x

@[simp]
lemma update_drop_self {n : ℕ} {c : Fin (n + 1) → C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (x : V (c i)) :
    (update p i x).drop i = p.drop i := by
  ext j
  simp [drop, update_eq_function_update]

/-!

## Components

-/

/-- Given an element `b` of `ComponentIdx c` and a pure tensor `p` then
  `component p b` is the element of the ring `k` corresponding to
  the component of `p` in the direction `b`.

  For example, if `p = v ⊗ₜ w` and `b = ⟨0, 1⟩` then `component p b = v⁰ ⊗ₜ w¹`. -/
noncomputable def component {n : ℕ} {c : Fin n → C} (p : Pure S c)
    (φ : ComponentIdx (S := S) c) : k :=
    ∏ i, (b (c i)).repr (p i) (φ i)

lemma component_eq {n : ℕ} {c : Fin n → C} (p : Pure S c) (φ : ComponentIdx c) :
    p.component φ = ∏ i, (b (c i)).repr (p i) (φ i) := by rfl

lemma component_eq_drop {n : ℕ} {c : Fin (n + 1) → C} (p : Pure S c) (i : Fin (n + 1))
    (φ : ComponentIdx c) :
    p.component φ = ((b (c i)).repr (p i) (φ i)) *
    ((drop p i).component (fun j => φ (i.succAbove j))) :=
  Fin.prod_univ_succAbove (fun j => (b (c j)).repr (p j) (φ j)) i

@[simp]
lemma component_update_add {n : ℕ} [inst : DecidableEq (Fin n)]
    {c : Fin n → C} (p : Pure S c) (i : Fin n)
    (x y :V (c i)) (b : ComponentIdx c) :
    (update p i (x + y)).component b = (update p i x).component b +
    (update p i y).component b := by
  cases n
  · exact Fin.elim0 i
  · simp [component_eq_drop _ i, add_mul]

@[simp]
lemma component_update_smul {n : ℕ} [inst : DecidableEq (Fin n)]
    {c : Fin n → C} (p : Pure S c) (i : Fin n)
    (x : k) (y : V (c i)) (b : ComponentIdx c) :
    (update p i (x • y)).component b = x * (update p i y).component b := by
  cases n
  · exact Fin.elim0 i
  · simp [component_eq_drop _ i, mul_assoc]

/-- The multilinear map taking pure tensors `p` to a map `ComponentIdx c → k` which when
  evaluated returns the components of `p`. -/
noncomputable def componentMap {n : ℕ} (c : Fin n → C) :
    MultilinearMap k (fun i => V (c i)) (ComponentIdx (S := S) c → k) where
  toFun p := fun b => component p b
  map_update_add' p i x y := by
    ext b
    change component (update p i (x + y)) b =
      component (update p i x) b + component (update p i y) b
    exact component_update_add p i x y b
  map_update_smul' p i x y := by
    ext b
    change component (update p i (x • y)) b = x * component (update p i y) b
    exact component_update_smul p i x y b

@[simp]
lemma componentMap_apply {n : ℕ} (c : Fin n → C)
    (p : Pure S c) : componentMap c p = p.component := by
  rfl

/-- Given an component idx `b` in `ComponentIdx c`, `basisVector c b` is the pure tensor
  formed by `S.basis (c i) (b i)`. -/
noncomputable def basisVector {n : ℕ} (c : Fin n → C) (φ : ComponentIdx (S := S) c) : Pure S c :=
  fun i => b (c i) (φ i)

@[simp]
lemma component_basisVector {n : ℕ} (c : Fin n → C) (b1 b2 : ComponentIdx (S := S) c) :
    (basisVector c b1).component b2 = if b1 = b2 then 1 else 0 := by
  simp [component_eq, basisVector, Finsupp.single_apply, Fintype.prod_boole, funext_iff]

end Pure

lemma induction_on_pure {n : ℕ} {c : Fin n → C} {P : S.Tensor c → Prop}
    (h : ∀ (p : Pure S c), P p.toTensor)
    (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t1 t2, P t1 → P t2 → P (t1 + t2)) (t : S.Tensor c) : P t := by
  refine PiTensorProduct.induction_on' t (fun r p => ?_) hadd
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod]
  exact hsmul r _ (h p)

/-!

## The basis

-/

noncomputable section Basis

/-- The linear map from tensors to its components. -/
def componentMap {n : ℕ} (c : Fin n → C) : S.Tensor c →ₗ[k] (ComponentIdx (S := S) c → k) :=
  PiTensorProduct.lift (Pure.componentMap c)

@[simp]
lemma componentMap_pure {n : ℕ} (c : Fin n → C)
    (p : Pure S c) : componentMap c (p.toTensor) = Pure.componentMap c p :=
  PiTensorProduct.lift.tprod p

/-- The tensor created from it's components. -/
def ofComponents {n : ℕ} (c : Fin n → C) :
    (ComponentIdx (S := S) c → k) →ₗ[k] S.Tensor c where
  toFun f := ∑ b, f b • (Pure.basisVector c b).toTensor
  map_add' fb gb := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' fb r := by
    simp [smul_smul, Finset.smul_sum]

@[simp]
lemma componentMap_ofComponents {n : ℕ} (c : Fin n → C) (f : ComponentIdx c → k) :
    componentMap c (ofComponents (S := S) c f) = f := by
  ext b
  simp [ofComponents]

@[simp]
lemma ofComponents_componentMap {n : ℕ} (c : Fin n → C) (t : S.Tensor c) :
    ofComponents c (componentMap c t) = t := by
  simp only [ofComponents, LinearMap.coe_mk, AddHom.coe_mk]
  induction t using induction_on_pure with
  | h p =>
    simp only [componentMap_pure, Pure.componentMap_apply]
    simp_rw [Pure.component_eq, Pure.toTensor, ← MultilinearMap.map_smul_univ, Pure.basisVector]
    trans (PiTensorProduct.tprod k) fun i =>
      ∑ x, ((b (c i)).repr (p i)) x • (b (c i)) x
    · exact (MultilinearMap.map_sum _ fun i j => ((b (c i)).repr (p i)) j • (b (c i)) j).symm
    exact congrArg _ (funext fun i => Basis.sum_equivFun (b (c i)) (p i))
  | hsmul r t ht =>
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, ht]
  | hadd t1 t2 h1 h2 => simp [add_smul, Finset.sum_add_distrib, h1, h2]

/-- The basis of tensors. -/
def basis {n : ℕ} (c : Fin n → C) : Basis (ComponentIdx (S := S) c) k (S.Tensor c) where
  repr := (LinearEquiv.mk (componentMap c) (ofComponents c)
    (fun x => by simp) (fun x => by simp)).trans
    (Finsupp.linearEquivFunOnFinite k k ((j : Fin n) → basisIdx (c j))).symm

lemma basis_apply {n : ℕ} (c : Fin n → C) (φ : ComponentIdx (S := S) c) :
    basis c φ = (Pure.basisVector c φ).toTensor := by
  change ofComponents c _ = _
  simp [ofComponents, Finsupp.linearEquivFunOnFinite_single, Pi.single_apply, ite_smul]

@[simp]
lemma basis_repr_pure {n : ℕ} (c : Fin n → C)
    (p : Pure S c) :
    (basis c).repr p.toTensor = p.component := by
  ext φ
  change componentMap c p.toTensor φ = _
  simp

lemma induction_on_basis {n : ℕ} {c : Fin n → C} {P : S.Tensor c → Prop}
    (h : ∀ b, P (basis c b)) (hzero : P 0)
    (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t1 t2, P t1 → P t2 → P (t1 + t2)) (t : S.Tensor c) : P t := by
  refine Submodule.span_induction ?_ hzero (fun t1 t2 _ _ => hadd t1 t2)
    (fun r t _ => hsmul r t) (Basis.mem_span (basis c) t)
  rintro x ⟨b, rfl⟩
  exact h b

/-- `componentMap` is the basis representation `(basis c).repr` definitionally; this bridges the two
notations wherever a component computation meets a `repr` rewrite. -/
lemma componentMap_eq_repr {n : ℕ} (c : Fin n → C) (t : S.Tensor c)
    (ψ : ComponentIdx (S := S) c) : componentMap c t ψ = (basis c).repr t ψ := rfl

/-- Two tensors with the same colour sequence are equal when all their components agree. -/
lemma componentMap_ext {n : ℕ} {c : Fin n → C} {t₁ t₂ : S.Tensor c}
    (h : ∀ b, componentMap c t₁ b = componentMap c t₂ b) : t₁ = t₂ := by
  rw [← ofComponents_componentMap c t₁, ← ofComponents_componentMap c t₂, funext h]

end Basis

/-!

## The rank

-/

instance {k : Type} [Field k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep b)
    {c : Fin n → C} : FiniteDimensional k (S.Tensor c) :=
  Module.Basis.finiteDimensional_of_finite (Tensor.basis c)

noncomputable instance {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep b)
    {c : Fin n → C} : TopologicalSpace (S.Tensor c) :=
  moduleTopology k (S.Tensor c)

instance {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep b)
    {c : Fin n → C} : IsTopologicalAddGroup (S.Tensor c) :=
  IsModuleTopology.isTopologicalAddGroup (R := k) (S.Tensor c)

/-!

## The action
-/

namespace Pure

noncomputable instance actionP : MulAction G (Pure S c) where
  smul g p := fun i => rep (c i) g (p i)
  one_smul p := by
    ext i
    change rep (c i) 1 (p i) = p i
    simp
  mul_smul g g' p := by
    ext i
    change rep (c i) (g * g') (p i) = rep (c i) g (rep (c i) g' (p i))
    simp

lemma actionP_eq {g : G} {p : Pure S c} : g • p = fun i => rep (c i) g (p i) := rfl

lemma rep_cast {g : G} {c c1 : C} (p : V c) (h : c = c1) :
    LinearEquiv.cast (R := k) h (rep c g p) = rep c1 g (LinearEquiv.cast (R := k) h p) := by
  subst h
  rfl

lemma actionP_cast {g : G} {p : Pure S c} (h : c = c1) :
    LinearEquiv.cast (R := k) h (g • p) = g • LinearEquiv.cast (R := k) h p := by
  subst h
  rfl

@[simp]
lemma drop_actionP {n : ℕ} {c : Fin (n + 1) → C} {i : Fin (n + 1)} {p : Pure S c} (g : G) :
    (g • p).drop i = g • (p.drop i) := by
  ext j
  rw [drop, actionP_eq, actionP_eq]
  simp only [Function.comp_apply]
  rfl

end Pure

/-!

## The action on tensors

-/

/- The action on `S.Tensor c` is given priority above `Tensorial.smulAction` (which has
  `priority := high` so that it beats Mathlib's left action on tensor products), so that for a
  bare tensor `g • t` elaborates to this instance, as used in the `*_equivariant` lemmas. -/
noncomputable instance (priority := high + 1) instSMul : SMul G (S.Tensor c) where
  smul g t := PiTensorProduct.map (fun i => rep (c i) g) t

lemma actionT_eq {g : G} {t : S.Tensor c} : g • t =
    PiTensorProduct.map (fun i => rep (c i) g) t := rfl

noncomputable instance (priority := high + 1) actionT : MulAction G (S.Tensor c) where
  one_smul t := by
    simp [actionT_eq]
  mul_smul g g' t := by
    simp [actionT_eq]
    change _ = (PiTensorProduct.map (fun i => rep (c i) g) ∘ₗ
      (PiTensorProduct.map (fun i => rep (c i) g'))) t
    rw [← PiTensorProduct.map_comp]
    rfl

lemma actionT_pure {g : G} {p : Pure S c} :
    g • p.toTensor = Pure.toTensor (g • p) :=
  PiTensorProduct.map_tprod (R := k) (fun i => rep (c i) g) p

lemma actionT_add {g : G} {t1 t2 : S.Tensor c} :
    g • (t1 + t2) = g • t1 + g • t2 := by
  simp [actionT_eq]

@[simp]
lemma actionT_smul {g : G} {r : k} {t : S.Tensor c} :
    g • (r • t) = r • (g • t) := by
  simp [actionT_eq]

lemma actionT_zero {g : G} : g • (0 : S.Tensor c) = 0 := by
  simp [actionT_eq]

lemma actionT_neg {g : G} {t : S.Tensor c} :
    g • (-t) = -(g • t) := by
  rw [actionT_eq]
  simp only [map_neg, neg_inj]
  rfl

noncomputable instance (priority := high + 1) : DistribMulAction G (S.Tensor c) where
  smul_zero g := by simp [actionT_zero]
  smul_add g t1 t2 := by simp [actionT_add]

instance : SMulCommClass k G (S.Tensor c) where
  smul_comm _ _ _ := actionT_smul.symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
instance : SMulCommClass G k (S.Tensor c) := SMulCommClass.symm _ _ _


/-!

## Permutations

-/

/-- Given a permutation `σ : Fin m → Fin n` of indices satisfying `IsReindexing` through `h`,
  and a pure tensor `p`, `permP σ h p` is the pure tensor permuted according to `σ`.

  For example if `m = n = 2` and `σ = ![1, 0]`, and `p = v ⊗ₜ w` then
  `permP σ _ p = w ⊗ₜ v`. -/
def Pure.permP {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) (p : Pure S c) : Pure S c1 :=
  fun i => LinearEquiv.cast (R := k) (by simp [h.preserve_color]) (p (σ i))

@[simp]
lemma Pure.permP_basisVector {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) (φ : ComponentIdx (S := S) c) :
    Pure.permP σ h (Pure.basisVector c φ) =
    Pure.basisVector c1 (fun i => basisIdxCongr (by simp [h.preserve_color]) (φ (σ i))) := by
  ext i
  simp only [permP, basisVector]
  apply map_basis_eq

lemma Pure.permP_equivariant {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (g : G) (p : Pure S c) :
    Pure.permP σ h (g • p) = g • Pure.permP σ h p := by
  ext i
  simp only [permP, actionP_eq]
  exact rep_cast _ _

/-- The reindexing of a tensor based on a map `σ : Fin m → Fin n` of indices
  satisfying `IsReindexing`. -/
noncomputable def permT {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) : S.Tensor c →ₗ[k] S.Tensor c1 :=
  PiTensorProduct.map (fun i => LinearEquiv.cast (R := k) (M := V)
    (by simp : c (h.toEquiv.symm i) = c1 i)) ∘ₗ
  (PiTensorProduct.reindex k _ h.toEquiv).toLinearMap

lemma permT_pure {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (p : Pure S c) :
    permT σ h p.toTensor = (p.permP σ h).toTensor := by
  simp only [permT, Pure.toTensor, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
  rfl

@[simp]
lemma Pure.permP_id_self {n : ℕ} {c : Fin n → C} (p : Pure S c) :
    Pure.permP (id : Fin n → Fin n) (by simp : IsReindexing c c id) p = p := by
  ext i
  simp [Pure.permP]

@[simp]
lemma permT_id_self {n : ℕ} {c : Fin n → C} (t : S.Tensor c) :
    permT (id : Fin n → Fin n) (by simp : IsReindexing c c id) t = t := by
  induction t using induction_on_pure with
  | h p => simp [permT_pure]
  | hsmul r t ht => simp [ht]
  | hadd t1 t2 h1 h2 => simp [h1, h2]

lemma permT_congr_eq_id {n : ℕ} {c : Fin n → C} (t : S.Tensor c)
    (σ : Fin n → Fin n) (hσ : IsReindexing c c σ) (h : σ = id) :
    permT σ (hσ) t = t := by
  subst h
  simp

lemma permT_congr_eq_id' {n : ℕ} {c : Fin n → C} (t t1 : S.Tensor c)
    (σ : Fin n → Fin n) (hσ : IsReindexing c c σ) (h : σ = id) (ht : t = t1) :
    permT σ (hσ) t = t1 := by
  subst h ht
  simp

@[simp]
lemma permT_equivariant {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (g : G) (t : S.Tensor c) :
    permT σ h (g • t) = g • permT σ h t := by
  induction t using induction_on_pure with
  | h p => simp [actionT_pure, permT_pure, Pure.permP_equivariant]
  | hsmul r t ht => simp [ht]
  | hadd t1 t2 h1 h2 => simp [h1, h2]

@[congr]
lemma Pure.permP_congr {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ σ1 : Fin m → Fin n} {h : IsReindexing c c1 σ} {h1 : IsReindexing c c1 σ1}
    {p p1 : Pure S c} (hmap : σ = σ1) (hpure : p = p1) :
    Pure.permP σ h p = Pure.permP σ1 h1 p1 := by
  subst hmap hpure
  rfl

@[congr]
lemma permT_congr {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ σ1 : Fin m → Fin n} {h : IsReindexing c c1 σ} {h1 : IsReindexing c c1 σ1}
    (hmap : σ = σ1) {t t1: S.Tensor c} (htensor : t = t1) :
    permT σ h t = permT σ1 h1 t1 := by
  subst hmap htensor
  rfl

@[simp]
lemma Pure.permP_permP {n m1 m2 : ℕ} {c : Fin n → C} {c1 : Fin m1 → C} {c2 : Fin m2 → C}
    {σ : Fin m1 → Fin n} {σ2 : Fin m2 → Fin m1} (h : IsReindexing c c1 σ)
    (h2 : IsReindexing c1 c2 σ2) (p : Pure S c) :
    Pure.permP σ2 h2 (Pure.permP σ h p) = Pure.permP (σ ∘ σ2) (h.comp h2) p := by
  ext i
  simp [permP]

@[simp]
lemma permT_permT {n m1 m2 : ℕ} {c : Fin n → C} {c1 : Fin m1 → C} {c2 : Fin m2 → C}
    {σ : Fin m1 → Fin n} {σ2 : Fin m2 → Fin m1} (h : IsReindexing c c1 σ)
    (h2 : IsReindexing c1 c2 σ2) (t : S.Tensor c) :
    permT σ2 h2 (permT σ h t) = permT (σ ∘ σ2) (h.comp h2) t := by
  induction t using induction_on_basis with
  | h b => rw [basis_apply, permT_pure, permT_pure, permT_pure, Pure.permP_permP]
  | hzero => simp
  | hsmul r t h1 => simp [h1]
  | hadd t1 t2 h1 h2 => simp [h1, h2]

lemma permT_basis_repr_symm_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (t : S.Tensor c)
    (φ : ComponentIdx c1) :
    (basis c1).repr (permT σ h t) φ =
    (basis c).repr t (fun i =>
      basisIdxCongr (by simp [IsReindexing.inv_perserve_color]) (φ (h.inv σ i))) := by
  induction t using induction_on_basis with
  | h b' =>
    rw [basis_apply, permT_pure, Pure.permP_basisVector, ← basis_apply, ← basis_apply]
    simp only [Basis.repr_self, Finsupp.single_apply]
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro h'
      funext x
      simpa [← h'] using ComponentIdx.congr_right _ _ _
        (IsReindexing.inv_apply_apply σ h x).symm
    · intro h'
      funext x
      simpa [h'] using (ComponentIdx.congr_right _ _ _
        (IsReindexing.apply_inv_apply σ h x).symm).symm
  | hzero => simp
  | hsmul r t h => simp [h]
  | hadd t1 t2 h1 h2 => simp [h1, h2]

lemma permT_basis {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ)
    (b : ComponentIdx c) :
    (permT σ h) (basis (S := S) c b) = basis c1 (fun i =>
      basisIdxCongr (by simp [h.2]) (b (σ i))) := by
  rw [basis_apply, permT_pure, Pure.permP_basisVector, ← basis_apply]

lemma permT_eq_zero_iff {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (t : S.Tensor c) :
    permT σ h t = 0 ↔ t = 0 := by
  refine ⟨fun h' => ?_, fun h' => by simp [h']⟩
  have h2 := congrArg (permT (h.inv σ) h.symm) h'
  rwa [permT_permT, map_zero, permT_congr_eq_id] at h2
  funext x
  simp [IsReindexing.inv_apply_apply]

/-- `permT` is injective. -/
lemma permT_injective {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) :
    Function.Injective (permT (S := S) σ h) :=
  (injective_iff_map_eq_zero' _).mpr (permT_eq_zero_iff h)

/-!
## field
-/

/-- The linear map between tensors with zero indices and the underlying field
  `k`. -/
noncomputable def toField {c : Fin 0 → C} : S.Tensor c →ₗ[k] k :=
  (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap

lemma toField_default {c : Fin 0 → C} :
    toField (Pure.toTensor default : S.Tensor c) = 1 := by
  simp [toField, Pure.toTensor]

lemma toField_injective {c : Fin 0 → C} :
    Function.Injective (toField : S.Tensor c → k) :=
  (PiTensorProduct.isEmptyEquiv (Fin 0)).injective

@[simp]
lemma toField_pure {c : Fin 0 → C} (p : Pure S c) :
    toField (p.toTensor : S.Tensor c) = 1 := by
  rw [Subsingleton.elim p default, toField_default]

lemma toField_permT {c c1 : Fin 0 → C} (σ : Fin 0 → Fin 0)
    (h : IsReindexing c c1 σ) (t : S.Tensor c) :
    toField (permT σ h t) = toField t := by
  induction' t using induction_on_basis with b r t ht t1 t2 h1 h2
  · simp [toField_pure, basis_apply, permT_pure]
  · simp
  · simp [ht]
  · simp [h1, h2]

@[simp]
lemma toField_basis_default {c : Fin 0 → C} :
    toField (basis c (@default (ComponentIdx (S := S) c) Unique.instInhabited)) = 1 := by
  simp [basis_apply]

lemma toField_basis {c : Fin 0 → C} (b : ComponentIdx (S := S) c) :
    toField (basis c b) = 1 := by
  simp [basis_apply]

lemma toField_eq_repr {c : Fin 0 → C} (t : Tensor S c) :
    t.toField = (basis c).repr t (fun j => Fin.elim0 j) := by
  obtain ⟨t, rfl⟩ := (basis c).repr.symm.surjective t
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination]
  rw [Finsupp.linearCombination_unique, map_smul, toField_basis_default, smul_eq_mul, mul_one]
  rfl

@[simp]
lemma toField_equivariant {c : Fin 0 → C} (g : G) (t : Tensor S c) :
    toField (g • t) = toField t := by
  induction t using induction_on_pure with
  | h p => simp [actionT_pure]
  | hsmul r t hp => simp [hp]
  | hadd t1 t2 hp1 hp2 => simp [hp1, hp2]

lemma eq_smul_toField {c : Fin 0 → C} (t : Tensor S c) :
    t = toField t • (basis c (@default (ComponentIdx (S := S) c) Unique.instInhabited)) := by
  apply toField_injective
  simp

end Tensor

end TensorSpecies
