/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.RCLike.Basic
/-!

# Tensors

-/

open Module IndexNotation CategoryTheory MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] (S : TensorSpecies k C G)

/-- The tensors associated with a list of indices of a given color
  `c : Fin n → C`. -/
noncomputable abbrev Tensor {n : ℕ} (c : Fin n → C) : Type := (S.F.obj (OverColor.mk c))

namespace Tensor

variable {S : TensorSpecies k C G} {n n' n2 : ℕ} {c : Fin n → C} {c' : Fin n' → C}
  {c2 : Fin n2 → C}

/-- Given a list of indices `c : Fin n → C` e.g. `![.up, .down]`, the type
  `ComponentIdx c` is the type of components indexes of a tensor with those indices
  e.g. `⟨0, 2⟩` corresponding to `T⁰₂`. -/
abbrev ComponentIdx {n : ℕ} (c : Fin n → C) : Type := Π j, Fin (S.repDim (c j))

lemma ComponentIdx.congr_right {n : ℕ} {c : Fin n → C} (b : ComponentIdx (S := S) c)
    (i j : Fin n) (h : i = j) : b i = Fin.cast (by simp [h]) (b j) := by
  subst h
  rfl

/-- Casting of a `ComponentIdx` through equivalent color maps. -/
def ComponentIdx.cast {n m : ℕ} {c : Fin n → C} {cm : Fin m → C}
    (h : n = m) (hc : c = cm ∘ Fin.cast h) (b : ComponentIdx (S := S) c) :
    ComponentIdx (S := S) cm := fun j =>
      Fin.cast (by simp [hc]) (b (Fin.cast h.symm j))

/-!

## Pure tensors

-/

/-- The type of pure tensors associated to a list of indices `c : OverColor C`.
  A pure tensor is a tensor which can be written in the form `v1 ⊗ₜ v2 ⊗ₜ v3 …`. -/
abbrev Pure (S : TensorSpecies k C G) (c : Fin n → C) : Type :=
    (i : Fin n) → S.FD.obj (Discrete.mk (c i))

namespace Pure

@[simp]
lemma congr_right {n : ℕ} {c : Fin n → C} (p : Pure S c)
    (i j : Fin n) (h : i = j) : S.FD.map (eqToHom (by rw [h])) (p j) = p i := by
  subst h
  simp

lemma congr_mid {n : ℕ} {c : Fin n → C} (c' : C) (p : Pure S c)
    (i j : Fin n) (h : i = j) (hi : c i = c') (hj : c j = c') :
    S.FD.map (eqToHom (by rw [hi] : { as := c i } = { as := c' })) (p i) =
    S.FD.map (eqToHom (by rw [hj] : { as := c j } = { as := c' })) (p j) := by
  subst hi
  simp only [eqToHom_refl, Discrete.functor_map_id, ConcreteCategory.id_apply]
  symm
  apply congr_right
  exact h

lemma map_mid_move_left {n n1 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C} (p : Pure S c)
    (p' : Pure S c1) {c' : C}
    (i : Fin n) (j : Fin n1) (hi : c i = c') (hj : c1 j = c') :
    S.FD.map (eqToHom (by rw [hi] : { as := c i } = { as := c' })) (p i) =
    S.FD.map (eqToHom (by rw [hj] : { as := c1 j } = { as := c' })) (p' j)
    ↔ S.FD.map (eqToHom (by rw [hi, hj] : { as := c i } = { as := c1 j})) (p i) =
    (p' j) := by
  subst hj
  simp_all only [eqToHom_refl, Discrete.functor_map_id, ConcreteCategory.id_apply]

lemma map_map_apply {n : ℕ} {c : Fin n → C} (c1 c2 : C) (p : Pure S c) (i : Fin n)
    (f : ({ as := c i } : Discrete C) ⟶ { as := c1 })
    (g : ({ as := c1 } : Discrete C) ⟶ { as := c2 }) :
    (ConcreteCategory.hom (S.FD.map g))
    ((ConcreteCategory.hom (S.FD.map f)) (p i)) =
    S.FD.map (f ≫ g) (p i) := by
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]

/-- The tensor corresponding to a pure tensor. -/
noncomputable def toTensor {n : ℕ} {c : Fin n → C} (p : Pure S c) : S.Tensor c :=
  PiTensorProduct.tprod k p

lemma toTensor_apply {n : ℕ} (c : Fin n → C) (p : Pure S c) :
    toTensor p = PiTensorProduct.tprod k p := rfl

/-- Given a list of indices `c` of `n` indices, a pure tensor `p`, an element `i : Fin n` and
  a `x` in `S.FD.obj (Discrete.mk (c i))` then `update p i x` corresponds to `p` where
  the `i`th part of `p` is replaced with `x`.

  E.g. if `n = 2` and `p = v₀ ⊗ₜ v₁` then `update p 0 x = x ⊗ₜ v₁`. -/
def update {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c) (i : Fin n)
    (x : S.FD.obj (Discrete.mk (c i))) : Pure S c := Function.update p i x

@[simp]
lemma update_same {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c) (i : Fin n)
    (x : S.FD.obj (Discrete.mk (c i))) : (update p i x) i = x := by
  simp [update]

@[simp]
lemma update_succAbove_apply {n : ℕ} {c : Fin (n + 1) → C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (j : Fin n) (x : S.FD.obj (Discrete.mk (c (i.succAbove j)))) :
    update p (i.succAbove j) x i = p i := by
  simp only [update]
  rw [Function.update_of_ne]
  exact Fin.ne_succAbove i j

@[simp]
lemma toTensor_update_add {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c)
    (i : Fin n) (x y : S.FD.obj (Discrete.mk (c i))) :
    (update p i (x + y)).toTensor = (update p i x).toTensor + (update p i y).toTensor := by
  simp [toTensor, update]

@[simp]
lemma toTensor_update_smul {n : ℕ} {c : Fin n → C} [inst : DecidableEq (Fin n)] (p : Pure S c)
    (i : Fin n) (r : k) (y : S.FD.obj (Discrete.mk (c i))) :
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
    (p : Pure S c) (i : Fin (n + 1)) (k : Fin n) (x : S.FD.obj (Discrete.mk (c (i.succAbove k)))) :
    (update p (i.succAbove k) x).drop i = (p.drop i).update k x := by
  ext j
  simp only [Function.comp_apply, drop, update]
  by_cases h : j = k
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne]
    · rfl
    · simp only [ne_eq]
      rw [Function.Injective.eq_iff (Fin.succAbove_right_injective (p := i))]
      exact h

@[simp]
lemma update_drop_self {n : ℕ} {c : Fin (n + 1) → C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (x : S.FD.obj (Discrete.mk (c i))) :
    (update p i x).drop i = p.drop i := by
  ext k
  simp only [Function.comp_apply, drop, update]
  rw [Function.update_of_ne]
  exact Fin.succAbove_ne i k

lemma μ_toTensor_tmul_toTensor {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (t : Pure S c) (t1 : Pure S c1) :
    ((Functor.LaxMonoidal.μ S.F _ _).hom (t.toTensor ⊗ₜ t1.toTensor)) =
    PiTensorProduct.tprod k (fun | Sum.inl i => t i | Sum.inr i => t1 i) := by
  change lift.μModEquiv _ _ _ (t.toTensor ⊗ₜ t1.toTensor) = _
  rw [lift.μModEquiv]
  simp only [lift.toRep_V_carrier, Functor.id_obj]
  rw [LinearEquiv.trans_apply]
  rw [toTensor, toTensor]
  rw [PhysLean.PiTensorProduct.tmulEquiv_tmul_tprod]
  simp only [tensorObj_of_left, tensorObj_of_hom, PiTensorProduct.congr_tprod]
  congr
  funext i
  match i with
  | Sum.inl i =>
    rfl
  | Sum.inr i =>
    rfl

/-!

## Components

-/

/-- Given an element `b` of `ComponentIdx c` and a pure tensor `p` then
  `component p b` is the element of the ring `k` corresponding to
  the component of `p` in the direction `b`.

  For example, if `p = v ⊗ₜ w` and `b = ⟨0, 1⟩` then `component p b = v⁰ ⊗ₜ w¹`. -/
noncomputable def component {n : ℕ} {c : Fin n → C} (p : Pure S c)
    (b : ComponentIdx (S := S) c) : k :=
    ∏ i, (S.basis (c i)).repr (p i) (b i)

lemma component_eq {n : ℕ} {c : Fin n → C} (p : Pure S c) (b : ComponentIdx c) :
    p.component b = ∏ i, (S.basis (c i)).repr (p i) (b i) := by rfl

lemma component_eq_drop {n : ℕ} {c : Fin (n + 1) → C} (p : Pure S c) (i : Fin (n + 1))
    (b : ComponentIdx c) :
    p.component b = ((S.basis (c i)).repr (p i) (b i)) *
    ((drop p i).component (fun j => b (i.succAbove j))) := by
  simp only [component, Function.comp_apply]
  rw [Fin.prod_univ_succAbove _ i]
  rfl

@[simp]
lemma component_update_add {n : ℕ} [inst : DecidableEq (Fin n)]
    {c : Fin n → C} (p : Pure S c) (i : Fin n)
    (x y : S.FD.obj (Discrete.mk (c i))) (b : ComponentIdx c) :
    (update p i (x + y)).component b = (update p i x).component b +
    (update p i y).component b := by
  cases n
  · exact Fin.elim0 i
  rename_i n
  rw [component_eq_drop _ i, component_eq_drop _ i, component_eq_drop _ i]
  simp [add_mul]

@[simp]
lemma component_update_smul {n : ℕ} [inst : DecidableEq (Fin n)]
    {c : Fin n → C} (p : Pure S c) (i : Fin n)
    (x : k) (y : S.FD.obj (Discrete.mk (c i))) (b : ComponentIdx c) :
    (update p i (x • y)).component b = x * (update p i y).component b := by
  cases n
  · exact Fin.elim0 i
  rename_i n
  rw [component_eq_drop _ i, component_eq_drop _ i]
  simp only [update_same, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, update_drop_self]
  ring

/-- The multilinear map taking pure tensors `p` to a map `ComponentIdx c → k` which when
  evaluated returns the components of `p`. -/
noncomputable def componentMap {n : ℕ} (c : Fin n → C) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i))) (ComponentIdx (S := S) c → k) where
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
noncomputable def basisVector {n : ℕ} (c : Fin n → C) (b : ComponentIdx (S := S) c) : Pure S c :=
  fun i => S.basis (c i) (b i)

@[simp]
lemma component_basisVector {n : ℕ} (c : Fin n → C) (b1 b2 : ComponentIdx (S := S) c) :
    (basisVector c b1).component b2 = if b1 = b2 then 1 else 0 := by
  simp only [basisVector, component_eq, funext_iff]
  simp only [Basis.repr_self]
  by_cases h : b1 = b2
  · subst h
    simp
  · rw [funext_iff] at h
    simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    split
    next h => simp_all only [not_true_eq_false]
    next h =>
      simp_all only [not_forall]
      obtain ⟨w, h⟩ := h
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Finsupp.single_eq_of_ne]
      exact fun a => hi (id (Eq.symm a))

end Pure

lemma induction_on_pure {n : ℕ} {c : Fin n → C} {P : S.Tensor c → Prop}
    (h : ∀ (p : Pure S c), P p.toTensor)
    (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t1 t2, P t1 → P t2 → P (t1 + t2)) (t : S.Tensor c) : P t := by
  refine PiTensorProduct.induction_on' t ?_ ?_
  · intro r p
    simpa using hsmul r _ (h p)
  · intro t1 t2
    exact fun a a_1 => hadd t1 t2 a a_1

/-!

## The basis

-/

noncomputable section Basis

/-- The linear map from tensors to its components. -/
def componentMap {n : ℕ} (c : Fin n → C) : S.Tensor c →ₗ[k] (ComponentIdx (S := S) c → k) :=
  PiTensorProduct.lift (Pure.componentMap c)

@[simp]
lemma componentMap_pure {n : ℕ} (c : Fin n → C)
    (p : Pure S c) : componentMap c (p.toTensor) = Pure.componentMap c p := by
  simp only [componentMap, Pure.toTensor]
  change (PiTensorProduct.lift (Pure.componentMap c)) ((PiTensorProduct.tprod k) p) = _
  simp

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
  apply induction_on_pure ?_ ?_ ?_ t
  · intro p
    simp only [componentMap_pure, Pure.componentMap_apply]
    have h1 (x : ComponentIdx c) : p.component x • (Pure.basisVector c x).toTensor =
        Pure.toTensor (fun i => ((S.basis (c i)).repr (p i)) (x i) • (S.basis (c i)) (x i)) := by
      rw [Pure.component_eq, Pure.toTensor]
      exact Eq.symm (MultilinearMap.map_smul_univ (PiTensorProduct.tprod k)
          (fun i => ((S.basis (c i)).repr (p i)) (x i)) fun i => (S.basis (c i)) (x i))
    conv_lhs =>
      enter [2, x]
      rw [h1]
    trans (PiTensorProduct.tprod k) fun i =>
      ∑ x, ((S.basis (c i)).repr (p i)) x • (S.basis (c i)) x
    · exact (MultilinearMap.map_sum (PiTensorProduct.tprod k) fun i j =>
        ((S.basis (c i)).repr (p i)) j • (S.basis (c i)) j).symm
    congr
    funext i
    exact Basis.sum_equivFun (S.basis (c i)) (p i)
  · intro r t ht
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, ← smul_smul]
    conv_rhs => rw [← ht]
    exact Eq.symm Finset.smul_sum
  · intro t1 t2 h1 h2
    simp [add_smul, Finset.sum_add_distrib, h1, h2]

/-- The basis of tensors. -/
def basis {n : ℕ} (c : Fin n → C) : Basis (ComponentIdx (S := S) c) k (S.Tensor c) where
  repr := (LinearEquiv.mk (componentMap c) (ofComponents c)
    (fun x => by simp) (fun x => by simp)).trans
    (Finsupp.linearEquivFunOnFinite k k ((j : Fin n) → Fin (S.repDim (c j)))).symm

lemma basis_apply {n : ℕ} (c : Fin n → C) (b : ComponentIdx (S := S) c) :
    basis c b = (Pure.basisVector c b).toTensor := by
  change ofComponents c _ = _
  simp only [ofComponents, LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, EquivLike.coe_coe,
    Finsupp.linearEquivFunOnFinite_single, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb
    rw [Pi.single_apply]
    simp [hb]
  · simp

@[simp]
lemma basis_repr_pure {n : ℕ} (c : Fin n → C)
    (p : Pure S c) :
    (basis c).repr p.toTensor = p.component := by
  ext b
  change componentMap c p.toTensor b = _
  simp

lemma induction_on_basis {n : ℕ} {c : Fin n → C} {P : S.Tensor c → Prop}
    (h : ∀ b, P (basis c b)) (hzero : P 0)
    (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t1 t2, P t1 → P t2 → P (t1 + t2)) (t : S.Tensor c) : P t := by
  let Pt (t : S.Tensor c)
      (ht : t ∈ Submodule.span k (Set.range (basis c))) := P t
  change Pt t (Basis.mem_span _ t)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨b, rfl⟩ := Set.mem_range.mp hx
    exact h b
  · simp [Pt, hzero]
  · intro t1 t2 h1 h2
    exact fun a a_1 => hadd t1 t2 a a_1
  · intro r t ht
    exact fun a => hsmul r t a

end Basis

/-!

## The rank

-/

lemma finrank_tensor_eq {n : ℕ} [StrongRankCondition k] (c : Fin n → C) :
    Module.finrank k (S.Tensor c) = ∏ x, S.repDim (c x) := by
  rw [(Tensor.basis c).repr.finrank_eq]
  rw [(Finsupp.linearEquivFunOnFinite _ _ _).finrank_eq]
  rw [Module.finrank_pi]
  simp

instance {k : Type} [Field k] {C G : Type} [Group G] (S : TensorSpecies k C G)
    {c : Fin n → C} : FiniteDimensional k (S.Tensor c) :=
  Module.Basis.finiteDimensional_of_finite (Tensor.basis c)

instance {k : Type} [RCLike k] {C G : Type} [Group G] (S : TensorSpecies k C G)
    {c : Fin n → C} : TopologicalSpace (S.Tensor c) :=
  moduleTopology k (S.Tensor c)

instance {k : Type} [RCLike k] {C G : Type} [Group G] (S : TensorSpecies k C G)
    {c : Fin n → C} : IsTopologicalAddGroup (S.Tensor c) :=
  IsModuleTopology.topologicalAddGroup (R := k) (S.Tensor c)

/-!

## The action
-/

namespace Pure

noncomputable instance actionP : MulAction G (Pure S c) where
  smul g p := fun i => (S.FD.obj _).ρ g (p i)
  one_smul p := by
    ext i
    change (S.FD.obj _).ρ 1 (p i) = p i
    simp
  mul_smul g g' p := by
    ext i
    change (S.FD.obj _).ρ (g * g') (p i) = (S.FD.obj _).ρ g ((S.FD.obj _).ρ g' (p i))
    simp

noncomputable instance : SMul (G) (Pure S c) := actionP.toSMul

lemma actionP_eq {g : G} {p : Pure S c} : g • p = fun i => (S.FD.obj _).ρ g (p i) := rfl

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
noncomputable instance actionT : MulAction G (S.Tensor c) where
  smul g t := (S.F.obj (OverColor.mk c)).ρ g t
  one_smul t := by
    change (S.F.obj (OverColor.mk c)).ρ 1 t = t
    simp
  mul_smul g g' t := by
    change (S.F.obj (OverColor.mk c)).ρ (g * g') t =
      (S.F.obj (OverColor.mk c)).ρ g ((S.F.obj (OverColor.mk c)).ρ g' t)
    simp

lemma actionT_eq {g : G} {t : S.Tensor c} : g • t = (S.F.obj (OverColor.mk c)).ρ g t := rfl

lemma actionT_pure {g : G} {p : Pure S c} :
    g • p.toTensor = Pure.toTensor (g • p) := by
  rw [actionT_eq, Pure.toTensor]
  simp only [F_def, lift, lift.toRepFunc, LaxBraidedFunctor.of_toFunctor]
  rw [lift.toRep_ρ_tprod]
  rfl

lemma actionT_add {g : G} {t1 t2 : S.Tensor c} :
    g • (t1 + t2) = g • t1 + g • t2 := by
  rw [actionT_eq, actionT_eq, actionT_eq]
  simp

@[simp]
lemma actionT_smul {g : G} {r : k} {t : S.Tensor c} :
    g • (r • t) = r • (g • t) := by
  rw [actionT_eq, actionT_eq (S := S)]
  simp

lemma actionT_zero {g : G} : g • (0 : S.Tensor c) = 0 := by
  simp [actionT_eq]

lemma actionT_neg {g : G} {t : S.Tensor c} :
    g • (-t) = -(g • t) := by
  rw [actionT_eq]
  simp only [map_neg, neg_inj]
  rfl

/-!

## Permutations

And their interactions with
- actions
-/

/-- Given two lists of indices `c : Fin n → C` and `c1 : Fin m → C` a map
  `σ : Fin m → Fin n` satisfies the condition `PermCond c c1 σ` if it is:
- A bijection
- Forms a commutative triangle with `c` and `c1`.
-/
def PermCond {n m : ℕ} (c : Fin n → C) (c1 : Fin m → C)
    (σ : Fin m → Fin n) : Prop :=
  Function.Bijective σ ∧ ∀ i, c (σ i) = c1 i

lemma PermCond.auto {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ := by {simp [PermCond]; try decide}) :
    PermCond c c1 σ := h

@[simp]
lemma PermCond.on_id {n : ℕ} {c c1 : Fin n → C} :
    PermCond c c1 (id : Fin n → Fin n) ↔ ∀ i, c i = c1 i := by
  simp [PermCond]

lemma PermCond.on_id_symm {n : ℕ} {c c1 : Fin n → C} (h : PermCond c1 c id) :
    PermCond c c1 (id : Fin n → Fin n) := by
  simp at h ⊢
  exact fun i => (h i).symm

/-- For a map `σ` satisfying `PermCond c c1 σ`, the inverse of that map. -/
def PermCond.inv {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : PermCond c c1 σ) : Fin n → Fin m :=
  Fintype.bijInv h.1

/-- For a map `σ : Fin m → Fin n` satisfying `PermCond c c1 σ`,
  that map lifted to an equivalence between
  `Fin n` and `Fin m`. -/
def PermCond.toEquiv {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    Fin n ≃ Fin m where
  toFun := PermCond.inv σ h
  invFun := σ
  left_inv := Fintype.rightInverse_bijInv h.1
  right_inv := Fintype.leftInverse_bijInv h.1

lemma PermCond.apply_inv_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : PermCond c c1 σ) (x : Fin m) :
    h.inv σ (σ x) = x := by
  change h.toEquiv (h.toEquiv.symm x) = x
  simp

lemma PermCond.inv_apply_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : PermCond c c1 σ) (x : Fin n) :
    σ (h.inv σ x) = x := by
  change h.toEquiv.symm (h.toEquiv x) = x
  simp

lemma PermCond.preserve_color {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    ∀ (x : Fin m), c1 x = (c ∘ σ) x := by
  intro x
  obtain ⟨y, rfl⟩ := h.toEquiv.surjective x
  simp only [Function.comp_apply]
  rw [h.2]

@[simp, nolint simpVarHead]
lemma PermCond.inv_perserve_color {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (x : Fin n) :
    c1 (h.inv σ x) = c x := by
  obtain ⟨x, rfl⟩ := h.toEquiv.symm.surjective x
  change c1 (h.toEquiv _) = _
  simp only [Equiv.apply_symm_apply]
  rw [h.preserve_color]
  rfl

lemma PermCond.symm {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    PermCond c1 c (h.inv σ) := by
  apply And.intro
  · refine Function.bijective_iff_has_inverse.mpr ?_
    use σ
    apply And.intro
    · intro x
      simp [inv_apply_apply]
    · intro x
      simp [apply_inv_apply]
  · intro x
    rw [h.inv_perserve_color]
/-- For a map `σ : Fin m → Fin n` satisfying `PermCond c c1 σ`,
  that map lifted to a morphism in the `OverColor C` category. -/
def PermCond.toHom {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    OverColor.mk c ⟶ OverColor.mk c1 :=
  equivToHomEq (h.toEquiv) (h.preserve_color)

/-- Given a morphism in the `OverColor C` between `c` and `c1` category the corresponding morphism
  `(Hom.toEquiv σ).symm` satisfies the `PermCond`. -/
lemma PermCond.ofHom {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : OverColor.mk c ⟶ OverColor.mk c1) :
    PermCond c c1 (Hom.toEquiv σ).symm := by
  apply And.intro
  · exact Equiv.bijective (Hom.toEquiv σ).symm
  · intro x
    simpa [OverColor.mk_hom] using Hom.toEquiv_symm_apply σ x

/-- The composition of two maps satisfying `PermCond` also satisfies the `PermCond`. -/
lemma PermCond.comp {n n1 n2 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C}
    {c2 : Fin n2 → C} {σ : Fin n1 → Fin n} {σ2 : Fin n2 → Fin n1}
    (h : PermCond c c1 σ) (h2 : PermCond c1 c2 σ2) :
    PermCond c c2 (σ ∘ σ2) := by
  apply And.intro
  · refine Function.Bijective.comp h.1 h2.1
  · intro x
    simp only [Function.comp_apply]
    rw [h.2, h2.2]

TODO "6VZ3C" "Prove that if `σ` satisfies `PermCond c c1 σ` then `PermCond.inv σ h`
  satisfies `PermCond c1 c (PermCond.inv σ h)`."

lemma fin_cast_permCond (n n1 : ℕ) {c : Fin n → C} (h : n1 = n) :
    PermCond c (c ∘ Fin.cast h) (Fin.cast h) := by
  apply And.intro
  · exact Equiv.bijective (finCongr h)
  · intro i
    rfl
/-!

## Permutations

-/

/-- Given a permutation `σ : Fin m → Fin n` of indices satisfying `PermCond` through `h`,
  and a pure tensor `p`, `permP σ h p` is the pure tensor permuted according to `σ`.

  For example if `m = n = 2` and `σ = ![1, 0]`, and `p = v ⊗ₜ w` then
  `permP σ _ p = w ⊗ₜ v`. -/
def Pure.permP {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : PermCond c c1 σ) (p : Pure S c) : Pure S c1 :=
  fun i => S.FD.map (eqToHom (by simp [h.preserve_color])) (p (σ i))

@[simp]
lemma Pure.permP_basisVector {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : PermCond c c1 σ) (b : ComponentIdx (S := S) c) :
    Pure.permP σ h (Pure.basisVector c b) =
    Pure.basisVector c1 (fun i => Fin.cast (by simp [h.preserve_color]) (b (σ i))) := by
  ext i
  simp only [permP, basisVector]
  have h1 {c1 c2 : C} (h : c1 = c2) (x : Fin (S.repDim c1)) :
      S.FD.map (eqToHom (by simp [h])) ((S.basis (c1)) x) =
      (S.basis c2) (Fin.cast (by simp [h]) x) := by
    subst h
    simp
  apply h1
  simp [h.preserve_color]

/-- Given a permutation `σ : Fin m → Fin n` of indices satisfying `PermCond` through `h`,
  and a tensor `t`, `permT σ h t` is the tensor tensor permuted according to `σ`. -/
noncomputable def permT {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : PermCond c c1 σ) : S.Tensor c →ₗ[k] S.Tensor c1 where
  toFun t := (ConcreteCategory.hom (S.F.map h.toHom).hom) t
  map_add' t1 t2 := by
    simp
  map_smul' r t := by
    simp

lemma permT_pure {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (p : Pure S c) :
    permT σ h p.toTensor = (p.permP σ h).toTensor := by
  simp only [F_def, permT, Pure.toTensor, LinearMap.coe_mk, AddHom.coe_mk]
  rw [OverColor.lift.map_tprod]
  rfl

@[simp]
lemma Pure.permP_id_self {n : ℕ} {c : Fin n → C} (p : Pure S c) :
    Pure.permP (id : Fin n → Fin n) (by simp : PermCond c c id) p = p := by
  ext i
  simp only [permP, Pure.permP]
  rw [eqToHom_refl]
  simp

@[simp]
lemma permT_id_self {n : ℕ} {c : Fin n → C} (t : S.Tensor c) :
    permT (id : Fin n → Fin n) (by simp : PermCond c c id) t = t := by
  let P (t : S.Tensor c) := permT (id : Fin n → Fin n) (by simp : PermCond c c id) t = t
  change P t
  apply induction_on_pure
  · intro p
    simp [P]
    rw [permT_pure]
    simp
  · intro r t ht
    simp [P, ht]
  · intro t1 t2 h1 h2
    simp [P, h1, h2]

lemma permT_congr_eq_id {n : ℕ} {c : Fin n → C} (t : S.Tensor c)
    (σ : Fin n → Fin n) (hσ : PermCond c c σ) (h : σ = id) :
    permT σ (hσ) t = t := by
  subst h
  simp

lemma permT_congr_eq_id' {n : ℕ} {c : Fin n → C} (t t1 : S.Tensor c)
    (σ : Fin n → Fin n) (hσ : PermCond c c σ) (h : σ = id) (ht : t = t1) :
    permT σ (hσ) t = t1 := by
  subst h ht
  simp

@[simp]
lemma permT_equivariant {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (g : G) (t : S.Tensor c) :
    permT σ h (g • t) = g • permT σ h t := by
  simp only [permT, actionT_eq, LinearMap.coe_mk, AddHom.coe_mk]
  exact Rep.hom_comm_apply (S.F.map h.toHom) g t

@[congr]
lemma Pure.permP_congr {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ σ1 : Fin m → Fin n} {h : PermCond c c1 σ} {h1 : PermCond c c1 σ1}
    {p p1 : Pure S c} (hmap : σ = σ1) (hpure : p = p1) :
    Pure.permP σ h p = Pure.permP σ1 h1 p1 := by
  subst hmap hpure
  rfl

@[congr]
lemma permT_congr {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ σ1 : Fin m → Fin n} {h : PermCond c c1 σ} {h1 : PermCond c c1 σ1}
    (hmap : σ = σ1) {t t1: S.Tensor c} (htensor : t = t1) :
    permT σ h t = permT σ1 h1 t1 := by
  subst hmap htensor
  rfl

@[simp]
lemma Pure.permP_permP {n m1 m2 : ℕ} {c : Fin n → C} {c1 : Fin m1 → C} {c2 : Fin m2 → C}
    {σ : Fin m1 → Fin n} {σ2 : Fin m2 → Fin m1} (h : PermCond c c1 σ) (h2 : PermCond c1 c2 σ2)
    (p : Pure S c) :
    Pure.permP σ2 h2 (Pure.permP σ h p) = Pure.permP (σ ∘ σ2) (PermCond.comp h h2) p := by
  ext i
  simp [permP, Pure.permP, Function.comp_apply, map_map_apply]

@[simp]
lemma permT_permT {n m1 m2 : ℕ} {c : Fin n → C} {c1 : Fin m1 → C} {c2 : Fin m2 → C}
    {σ : Fin m1 → Fin n} {σ2 : Fin m2 → Fin m1} (h : PermCond c c1 σ) (h2 : PermCond c1 c2 σ2)
    (t : S.Tensor c) :
    permT σ2 h2 (permT σ h t) = permT (σ ∘ σ2) (PermCond.comp h h2) t := by
  let P (t : S.Tensor c) := permT σ2 h2 (permT σ h t) = permT (σ ∘ σ2) (PermCond.comp h h2) t
  change P t
  apply induction_on_basis
  · intro b
    simp only [P]
    rw [basis_apply, permT_pure, permT_pure, permT_pure]
    simp
  · simp [P]
  · intro r t h1
    simp_all [P]
  · intro t1 t2 h1 h2
    simp_all [P]

lemma permT_basis_repr_symm_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (t : S.Tensor c)
    (b : ComponentIdx c1) :
    (basis c1).repr (permT σ h t) b =
    (basis c).repr t (fun i =>
      Fin.cast (by simp [PermCond.inv_perserve_color]) (b (h.inv σ i))) := by
  apply induction_on_basis (t := t)
  · intro b'
    rw [basis_apply]
    rw [permT_pure, Pure.permP_basisVector, ← basis_apply, ← basis_apply]
    simp only [Basis.repr_self]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    congr 1
    simp only [eq_iff_iff]
    apply Iff.intro
    · intro h'
      funext x
      conv_rhs => rw [← h']
      simp [Fin.ext_iff]
      congr
      · exact Eq.symm (PermCond.inv_apply_apply σ h x)
      · exact Eq.symm (PermCond.inv_apply_apply σ h x)
    · intro h'
      funext x
      rw [h']
      simp [Fin.ext_iff]
      congr
      · exact PermCond.apply_inv_apply σ h x
      · exact PermCond.apply_inv_apply σ h x
  · simp
  · intro r t h
    simp [h]
  · intro t1 t2 h1 h2
    simp [h1, h2]

lemma permT_eq_zero_iff {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (t : S.Tensor c) :
    permT σ h t = 0 ↔ t = 0 := by
  apply Iff.intro
  · intro h'
    trans permT (h.inv σ) (PermCond.symm h) ((permT σ h) t)
    · rw [permT_permT]
      rw [permT_congr_eq_id']
      · funext x
        simp [PermCond.inv_apply_apply]
      · rfl
    · rw [h']
      simp
  · intro hzero
    rw [hzero]
    simp

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
  erw [PiTensorProduct.isEmptyEquiv_apply_tprod]

@[simp]
lemma toField_pure {c : Fin 0 → C} (p : Pure S c) :
    toField (p.toTensor : S.Tensor c) = 1 := by
  rw [← toField_default (S := S)]
  congr
  ext i
  exact Fin.elim0 i

@[simp]
lemma toField_basis_default {c : Fin 0 → C} :
    toField (basis c (@default (ComponentIdx (S := S) c) Unique.instInhabited)) = 1 := by
  simp [basis_apply]

lemma toField_eq_repr {c : Fin 0 → C} (t : Tensor S c) :
    t.toField = (basis c).repr t (fun j => Fin.elim0 j) := by
  obtain ⟨t, rfl⟩ := (basis c).repr.symm.surjective t
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination]
  rw [@Finsupp.linearCombination_unique]
  rw [map_smul]
  conv_lhs =>
    enter [2]
    rw [toField_basis_default (c := c)]
  simp only [smul_eq_mul, mul_one]
  rfl

@[simp]
lemma toField_equivariant {c : Fin 0 → C} (g : G) (t : Tensor S c) :
    toField (g • t) = toField t := by
  apply induction_on_pure (t := t)
  · intro p
    rw [actionT_pure]
    simp
  · intro r t hp
    simp [hp]
  · intro t1 t2 hp1 hp2
    simp [hp1, hp2, actionT_add]

end Tensor

end TensorSpecies
