/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
/-!
# Pi Tensor Products

The purpose of this file is to define some results about Pi tensor products not currently
in Mathlib.

At some point these should either be up-streamed to Mathlib or replaced with definitions already
in Mathlib.

-/

@[expose] public section
namespace PhysLean.PiTensorProduct

noncomputable section tmulEquiv

variable {R ι1 ι2 ι3 M N : Type} [CommSemiring R]
  {s1 : ι1 → Type} [inst1 : (i : ι1) → AddCommMonoid (s1 i)] [inst1' : (i : ι1) → Module R (s1 i)]
  {s2 : ι2 → Type} [inst2 : (i : ι2) → AddCommMonoid (s2 i)] [inst2' : (i : ι2) → Module R (s2 i)]
  {s3 : ι3 → Type} [inst3 : (i : ι3) → AddCommMonoid (s3 i)] [inst3' : (i : ι3) → Module R (s3 i)]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

open TensorProduct

/-!

## induction principals for pi tensor products

-/
attribute [local ext] TensorProduct.ext

lemma induction_tmul {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) →ₗ[R] M}
    (h : ∀ p q, f (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)
    = g (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)) : f = g := by
  ext
  exact h _ _

lemma induction_assoc
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i) ⊗[R] (⨂[R] i : ι3, s3 i)) →ₗ[R] M}
    (h : ∀ p q m, f (PiTensorProduct.tprod R p ⊗ₜ[R]
    PiTensorProduct.tprod R q ⊗ₜ[R] PiTensorProduct.tprod R m)
    = g (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q
    ⊗ₜ[R] PiTensorProduct.tprod R m)) : f = g := by
  ext
  exact h _ _ _

lemma induction_assoc'
    {f g : (((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) ⊗[R] (⨂[R] i : ι3, s3 i)) →ₗ[R] M}
    (h : ∀ p q m, f ((PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q) ⊗ₜ[R]
    PiTensorProduct.tprod R m) = g ((PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)
    ⊗ₜ[R] PiTensorProduct.tprod R m)) : f = g := by
  ext
  exact h _ _ _

lemma induction_tmul_mod
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] N) →ₗ[R] M}
    (h : ∀ p m, f (PiTensorProduct.tprod R p ⊗ₜ[R] m) = g (PiTensorProduct.tprod R p ⊗ₜ[R] m)) :
    f = g := by
  ext
  exact h _ _

lemma induction_mod_tmul
    {f g : (N ⊗[R] (⨂[R] i : ι1, s1 i)) →ₗ[R] M}
    (h : ∀ m p, f (m ⊗ₜ[R] PiTensorProduct.tprod R p) = g (m ⊗ₜ[R] PiTensorProduct.tprod R p)) :
    f = g := by
  ext
  exact h _ _

/-!

# Dependent type version of PiTensorProduct.tmulEquiv
-/

/-- Given two maps `s1` and `s2` whose targets carry an instance of an additive commutative
  monoid, the target of the sum of these two maps also carry an instance thereof. -/
instance : (i : ι1 ⊕ ι2) → AddCommMonoid ((fun i => Sum.elim s1 s2 i) i) := fun i =>
  match i with
  | Sum.inl i => inst1 i
  | Sum.inr i => inst2 i

/-- Given two maps `s1` and `s2` whose targets carry an instance of a module over `R`,
  the target of the sum of these two maps also carry an instance thereof. -/
instance : (i : ι1 ⊕ ι2) → Module R ((fun i => Sum.elim s1 s2 i) i) := fun i =>
  match i with
  | Sum.inl i => inst1' i
  | Sum.inr i => inst2' i

/-- Takes a map `(i : ι1 ⊕ ι2) → Sum.elim s1 s2 i` to the underlying map `(i : ι1) → s1 i `. -/
def pureInl (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) : (i : ι1) → s1 i :=
  fun i => f (Sum.inl i)

/-- Takes a map `(i : ι1 ⊕ ι2) → Sum.elim s1 s2 i` to the underlying map `(i : ι2) → s2 i `. -/
def pureInr (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) : (i : ι2) → s2 i :=
  fun i => f (Sum.inr i)

section

variable [DecidableEq (ι1 ⊕ ι2)]
omit inst1 inst2

lemma pureInl_update_left [DecidableEq ι1] (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι1)
    (v1 : s1 x) : pureInl (Function.update f (Sum.inl x) v1) =
    Function.update (pureInl f) x v1 := by
  funext y
  simp only [pureInl, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  · rename_i h
    subst h
    rfl
  · rfl

lemma pureInr_update_left (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι1)
    (v2 : s1 x) :
    pureInr (Function.update f (Sum.inl x) v2) = (pureInr f) := by
  funext y
  simp [pureInr, Function.update]

lemma pureInr_update_right [DecidableEq ι2] (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι2)
    (v2 : s2 x) : pureInr (Function.update f (Sum.inr x) v2) =
    Function.update (pureInr f) x v2 := by
  funext y
  simp only [pureInr, Function.update, Sum.inr.injEq, Sum.elim_inr]
  split
  · rename_i h
    subst h
    rfl
  · rfl

lemma pureInl_update_right (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι2)
    (v1 : s2 x) :
    pureInl (Function.update f (Sum.inr x) v1) = (pureInl f) := by
  funext y
  simp [pureInl, Function.update]

end

/-- The multilinear map from `(Sum.elim s1 s2)` to `((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i)`
  defined by splitting elements of `(Sum.elim s1 s2)` into two parts. -/
def domCoprod :
    MultilinearMap R (Sum.elim s1 s2) ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) where
  toFun f := (PiTensorProduct.tprod R (pureInl f)) ⊗ₜ
    (PiTensorProduct.tprod R (pureInr f))
  map_update_add' f xy v1 v2 := by
    haveI : DecidableEq (ι1 ⊕ ι2) := inferInstance
    haveI : DecidableEq ι1 :=
      @Function.Injective.decidableEq ι1 (ι1 ⊕ ι2) Sum.inl _ Sum.inl_injective
    haveI : DecidableEq ι2 :=
      @Function.Injective.decidableEq ι2 (ι1 ⊕ ι2) Sum.inr _ Sum.inr_injective
    match xy with
    | Sum.inl xy =>
      simp only [Sum.elim_inl, pureInl_update_left, MultilinearMap.map_update_add,
        pureInr_update_left, ← add_tmul]
    | Sum.inr xy =>
      simp only [Sum.elim_inr, pureInl_update_right, pureInr_update_right,
        MultilinearMap.map_update_add, ← tmul_add]
  map_update_smul' f xy r p := by
    haveI : DecidableEq (ι1 ⊕ ι2) := inferInstance
    haveI : DecidableEq ι1 :=
      @Function.Injective.decidableEq ι1 (ι1 ⊕ ι2) Sum.inl _ Sum.inl_injective
    haveI : DecidableEq ι2 :=
      @Function.Injective.decidableEq ι2 (ι1 ⊕ ι2) Sum.inr _ Sum.inr_injective
    match xy with
    | Sum.inl x =>
      simp only [Sum.elim_inl, pureInl_update_left, MultilinearMap.map_update_smul,
        pureInr_update_left, smul_tmul, tmul_smul]
    | Sum.inr y =>
      simp only [Sum.elim_inr, pureInl_update_right, pureInr_update_right,
        MultilinearMap.map_update_smul, tmul_smul]

/-- Expand `PiTensorProduct` on sums into a `TensorProduct` of two factors. -/
def tmulSymm : (⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i) →ₗ[R]
    ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) := PiTensorProduct.lift domCoprod

/-- Produces a map `(i : ι1 ⊕ ι2) → Sum.elim s1 s2 i` from a map `(i : ι1) → s1 i` and a
  map `q : (i : ι2) → s2 i`. -/
def elimPureTensor (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i) : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i :=
  fun x =>
    match x with
    | Sum.inl x => p x
    | Sum.inr x => q x

section

variable [DecidableEq ι1] [DecidableEq ι2]
omit inst1 inst2

lemma elimPureTensor_update_right (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i)
    (y : ι2) (r : s2 y) : elimPureTensor p (Function.update q y r) =
    Function.update (elimPureTensor p q) (Sum.inr y) r := by
  funext x
  match x with
  | Sum.inl x =>
    rfl
  | Sum.inr x =>
    change Function.update q y r x = _
    simp only [Function.update, Sum.inr.injEq, Sum.elim_inr]
    split_ifs
    · rename_i h
      subst h
      rfl
    · rfl

@[simp]
lemma elimPureTensor_update_left (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i)
    (x : ι1) (r : s1 x) : elimPureTensor (Function.update p x r) q =
    Function.update (elimPureTensor p q) (Sum.inl x) r := by
  funext y
  match y with
  | Sum.inl y =>
    change (Function.update p x r) y = _
    simp only [Function.update, Sum.inl.injEq, Sum.elim_inl]
    split_ifs
    · rename_i h
      subst h
      rfl
    · rfl
  | Sum.inr y =>
    rfl

end

/-- The multilinear map valued in multilinear maps defined by combining
  `(i : ι1) → s1 i` and `q : (i : ι2) → s2 i` into a PiTensorProduct. -/
def elimPureTensorMulLin : MultilinearMap R s1
    (MultilinearMap R s2 (⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i)) where
  toFun p := {
    toFun := fun q => PiTensorProduct.tprod R (elimPureTensor p q)
    map_update_add' := fun m x v1 v2 => by
      haveI : DecidableEq ι2 := inferInstance
      haveI := Classical.decEq ι1
      simp only [elimPureTensor_update_right, MultilinearMap.map_update_add]
    map_update_smul' := fun m x r v => by
      haveI : DecidableEq ι2 := inferInstance
      haveI := Classical.decEq ι1
      simp only [elimPureTensor_update_right, MultilinearMap.map_update_smul]}
  map_update_add' p x v1 v2 := by
    haveI : DecidableEq ι1 := inferInstance
    haveI := Classical.decEq ι2
    apply MultilinearMap.ext
    intro y
    simp
  map_update_smul' p x r v := by
    haveI : DecidableEq ι1 := inferInstance
    haveI := Classical.decEq ι2
    apply MultilinearMap.ext
    intro y
    simp

/-- Collapse a `TensorProduct` of `PiTensorProduct` into a `PiTensorProduct`. -/
def tmul : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) →ₗ[R]
    ⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i := TensorProduct.lift {
    toFun := fun a ↦
      PiTensorProduct.lift <|
          PiTensorProduct.lift elimPureTensorMulLin a,
    map_add' := fun a b ↦ by simp
    map_smul' := fun r a ↦ by simp}

/-- The equivalence formed by combining a `TensorProduct` into a `PiTensorProduct`. -/
def tmulEquiv : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) ≃ₗ[R]
    ⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i :=
  LinearEquiv.ofLinear tmul tmulSymm
  (by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro p
    simp only [tmul, tmulSymm, domCoprod, LinearMap.compMultilinearMap_apply,
      LinearMap.coe_comp, Function.comp_apply, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk,
      lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [elimPureTensorMulLin, MultilinearMap.coe_mk, LinearMap.id_coe, id_eq]
    apply congrArg
    funext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  (by
    apply induction_tmul
    intro p q
    simp only [tmulSymm, domCoprod, tmul, elimPureTensorMulLin, LinearMap.coe_comp,
      Function.comp_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod,
      MultilinearMap.coe_mk, LinearMap.id_coe, id_eq]
    rfl)

@[simp]
lemma tmulEquiv_tmul_tprod (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i) :
    tmulEquiv ((PiTensorProduct.tprod R) p ⊗ₜ[R] (PiTensorProduct.tprod R) q) =
    (PiTensorProduct.tprod R) (elimPureTensor p q) := by
  simp only [tmulEquiv, tmul, elimPureTensorMulLin, LinearEquiv.ofLinear_apply, lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk]

end tmulEquiv
end PhysLean.PiTensorProduct
