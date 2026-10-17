/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Modules.ConjModule
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.Ring
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
/-!
# Algebras, duals and representations on a conjugate module

The conjugate module of an algebra, the conjugate dual, and the conjugate of a representation.

## i. Overview

`Physlib.Mathematics.Modules.ConjModule` carries `ConjModule M`, the module `M` with scalars
acting through `star`, together with the conjugate-linear equivalence `conjEquiv`. This module
extends that in three directions, all of which a conjugate Weyl field needs.

First, when the module is a ring the conjugate module is a ring too, and the conjugate module
of a `k`-algebra is a `k`-algebra: the same multiplication, with scalars acting through `star`.

Second, the dual of `M` and the dual of `ConjModule M` are conjugate-linearly equivalent, by
`conjDualEquiv`, so a linear functional on a field has a conjugate functional on the conjugate
field.

Third, a representation `ρ` of `G` on `M` has a conjugate representation `ρ.conj` of `G` on
`ConjModule M`, given by the same maps `ρ g` read through `conjEquiv`. Conjugation commutes
with the constructions representations are built from: it is involutive, it passes through
products and `Pi` types, and over `ℂ` it turns a complex-linear endomorphism into its
conjugate.

## ii. Key results

- `ConjModule.instAlgebra` : the conjugate module of a `k`-algebra is a `k`-algebra.
- `ConjModule.conjDualEquiv` : the dual of `M` and the dual of `ConjModule M` are
  conjugate-linearly equivalent.
- `Representation.conj` : the conjugate of a representation.
- `ConjModule.prodEquiv`, `ConjModule.piEquiv` : conjugation commutes with products.

## iii. Table of contents

- A. The conjugate module of an algebra
- B. The conjugate dual
- C. The conjugate of a representation
- D. Functoriality, and conjugation of tensor products
- E. Endomorphisms of the conjugate module

## iv. References

The conjugate module itself is in `Physlib.Mathematics.Modules.ConjModule`.

-/

@[expose] public section

open Module
open scoped TensorProduct

variable {k : Type*} [CommRing k] [StarRing k]
variable {M : Type*} [AddCommGroup M] [Module k M]

namespace ConjModule

/-!

## A. The conjugate module of an algebra

-/

variable {A : Type*} [Ring A]

instance : Ring (ConjModule A) :=
  let i1 : AddCommGroup (ConjModule A) := inferInstanceAs (AddCommGroup (ConjModule A))
  let i2 : Ring A := inferInstanceAs (Ring A)
  { i1, i2 with }

/-- The conjugate module of a `k`-algebra is a `k`-algebra: the same ring, with scalars
acting through `star`. -/
instance instAlgebra [Algebra k A] : Algebra k (ConjModule A) :=
  Algebra.ofModule (fun r x y => smul_mul_assoc (β := A) (star r) x y)
    (fun r x y => mul_smul_comm (β := A) (star r) x y)

end ConjModule

/-!

## B. The conjugate dual

-/

/-- The canonical conjugate-linear equivalence between the dual of a module `M` and
  the dual of its conjugate. -/
def conjDualEquiv : Module.Dual k M ≃ₛₗ[starRingEnd k] Module.Dual k (ConjModule M) where
  toFun f := (starRingEnd k).toSemilinearMap.comp
    (f.comp (conjEquiv (k := k) (M := M)).symm.toLinearMap)
  invFun f := (starRingEnd k).toSemilinearMap.comp
    (f.comp (conjEquiv (k := k) (M := M)).toLinearMap)
  map_add' f g := by
    ext x
    simp
  map_smul' r f := by
    ext x
    simp
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp

namespace ConjModule

variable {ι : Type*}

/-!

## C. The conjugate of a representation

-/


/-- The conjugate of a representation `ρ` of `G` on `M`: the same maps `ρ g`, acting on
`ConjModule M` through `conjEquiv`. -/
def _root_.Representation.conj {G} [Group G] (ρ : Representation k G M) :
    Representation k G (ConjModule M) where
  toFun g := {
    toFun := conjEquiv (k := k) (M := M) ∘ ρ g ∘ (conjEquiv (k := k) (M := M)).symm
    map_add' x y := (ρ g).map_add x y
    map_smul' a m := (ρ g).map_smul (star a) m }
  map_one' := LinearMap.ext fun _ =>
    congrArg (conjEquiv (k := k)) (LinearMap.congr_fun (map_one ρ) _)
  map_mul' g h := LinearMap.ext fun _ =>
    congrArg (conjEquiv (k := k)) (LinearMap.congr_fun (map_mul ρ g h) _)

lemma _root_.Representation.conj_apply {G} [Group G] (ρ : Representation k G M) (g : G)
    (m : ConjModule M) :
    ρ.conj g m = conjEquiv (k := k) (M := M) (ρ g ((conjEquiv (k := k) (M := M)).symm m)) := rfl

/-- The conjugate of the trivial representation acts trivially. -/
@[simp] lemma _root_.Representation.conj_trivial_apply {G : Type*} [Group G] (g : G)
    (m : ConjModule M) : (Representation.trivial k G M).conj g m = m := by
  rw [Representation.conj_apply]
  simp

/-- The dual of the conjugate of the trivial representation acts trivially. -/
lemma _root_.Representation.conj_trivial_dual_apply {G : Type*} [Group G] (g : G)
    (φ : Module.Dual k (ConjModule M)) :
    ((Representation.trivial k G M).conj).dual g φ = φ := by
  ext m
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

/-!

## D. Functoriality, and conjugation of tensor products

Conjugation is monoidal: `ConjModule M ⊗ ConjModule N ≃ ConjModule (M ⊗ N)`, the identity
on pure tensors. The map is honestly `k`-linear because the twist on each factor cancels
against the twist on the target.

Everything below routes through `conjEquiv` rather than relying on definitional unfolding
of the `ConjModule` synonym. Writing `m ⊗ₜ n` for `m : ConjModule M` makes elaboration
pick the *twisted* module instances, landing in the wrong tensor product; converting
explicitly with `conjEquiv` fixes every instance by construction.

-/

variable {N : Type*} [AddCommGroup N] [Module k N]

/-- Functoriality of conjugation: a `k`-linear map induces a `k`-linear map of the
conjugate modules, given by the same underlying function. -/
def map (f : M →ₗ[k] N) : ConjModule M →ₗ[k] ConjModule N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := f.map_smul (star c) x

@[simp]
lemma map_apply (f : M →ₗ[k] N) (x : ConjModule M) : map f x = f x := rfl

/-- **Conjugation commutes with finite products.** The conjugate of a product is the product
of the conjugates, by the identity underlying function: the twisted scalar action is applied
componentwise. -/
def prodEquiv : ConjModule (M × N) ≃ₗ[k] ConjModule M × ConjModule N where
  toFun x := (map (LinearMap.fst k M N) x, map (LinearMap.snd k M N) x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := (x.1, x.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma prodEquiv_apply (x : ConjModule (M × N)) :
    prodEquiv (k := k) x = (map (LinearMap.fst k M N) x, map (LinearMap.snd k M N) x) := rfl

section Pi

variable {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

/-- **Conjugation commutes with arbitrary products.** The conjugate of a product of a
family of modules is the product of their conjugates, by the identity underlying
function: the twisted scalar action is applied componentwise, so no finiteness of the
index type is needed. -/
def piEquiv : ConjModule (∀ i, P i) ≃ₗ[k] ∀ i, ConjModule (P i) where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x i := x i
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma piEquiv_apply (x : ConjModule (∀ i, P i)) (i : ι) :
    (piEquiv P : ConjModule (∀ i, P i) ≃ₗ[k] ∀ i, ConjModule (P i)) x i
      = map (k := k) (LinearMap.proj i) x := rfl

lemma piEquiv_symm_apply (x : ∀ i, ConjModule (P i)) (i : ι) :
    map (k := k) (LinearMap.proj i)
        ((piEquiv P : ConjModule (∀ i, P i) ≃ₗ[k] ∀ i, ConjModule (P i)).symm x) = x i := rfl

end Pi

/-- The conjugate module of a finite free module is finite: the conjugated basis
`Basis.conj` is indexed by the same type. -/
instance instFinite [Module.Free k M] [Module.Finite k M] :
    Module.Finite k (ConjModule M) :=
  Module.Finite.of_basis (Basis.conj (Module.Free.chooseBasis k M))

/-- The canonical `k`-linear map `ConjModule M ⊗ ConjModule N → ConjModule (M ⊗ N)`,
the identity on pure tensors. -/
noncomputable def tensorHom : ConjModule M ⊗[k] ConjModule N →ₗ[k] ConjModule (M ⊗[k] N) :=
  TensorProduct.lift
    { toFun := fun m =>
        { toFun := fun n => conjEquiv (k := k) (M := M ⊗[k] N)
            ((conjEquiv (k := k) (M := M)).symm m ⊗ₜ[k] (conjEquiv (k := k) (M := N)).symm n)
          map_add' := by
            intro n₁ n₂
            rw [map_add, TensorProduct.tmul_add, map_add]
          map_smul' := by
            intro c n
            rw [map_smulₛₗ, TensorProduct.tmul_smul, map_smulₛₗ]
            simp }
      map_add' := by
        intro m₁ m₂
        ext n
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [map_add, TensorProduct.add_tmul, map_add]
      map_smul' := by
        intro c m
        ext n
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        rw [map_smulₛₗ, ← TensorProduct.smul_tmul', map_smulₛₗ]
        simp }

@[simp]
lemma tensorHom_tmul (m : ConjModule M) (n : ConjModule N) :
    tensorHom (k := k) (m ⊗ₜ[k] n)
      = conjEquiv (k := k) (M := M ⊗[k] N)
        ((conjEquiv (k := k) (M := M)).symm m ⊗ₜ[k] (conjEquiv (k := k) (M := N)).symm n) :=
  rfl

/-- The inverse map `ConjModule (M ⊗ N) → ConjModule M ⊗ ConjModule N`, again the identity
on pure tensors. A `k`-linear map out of `ConjModule X` is the same data as a `k`-linear
map into `ConjModule` of the target, which is what `map` and `involution` package here. -/
noncomputable def tensorInv : ConjModule (M ⊗[k] N) →ₗ[k] ConjModule M ⊗[k] ConjModule N :=
  (involution (k := k) (M := ConjModule M ⊗[k] ConjModule N)).toLinearMap ∘ₗ
    map (TensorProduct.lift
      { toFun := fun m =>
          { toFun := fun n => conjEquiv (k := k) (M := ConjModule M ⊗[k] ConjModule N)
              (conjEquiv (k := k) (M := M) m ⊗ₜ[k] conjEquiv (k := k) (M := N) n)
            map_add' := by
              intro n₁ n₂
              rw [map_add, TensorProduct.tmul_add, map_add]
            map_smul' := by
              intro c n
              rw [map_smulₛₗ, TensorProduct.tmul_smul, map_smulₛₗ]
              simp }
        map_add' := by
          intro m₁ m₂
          ext n
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [map_add, TensorProduct.add_tmul, map_add]
        map_smul' := by
          intro c m
          ext n
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
          rw [map_smulₛₗ, ← TensorProduct.smul_tmul', map_smulₛₗ]
          simp })

/-- **Conjugation is monoidal.** `ConjModule M ⊗ ConjModule N ≃ₗ[k] ConjModule (M ⊗ N)`,
the identity on pure tensors. Injectivity comes from `tensorInv` being a left inverse;
surjectivity from every element of `M ⊗ N` being a sum of pure tensors. -/
noncomputable def tensorEquiv :
    ConjModule M ⊗[k] ConjModule N ≃ₗ[k] ConjModule (M ⊗[k] N) :=
  LinearEquiv.ofBijective tensorHom
    ⟨by
      have h : ∀ w : ConjModule M ⊗[k] ConjModule N, tensorInv (tensorHom w) = w := by
        intro w
        induction w using TensorProduct.inductionOn with
        | tmul m n => rfl
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      exact Function.LeftInverse.injective h,
     by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul m n =>
          exact ⟨conjEquiv (k := k) (M := M) m ⊗ₜ[k] conjEquiv (k := k) (M := N) n, rfl⟩
      | add x y hx hy =>
          obtain ⟨w₁, h₁⟩ := hx
          obtain ⟨w₂, h₂⟩ := hy
          refine ⟨w₁ + w₂, ?_⟩
          rw [map_add, h₁, h₂]
          rfl⟩

@[simp]
lemma tensorEquiv_tmul (m : ConjModule M) (n : ConjModule N) :
    tensorEquiv (k := k) (m ⊗ₜ[k] n)
      = conjEquiv (k := k) (M := M ⊗[k] N)
        ((conjEquiv (k := k) (M := M)).symm m ⊗ₜ[k] (conjEquiv (k := k) (M := N)).symm n) :=
  rfl

@[simp]
lemma tensorEquiv_symm_conjEquiv_tmul (m : M) (n : N) :
    (tensorEquiv (k := k) (M := M) (N := N)).symm
        (conjEquiv (k := k) (M := M ⊗[k] N) (m ⊗ₜ[k] n))
      = conjEquiv (k := k) (M := M) m ⊗ₜ[k] conjEquiv (k := k) (M := N) n := by
  rw [LinearEquiv.symm_apply_eq, tensorEquiv_tmul]
  simp

/-!

## E. Endomorphisms of the conjugate module

An endomorphism of `M` is read on `ConjModule M` through `conjEquiv`. Conjugating twists
nothing at the level of the additive group, so the structural identities hold
definitionally; only the real-scalar one needs an argument.

-/

/-- A linear endomorphism read on the conjugate module: the same underlying map,
  through the identity `conjEquiv`. Conjugating twists nothing at the level of the
  additive group, so all structural identities (`comp`, `add`, `neg`, sums) hold
  definitionally. -/
def endConj {k : Type*} [CommRing k] [StarRing k] {M : Type*}
    [AddCommGroup M] [Module k M] (f : M →ₗ[k] M) :
    ConjModule M →ₗ[k] ConjModule M where
  toFun v := conjEquiv (k := k) (M := M) (f ((conjEquiv (k := k) (M := M)).symm v))
  map_add' v w := f.map_add v w
  map_smul' a v := f.map_smul (star a) v

@[simp]
lemma endConj_apply {k : Type*} [CommRing k] [StarRing k] {M : Type*}
    [AddCommGroup M] [Module k M] (f : M →ₗ[k] M) (v : ConjModule M) :
    ConjModule.endConj f v =
      conjEquiv (k := k) (M := M) (f ((conjEquiv (k := k) (M := M)).symm v)) := rfl

lemma endConj_id {k : Type*} [CommRing k] [StarRing k] {M : Type*}
    [AddCommGroup M] [Module k M] :
    ConjModule.endConj (LinearMap.id : M →ₗ[k] M) = LinearMap.id := rfl

lemma endConj_comp {k : Type*} [CommRing k] [StarRing k] {M : Type*}
    [AddCommGroup M] [Module k M] (f g : M →ₗ[k] M) :
    ConjModule.endConj (f ∘ₗ g) = ConjModule.endConj f ∘ₗ ConjModule.endConj g := rfl

lemma endConj_add {k : Type*} [CommRing k] [StarRing k] {M : Type*}
    [AddCommGroup M] [Module k M] (f g : M →ₗ[k] M) :
    ConjModule.endConj (f + g) = ConjModule.endConj f + ConjModule.endConj g := rfl

lemma endConj_neg {k : Type*} [CommRing k] [StarRing k] {M : Type*}
    [AddCommGroup M] [Module k M] (f : M →ₗ[k] M) :
    ConjModule.endConj (-f) = -ConjModule.endConj f := rfl

lemma endConj_multiset_sum {k : Type*} [CommRing k] [StarRing k]
    {M : Type*} [AddCommGroup M] [Module k M] (S : Multiset (M →ₗ[k] M)) :
    ConjModule.endConj S.sum = (S.map ConjModule.endConj).sum := by
  induction S using Multiset.induction_on with
  | empty => rfl
  | cons f S ih =>
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        ConjModule.endConj_add, ih]

/-- Conjugation of endomorphisms commutes with real scalars: the star on the
  conjugated complex scalar is invisible on the reals. -/
lemma endConj_real_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (r : ℝ) (f : M →ₗ[ℂ] M) :
    ConjModule.endConj (r • f) = r • ConjModule.endConj f := by
  refine LinearMap.ext fun v => ?_
  show (algebraMap ℝ ℂ r) • (f ((conjEquiv (k := ℂ) (M := M)).symm v))
      = (starRingEnd ℂ) (algebraMap ℝ ℂ r) • (f ((conjEquiv (k := ℂ) (M := M)).symm v))
  rw [show (starRingEnd ℂ) (algebraMap ℝ ℂ r) = algebraMap ℝ ℂ r from
    Complex.conj_ofReal r]

end ConjModule
