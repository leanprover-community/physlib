/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!

# Complex Lorentz tensors from real Lorentz tensors

## i. Overview

In this module we describe how to pass from real Lorentz tensors to complex Lorentz tensors
in a functorial way.
Specifically, we construct a canonical equivariant semilinear map

* `toComplex : ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c)`

which is compatible with the natural operations on tensors (permutations of
indices, tensor products, contractions and evaluations).

## ii. Key results

The main definitions and statements are:

* `colorToComplex` upgrades the colour of a real Lorentz tensor to the
  corresponding complex Lorentz colour.
* `TensorSpecies.Tensor.ComponentIdx.complexify` transports component indices
  along `colorToComplex`.
* `toComplex` is the basic semilinear map from real to complex Lorentz tensors.
* `toComplex_basis` and `toComplex_pure_basisVector` show that `toComplex`
  sends basis tensors to basis tensors.
* `toComplex_eq_zero_iff` and `toComplex_injective` show that `toComplex` is
  injective.
* `toComplex_equivariant` states that `toComplex` is equivariant for the action
  of the complexified Lorentz group.
* `permT_toComplex`, `prodT_toComplex`, `contrT_toComplex` and `evalT_toComplex`
  express that `toComplex` commutes with the basic tensor operations.

## iii. Table of contents

* A. Colours and component indices
* B. The semilinear map `toComplex`
  * B.1. Expression in the tensor basis
  * B.2. Behaviour on basis vectors and injectivity
  * B.3. Equivariance under the Lorentz action
* C. Compatibility with permutations: `permT`
* D. Compatibility with tensor products: `prodT`
* E. Compatibility with contraction: `contrT`
* F. Compatibility with evaluation: `evalT`

## iv. References

* None — the general formalism of Lorentz tensors and their operations is
  developed in other parts of the library; here we only specialise to the
  passage from real to complex Lorentz tensors.
-/

@[expose] public section

namespace realLorentzTensor

open Module TensorSpecies
open Tensor
open complexLorentzTensor

/-!

## A. Colours and component indices

We first explain how the Lorentz colour data and component indices for real
tensors are transported to the complex setting.

-/

/-- The map from colors of real Lorentz tensors to complex Lorentz tensors. -/
def colorToComplex (c : realLorentzTensor.Color) : complexLorentzTensor.Color :=
  match c with
  | .up => .up
  | .down => .down

lemma repDim_colorToComplex {c : realLorentzTensor.Color} :
    complexLorentzTensor.repDim (colorToComplex c) = 4 := by
  cases c <;> rfl

/-- `simp` helper: reduce `match c j` after a case split on `c j`
  (avoids dependent `rw` / `Pi.smul_apply`). -/
lemma colorToComplex_match_up {n} {c : Fin n → realLorentzTensor.Color} {j}
    (hc : c j = realLorentzTensor.Color.up) :
    (match c j with
      | .up => complexLorentzTensor.Color.up
      | .down => complexLorentzTensor.Color.down)
      = complexLorentzTensor.Color.up := by
  rw [hc]

lemma colorToComplex_match_down {n} {c : Fin n → realLorentzTensor.Color} {j}
    (hc : c j = realLorentzTensor.Color.down) :
    (match c j with
      | .up => complexLorentzTensor.Color.up
      | .down => complexLorentzTensor.Color.down)
      = complexLorentzTensor.Color.down := by
  rw [hc]

lemma colorToComplex_comp_eq_match {n} (c : Fin n → realLorentzTensor.Color) (j : Fin n) :
    (colorToComplex ∘ c) j =
      (match c j with
        | .up => complexLorentzTensor.Color.up
        | .down => complexLorentzTensor.Color.down) := by
  cases hc : c j <;> simp [colorToComplex, hc]

/-- The complexification of the component index of a real Lorentz tensor to
  a complex Lorentz tensor. -/
noncomputable def _root_.TensorSpecies.Tensor.ComponentIdx.complexify {n}
    {c : Fin n → realLorentzTensor.Color} :
    ComponentIdx (S := realLorentzTensor) c ≃
      ComponentIdx (S := complexLorentzTensor) (colorToComplex ∘ c) where
  toFun b := fun j => Fin.cast repDim_colorToComplex.symm (finSumFinEquiv (b j))
  invFun i := fun j => finSumFinEquiv.symm <| Fin.cast repDim_colorToComplex (i j)
  left_inv i := by simp
  right_inv i := by simp

@[simp]
lemma ComponentIdx.complexify_apply {n} {c : Fin n → realLorentzTensor.Color}
    (f : ComponentIdx (S := realLorentzTensor) c) (j : Fin n) :
    (ComponentIdx.complexify f) j = Fin.cast repDim_colorToComplex.symm (finSumFinEquiv (f j)) :=
  rfl

@[simp]
lemma ComponentIdx.complexify_toFun_apply {n} {c : Fin n → realLorentzTensor.Color}
    (f : ComponentIdx (S := realLorentzTensor) c) (j : Fin n) :
    (ComponentIdx.complexify.toFun f) j = (ComponentIdx.complexify f) j :=
  rfl

/-!

## B. The semilinear map `toComplex`

We now define the basic semilinear map from real Lorentz tensors to complex
Lorentz tensors. It is characterised by sending the standard tensor basis on
the real side to the corresponding basis on the complex side, and is therefore
determined by the behaviour on components.

-/

/-- The semilinear map from real Lorentz tensors to complex Lorentz tensors,
  defined through basis. -/
noncomputable def toComplex {n} {c : Fin n → realLorentzTensor.Color} :
    ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c) where
  toFun v := ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v i •
    Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i.complexify
  map_smul' c v := by
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofRealHom_eq_coe]
    rw [Finset.smul_sum]
    congr
    funext i
    rw [← smul_smul]
    rfl
  map_add' c v := by
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr
    funext i
    simp [add_smul]

lemma toComplex_eq_sum_basis {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v
      (ComponentIdx.complexify.symm i) •
      Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i := by
  rw [← Equiv.sum_comp ComponentIdx.complexify]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- The representation of `toComplex v` in the complexified basis equals
  the real representation coerced to complex. -/
lemma toComplex_repr {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (i : ComponentIdx (S := realLorentzTensor) c) :
    (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)).repr
      (toComplex v) i.complexify =
    ↑((Tensor.basis (S := realLorentzTensor) c).repr v i) := by
  rw [toComplex_eq_sum_basis, map_sum]
  simp only [← Complex.coe_smul, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Equiv.symm_apply_apply]

/-- `toComplex` sends basis elements to basis elements. -/
@[simp]
lemma toComplex_basis {n} {c : Fin n → realLorentzTensor.Color}
    (i : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c) ((Tensor.basis (S := realLorentzTensor) c) i) =
      (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)) i.complexify := by
  simp only [toComplex, LinearMap.coe_mk, AddHom.coe_mk]
  simp [Finsupp.single_apply, ite_smul]

/-- `toComplex` on a pure basis vector. -/
@[simp]
lemma toComplex_pure_basisVector {n} {c : Fin n → realLorentzTensor.Color}
    (b : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c) (Pure.basisVector c b |>.toTensor)
      =
    (Pure.basisVector (colorToComplex ∘ c) b.complexify).toTensor := by
  simp [← Tensor.basis_apply]

lemma toComplex_map_smul {n} (c : Fin n → realLorentzTensor.Color) (r : ℝ) (t : ℝT(3, c)) :
    toComplex (c := c) (r • t) = (Complex.ofReal r) • toComplex (c := c) t :=
  (toComplex (c := c)).map_smulₛₗ r t

@[simp]
lemma toComplex_eq_zero_iff {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (Tensor.basis (S := realLorentzTensor) c).repr.injective
    ext i
    simpa [h] using (toComplex_repr v i).symm
  · rintro rfl
    simp

/-- The map `toComplex` is injective. -/
lemma toComplex_injective {n} (c : Fin n → realLorentzTensor.Color) :
    Function.Injective (toComplex (c := c)) :=
  (injective_iff_map_eq_zero' toComplex).mpr (toComplex_eq_zero_iff c)

open Matrix
open MatrixGroups
open CategoryTheory
open complexLorentzTensor
open Lorentz.SL2C
/-!

## pure
-/

set_option backward.isDefEq.respectTransparency false in
/-- For a given color, the map turning a real Lorentz vector into a complex one. -/
noncomputable def toComplexVector (c : realLorentzTensor.Color) :
  realLorentzTensor.modules 3 c →ₛₗ[Complex.ofRealHom] complexLorentzTensor.modules
    (colorToComplex c) where
  toFun v := match c with
    | Color.up => ∑ i, ((Lorentz.contrBasis 3).repr v i) •
      Lorentz.complexContrBasisFin4 (finSumFinEquiv i)
    | Color.down => ∑ i, ((Lorentz.coBasis 3).repr v i) •
      Lorentz.complexCoBasisFin4 (finSumFinEquiv i)
  map_add' v1 v2 := by
    match c with
    | Color.up =>
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, Nat.reduceAdd, ← Finset.sum_add_distrib]
      congr
      funext x
      rw [add_smul]
    | Color.down =>
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, Nat.reduceAdd, ← Finset.sum_add_distrib]
      congr
      funext x
      rw [add_smul]
  map_smul' r v := by
    match c with
    | Color.up =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.reduceAdd,
        Complex.ofRealHom_eq_coe, Complex.coe_smul]
      rw [Finset.smul_sum]
      congr
      funext x
      rw [← smul_smul]
    | Color.down =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.reduceAdd,
        Complex.ofRealHom_eq_coe, Complex.coe_smul]
      rw [Finset.smul_sum]
      congr
      funext x
      rw [← smul_smul]

lemma toComplexVector_up_eq_inclCongrRealLorentz (v : Lorentz.ContrMod 3) :
    toComplexVector Color.up v = Lorentz.inclCongrRealLorentz v := by
  trans ∑ i, v.toFin1dℝ i • Lorentz.complexContrBasis i
  · simp [toComplexVector, Lorentz.contrBasis_repr_apply,
      Lorentz.complexContrBasisFin4, Lorentz.ContrMod.toFin1dℝ_eq_val]
  · conv_rhs => rw [Lorentz.ContrMod.stdBasis_decomp v]
    simp only [map_sum, LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe, Complex.coe_smul,
      Lorentz.complexContrBasis_of_real]
    rfl

lemma toComplexVector_down_eq_inclCoRealLorentz (v : Lorentz.CoMod 3) :
    toComplexVector Color.down v = Lorentz.inclCoRealLorentz v := by
  trans ∑ i, v.toFin1dℝ i • Lorentz.complexCoBasis i
  · simp [toComplexVector, Lorentz.coBasis_repr_apply, Lorentz.complexCoBasisFin4]
    rfl
  · conv_rhs => rw [Lorentz.CoMod.stdBasis_decomp v]
    simp only [map_sum, LinearMap.map_smulₛₗ, Complex.ofRealHom_eq_coe, Complex.coe_smul,
      Lorentz.complexCoBasis_of_real]
    rfl

/-- The function which turns a real pure tensor into a complex one. -/
noncomputable def toComplexPure {c : Fin n → Color} (p : Pure realLorentzTensor c) :
    Pure complexLorentzTensor (colorToComplex ∘ c) := fun i =>
  toComplexVector (c i) (p i)

lemma toComplexPure_component {c : Fin n → Color} (p : Pure realLorentzTensor c)
    (φ : ComponentIdx c) : (toComplexPure p).component (ComponentIdx.complexify φ) =
      p.component φ := by
  simp [Pure.component, toComplexPure]
  congr
  funext x
  generalize φ x = φx at *
  generalize p x = px at *
  clear φ p
  generalize_proofs h1 h2 h3
  let b (c : Color) : Basis (Fin (complexLorentzTensor.repDim (colorToComplex c))) ℂ
      (complexLorentzTensor.modules (colorToComplex c)) :=
    match colorToComplex c with
    | Color.upL => Fermion.LeftHandedWeyl.basis
    | Color.downL => Fermion.DualLeftHandedWeyl.basis
    | Color.upR => Fermion.RightHandedWeyl.basis
    | Color.downR => Fermion.DualRightHandedWeyl.basis
    | complexLorentzTensor.Color.up => Lorentz.complexContrBasisFin4
    | complexLorentzTensor.Color.down => Lorentz.complexCoBasisFin4
  let b' (c : Color) : Basis (Fin 1 ⊕ Fin 3) ℝ (realLorentzTensor.modules 3 c) :=
    (match c with
      | Color.up => Lorentz.contrBasis
      | Color.down => Lorentz.coBasis : Basis (Fin 1 ⊕ Fin 3) ℝ (realLorentzTensor.modules 3 c))
  let P (c : Color) (px : realLorentzTensor.modules 3 c) (φx : Fin 1 ⊕ Fin 3)
    (h2 : 4 = repDim (colorToComplex c)) : Prop :=
    ((b c).repr
      (toComplexVector c px))
    (Fin.cast h2 (finSumFinEquiv φx)) =
  ↑(((b' c).repr
        px)
      φx)
  suffices h : P (c x) px φx h2 by exact h
  generalize c x = c at *
  fin_cases c
  · simp only [colorToComplex, toComplexVector, Nat.reduceAdd, Fin.cast_eq_self, P, b, b']
    trans (∑ x, (Lorentz.complexContrBasisFin4.repr ((Lorentz.contrBasis.repr px) x •
        Lorentz.complexContrBasisFin4 (finSumFinEquiv x))))
      (finSumFinEquiv φx)
    · simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Nat.reduceAdd, Finsupp.coe_add, Finsupp.coe_finsetSum, Pi.add_apply,
      Finset.sum_apply]
      rfl
    simp [- Fintype.sum_sum_type, Lorentz.complexContrBasisFin4]
    trans ∑ x, (((Lorentz.contrBasis.repr px) x • Lorentz.complexContrBasis.repr
      (Lorentz.complexContrBasis x) φx))
    · simp [Basis.repr_self, Complex.real_smul]
      rfl
    simp [- Fintype.sum_sum_type, Finsupp.single_apply]
  · simp only [colorToComplex, toComplexVector, Nat.reduceAdd, Fin.cast_eq_self, P, b, b']
    trans (∑ x, (Lorentz.complexCoBasisFin4.repr ((Lorentz.coBasis.repr px) x •
      Lorentz.complexCoBasisFin4 (finSumFinEquiv x))))
      (finSumFinEquiv φx)
    · simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Nat.reduceAdd, Finsupp.coe_add, Finsupp.coe_finsetSum, Pi.add_apply,
      Finset.sum_apply]
      rfl
    simp [- Fintype.sum_sum_type, Lorentz.complexCoBasisFin4]
    trans ∑ x, (((Lorentz.coBasis.repr px) x •
      Lorentz.complexCoBasis.repr (Lorentz.complexCoBasis x) φx))
    · simp [Basis.repr_self, Complex.real_smul]
      rfl
    simp [- Fintype.sum_sum_type, Finsupp.single_apply]

lemma actionP_toComplexPure {n : ℕ} (c : Fin n → Color) (p : Pure realLorentzTensor c)
    (Λ : SL(2, ℂ)) :
    Λ • toComplexPure p = toComplexPure (toLorentzGroup Λ • p) := by
  ext i
  simp [Pure.actionP_eq, toComplexPure]
  let b (c : Color) : Representation ℂ _ (complexLorentzTensor.modules (colorToComplex c)) :=
    match colorToComplex c with
    | Color.upL => Fermion.LeftHandedWeyl.rep
    | Color.downL => Fermion.DualLeftHandedWeyl.rep
    | Color.upR => Fermion.RightHandedWeyl.rep
    | Color.downR => Fermion.DualRightHandedWeyl.rep
    | complexLorentzTensor.Color.up => Lorentz.ContrℂModule.SL2CRep
    | complexLorentzTensor.Color.down => Lorentz.CoℂModule.SL2CRep
  let b' (c : Color) : Representation ℝ _ (realLorentzTensor.modules 3 c) :=
    (match c with
    | Color.up => Lorentz.ContrMod.rep
    | Color.down => Lorentz.CoMod.rep)
  let P (c : Color) (px : realLorentzTensor.modules 3 c) : Prop :=
    b c Λ (toComplexVector c px) = toComplexVector c (b' c (toLorentzGroup Λ) px)
  change P (c i) (p i)
  generalize p i = p at *
  generalize c i = c at *
  fin_cases c
  · simp_all [P, b, b', colorToComplex]
    exact ((congrArg (Lorentz.ContrℂModule.SL2CRep Λ)
      (toComplexVector_up_eq_inclCongrRealLorentz p)).trans
        (Lorentz.inclCongrRealLorentz_ρ Λ p)).trans
      (toComplexVector_up_eq_inclCongrRealLorentz _).symm
  · simp_all [P, b, b', colorToComplex]
    exact ((congrArg (Lorentz.CoℂModule.SL2CRep Λ)
      (toComplexVector_down_eq_inclCoRealLorentz p)).trans
        (Lorentz.inclCoRealLorentz_ρ Λ p)).trans
      (toComplexVector_down_eq_inclCoRealLorentz _).symm

lemma toComplex_pure {n : ℕ} (c : Fin n → Color) (p : Pure realLorentzTensor c) :
    toComplex p.toTensor = (toComplexPure p).toTensor := by
  apply (Tensor.basis _).repr.injective
  ext φ
  obtain ⟨φ, rfl⟩ := TensorSpecies.Tensor.ComponentIdx.complexify.surjective φ
  simp [toComplex_repr, toComplexPure_component]

/-!

### B.3. Equivariance under the Lorentz action

Finally we record that `toComplex` is equivariant for the natural action of
`SL(2, ℂ)` (and hence the induced Lorentz action) on tensors.

-/

/-- The map `toComplex` is equivariant. -/
lemma toComplex_equivariant {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (Λ : SL(2, ℂ)) :
    Λ • (toComplex v) = toComplex (Lorentz.SL2C.toLorentzGroup Λ • v) := by
  induction' v using induction_on_pure with p r t h t1 t2
  · rw [actionT_pure, toComplex_pure, actionT_pure, actionP_toComplexPure, toComplex_pure]
  · simpa [← h] using actionT_smul (g := Λ) (r := (r : ℂ)) (t := toComplex t)
  · simp_all

/-!

## C. Compatibility with permutations: `permT`

We first show that complexification is compatible with permutation of tensor
slots. On colours this is encoded in the `IsReindexing` predicate, and on tensors
by the operator `permT`.

-/

/-- The `IsReindexing` condition is preserved under `colorToComplex`. -/
@[simp] lemma isReindexing_colorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) :
    IsReindexing (colorToComplex ∘ c) (colorToComplex ∘ c1) σ :=
  ⟨h.1, fun i => congrArg colorToComplex (h.2 i)⟩

/-- `permT` sends basis vectors to basis vectors. -/
@[simp] lemma permT_basis_real {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ)
    (b : ComponentIdx (S := realLorentzTensor) c) :
    permT (S := realLorentzTensor) σ h ((Tensor.basis (S := realLorentzTensor) c) b)
    = (Tensor.basis (S := realLorentzTensor) c1)
      (fun j => b (σ j)) := by
  simp [Tensor.basis_apply, permT_pure, Pure.permP_basisVector]

@[simp] lemma permT_basis_complex {n m : ℕ}
    {c : Fin n → complexLorentzTensor.Color} {c1 : Fin m → complexLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ)
    (b : ComponentIdx (S := complexLorentzTensor) c) :
    permT (S := complexLorentzTensor) σ h ((Tensor.basis (S := complexLorentzTensor) c) b)
      =
    (Tensor.basis (S := complexLorentzTensor) c1)
      (fun j => Fin.cast
        (by
          -- from the color agreement we get the repDim agreement
          -- if one has `h.2 j : c1 j = c (σ j)`, then replace it with `(h.2 j).symm`
          simpa using congrArg (fun col => complexLorentzTensor.repDim col) (h.2 j))
        (b (σ j))) := by
  simp [Tensor.basis_apply, permT_pure, Pure.permP_basisVector, basisIdxCongr_eq_cast]

set_option backward.isDefEq.respectTransparency false in
/-- The map `toComplex` commutes with permT. -/
lemma permT_toComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (t : ℝT(3, c)) :
    toComplex (permT (S := realLorentzTensor) σ h t)
      =
    permT (S := complexLorentzTensor) σ (isReindexing_colorToComplex (c := c) (c1 := c1) h)
      (toComplex (c := c) t) := by
  induction t using induction_on_basis with
  | h b =>
    simp only [permT_basis_real, toComplex_basis, permT_basis_complex]
    apply congrArg (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c1))
    funext j
    simp [TensorSpecies.Tensor.ComponentIdx.complexify, colorToComplex, Function.comp_apply]
  | hzero => simp
  | hsmul r t ht => simp [map_smul, ht]
  | hadd t1 t2 h1 h2 => simp [map_add, h1, h2]

/-!

### D. Compatibility with tensor products: `prodT`

-/

/-- `colorToComplex` commutes with `Fin.append` (as functions). -/
@[simp]
lemma colorToComplex_append {n m : ℕ}
    (c : Fin n → realLorentzTensor.Color) (c1 : Fin m → realLorentzTensor.Color) :
    (colorToComplex ∘ Fin.append c c1) = Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x <;> simp [Fin.append]

lemma isReindexing_prodTColorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color} :
    IsReindexing (Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1))
      (colorToComplex ∘ Fin.append c c1)
      (id : Fin (n + m) → Fin (n + m)) :=
  ⟨Function.bijective_id, fun i => (congrFun (colorToComplex_append c c1) i).symm⟩

/-- `prodT` on the complex side, with colors written as `colorToComplex ∘ Fin.append ...`.
This is `prodT` followed by a cast using `colorToComplex_append`. -/
noncomputable def prodTColorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color} :
    ℂT(colorToComplex ∘ c) → ℂT(colorToComplex ∘ c1) → ℂT(colorToComplex ∘ Fin.append c c1) :=
  fun x y =>
    permT (S := complexLorentzTensor) (σ := (id : Fin (n + m) → Fin (n + m)))
      (isReindexing_prodTColorToComplex (c := c) (c1 := c1))
      (prodT (S := complexLorentzTensor) x y)

private lemma cast_componentIdx_apply {n : ℕ} {c c' : Fin n → complexLorentzTensor.Color}
    (h : c' = c) (f : ComponentIdx (S := complexLorentzTensor) c') (x : Fin n) :
    (cast (congr_arg ComponentIdx h) f) x =
      Fin.cast (congr_arg (fun c => complexLorentzTensor.repDim (c x)) h) (f x) := by
  subst h
  rfl

@[simp]
private lemma cast_componentIdx_eq_fun {n : ℕ}
    {c c' : Fin n → complexLorentzTensor.Color}
    (h : c' = c) (f : ComponentIdx (S := complexLorentzTensor) c') :
    cast (congr_arg ComponentIdx h) f =
      (fun x =>
        Fin.cast (congr_arg (fun col => complexLorentzTensor.repDim (col x)) h) (f x)) :=
  funext fun x => cast_componentIdx_apply h f x

set_option backward.isDefEq.respectTransparency false in
/-- `complexify` commutes with `prod` of component indices. -/
@[simp]
lemma complexify_prod {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    (b : ComponentIdx (S := realLorentzTensor) c)
    (b1 : ComponentIdx (S := realLorentzTensor) c1) :
    ComponentIdx.complexify (c := Fin.append c c1) (ComponentIdx.prod.symm (b, b1))
      =
    cast (congr_arg ComponentIdx (colorToComplex_append c c1).symm)
      (ComponentIdx.prod.symm (ComponentIdx.complexify (c := c) b,
        ComponentIdx.complexify (c := c1) b1)) := by
  ext x
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  cases i
  all_goals
    rw [ComponentIdx.complexify_apply]
    simp [ComponentIdx.prod]
    erw [basisIdxCongr_eq_cast]
    simp

/-- The map `toComplex` commutes with prodT. -/
lemma prodT_toComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    (t : ℝT(3, c)) (t1 : ℝT(3, c1)) :
    toComplex (c := Fin.append c c1) (prodT (S := realLorentzTensor) t t1)
      =
    prodTColorToComplex (c := c) (c1 := c1)
      (toComplex (c := c) t) (toComplex (c := c1) t1) := by
  -- Double induction on the tensor basis: first over `t`, then over `t1`. The zero, scalar and
  -- additive cases follow from linearity of `prodT`, `toComplex` and `prodTColorToComplex`.
  induction t using induction_on_basis with
  | h b =>
    induction t1 using induction_on_basis with
    | h b1 =>
      simp [prodTColorToComplex, prodT_pure, permT_pure, Pure.prodP_basisVector,
        Pure.permP_basisVector, Tensor.basis_apply, toComplex_pure_basisVector,
        colorToComplex_append, basisIdxCongr_eq_cast]
    | hzero => simp [prodTColorToComplex]
    | hsmul r ta hta => simp [map_smul, hta, prodTColorToComplex]
    | hadd ta tb hta htb => simp [map_add, hta, htb, prodTColorToComplex]
  | hzero => simp [prodTColorToComplex]
  | hsmul r ta hta => simp [map_smul, hta, prodTColorToComplex]
  | hadd ta tb hta htb => simp [map_add, hta, htb, prodTColorToComplex]

/-!

### E. Compatibility with contraction: `contrT`

-/

/-- `τ` commutes with `colorToComplex` on the Lorentz `up/down` colors. -/
@[simp]
lemma tau_colorToComplex (x : realLorentzTensor.Color) :
    (complexLorentzTensor).τ (colorToComplex x) = colorToComplex ((realLorentzTensor).τ x) := by
  cases x <;> rfl

/-- `complexify` commutes with precomposition by `succSuccAbove`.
  We use `fun k => b (Fin.succSuccAbove i j k)` and direct application
  `(ComponentIdx.complexify b) (Fin.succSuccAbove i j m)` rather than composition so that
  dependent `ComponentIdx` types unify correctly (avoiding `Function.comp` type mismatch). -/
@[simp]
lemma ComponentIdx.complexify_comp_succSuccAbove
    {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} (b : ComponentIdx (S := realLorentzTensor) c) (m : Fin n) :
    (ComponentIdx.complexify (c := c ∘ Fin.succSuccAbove i j)
      (fun k => b (Fin.succSuccAbove i j k))) m =
    (ComponentIdx.complexify (c := c) b) (Fin.succSuccAbove i j m) := by
  simp only [ComponentIdx.complexify_apply, Function.comp_apply]

/-- For a real basis vector, `toComplex(contrP(basisVector c b))` equals
  `contrP(basisVector (colorToComplex ∘ c) (complexify b))` (complex species). -/
lemma toComplex_contrP_basisVector {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} (h : i ≠ j ∧ (realLorentzTensor).τ (c i) = c j)
    (b : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c ∘ Fin.succSuccAbove i j)
      (Pure.contrP (S := realLorentzTensor) i j h (Pure.basisVector c b))
      =
    Pure.contrP (S := complexLorentzTensor) i j
      (by
        simpa [Function.comp_apply] using And.intro h.1
          (by simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
      (Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b)) := by
  let c' := c ∘ Fin.succSuccAbove i j
  simp only [Pure.contrP]
  rw [toComplex_map_smul c' (Pure.contrPCoeff i j h (Pure.basisVector c b))
    ((Pure.dropPair i j h.1 (Pure.basisVector c b)).toTensor),
    Pure.dropPair_basisVector (c := c),
    ← Tensor.basis_apply (S := realLorentzTensor) c' (fun k => b (Fin.succSuccAbove i j k)),
    toComplex_basis (c := c') (i := fun k => b (Fin.succSuccAbove i j k))]
  congr 1
  · -- contrPCoeff: real and complex both equal 0 or 1 with same condition
    rw [contrPCoeff_basis, complexLorentzTensor.contrPCoeff_basis]
    simp only [Function.comp_apply, ComponentIdx.complexify_apply, Nat.reduceAdd, Fin.cast_cast,
      Fin.cast_inj, EmbeddingLike.apply_eq_iff_eq]
    split <;> simp_all
  · -- complexify(fun k => b (succSuccAbove k)) = (complexify b) ∘ succSuccAbove
    rw [Pure.dropPair_basisVector, ← Tensor.basis_apply]
    exact congr_arg _ (funext fun m => ComponentIdx.complexify_comp_succSuccAbove b m)

/-- The map `toComplex` commutes with `contrT`. -/
lemma contrT_toComplex {n : ℕ}
    {c : Fin (n + 1 + 1) → realLorentzTensor.Color} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ (realLorentzTensor).τ (c i) = c j) (t : ℝT(3, c)) :
    toComplex (c := c ∘ Fin.succSuccAbove i j) (contrT (S := realLorentzTensor) n i j h t)
      =
    contrT (S := complexLorentzTensor) n i j (by
        simpa [Function.comp_apply] using
          And.intro h.1 (by
            simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
      (toComplex (c := c) t) := by
  induction t using induction_on_basis with
  | h b =>
    rw [Tensor.basis_apply (S := realLorentzTensor) c b,
      contrT_pure (S := realLorentzTensor) (p := Pure.basisVector c b),
      toComplex_pure_basisVector (c := c) b,
      contrT_pure (S := complexLorentzTensor)
        (p := Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b))]
    exact toComplex_contrP_basisVector h b
  | hzero => simp
  | hsmul r t ht => simp [map_smul, ht]
  | hadd t1 t2 h1 h2 => simp [map_add, h1, h2]

/-!

### F. Compatibility with evaluation: `evalT`

-/

/-- `complexify` commutes with precomposition by `succAbove`. -/
@[simp]
lemma ComponentIdx.complexify_comp_succAbove
    {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : ComponentIdx (S := realLorentzTensor) c) (m : Fin n) :
    (ComponentIdx.complexify (c := c ∘ i.succAbove) (fun k => b (i.succAbove k))) m =
    (ComponentIdx.complexify (c := c) b) (i.succAbove m) := by
  simp only [ComponentIdx.complexify_apply, Function.comp_apply]

/-- Convert an evaluation index from the real repDim to the complex repDim. -/
noncomputable def evalIdxToComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : Fin 1 ⊕ Fin 3) : Fin (complexLorentzTensor.repDim ((colorToComplex ∘ c) i)) :=
  Fin.cast repDim_colorToComplex.symm (finSumFinEquiv b)

/-- `evalT` on the complex side, but with output colors as `colorToComplex ∘ (c ∘ i.succAbove)`.
Implemented via `permT (σ := id) (by simp)` as a transport. -/
noncomputable def evalTColorToComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : Fin 1 ⊕ Fin 3) :
    ℂT(colorToComplex ∘ c) → ℂT(colorToComplex ∘ (c ∘ i.succAbove)) :=
  fun t =>
    permT (S := complexLorentzTensor) (σ := (id : Fin n → Fin n))
      (by
        -- transport ((colorToComplex ∘ c) ∘ i.succAbove) and (colorToComplex ∘ (c ∘ i.succAbove))
        simp [Function.comp_apply])
      ((TensorSpecies.Tensor.evalT (S := complexLorentzTensor) (c := (colorToComplex ∘ c))
          i (evalIdxToComplex (c := c) i b)) t)

set_option backward.isDefEq.respectTransparency false in
/-- For a real basis vector, `toComplex(evalP(basisVector c b))` equals
  `evalP(basisVector (colorToComplex ∘ c) (complexify b))` (complex species). -/
lemma toComplex_evalP_basisVector {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin 1 ⊕ Fin 3)
    (b' : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c ∘ i.succAbove)
      (Pure.evalP (S := realLorentzTensor) i b (Pure.basisVector c b'))
      =
    permT (S := complexLorentzTensor) (σ := (id : Fin n → Fin n))
      (by simp [Function.comp_apply])
      (Pure.evalP (S := complexLorentzTensor) i (evalIdxToComplex (c := c) i b)
        (Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b'))) := by
  simp only [Pure.evalP]
  have hdrop : (Pure.basisVector c b').drop i =
    Pure.basisVector (c ∘ i.succAbove) (fun k => b' (i.succAbove k)) := by
    ext j; simp only [Pure.drop, Pure.basisVector, Function.comp_apply]
  rw [hdrop, toComplex_map_smul (c ∘ i.succAbove) (Pure.evalPCoeff i b (Pure.basisVector c b'))
    ((Pure.basisVector (c ∘ i.succAbove)) (fun k => b' (i.succAbove k)) |>.toTensor)]
  · -- evalPCoeff: real and complex match; then tensor equality
    simp only [Pure.evalPCoeff, Pure.basisVector, Basis.repr_self, Finsupp.single_apply,
      ComponentIdx.complexify_apply, evalIdxToComplex]
    · by_cases h : b' i = b
      · simp [h]
        have hdrop' : (Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b')).drop i =
          Pure.basisVector (colorToComplex ∘ (c ∘ i.succAbove))
            (ComponentIdx.complexify (c := c ∘ i.succAbove) (fun k => b' (i.succAbove k))) := by
          ext j; simp only [Pure.drop, Pure.basisVector, ComponentIdx.complexify_apply,
            Function.comp_apply]
        rw [hdrop']
        exact (permT_id_self _).symm
      · simp [h]

/-- The map `toComplex` commutes with `evalT`. -/
lemma evalT_toComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin 1 ⊕ Fin 3) (t : ℝT(3, c)) :
    toComplex (c := c ∘ i.succAbove)
        ((TensorSpecies.Tensor.evalT (S := realLorentzTensor) (c := c) i b) t)
      =
    evalTColorToComplex (c := c) i b (toComplex (c := c) t) := by
  induction t using induction_on_basis with
  | h b' =>
    rw [Tensor.basis_apply (S := realLorentzTensor) c b']
    simp only [evalTColorToComplex]
    rw [evalT_pure (S := realLorentzTensor) (p := Pure.basisVector c b'),
      toComplex_pure_basisVector (c := c) b',
      evalT_pure (S := complexLorentzTensor)
        (p := Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b'))]
    exact toComplex_evalP_basisVector i b b'
  | hzero => simp [evalTColorToComplex]
  | hsmul r t' ht' => simp [evalTColorToComplex, ht']
  | hadd t1 t2 h1 h2 => simp [evalTColorToComplex, h1, h2]

end realLorentzTensor
