/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.PauliMatrices.SelfAdjoint
import Mathlib.RepresentationTheory.Basic
import PhysLean.Relativity.LorentzGroup.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

## Modules associated with Real Lorentz vectors

We define the modules underlying real Lorentz vectors.

These definitions are preludes to the definitions of
`Lorentz.contr` and `Lorentz.co`.

-/

namespace Lorentz

noncomputable section
open Matrix Module MatrixGroups Complex

/-- The module for contravariant (up-index) real Lorentz vectors. -/
structure ContrMod (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ

namespace ContrMod

variable {d : ℕ}

@[ext]
lemma ext {ψ ψ' : ContrMod d} (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl

/-- The equivalence between `ContrℝModule` and `Fin 1 ⊕ Fin d → ℂ`. -/
def toFin1dℝFun : ContrMod d ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommMonoid (ContrMod d) := Equiv.addCommMonoid toFin1dℝFun

/-- The instance of `AddCommGroup` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommGroup (ContrMod d) := Equiv.addCommGroup toFin1dℝFun

/-- The instance of `Module` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : Module ℝ (ContrMod d) := Equiv.module ℝ toFin1dℝFun

@[simp]
lemma val_add (ψ ψ' : ContrMod d) : (ψ + ψ').val = ψ.val + ψ'.val := rfl

@[simp]
lemma val_smul (r : ℝ) (ψ : ContrMod d) : (r • ψ).val = r • ψ.val := rfl

/-- The linear equivalence between `ContrℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
def toFin1dℝEquiv : ContrMod d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  Equiv.linearEquiv ℝ toFin1dℝFun

/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `ContrℝModule` defined
  through the linear equivalence `toFin1dℝEquiv`. -/
abbrev toFin1dℝ (ψ : ContrMod d) := toFin1dℝEquiv ψ

lemma toFin1dℝ_eq_val (ψ : ContrMod d) : ψ.toFin1dℝ = ψ.val := by rfl
/-!

## The standard basis.

-/

/-- The standard basis of `ContrℝModule` indexed by `Fin 1 ⊕ Fin d`. -/
@[simps!]
def stdBasis : Basis (Fin 1 ⊕ Fin d) ℝ (ContrMod d) := Basis.ofEquivFun toFin1dℝEquiv

@[simp]
lemma stdBasis_toFin1dℝEquiv_apply_same (μ : Fin 1 ⊕ Fin d) :
    toFin1dℝEquiv (stdBasis μ) μ = 1 := by
  simp only [stdBasis, Basis.ofEquivFun, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_single]
  rw [@LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_same μ 1

@[simp]
lemma stdBasis_apply_same (μ : Fin 1 ⊕ Fin d) : (stdBasis μ).val μ = 1 :=
  stdBasis_toFin1dℝEquiv_apply_same μ

lemma stdBasis_toFin1dℝEquiv_apply_ne {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) :
    toFin1dℝEquiv (stdBasis μ) ν = 0 := by
  simp only [stdBasis, Basis.ofEquivFun, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_single]
  rw [@LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_of_ne' h 1

@[simp]
lemma stdBasis_inl_apply_inr (i : Fin d) : (stdBasis (Sum.inl 0)).val (Sum.inr i) = 0 := by
  refine stdBasis_toFin1dℝEquiv_apply_ne ?_
  simp

lemma stdBasis_apply (μ ν : Fin 1 ⊕ Fin d) : (stdBasis μ).val ν = if μ = ν then 1 else 0 := by
  simp only [stdBasis, Basis.coe_ofEquivFun]
  change Pi.single μ 1 ν = _
  simp only [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- Decomposition of a contravariant Lorentz vector into the standard basis. -/
lemma stdBasis_decomp (v : ContrMod d) : v = ∑ i, v.toFin1dℝ i • stdBasis i := by
  apply toFin1dℝEquiv.injective
  simp only [map_sum, _root_.map_smul]
  funext μ
  rw [Fintype.sum_apply μ fun c => toFin1dℝEquiv v c • toFin1dℝEquiv (stdBasis c)]
  change _ = ∑ x : Fin 1 ⊕ Fin d, toFin1dℝEquiv v x • (toFin1dℝEquiv (stdBasis x) μ)
  rw [Finset.sum_eq_single_of_mem μ (Finset.mem_univ μ)]
  · simp only [stdBasis_toFin1dℝEquiv_apply_same, smul_eq_mul, mul_one]
  · intro b _ hbμ
    rw [stdBasis_toFin1dℝEquiv_apply_ne hbμ]
    simp only [smul_eq_mul, mul_zero]

/-!

## mulVec

-/

/-- Multiplication of a matrix with a vector in `ContrMod`. -/
abbrev mulVec (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : ContrMod d) :
    ContrMod d := Matrix.toLinAlgEquiv stdBasis M v

/-- Multiplication of a matrix with a vector in `ContrMod`. -/
scoped[Lorentz] infixr:73 " *ᵥ " => ContrMod.mulVec

@[simp]
lemma mulVec_toFin1dℝ (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : ContrMod d) :
    (M *ᵥ v).toFin1dℝ = M *ᵥ v.toFin1dℝ := by
  rfl

@[simp]
lemma mulVec_val (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : ContrMod d) :
    (M *ᵥ v).val = M *ᵥ v.val := by
  rfl

lemma mulVec_sub (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v w : ContrMod d) :
    M *ᵥ (v - w) = M *ᵥ v - M *ᵥ w := by
  simp only [mulVec, LinearMap.map_sub]

lemma sub_mulVec (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : ContrMod d) :
    (M - N) *ᵥ v = M *ᵥ v - N *ᵥ v := by
  simp only [mulVec, map_sub, LinearMap.sub_apply]

lemma mulVec_add (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v w : ContrMod d) :
    M *ᵥ (v + w) = M *ᵥ v + M *ᵥ w := by
  simp only [mulVec, LinearMap.map_add]

@[simp]
lemma one_mulVec (v : ContrMod d) : (1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) *ᵥ v = v := by
  simp [mulVec, _root_.map_one]

lemma mulVec_mulVec (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : ContrMod d) :
    M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v := by
  simp [mulVec, _root_.map_mul]

/-!

## The norm

(Not the Minkowski norm, but the norm of a vector in `ContrℝModule d`.)
-/

/-- A `NormedAddCommGroup` structure on `ContrMod`. This is not an instance, as we
  don't want it to be applied always. -/
def norm : NormedAddCommGroup (ContrMod d) where
  norm v := ‖v.val‖₊
  dist_self x := Pi.normedAddCommGroup.dist_self x.val
  dist_triangle x y z := Pi.normedAddCommGroup.dist_triangle x.val y.val z.val
  dist_comm x y := Pi.normedAddCommGroup.dist_comm x.val y.val
  eq_of_dist_eq_zero {x y} := fun h => ext (MetricSpace.eq_of_dist_eq_zero h)

/-- The underlying space part of a `ContrMod` formed by removing the first element.
  A better name for this might be `tail`. -/
def toSpace (v : ContrMod d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (v.val ∘ Sum.inr)

/-!

## The representation.

-/

/-- The representation of the Lorentz group acting on `ContrℝModule d`. -/
def rep : Representation ℝ (LorentzGroup d) (ContrMod d) where
  toFun g := Matrix.toLinAlgEquiv stdBasis g
  map_one' := EmbeddingLike.map_eq_one_iff.mpr rfl
  map_mul' x y := by
    simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul]

lemma rep_apply_toFin1dℝ (g : LorentzGroup d) (ψ : ContrMod d) :
    (rep g ψ).toFin1dℝ = g.1 *ᵥ ψ.toFin1dℝ := by
  rfl

/-!

## To Self-Adjoint Matrix
-/

/-- The linear equivalence between the vector-space `ContrMod 3` and self-adjoint
  `2×2`-complex matrices. -/
def toSelfAdjoint : ContrMod 3 ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  toFin1dℝEquiv ≪≫ₗ (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin 3)).symm ≪≫ₗ
  PauliMatrix.pauliBasis'.repr.symm

open PauliMatrix in
lemma toSelfAdjoint_apply (x : ContrMod 3) : toSelfAdjoint x =
    x.toFin1dℝ (Sum.inl 0) • ⟨pauliMatrix (Sum.inl 0), pauliMatrix_selfAdjoint _⟩
    - x.toFin1dℝ (Sum.inr 0) • ⟨pauliMatrix (Sum.inr 0), pauliMatrix_selfAdjoint _⟩
    - x.toFin1dℝ (Sum.inr 1) • ⟨pauliMatrix (Sum.inr 1), pauliMatrix_selfAdjoint _⟩
    - x.toFin1dℝ (Sum.inr 2) • ⟨pauliMatrix (Sum.inr 2), pauliMatrix_selfAdjoint _⟩ := by
  simp only [toSelfAdjoint, PauliMatrix.pauliBasis', LinearEquiv.trans_apply, Basis.repr_symm_apply,
    Basis.coe_mk, Fin.isValue]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · change (∑ i : Fin 1 ⊕ Fin 3, x.toFin1dℝ i • PauliMatrix.pauliSelfAdjoint' i) = _
    simp only [pauliSelfAdjoint', Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, Fin.sum_univ_three]
    apply Subtype.ext
    simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg,
      AddSubgroupClass.coe_sub]
    simp only [add_assoc, sub_eq_add_neg]
  · simp_all only [Finset.coe_univ, Finsupp.supported_univ, Submodule.mem_top]

lemma toSelfAdjoint_apply_coe (x : ContrMod 3) : (toSelfAdjoint x).1 =
    x.toFin1dℝ (Sum.inl 0) • PauliMatrix.pauliMatrix (Sum.inl 0)
    - x.toFin1dℝ (Sum.inr 0) • PauliMatrix.pauliMatrix (Sum.inr 0)
    - x.toFin1dℝ (Sum.inr 1) • PauliMatrix.pauliMatrix (Sum.inr 1)
    - x.toFin1dℝ (Sum.inr 2) • PauliMatrix.pauliMatrix (Sum.inr 2) := by
  rw [toSelfAdjoint_apply]
  rfl

lemma toSelfAdjoint_stdBasis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjoint (stdBasis i) = PauliMatrix.pauliBasis' i := by
  rw [toSelfAdjoint_apply]
  match i with
  | Sum.inl 0 =>
    simp only [stdBasis, Fin.isValue, Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply,
      Pi.single_eq_same, one_smul, ne_eq, reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne,
      zero_smul, sub_zero, PauliMatrix.pauliBasis', Basis.coe_mk, PauliMatrix.pauliSelfAdjoint']
  | Sum.inr 0 =>
    simp only [stdBasis, Fin.isValue, Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply, ne_eq,
      reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul, Pi.single_eq_same, one_smul,
      zero_sub, Sum.inr.injEq, one_ne_zero, sub_zero, Fin.reduceEq, PauliMatrix.pauliBasis',
      Basis.coe_mk, PauliMatrix.pauliSelfAdjoint']
    rfl
  | Sum.inr 1 =>
    simp only [stdBasis, Fin.isValue, Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply, ne_eq,
      reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul, Sum.inr.injEq, zero_ne_one,
      sub_self, Pi.single_eq_same, one_smul, zero_sub, Fin.reduceEq, sub_zero,
      PauliMatrix.pauliBasis', Basis.coe_mk, PauliMatrix.pauliSelfAdjoint']
    rfl
  | Sum.inr 2 =>
    simp only [stdBasis, Fin.isValue, Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply, ne_eq,
      reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul, Sum.inr.injEq, Fin.reduceEq,
      sub_self, Pi.single_eq_same, one_smul, zero_sub, PauliMatrix.pauliBasis', Basis.coe_mk,
      PauliMatrix.pauliSelfAdjoint']
    rfl

@[simp]
lemma toSelfAdjoint_symm_basis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjoint.symm (PauliMatrix.pauliBasis' i) = (stdBasis i) := by
  refine (LinearEquiv.symm_apply_eq toSelfAdjoint).mpr ?_
  rw [toSelfAdjoint_stdBasis]

/-!
## Topology
-/

/-- The type `ContrMod d` carries an instance of a topological group, induced by
  it's equivalence to `Fin 1 ⊕ Fin d → ℝ`. -/
instance : TopologicalSpace (ContrMod d) := TopologicalSpace.induced
  ContrMod.toFin1dℝEquiv (Pi.topologicalSpace)

open Topology

lemma toFin1dℝEquiv_isInducing : IsInducing (@ContrMod.toFin1dℝEquiv d) := by
  exact { eq_induced := rfl }

lemma toFin1dℝEquiv_symm_isInducing : IsInducing ((@ContrMod.toFin1dℝEquiv d).symm) := by
  let x := Equiv.toHomeomorphOfIsInducing (@ContrMod.toFin1dℝEquiv d).toEquiv
    toFin1dℝEquiv_isInducing
  exact Homeomorph.isInducing x.symm

end ContrMod

/-- The module for covariant (up-index) complex Lorentz vectors. -/
structure CoMod (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ

namespace CoMod

variable {d : ℕ}

@[ext]
lemma ext {ψ ψ' : CoMod d} (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl

/-- The equivalence between `CoℝModule` and `Fin 1 ⊕ Fin d → ℝ`. -/
def toFin1dℝFun : CoMod d ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommMonoid (CoMod d) := Equiv.addCommMonoid toFin1dℝFun

/-- The instance of `AddCommGroup` on `CoℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommGroup (CoMod d) := Equiv.addCommGroup toFin1dℝFun

/-- The instance of `Module` on `CoℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : Module ℝ (CoMod d) := Equiv.module ℝ toFin1dℝFun

/-- The linear equivalence between `CoℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
def toFin1dℝEquiv : CoMod d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  Equiv.linearEquiv ℝ toFin1dℝFun

/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `CoℝModule` defined
  through the linear equivalence `toFin1dℝEquiv`. -/
abbrev toFin1dℝ (ψ : CoMod d) := toFin1dℝEquiv ψ

/-!

## The standard basis.

-/

/-- The standard basis of `CoℝModule` indexed by `Fin 1 ⊕ Fin d`. -/
@[simps!]
def stdBasis : Basis (Fin 1 ⊕ Fin d) ℝ (CoMod d) := Basis.ofEquivFun toFin1dℝEquiv

@[simp]
lemma stdBasis_toFin1dℝEquiv_apply_same (μ : Fin 1 ⊕ Fin d) :
    toFin1dℝEquiv (stdBasis μ) μ = 1 := by
  simp only [stdBasis, Basis.ofEquivFun, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_single]
  rw [@LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_same μ 1

@[simp]
lemma stdBasis_apply_same (μ : Fin 1 ⊕ Fin d) : (stdBasis μ).val μ = 1 :=
  stdBasis_toFin1dℝEquiv_apply_same μ

lemma stdBasis_toFin1dℝEquiv_apply_ne {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) :
    toFin1dℝEquiv (stdBasis μ) ν = 0 := by
  simp only [stdBasis, Basis.ofEquivFun, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_single]
  rw [@LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_of_ne' h 1

lemma stdBasis_apply (μ ν : Fin 1 ⊕ Fin d) : (stdBasis μ).val ν = if μ = ν then 1 else 0 := by
  simp only [stdBasis, Basis.coe_ofEquivFun]
  change Pi.single μ 1 ν = _
  simp only [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- Decomposition of a covariant Lorentz vector into the standard basis. -/
lemma stdBasis_decomp (v : CoMod d) : v = ∑ i, v.toFin1dℝ i • stdBasis i := by
  apply toFin1dℝEquiv.injective
  simp only [map_sum, _root_.map_smul]
  funext μ
  rw [Fintype.sum_apply μ fun c => toFin1dℝEquiv v c • toFin1dℝEquiv (stdBasis c)]
  change _ = ∑ x : Fin 1 ⊕ Fin d, toFin1dℝEquiv v x • (toFin1dℝEquiv (stdBasis x) μ)
  rw [Finset.sum_eq_single_of_mem μ (Finset.mem_univ μ)]
  · simp only [stdBasis_toFin1dℝEquiv_apply_same, smul_eq_mul, mul_one]
  · intro b _ hbμ
    rw [stdBasis_toFin1dℝEquiv_apply_ne hbμ]
    simp only [smul_eq_mul, mul_zero]

/-!

## mulVec

-/

/-- Multiplication of a matrix with a vector in `CoMod`. -/
abbrev mulVec (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : CoMod d) :
    CoMod d := Matrix.toLinAlgEquiv stdBasis M v

/-- Multiplication of a matrix with a vector in `CoMod`. -/
scoped[Lorentz] infixr:73 " *ᵥ " => CoMod.mulVec

@[simp]
lemma mulVec_toFin1dℝ (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : CoMod d) :
    (M *ᵥ v).toFin1dℝ = M *ᵥ v.toFin1dℝ := by
  rfl

@[simp]
lemma mulVec_val (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : CoMod d) :
    (M *ᵥ v).val = M *ᵥ v.val := by
  rfl
/-!

## The representation

-/

/-- The representation of the Lorentz group acting on `CoℝModule d`. -/
def rep : Representation ℝ (LorentzGroup d) (CoMod d) where
  toFun g := Matrix.toLinAlgEquiv stdBasis (LorentzGroup.transpose g⁻¹)
  map_one' := by
    simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe, _root_.map_one]
  map_mul' x y := by
    simp only [_root_.mul_inv_rev, LorentzGroup.inv_eq_dual, LorentzGroup.transpose_mul,
      lorentzGroupIsGroup_mul_coe, _root_.map_mul]

end CoMod

end
end Lorentz
