/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.AdjointCoeff
public import PhyslibAlpha.Mathematics.MultisetAntidiagonal
/-!
# The bracket of adjoint families

Families of symbols with one adjoint index, valued in an arbitrary algebra, and their bracket.

## i. Overview

A gauge field in an algebra `B` of local expressions is a family of symbols `A^φ`, indexed by a
dual vector `φ` of the gauge algebra, that is a linear map
`Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B`. Such an adjoint family is assembled into a field in
`B ⊗ G.lieSubalgebra` by `dualPairEquiv`, so that its adjoint index can be contracted with the
Lie bracket. This gives the bracket of two families, `bracketFam`, the physicists'
`f^a_{bc} f^b g^c`, and the derived commutators `commutatorFam`, the Leibniz convolutions
`∂_s ⁅A_μ, A_ν⁆` of the derivative symbols.

Nothing here assumes that `B` is commutative, and no gauge action is part of the data. The
gauge action enters only in `repGauge_bracketFam`, for an action by multiplicative maps. The field
strength and the covariant derivative in the adjoint are built from these formulas in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.CovariantDeriv`.

## ii. Key results

- `GaugeBoson.dualPairEquiv`, `GaugeBoson.tensorBracket` : the tensor bookkeeping of the
  adjoint index.
- `GaugeBoson.bracketFam` : the bracket of two adjoint families.
- `GaugeBoson.commutatorFam` : the derived commutators `∂_s ⁅A_μ, A_ν⁆`.
- `GaugeBoson.repGauge_bracketFam` : the gauge transformation of a bracket of two families with
  affine transformation laws.
- `GaugeBoson.bracketFam_adjointDualCoeff` : the bracket against the dual adjoint Taylor
  coefficients of a jet.
- `GaugeBoson.massWeightEigenspace`, `GaugeBoson.anticommuteSubmodule` : the submodules through
  which the mass weights and the statistics of covariant towers are checked term by term.

## iii. Table of contents

- A. Pure-tensor computations for `dualPairEquiv` and `tensorBracket`
- B. The bracket of general component families
- C. Antisymmetry and order of the derived commutators
- D. The gauge transformation of a bracket
- E. Iterated Leibniz expansions
- F. The bracket of families against the adjoint coefficients
- G. Mass-weight eigenspaces and anticommutants

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct
variable {B : Type} [Ring B]
variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

namespace GaugeBoson

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

/-- The canonical equivalence, through finite-dimensional duality, between
  algebra-valued fields `B ⊗ G.lieSubalgebra` and their component families `φ ↦ A^φ`, the element
  `b ⊗ a` corresponds to the family `φ ↦ φ(a) b`. -/
noncomputable def dualPairEquiv :
    (B ⊗[ℝ] G.lieSubalgebra) ≃ₗ[ℝ] (Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :=
  TensorProduct.comm ℝ B G.lieSubalgebra ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv ℝ G.lieSubalgebra) (LinearEquiv.refl ℝ B) ≪≫ₗ
    dualTensorHomEquiv ℝ (Module.Dual ℝ G.lieSubalgebra) B

/-- The bracket of two algebra-valued fields, multiplication in `B` on the first
  factors, the Lie bracket of the gauge algebra on the second, so that on pure
  tensors `⁅b₁ ⊗ a₁, b₂ ⊗ a₂⁆ = (b₁ b₂) ⊗ ⁅a₁, a₂⁆`. -/
noncomputable def tensorBracket :
    (B ⊗[ℝ] G.lieSubalgebra) →ₗ[ℝ] (B ⊗[ℝ] G.lieSubalgebra) →ₗ[ℝ] B ⊗[ℝ] G.lieSubalgebra :=
  TensorProduct.curry
    ((TensorProduct.map (TensorProduct.lift (LinearMap.mul ℝ B))
        (TensorProduct.lift (LinearMap.mk₂ ℝ (fun a b => ⁅a, b⁆)
          (fun a a' b => add_lie a a' b) (fun t a b => smul_lie t a b)
          (fun a b b' => lie_add a b b') (fun t a b => lie_smul t a b)))) ∘ₗ
      (TensorProduct.tensorTensorTensorComm ℝ B G.lieSubalgebra B G.lieSubalgebra).toLinearMap)

/-- The commutator term `⁅A_μ, A_ν⁆` of the field strength, as a component family. It is
  the physicists' `f^a_{bc} A_μ^b A_ν^c` contracted with a dual adjoint vector, without a
  basis. The two fields are assembled into `B ⊗ G.lieSubalgebra` by `dualPairEquiv.symm`,
  bracketed there by `tensorBracket`, and read back out as components. -/
noncomputable def commutator
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm (A 0 μ)) (dualPairEquiv.symm (A 0 ν)))

end RealScalars

/-!

## A. Pure-tensor computations for `dualPairEquiv` and `tensorBracket`

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
@[simp]
lemma dualPairEquiv_tmul (b : B) (a : G.lieSubalgebra) (φ : Module.Dual ℝ G.lieSubalgebra) :
    dualPairEquiv (b ⊗ₜ[ℝ] a) φ = φ a • b := by
  simp [dualPairEquiv, dualTensorHomEquiv, Module.evalEquiv_apply]

@[simp]
lemma tensorBracket_tmul (b₁ b₂ : B) (a₁ a₂ : G.lieSubalgebra) :
    tensorBracket (b₁ ⊗ₜ[ℝ] a₁) (b₂ ⊗ₜ[ℝ] a₂) = (b₁ * b₂) ⊗ₜ[ℝ] ⁅a₁, a₂⁆ := by
  simp [tensorBracket, TensorProduct.tensorTensorTensorComm_tmul]

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
lemma dualPairEquiv_map_left (Φ : B →ₗ[ℝ] B) (t : B ⊗[ℝ] G.lieSubalgebra)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    dualPairEquiv ((TensorProduct.map Φ LinearMap.id) t) φ = Φ (dualPairEquiv t φ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
lemma dualPairEquiv_map_right (T : G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra)
    (t : B ⊗[ℝ] G.lieSubalgebra) (φ : Module.Dual ℝ G.lieSubalgebra) :
    dualPairEquiv ((TensorProduct.map LinearMap.id T) t) φ =
      dualPairEquiv t (T.dualMap φ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
lemma symm_comp_left (Φ : B →ₗ[ℝ] B) (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm (Φ ∘ₗ f) =
      (TensorProduct.map Φ LinearMap.id) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_left, LinearEquiv.apply_symm_apply]
  rfl

omit [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] in
lemma symm_comp_right (T : G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra)
    (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    dualPairEquiv.symm (f ∘ₗ T.dualMap) =
      (TensorProduct.map LinearMap.id T) (dualPairEquiv.symm f) := by
  apply dualPairEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  rw [dualPairEquiv_map_right, LinearEquiv.apply_symm_apply]
  rfl

lemma tensorBracket_map_left (Φ : B →ₗ[ℝ] B)
    (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂) (s t : B ⊗[ℝ] G.lieSubalgebra) :
    tensorBracket ((TensorProduct.map Φ LinearMap.id) s)
        ((TensorProduct.map Φ LinearMap.id) t) =
      (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) := by
  induction s using TensorProduct.inductionOn with
  | tmul b₁ a₁ =>
      induction t using TensorProduct.inductionOn with
      | tmul b₂ a₂ => simp [hΦ]
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma tensorBracket_one_right (c : G.lieSubalgebra) (s : B ⊗[ℝ] G.lieSubalgebra) :
    tensorBracket s ((1 : B) ⊗ₜ[ℝ] c) =
      -(TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ G.lieSubalgebra c)) s := by
  induction s using TensorProduct.inductionOn with
  | tmul b a =>
      rw [tensorBracket_tmul, mul_one, ← lie_skew, TensorProduct.tmul_neg]
      simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hy]
      abel

lemma tensorBracket_one_left (c : G.lieSubalgebra) (t : B ⊗[ℝ] G.lieSubalgebra) :
    tensorBracket ((1 : B) ⊗ₜ[ℝ] c) t =
      (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ G.lieSubalgebra c)) t := by
  induction t using TensorProduct.inductionOn with
  | tmul b a => simp
  | add x y hx hy => simp [hx, hy]

end RealScalars

section ComplexScalars

variable [Algebra ℂ B]

lemma dualPairEquiv_one_tmul (c : G.lieSubalgebra) (φ : Module.Dual ℝ G.lieSubalgebra) :
    dualPairEquiv ((1 : B) ⊗ₜ[ℝ] c) φ = algebraMap ℂ B (φ c) := by
  rw [dualPairEquiv_tmul, Algebra.algebraMap_eq_smul_one,
    show ((φ c : ℝ) : ℂ) = algebraMap ℝ ℂ (φ c) from rfl, algebraMap_smul]

end ComplexScalars

/-!

## B. The bracket of general component families

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

/-- The bracket of two arbitrary component families, generalizing `commutator` (which
  is the case of two field symbols). The families are assembled into `B ⊗ G.lieSubalgebra`
  by `dualPairEquiv.symm`, bracketed by `tensorBracket`, and read back out as components. -/
noncomputable def bracketFam (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  dualPairEquiv (tensorBracket (dualPairEquiv.symm f) (dualPairEquiv.symm g))

lemma commutator_eq_bracketFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : commutator A μ ν = bracketFam (A 0 μ) (A 0 ν) := rfl

/-- The derived commutator family, the `s`-derivative of the commutator term, given
  by the Leibniz convolution of the derivative symbols over the multiset antidiagonal.
  With the derivative symbols as primitives this convolution is the definition. For
  `s = 0` it is the commutator itself (`commutatorFam_zero`). -/
noncomputable def commutatorFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  (s.antidiagonal.map fun p => bracketFam (A p.1 μ) (A p.2 ν)).sum

lemma commutatorFam_zero
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) : commutatorFam A μ ν 0 = commutator A μ ν := by
  rw [commutatorFam, Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton, commutator_eq_bracketFam]

lemma bracketFam_add_left (f₁ f₂ g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam (f₁ + f₂) g = bracketFam f₁ g + bracketFam f₂ g := by
  simp only [bracketFam, map_add, LinearMap.add_apply]

lemma bracketFam_add_right (f g₁ g₂ : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam f (g₁ + g₂) = bracketFam f g₁ + bracketFam f g₂ := by
  simp only [bracketFam, map_add]

lemma bracketFam_smul_left (c : ℝ) (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam (c • f) g = c • bracketFam f g := by
  simp only [bracketFam, map_smul, LinearMap.smul_apply]

lemma bracketFam_smul_right (c : ℝ) (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam f (c • g) = c • bracketFam f g := by
  simp only [bracketFam, map_smul]

/-- The bracket of two component families expanded through a basis of the gauge
  algebra, the physicists' `f^a_{bc} f^b g^c`, with `φ⁅e_j, e_k⁆` the structure
  constants contracted with the dual vector. -/
lemma bracketFam_apply_eq_sum (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    bracketFam f g φ = ∑ j, ∑ k,
      φ ⁅Module.Free.chooseBasis ℝ G.lieSubalgebra j,
          Module.Free.chooseBasis ℝ G.lieSubalgebra k⁆ •
        (f ((Module.Free.chooseBasis ℝ G.lieSubalgebra).coord j) *
          g ((Module.Free.chooseBasis ℝ G.lieSubalgebra).coord k)) := by
  classical
  set bv := Module.Free.chooseBasis ℝ G.lieSubalgebra with hbv
  have hdual : ∀ ψ : Module.Dual ℝ G.lieSubalgebra, ∑ j, ψ (bv j) • bv.coord j = ψ := by
    intro ψ
    refine LinearMap.ext fun x => ?_
    conv_rhs => rw [← bv.sum_repr x, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul, map_smul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hbasis : ∀ h : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B,
      dualPairEquiv.symm h = ∑ j, h (bv.coord j) ⊗ₜ[ℝ] bv j := by
    intro h
    apply dualPairEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    refine LinearMap.ext fun ψ => ?_
    calc h ψ = h (∑ j, ψ (bv j) • bv.coord j) := by rw [hdual]
      _ = ∑ j, ψ (bv j) • h (bv.coord j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => map_smul h _ _
      _ = dualPairEquiv (∑ j, h (bv.coord j) ⊗ₜ[ℝ] bv j) ψ := by simp
  rw [bracketFam, hbasis f, hbasis g]
  simp [tensorBracket_tmul, dualPairEquiv_tmul]
  rw [Finset.sum_comm]

/-- A dual vector vanishing on every bracket of the gauge algebra, such as the coordinate of an
  abelian factor, vanishes on the bracket of any two families. Every structure constant
  `φ⁅e_j, e_k⁆` it sees is zero. -/
lemma bracketFam_apply_eq_zero_of_map_lie {φ : Module.Dual ℝ G.lieSubalgebra}
    (hφ : ∀ x y : G.lieSubalgebra, φ ⁅x, y⁆ = 0) (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam f g φ = 0 := by
  simp [bracketFam_apply_eq_sum, hφ]

/-- The bracket of families is natural in the algebra. A multiplicative linear map carries
  the bracket of two families to the bracket of their images. -/
lemma bracketFam_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam (Φ ∘ₗ f) (Φ ∘ₗ g) = Φ ∘ₗ bracketFam f g := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, bracketFam_apply_eq_sum, bracketFam_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hΦ]
  rfl

/-- The derived commutator family is natural in the algebra. -/
lemma commutatorFam_map {B' : Type} [Ring B'] [Module ℝ B'] [SMulCommClass ℝ B' B']
    [IsScalarTower ℝ B' B'] (Φ : B →ₗ[ℝ] B') (hΦ : ∀ b₁ b₂, Φ (b₁ * b₂) = Φ b₁ * Φ b₂)
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    commutatorFam (fun p ρ => Φ ∘ₗ A p ρ) μ ν s = Φ ∘ₗ commutatorFam A μ ν s := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, commutatorFam, commutatorFam, Multiset.sum_linearMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Multiset.map_map, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [bracketFam_map Φ hΦ]
  rfl

/-- `tensorBracket` is a derivation in the algebra factor. For `Δ` satisfying the
  Leibniz rule on `B`, applying `Δ ⊗ id` to a bracket distributes over the two
  arguments. -/
lemma tensorBracket_map_left_derivation (Δ : B →ₗ[ℝ] B)
    (hΔ : ∀ b₁ b₂, Δ (b₁ * b₂) = Δ b₁ * b₂ + b₁ * Δ b₂) (s t : B ⊗[ℝ] G.lieSubalgebra) :
    (TensorProduct.map Δ LinearMap.id) (tensorBracket s t) =
      tensorBracket ((TensorProduct.map Δ LinearMap.id) s) t +
      tensorBracket s ((TensorProduct.map Δ LinearMap.id) t) := by
  induction s using TensorProduct.inductionOn with
  | tmul b₁ a₁ =>
      induction t using TensorProduct.inductionOn with
      | tmul b₂ a₂ => simp [hΔ, TensorProduct.add_tmul]
      | add x y hx hy =>
          simp only [map_add, hx, hy]
          abel
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
      abel

/-- The bracket of families under a derivation of the algebra, the Leibniz rule, in
  family form. -/
lemma bracketFam_derivation (Δ : B →ₗ[ℝ] B)
    (hΔ : ∀ b₁ b₂, Δ (b₁ * b₂) = Δ b₁ * b₂ + b₁ * Δ b₂)
      (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    Δ ∘ₗ bracketFam f g = bracketFam (Δ ∘ₗ f) g + bracketFam f (Δ ∘ₗ g) := by
  refine LinearMap.ext fun φ => ?_
  show Δ (dualPairEquiv (tensorBracket (dualPairEquiv.symm f) (dualPairEquiv.symm g)) φ) = _
  rw [← dualPairEquiv_map_left, tensorBracket_map_left_derivation Δ hΔ, map_add,
    LinearMap.add_apply, ← symm_comp_left, ← symm_comp_left]
  rfl

end RealScalars

/-!

## C. Antisymmetry and order of the derived commutators

The bracket of two families is antisymmetric as soon as the values of the two families
commute, and every derived commutator is a polynomial in symbols of no higher order.

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

/-- The bracket of two component families with commuting values is antisymmetric. In
  the basis expansion the structure constants are antisymmetric in the two gauge
  indices, and the two field factors of each term may be exchanged. -/
lemma bracketFam_swap_of_commute {f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hfg : ∀ φ ψ, Commute (f φ) (g ψ)) :
    bracketFam g f = - bracketFam f g := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.neg_apply, bracketFam_apply_eq_sum, bracketFam_apply_eq_sum]
  set bv := Module.Free.chooseBasis ℝ G.lieSubalgebra with hbv
  have hstep : ∀ j k, φ ⁅bv j, bv k⁆ • (g (bv.coord j) * f (bv.coord k)) =
      -(φ ⁅bv k, bv j⁆ • (f (bv.coord k) * g (bv.coord j))) := by
    intro j k
    rw [(hfg (bv.coord k) (bv.coord j)).eq, ← lie_skew (bv k) (bv j), map_neg,
      neg_smul, neg_neg]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hstep j k]
  simp only [Finset.sum_neg_distrib]
  exact congrArg Neg.neg Finset.sum_comm

/-- The derived commutator term is antisymmetric in its two directions when the symbols
  of the gauge field commute. Swapping the two parts of the antidiagonal matches the
  Leibniz convolution with the swapped one termwise. -/
lemma commutatorFam_swap
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (hA : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
      (ψ ψ' : Module.Dual ℝ G.lieSubalgebra), Commute (A s μ ψ) (A s' μ' ψ'))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    commutatorFam A ν μ s = - commutatorFam A μ ν s := by
  rw [commutatorFam, commutatorFam,
    Multiset.sum_antidiagonal_swap s (fun a b => bracketFam (A a ν) (A b μ)),
    ← Multiset.sum_map_neg'']
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ =>
    bracketFam_swap_of_commute fun φ ψ => hA _ _ _ _ _ _)

/-- The bracket of families is odd in its second argument. -/
lemma bracketFam_neg_right (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam f (-g) = - bracketFam f g := by
  rw [← neg_one_smul ℝ g, bracketFam_smul_right]
  ext φ
  simp

end RealScalars

section ComplexScalars

variable [Algebra ℂ B]

/-- Every derived commutator term is a polynomial in derivative symbols of order at
  most that of the derivative. Each Leibniz splitting contributes a product of two
  lower-order symbols. -/
lemma commutatorFam_mem
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (ν lam : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    commutatorFam A ν lam s' φ ∈
      Algebra.adjoin ℂ {b : B | ∃ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
        (φ : Module.Dual ℝ G.lieSubalgebra), p.card ≤ s'.card ∧ b = A p μ φ} := by
  classical
  rw [commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine multiset_sum_mem _ fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  have hle := Multiset.mem_antidiagonal.mp hp
  rw [Function.comp_apply, bracketFam_apply_eq_sum]
  refine Subalgebra.sum_mem _ fun j _ => Subalgebra.sum_mem _ fun k _ => ?_
  rw [← algebraMap_smul ℂ (φ ⁅Module.Free.chooseBasis ℝ G.lieSubalgebra j,
      Module.Free.chooseBasis ℝ G.lieSubalgebra k⁆)]
  refine Subalgebra.smul_mem _ ?_ _
  refine mul_mem
    (Algebra.subset_adjoin ⟨p.1, ν, (Module.Free.chooseBasis ℝ G.lieSubalgebra).coord j, ?_, rfl⟩)
    (Algebra.subset_adjoin ⟨p.2, lam, (Module.Free.chooseBasis ℝ G.lieSubalgebra).coord k, ?_, rfl⟩)
  · exact hle ▸ Multiset.card_le_card (Multiset.le_add_right _ _)
  · exact hle ▸ Multiset.card_le_card (Multiset.le_add_left _ _)

end ComplexScalars

/-!

## D. The gauge transformation of a bracket

-/

section ComplexScalars

variable [Algebra ℂ B] {repGauge : Representation ℂ G.gaugeJetGroup B}

/-- An affine transformation law of a family, read on the field it assembles. If `Φ` sends
  each component `f ψ` to `f' ψ + ψ(c)·1`, then `Φ ⊗ id` sends the field of `f` to the field of
  `f'` plus `1 ⊗ c`. -/
lemma map_dualPairEquiv_symm_of_affine (Φ : B →ₗ[ℝ] B)
    {f f' : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B} {c : G.lieSubalgebra}
    (hf : ∀ ψ : Module.Dual ℝ G.lieSubalgebra, Φ (f ψ) = f' ψ + algebraMap ℂ B (ψ c)) :
    (TensorProduct.map Φ LinearMap.id) (dualPairEquiv.symm f) =
      dualPairEquiv.symm f' + (1 : B) ⊗ₜ[ℝ] c := by
  rw [← symm_comp_left, show Φ ∘ₗ f = f' + dualPairEquiv ((1 : B) ⊗ₜ[ℝ] c) from
      LinearMap.ext fun ψ => by
        rw [LinearMap.comp_apply, LinearMap.add_apply, hf ψ, dualPairEquiv_one_tmul],
    map_add, LinearEquiv.symm_apply_apply]

/-- The bracket of two fields shifted by constant fields `1 ⊗ c_f` and `1 ⊗ c_g`. It is the
  bracket of the unshifted fields, two `ad` cross terms, and the constant bracket. -/
lemma tensorBracket_add_one_tmul (s t : B ⊗[ℝ] G.lieSubalgebra) (cf cg : G.lieSubalgebra) :
    tensorBracket (s + (1 : B) ⊗ₜ[ℝ] cf) (t + (1 : B) ⊗ₜ[ℝ] cg) =
      tensorBracket s t
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ G.lieSubalgebra cf)) t
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ G.lieSubalgebra cg)) s
      + (1 : B) ⊗ₜ[ℝ] ⁅cf, cg⁆ := by
  simp only [map_add, LinearMap.add_apply]
  rw [tensorBracket_one_right, tensorBracket_one_left, tensorBracket_tmul, one_mul]
  abel

/-- The gauge transformation of the bracket of two component families with affine
  transformation laws `f ↦ f' + φ(c_f)·1` and `g ↦ g' + φ(c_g)·1` is the bracket of the
  transformed families, two `ad` cross terms, and the constant bracket `⁅c_f, c_g⁆`.
  Pure bilinearity, with `tensorBracket_add_one_tmul` computing the cross terms. Only the
  multiplicativity of the action of `U` is used. -/
lemma repGauge_bracketFam
    (U : G.gaugeJetGroup)
    (hmul : ∀ b₁ b₂ : B, repGauge U (b₁ * b₂) = repGauge U b₁ * repGauge U b₂)
    {f g f' g' : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    {cf cg : G.lieSubalgebra}
    (hf : ∀ ψ : Module.Dual ℝ G.lieSubalgebra,
      repGauge U (f ψ) = f' ψ + algebraMap ℂ B (ψ cf))
    (hg : ∀ ψ : Module.Dual ℝ G.lieSubalgebra,
      repGauge U (g ψ) = g' ψ + algebraMap ℂ B (ψ cg))
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    repGauge U (bracketFam f g φ) =
      bracketFam f' g' φ
      + g' (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra cf)
      - f' (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra cg)
      + algebraMap ℂ B (φ ⁅cf, cg⁆) := by
  set Φ : B →ₗ[ℝ] B := (repGauge U).restrictScalars ℝ with hΦdef
  have hΦmul : ∀ b₁ b₂ : B, Φ (b₁ * b₂) = Φ b₁ * Φ b₂ := hmul
  set s : B ⊗[ℝ] G.lieSubalgebra := dualPairEquiv.symm f with hs
  set t : B ⊗[ℝ] G.lieSubalgebra := dualPairEquiv.symm g with ht
  set s' : B ⊗[ℝ] G.lieSubalgebra := dualPairEquiv.symm f' with hs'
  set t' : B ⊗[ℝ] G.lieSubalgebra := dualPairEquiv.symm g' with ht'
  have hfm : (TensorProduct.map Φ LinearMap.id) s = s' + (1 : B) ⊗ₜ[ℝ] cf := by
    rw [hs, hs']; exact map_dualPairEquiv_symm_of_affine Φ hf
  have hgm : (TensorProduct.map Φ LinearMap.id) t = t' + (1 : B) ⊗ₜ[ℝ] cg := by
    rw [ht, ht']; exact map_dualPairEquiv_symm_of_affine Φ hg
  have hbra : dualPairEquiv (tensorBracket s t) = bracketFam f g := by
    rw [hs, ht]; rfl
  have hbra' : dualPairEquiv (tensorBracket s' t') = bracketFam f' g' := by
    rw [hs', ht']; rfl
  have hπs' : dualPairEquiv s' = f' := by
    rw [hs']; exact dualPairEquiv.apply_symm_apply _
  have hπt' : dualPairEquiv t' = g' := by
    rw [ht']; exact dualPairEquiv.apply_symm_apply _
  clear_value Φ s t s' t'
  have htensor : (TensorProduct.map Φ LinearMap.id) (tensorBracket s t) =
      tensorBracket s' t'
      + (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ G.lieSubalgebra cf)) t'
      - (TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ G.lieSubalgebra cg)) s'
      + (1 : B) ⊗ₜ[ℝ] ⁅cf, cg⁆ := by
    exact (tensorBracket_map_left Φ hΦmul s t).symm.trans
      ((congrArg₂ (fun X Y => tensorBracket X Y) hfm hgm).trans
        (tensorBracket_add_one_tmul s' t' cf cg))
  have hread := congrArg (fun z => dualPairEquiv z φ) htensor
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    dualPairEquiv_map_left, dualPairEquiv_map_right, dualPairEquiv_one_tmul] at hread
  rw [show repGauge U (bracketFam f g φ) = Φ (dualPairEquiv (tensorBracket s t) φ) from by
      rw [hbra, hΦdef]; rfl,
    hread, hbra', hπs', hπt']
  rfl

end ComplexScalars

/-!

## E. Iterated Leibniz expansions

-/

section RealScalars

variable [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]

lemma bracketFam_zero_left (g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam 0 g = 0 := by
  simp [bracketFam]

lemma bracketFam_zero_right (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam f 0 = 0 := by
  simp [bracketFam]

lemma bracketFam_sum_left (S : Multiset (Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B))
    (g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam S.sum g = (S.map fun f => bracketFam f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [bracketFam_zero_left]
  | cons f S ih => simp [bracketFam_add_left, ih]

lemma bracketFam_sum_right (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)
    (S : Multiset (Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B)) :
    bracketFam f S.sum = (S.map fun g => bracketFam f g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [bracketFam_zero_right]
  | cons g S ih => simp [bracketFam_add_right, ih]

lemma bracketFam_finset_sum_left {ι : Type*} (S : Finset ι)
    (f : ι → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) (g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam (∑ i ∈ S, f i) g = ∑ i ∈ S, bracketFam (f i) g := by
  simp only [bracketFam, map_sum, LinearMap.sum_apply]

lemma bracketFam_finset_sum_right {ι : Type*} (S : Finset ι)
    (f : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) (g : ι → Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) :
    bracketFam f (∑ i ∈ S, g i) = ∑ i ∈ S, bracketFam f (g i) := by
  simp only [bracketFam, map_sum]

/-!

## F. The bracket of families against the adjoint coefficients

-/

/-- `tensorBracket` under an antidiagonal family of transports on the Lie factor. If `T x`
  distributes over the bracket as the antidiagonal convolution of the
  `T m`, so does `id ⊗ T x` over `tensorBracket`. -/
lemma tensorBracket_map_right_antidiagonal
    (T : Multiset (Fin 1 ⊕ Fin 3) → G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra)
    (x : Multiset (Fin 1 ⊕ Fin 3))
    (hT : ∀ a b : G.lieSubalgebra, T x ⁅a, b⁆ =
      (x.antidiagonal.map fun p => ⁅T p.1 a, T p.2 b⁆).sum)
    (s t : B ⊗[ℝ] G.lieSubalgebra) :
    (x.antidiagonal.map fun p =>
      tensorBracket ((TensorProduct.map LinearMap.id (T p.1)) s)
        ((TensorProduct.map LinearMap.id (T p.2)) t)).sum =
      (TensorProduct.map LinearMap.id (T x)) (tensorBracket s t) := by
  induction s using TensorProduct.inductionOn with
  | tmul b₁ a₁ =>
      induction t using TensorProduct.inductionOn with
      | tmul b₂ a₂ =>
          simp only [tensorBracket_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
          rw [hT, Multiset.tmul_sum, Multiset.map_map]
          exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
            simp)
      | add y z hy hz =>
          rw [Multiset.map_congr rfl (fun p hp => by rw [map_add, map_add]),
            Multiset.sum_map_add, hy, hz, ← map_add, ← map_add]
  | add y z hy hz =>
      rw [Multiset.map_congr rfl (fun p hp => by
          rw [map_add, map_add, LinearMap.add_apply]),
        Multiset.sum_map_add, hy, hz, ← map_add, ← LinearMap.add_apply, ← map_add]

/-- The bracket of families against an iterated dual adjoint coefficient is the
  antidiagonal convolution of the brackets against the coefficients of the two factors. -/
lemma bracketFam_adjointDualCoeff (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3))
    (f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B) (φ : Module.Dual ℝ G.lieSubalgebra) :
    bracketFam f g (G.adjointDualCoeff U x φ) =
      (x.antidiagonal.map fun p =>
        bracketFam (f ∘ₗ G.adjointDualCoeff U p.1)
          (g ∘ₗ G.adjointDualCoeff U p.2) φ).sum := by
  have hcoeff : ∀ m, G.adjointDualCoeff U m = (G.adjointCoeff U m).dualMap :=
    fun m => rfl
  rw [hcoeff x,
    show bracketFam f g ((G.adjointCoeff U x).dualMap φ) =
      dualPairEquiv ((TensorProduct.map LinearMap.id (G.adjointCoeff U x)) (tensorBracket
        (dualPairEquiv.symm f) (dualPairEquiv.symm g))) φ from
      (dualPairEquiv_map_right (G.adjointCoeff U x) _ φ).symm,
    ← tensorBracket_map_right_antidiagonal (G.adjointCoeff U) x (G.adjointCoeff_lie U x),
    map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [← symm_comp_right, ← symm_comp_right, hcoeff p.1, hcoeff p.2]
  rfl

end RealScalars

/-!

## G. Mass-weight eigenspaces and anticommutants

A covariant tower is a sum of products of symbols, so its mass weight and its statistics
can be checked term by term once each property is a submodule. The weight-`w` eigenspace of
an algebra map `P : B →ₐ[ℂ] Polynomial B` and the elements anticommuting with a fixed one
are both submodules, and the bracket of two families lands in any submodule containing the
products of their components.

-/

section ComplexScalars

variable [Algebra ℂ B]

/-- The bracket pairing of two adjoint families lands in any submodule containing the
  products of their components. It is the sum of the structure constants against them. -/
lemma bracketFam_apply_mem_submodule {M : Submodule ℂ B}
    {f g : Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B}
    (hfg : ∀ ψ χ, f ψ * g χ ∈ M) (φ : Module.Dual ℝ G.lieSubalgebra) :
    bracketFam f g φ ∈ M := by
  rw [bracketFam_apply_eq_sum]
  refine sum_mem fun j _ => sum_mem fun k _ => ?_
  rw [← algebraMap_smul ℂ]
  exact M.smul_mem _ (hfg _ _)

/-- The weight-`w` part of `B` for a mass-weight algebra map `P`, the elements on which `P`
  is the monomial `X ^ w`. -/
noncomputable def massWeightEigenspace (P : B →ₐ[ℂ] Polynomial B) (w : ℕ) : Submodule ℂ B :=
  LinearMap.ker (P.toLinearMap
    - (Polynomial.monomial w : B →ₗ[B] Polynomial B).restrictScalars ℂ)

/-- Membership of the weight-`w` part is the eigenvector equation itself. -/
lemma mem_massWeightEigenspace_iff {P : B →ₐ[ℂ] Polynomial B} {w : ℕ} {b : B} :
    b ∈ massWeightEigenspace P w ↔ P b = Polynomial.monomial w b := by
  rw [massWeightEigenspace, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars,
    sub_eq_zero]

/-- The mass weight is additive on products. `P` is an algebra map and monomials multiply by
  adding their degrees. -/
lemma mul_mem_massWeightEigenspace {P : B →ₐ[ℂ] Polynomial B} {w w' : ℕ} {b b' : B}
    (hb : b ∈ massWeightEigenspace P w) (hb' : b' ∈ massWeightEigenspace P w') :
    b * b' ∈ massWeightEigenspace P (w + w') := by
  rw [mem_massWeightEigenspace_iff] at hb hb' ⊢
  rw [map_mul, hb, hb', Polynomial.monomial_mul_monomial]

/-- The elements of `B` anticommuting with a fixed element. It is a submodule, which is what
  lets the anticommutation of a tower be checked term by term. -/
def anticommuteSubmodule (x : B) : Submodule ℂ B where
  carrier := {y : B | x * y = -(y * x)}
  add_mem' {a b} (ha : x * a = -(a * x)) (hb : x * b = -(b * x)) :=
    show x * (a + b) = -((a + b) * x) by rw [mul_add, add_mul, ha, hb, neg_add]
  zero_mem' := by simp
  smul_mem' c y (hy : x * y = -(y * x)) :=
    show x * (c • y) = -((c • y) * x) by rw [mul_smul_comm, hy, smul_neg, smul_mul_assoc]

/-- Membership of the anticommutant is the anticommutation relation itself. -/
lemma mem_anticommuteSubmodule_iff {x y : B} :
    y ∈ anticommuteSubmodule x ↔ x * y = -(y * x) := Iff.rfl

omit [Algebra ℂ B] in
/-- Anticommutation is symmetric in its two arguments. -/
lemma anticomm_symm {a b : B} (hab : a * b = -(b * a)) : b * a = -(a * b) := by
  rw [hab, neg_neg]

/-- Multiplying an anticommuting element on the left by a commuting one keeps it
  anticommuting. -/
lemma mul_mem_anticommuteSubmodule {x a b : B} (ha : Commute x a)
    (hb : b ∈ anticommuteSubmodule x) : a * b ∈ anticommuteSubmodule x := by
  rw [mem_anticommuteSubmodule_iff] at hb ⊢
  rw [← mul_assoc, ha.eq, mul_assoc, hb, mul_neg, mul_assoc]

end ComplexScalars

end GaugeBoson
