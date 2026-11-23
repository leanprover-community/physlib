/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import PhyslibAlpha.Mathematics.ForMathlib.Analysis.Normed.Algebra.MatrixExponential
/-!
# The product of global gauge groups

The product `G₁ × G₂` of two global gauge groups, acting block-diagonally.

## i. Overview

The gauge group of a theory with several independent gauge interactions is a product of
groups, such as `SU(3) × SU(2) × U(1)` for the Standard Model. For global gauge groups
`G₁ ⊆ GL(κ₁, ℂ)` and `G₂ ⊆ GL(κ₂, ℂ)` the product sits inside `GL(κ₁ ⊕ κ₂, ℂ)` as the
block-diagonal matrices `diag(g₁, g₂)` with `g₁ ∈ G₁` and `g₂ ∈ G₂`. Taking the two diagonal
blocks is a continuous left inverse of `(A₁, A₂) ↦ diag(A₁, A₂)`, so this embedding is
closed, and so is the induced embedding of pairs of invertible matrices. The product group is
the image of the closed set `G₁ × G₂` under it, and so it is closed.

The Lie algebra of the product is the direct sum of the Lie algebras. A block-diagonal
matrix `diag(X₁, X₂)` of generators is a generator of the product, since the exponential of
a block-diagonal matrix is taken blockwise. Conversely, the one-parameter subgroup of a
generator of the product lies in the closed subspace of block-diagonal matrices, so the
generator, its derivative at `t = 0`, does too, and its diagonal blocks are generators.

## ii. Key results

- `GlobalGaugeGroup.prod` : the product of two global gauge groups.
- `GlobalGaugeGroup.mem_prod_iff` : the elements of the product are the block-diagonal
  matrices `diag(g₁, g₂)` with `g₁ ∈ G₁` and `g₂ ∈ G₂`.
- `GlobalGaugeGroup.prodGroupEquiv` : the elements of the product are the pairs of elements of
  the factors.
- `GlobalGaugeGroup.exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod` : the exponential of a
  generator of the product is taken blockwise.
- `GlobalGaugeGroup.mem_lieAlgebra_prod_iff` : the generators of the product are the
  block-diagonal matrices of generators.

## iii. Table of contents

- A. The product of global gauge groups
  - A.1. Pairs of elements
- B. The Lie algebra of the product
  - B.1. The generators of the product

## iv. References

* None.

-/

@[expose] public section

open Matrix NormedSpace Topology

namespace GlobalGaugeGroup

variable {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
  (G₁ : GlobalGaugeGroup κ₁) (G₂ : GlobalGaugeGroup κ₂)

/-!

## A. The product of global gauge groups

-/

/-- The product of two global gauge groups `G₁` and `G₂`, made of the block-diagonal matrices
  `diag(g₁, g₂)` with `g₁ ∈ G₁` and `g₂ ∈ G₂`. It is the image of `G₁ × G₂` under the
  block-diagonal embedding of pairs of invertible matrices, which is closed since taking the
  two diagonal blocks is a continuous left inverse. -/
def prod : GlobalGaugeGroup (κ₁ ⊕ κ₂) where
  group := (G₁.group.prod G₂.group).map <|
    (Units.map
      { toFun A := fromBlocks A.1 0 0 A.2
        map_one' := fromBlocks_one
        map_mul' A B := by simp [fromBlocks_multiply] :
        Matrix κ₁ κ₁ ℂ × Matrix κ₂ κ₂ ℂ →* Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ}).comp
      MulEquiv.prodUnits.symm.toMonoidHom
  isClosed := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    refine IsClosedEmbedding.isClosedMap ?_ _ (G₁.isClosed.prod G₂.isClosed)
    rw [MonoidHom.coe_comp]
    refine (IsClosedEmbedding.units_map ?_).comp (Homeomorph.prodUnits).symm.isClosedEmbedding
    exact Function.LeftInverse.isClosedEmbedding (f := fun M => (M.toBlocks₁₁, M.toBlocks₂₂))
      (fun A => by simp)
      ((continuous_matrix fun _ _ => continuous_id.matrix_elem _ _).prodMk
        (continuous_matrix fun _ _ => continuous_id.matrix_elem _ _))
      (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd)

/-- The elements of the product are the block-diagonal matrices `diag(g₁, g₂)` with
  `g₁ ∈ G₁` and `g₂ ∈ G₂`. -/
lemma mem_prod_iff {g : GeneralLinearGroup (κ₁ ⊕ κ₂) ℂ} :
    g ∈ (G₁.prod G₂).group ↔ ∃ g₁ ∈ G₁.group, ∃ g₂ ∈ G₂.group,
      fromBlocks (g₁ : Matrix κ₁ κ₁ ℂ) 0 0 (g₂ : Matrix κ₂ κ₂ ℂ) = g := by
  constructor
  · rintro ⟨⟨g₁, g₂⟩, ⟨hg₁, hg₂⟩, rfl⟩
    exact ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  · rintro ⟨g₁, hg₁, g₂, hg₂, h⟩
    exact ⟨(g₁, g₂), ⟨hg₁, hg₂⟩, Units.ext h⟩

/-!

### A.1. Pairs of elements

-/

/-- The pair `(g₁, g₂)` as the element `diag(g₁, g₂)` of the product. -/
noncomputable def prodGroupHom : G₁.group × G₂.group →* (G₁.prod G₂).group where
  toFun g := ⟨_, Subgroup.mem_map_of_mem _
    (show ((g.1 : GeneralLinearGroup κ₁ ℂ), (g.2 : GeneralLinearGroup κ₂ ℂ)) ∈
      G₁.group.prod G₂.group from ⟨g.1.2, g.2.2⟩)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ (((g.1 : GeneralLinearGroup κ₁ ℂ),
    (g.2 : GeneralLinearGroup κ₂ ℂ))) (((h.1 : GeneralLinearGroup κ₁ ℂ),
      (h.2 : GeneralLinearGroup κ₂ ℂ))))

@[simp]
lemma prodGroupHom_val (g : G₁.group × G₂.group) :
    (((prodGroupHom G₁ G₂ g : (G₁.prod G₂).group) : GeneralLinearGroup (κ₁ ⊕ κ₂) ℂ) :
      Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ) = fromBlocks ((g.1 : GeneralLinearGroup κ₁ ℂ) :
        Matrix κ₁ κ₁ ℂ) 0 0 ((g.2 : GeneralLinearGroup κ₂ ℂ) : Matrix κ₂ κ₂ ℂ) := rfl

/-- Every element of the product is a block-diagonal matrix `diag(g₁, g₂)`. -/
lemma prodGroupHom_surjective : Function.Surjective (prodGroupHom G₁ G₂) := by
  rintro ⟨g, hg⟩
  obtain ⟨⟨g₁, g₂⟩, ⟨h₁, h₂⟩, rfl⟩ := Subgroup.mem_map.1 hg
  exact ⟨(⟨g₁, h₁⟩, ⟨g₂, h₂⟩), rfl⟩

/-- A block-diagonal matrix determines its two blocks. -/
lemma prodGroupHom_injective : Function.Injective (prodGroupHom G₁ G₂) := fun g h hgh => by
  obtain ⟨h1, -, -, h2⟩ := fromBlocks_inj.1 (congrArg (fun x =>
    ((x.1 : GeneralLinearGroup (κ₁ ⊕ κ₂) ℂ) : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ)) hgh)
  exact Prod.ext (Subtype.ext (Units.ext h1)) (Subtype.ext (Units.ext h2))

/-- The elements of the product of two global gauge groups are the pairs of their elements, as
  block-diagonal matrices. -/
noncomputable def prodGroupEquiv : G₁.group × G₂.group ≃* (G₁.prod G₂).group :=
  MulEquiv.ofBijective (prodGroupHom G₁ G₂)
    ⟨prodGroupHom_injective G₁ G₂, prodGroupHom_surjective G₁ G₂⟩

@[simp]
lemma prodGroupEquiv_apply (g : G₁.group × G₂.group) :
    prodGroupEquiv G₁ G₂ g = prodGroupHom G₁ G₂ g := rfl

/-!

## B. The Lie algebra of the product

### B.1. The generators of the product

-/

/-- A block-diagonal matrix `diag(X₁, X₂)` of generators of `G₁` and `G₂` is a generator of
  the product, since its exponential is taken blockwise. -/
lemma fromBlocks_mem_lieAlgebra_prod {X₁ : Matrix κ₁ κ₁ ℂ} {X₂ : Matrix κ₂ κ₂ ℂ}
    (hX₁ : X₁ ∈ G₁.lieAlgebra) (hX₂ : X₂ ∈ G₂.lieAlgebra) :
    fromBlocks X₁ 0 0 X₂ ∈ (G₁.prod G₂).lieAlgebra := by
  intro t
  obtain ⟨g₁, hg₁⟩ := hX₁ t
  obtain ⟨g₂, hg₂⟩ := hX₂ t
  refine ⟨⟨_, Subgroup.mem_map_of_mem _
    (show (g₁.1, g₂.1) ∈ G₁.group.prod G₂.group from ⟨g₁.2, g₂.2⟩)⟩, ?_⟩
  show fromBlocks ((g₁ : GeneralLinearGroup κ₁ ℂ) : Matrix κ₁ κ₁ ℂ) 0 0
    ((g₂ : GeneralLinearGroup κ₂ ℂ) : Matrix κ₂ κ₂ ℂ) = _
  simp only [hg₁, hg₂, fromBlocks_smul, smul_zero, exp_fromBlocks_zero]

/-- A generator of the product is block-diagonal. Its one-parameter subgroup lies in the
  closed subspace of block-diagonal matrices, and so does its derivative at `t = 0`. -/
lemma eq_fromBlocks_of_mem_lieAlgebra_prod {X : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ}
    (hX : X ∈ (G₁.prod G₂).lieAlgebra) : X = fromBlocks X.toBlocks₁₁ 0 0 X.toBlocks₂₂ := by
  let _ : NormedRing (Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ) := Matrix.linftyOpNormedAlgebra
  -- The block-diagonal matrices, as a real subspace.
  let S : Submodule ℝ (Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ) :=
    { carrier := {M | ∀ i j, M (.inl i) (.inr j) = 0 ∧ M (.inr j) (.inl i) = 0}
      add_mem' hM hN i j := by simp [(hM i j).1, (hM i j).2, (hN i j).1, (hN i j).2]
      zero_mem' i j := by simp
      smul_mem' c M hM i j := by simp [(hM i j).1, (hM i j).2] }
  have hmem (t : ℝ) : exp (t • X) ∈ S := by
    obtain ⟨⟨g, hg⟩, hgX⟩ := hX t
    obtain ⟨g₁, -, g₂, -, hg₁₂⟩ := (G₁.mem_prod_iff G₂).1 hg
    rw [← hgX]
    intro i j
    simp [← hg₁₂]
  have hf := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  simp only [zero_smul, exp_zero, one_mul] at hf
  have hXS : X ∈ S := (Submodule.isClosed_of_finiteDimensional S).mem_of_tendsto
    hf.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      S.smul_mem _ (S.sub_mem (hmem _) (hmem _)))
  conv_lhs => rw [← fromBlocks_toBlocks X]
  congr 1
  · ext i j
    exact (hXS i j).1
  · ext i j
    exact (hXS j i).2

/-- The diagonal blocks of a generator of the product are generators of `G₁` and `G₂`. -/
lemma toBlocks_mem_lieAlgebra_of_mem_lieAlgebra_prod {X : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ}
    (hX : X ∈ (G₁.prod G₂).lieAlgebra) :
    X.toBlocks₁₁ ∈ G₁.lieAlgebra ∧ X.toBlocks₂₂ ∈ G₂.lieAlgebra := by
  have hX' := G₁.eq_fromBlocks_of_mem_lieAlgebra_prod G₂ hX
  have key (t : ℝ) : ∃ g₁ ∈ G₁.group, ∃ g₂ ∈ G₂.group,
      (g₁ : Matrix κ₁ κ₁ ℂ) = exp (t • X.toBlocks₁₁) ∧
        (g₂ : Matrix κ₂ κ₂ ℂ) = exp (t • X.toBlocks₂₂) := by
    obtain ⟨⟨g, hg⟩, hgX⟩ := hX t
    obtain ⟨g₁, hg₁, g₂, hg₂, hg₁₂⟩ := (G₁.mem_prod_iff G₂).1 hg
    have htX : t • X = fromBlocks (t • X.toBlocks₁₁) 0 0 (t • X.toBlocks₂₂) := by
      conv_lhs => rw [hX']
      simp only [fromBlocks_smul, smul_zero]
    have h : fromBlocks (g₁ : Matrix κ₁ κ₁ ℂ) 0 0 (g₂ : Matrix κ₂ κ₂ ℂ) =
        fromBlocks (exp (t • X.toBlocks₁₁)) 0 0 (exp (t • X.toBlocks₂₂)) := by
      rw [← exp_fromBlocks_zero, ← htX, hg₁₂]
      exact hgX
    obtain ⟨h₁, -, -, h₂⟩ := fromBlocks_inj.1 h
    exact ⟨g₁, hg₁, g₂, hg₂, h₁, h₂⟩
  refine ⟨fun t => ?_, fun t => ?_⟩
  · obtain ⟨g₁, hg₁, -, -, h₁, -⟩ := key t
    exact ⟨⟨g₁, hg₁⟩, h₁⟩
  · obtain ⟨-, -, g₂, hg₂, -, h₂⟩ := key t
    exact ⟨⟨g₂, hg₂⟩, h₂⟩

/-- The exponential of a generator of the product is the block-diagonal matrix of the
  exponentials of its diagonal blocks. -/
lemma exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod {X : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ}
    (hX : X ∈ (G₁.prod G₂).lieAlgebra) (t : ℝ) :
    exp (t • X) = fromBlocks (exp (t • X.toBlocks₁₁)) 0 0 (exp (t • X.toBlocks₂₂)) := by
  conv_lhs => rw [G₁.eq_fromBlocks_of_mem_lieAlgebra_prod G₂ hX]
  rw [fromBlocks_smul, smul_zero, smul_zero, exp_fromBlocks_zero]

/-- The generators of the product of global gauge groups are the block-diagonal matrices
  `diag(X₁, X₂)` with `X₁` a generator of `G₁` and `X₂` a generator of `G₂`. -/
lemma mem_lieAlgebra_prod_iff {X : Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ} :
    X ∈ (G₁.prod G₂).lieAlgebra ↔
      ∃ X₁ ∈ G₁.lieAlgebra, ∃ X₂ ∈ G₂.lieAlgebra, X = fromBlocks X₁ 0 0 X₂ := by
  refine ⟨fun hX => ?_, ?_⟩
  · obtain ⟨h₁, h₂⟩ := G₁.toBlocks_mem_lieAlgebra_of_mem_lieAlgebra_prod G₂ hX
    exact ⟨_, h₁, _, h₂, G₁.eq_fromBlocks_of_mem_lieAlgebra_prod G₂ hX⟩
  · rintro ⟨X₁, hX₁, X₂, hX₂, rfl⟩
    exact G₁.fromBlocks_mem_lieAlgebra_prod G₂ hX₁ hX₂

end GlobalGaugeGroup
