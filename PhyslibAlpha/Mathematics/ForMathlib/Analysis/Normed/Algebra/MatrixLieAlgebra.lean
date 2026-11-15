/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.ForMathlib.Analysis.Normed.Algebra.LieProductFormula
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# The Lie algebra of a closed group of matrices

The generators of the one-parameter subgroups of a closed subgroup of `GL(κ, ℂ)`.

## i. Overview

For a subgroup `H` of `GL(κ, ℂ)`, the generators of its one-parameter subgroups are the
matrices `X` with `exp (t X) ∈ H` for every real `t`. When `H` is closed they form a real
subspace `lieAlgebraOfIsClosed H hH`, its Lie algebra:

* closure under real multiples is immediate;
* closure under addition is the Lie product formula: `exp (t (X + Y))` is the limit of
  `(exp (t X / n) exp (t Y / n)) ^ n`, a sequence in `H` whose inverses also converge, so the
  limit lies in `H` because `H` is closed.

The Lie algebra is invariant under conjugation by `H`, and it is closed under the
commutator: it is a closed subspace containing the conjugates `exp (t X) Y exp (−t X)`, and
so their derivative `X Y − Y X` at `t = 0`.

## ii. Key results

- `Matrix.exp_add_mem_of_isClosed` : the one-parameter subgroups of a closed group of
  matrices are closed under adding generators.
- `Matrix.lieAlgebraOfIsClosed` : the Lie algebra of a closed group of matrices.
- `Matrix.conj_mem_lieAlgebraOfIsClosed` : it is invariant under conjugation by the group.
- `Matrix.commutator_mem_lieAlgebraOfIsClosed` : it is closed under the commutator.

## iii. Table of contents

- A. Closure under addition
- B. The Lie algebra
- C. Conjugation and the commutator

## iv. References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

open Filter Topology NormedSpace

namespace Matrix

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-!

## A. Closure under addition

-/

/-- In a closed group of matrices, if the one-parameter subgroups of `X` and of `Y` lie in
  the group, then so does `exp (X + Y)`: it is the limit of the products
  `(exp (X / n) exp (Y / n)) ^ n` of group elements, by the Lie product formula. -/
lemma exp_add_mem_of_isClosed {H : Subgroup (GeneralLinearGroup κ ℂ)}
    (hH : IsClosed (H : Set (GeneralLinearGroup κ ℂ))) {X Y : Matrix κ κ ℂ}
    (hX : ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : H => (g.1 : Matrix κ κ ℂ))
    (hY : ∀ t : ℝ, exp (t • Y) ∈ Set.range fun g : H => (g.1 : Matrix κ κ ℂ)) :
    exp (X + Y) ∈ Set.range fun g : H => (g.1 : Matrix κ κ ℂ) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨1, Matrix.ext fun i => isEmptyElim i⟩
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : NormOneClass (Matrix κ κ ℂ) := Matrix.linfty_opNormOneClass
  choose g₁ hg₁ using fun n : ℕ => hX (n : ℝ)⁻¹
  choose g₂ hg₂ using fun n : ℕ => hY (n : ℝ)⁻¹
  beta_reduce at hg₁ hg₂
  set g : ℕ → H := fun n => (g₁ n * g₂ n) ^ n
  -- The group elements and their inverses are the products of the Lie product formula.
  have hval : ∀ n, ((g n).1 : Matrix κ κ ℂ) =
      (exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y)) ^ n := fun n => by
    simp [g, ← hg₁ n, ← hg₂ n]
  have hinv : ∀ n, (↑(g n).1⁻¹ : Matrix κ κ ℂ) =
      (exp ((n : ℝ)⁻¹ • -Y) * exp ((n : ℝ)⁻¹ • -X)) ^ n := fun n => by
    have h₁ : (↑(g₁ n).1⁻¹ : Matrix κ κ ℂ) = exp ((n : ℝ)⁻¹ • -X) := by
      rw [Matrix.coe_units_inv, hg₁ n, smul_neg, Matrix.exp_neg]
    have h₂ : (↑(g₂ n).1⁻¹ : Matrix κ κ ℂ) = exp ((n : ℝ)⁻¹ • -Y) := by
      rw [Matrix.coe_units_inv, hg₂ n, smul_neg, Matrix.exp_neg]
    simp only [g, Subgroup.coe_pow, Subgroup.coe_mul, ← inv_pow, _root_.mul_inv_rev,
      Units.val_pow_eq_pow_val, Units.val_mul, h₁, h₂]
  -- They converge in the group of units, to the unit `exp (X + Y)`.
  set u : GeneralLinearGroup κ ℂ := (Matrix.isUnit_exp (X + Y)).unit
  have hu : Tendsto (fun n => (g n).1) atTop (𝓝 u) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply]
    refine Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · rw [IsUnit.unit_spec]
      exact (tendsto_exp_mul_exp_pow X Y).congr fun n => (hval n).symm
    · rw [Matrix.coe_units_inv, IsUnit.unit_spec, ← Matrix.exp_neg, neg_add_rev]
      exact (tendsto_exp_mul_exp_pow (-Y) (-X)).congr fun n => (hinv n).symm
  exact ⟨⟨u, hH.mem_of_tendsto hu (Eventually.of_forall fun n => (g n).2)⟩,
    IsUnit.unit_spec _⟩

/-!

## B. The Lie algebra

-/

/-- The Lie algebra of a closed subgroup of `GL(κ, ℂ)`: the real subspace of matrices whose
  one-parameter subgroups lie in the group. -/
def lieAlgebraOfIsClosed (H : Subgroup (GeneralLinearGroup κ ℂ))
    (hH : IsClosed (H : Set (GeneralLinearGroup κ ℂ))) : Submodule ℝ (Matrix κ κ ℂ) where
  carrier := {X | ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : H => (g.1 : Matrix κ κ ℂ)}
  zero_mem' t := ⟨1, by simp⟩
  smul_mem' r X hX t := by
    rw [smul_smul]
    exact hX (t * r)
  add_mem' {X Y} hX hY t := by
    rw [smul_add]
    refine exp_add_mem_of_isClosed hH (fun s => ?_) (fun s => ?_)
    · rw [smul_smul]
      exact hX (s * t)
    · rw [smul_smul]
      exact hY (s * t)

lemma mem_lieAlgebraOfIsClosed_iff {H : Subgroup (GeneralLinearGroup κ ℂ)}
    {hH : IsClosed (H : Set (GeneralLinearGroup κ ℂ))} {X : Matrix κ κ ℂ} :
    X ∈ lieAlgebraOfIsClosed H hH ↔
      ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : H => (g.1 : Matrix κ κ ℂ) := Iff.rfl

/-!

## C. Conjugation and the commutator

-/

variable {H : Subgroup (GeneralLinearGroup κ ℂ)} {hH : IsClosed (H : Set (GeneralLinearGroup κ ℂ))}

/-- The Lie algebra is invariant under conjugation by the group: the one-parameter subgroup
  of the conjugate of a generator by a group element is the conjugate of the one-parameter
  subgroup of the generator. -/
lemma conj_mem_lieAlgebraOfIsClosed (g : H) {X : Matrix κ κ ℂ}
    (hX : X ∈ lieAlgebraOfIsClosed H hH) :
    (g.1 : Matrix κ κ ℂ) * X * (↑g.1⁻¹ : Matrix κ κ ℂ) ∈ lieAlgebraOfIsClosed H hH := by
  set U : Matrix κ κ ℂ := g.1.val
  have hinv : U⁻¹ = ↑g.1⁻¹ := (Matrix.coe_units_inv g.1).symm
  intro t
  obtain ⟨h, hh⟩ := hX t
  refine ⟨g * h * g⁻¹, ?_⟩
  rw [← hinv, show t • (U * X * U⁻¹) = U * (t • X) * U⁻¹ by
    rw [mul_smul_comm, smul_mul_assoc], Matrix.exp_conj _ _ g.1.isUnit, ← hh, hinv]
  rfl

/-- The Lie algebra is closed under the commutator. The conjugates
  `exp (t X) Y exp (−t X)` lie in the Lie algebra, a closed subspace, and so does their
  derivative `X Y − Y X` at `t = 0`. -/
lemma commutator_mem_lieAlgebraOfIsClosed {X Y : Matrix κ κ ℂ}
    (hX : X ∈ lieAlgebraOfIsClosed H hH) (hY : Y ∈ lieAlgebraOfIsClosed H hH) :
    X * Y - Y * X ∈ lieAlgebraOfIsClosed H hH := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  set f : ℝ → Matrix κ κ ℂ := fun t => exp (t • X) * Y * exp (t • -X)
  have hf : HasDerivAt f (X * Y - Y * X) 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
    simp only [zero_smul, exp_zero, one_mul, mul_one, mul_neg] at h
    rw [sub_eq_add_neg]
    exact h
  have hmem : ∀ t, f t ∈ lieAlgebraOfIsClosed H hH := fun t => by
    obtain ⟨g, hg⟩ := hX t
    have hinv : exp (t • -X) = ↑g.1⁻¹ := by
      rw [smul_neg, Matrix.exp_neg, ← hg, Matrix.coe_units_inv]
    simp only [f, hinv, ← hg]
    exact conj_mem_lieAlgebraOfIsClosed g hY
  refine (Submodule.closed_of_finiteDimensional _).mem_of_tendsto
    hf.tendsto_slope_zero (Eventually.of_forall fun t => ?_)
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmem _) (hmem _))

end Matrix
