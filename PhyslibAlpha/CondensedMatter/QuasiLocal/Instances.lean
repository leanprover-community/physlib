/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.QuasiLocal.Local
public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.AlgebraNet

/-!

# The quantum and classical nets of a system with finite site spaces

The two nets of algebras over a set of sites with finite configuration spaces: operators and
functions.

## i. Overview

For sites `s` carrying finite sets `Ω s`, the quantum net assigns to a region the matrices on its
configurations, with the inclusions `M ↦ M ⊗ 1`. The classical net assigns to a region the complex
functions on its configurations, which are the diagonal operators, with the inclusions
`f ↦ f ∘ restr`: a function of the values in `X` is a function of the values in `Y ⊇ X`. Both
satisfy the axioms of a net, and the classical net sits in the quantum net as diagonal matrices.
Both have a quasi-local algebra by the construction on any net.

The inclusions are injective as soon as every site space is nonempty.

## ii. Key results

- `quantumNet` : the net of operators.
- `classicalNet` : the net of functions of configurations.
- `diagonalInclusion` : the classical algebra of a region as diagonal operators.
- `diagonalInclusion_incl` : the classical net is a subnet of the quantum net.

## iii. Table of contents

- A. The quantum net
- B. The classical net

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.1.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory.QuasiLocal

open scoped Matrix

variable {S : Type*} [DecidableEq S]
variable (Ω : S → Type*) [∀ s, Fintype (Ω s)] [∀ s, DecidableEq (Ω s)]

/-! ## A. The quantum net -/

/-- **The quantum net**: the matrices on the configurations of each region, with `M ↦ M ⊗ 1` as
inclusion. -/
def quantumNet : AlgebraNet S where
  A X := Alg Ω X
  incl h := inclStarAlg h
  incl_refl _X a := inclMat_refl a
  incl_trans h₁ h₂ a := inclMat_trans h₁ h₂ a

/-! ## B. The classical net -/

/-- The classical algebra of a region: the complex functions on its configurations. -/
abbrev CAlg (X : Finset S) : Type _ := Cfg Ω X → ℂ

/-- A function of the values in `X` is a function of the values in a larger region `Y`. -/
def classicalIncl {X Y : Finset S} (h : X ≤ Y) : CAlg Ω X →⋆ₐ[ℂ] CAlg Ω Y where
  toFun f c := f (restr h c)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- **The classical net**: the functions on the configurations of each region. -/
def classicalNet : AlgebraNet S where
  A X := CAlg Ω X
  incl h := classicalIncl Ω h
  incl_refl _X _a := rfl
  incl_trans _h₁ _h₂ _a := rfl

/-- The classical algebra of a region as the diagonal operators. -/
def diagonalInclusion (X : Finset S) : CAlg Ω X →⋆ₐ[ℂ] Alg Ω X where
  toFun := Matrix.diagonal
  map_one' := Matrix.diagonal_one
  map_mul' f g := (Matrix.diagonal_mul_diagonal f g).symm
  map_zero' := Matrix.diagonal_zero
  map_add' f g := (Matrix.diagonal_add f g).symm
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext c c'
    by_cases h : c = c' <;> simp [h]
  map_star' f := by
    ext c c'
    by_cases h : c = c'
    · subst h; simp
    · simp [h, Ne.symm h]

/-- **The classical net is a subnet of the quantum net**: the diagonal inclusion commutes with the
inclusions of regions. -/
lemma diagonalInclusion_incl {X Y : Finset S} (h : X ≤ Y) (f : CAlg Ω X) :
    inclMat h (diagonalInclusion Ω X f) = diagonalInclusion Ω Y (classicalIncl Ω h f) := by
  ext c c'
  simp only [inclMat_apply, diagonalInclusion, StarAlgHom.coe_mk,
    Matrix.diagonal_apply, classicalIncl]
  by_cases hc : c = c'
  · subst hc
    simp [agree_refl h c]
    rfl
  · by_cases ha : Agree h c c'
    · have hr : restr h c ≠ restr h c' := fun hr => hc (eq_of_agree_of_restr_eq ha hr)
      simp [ha, hr, hc]
    · simp [ha, hc]

end QuasiLocal

end CondensedMatter

end
