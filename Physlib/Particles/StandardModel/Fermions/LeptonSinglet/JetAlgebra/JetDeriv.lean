/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
/-!
# The formal total derivative on the charged-lepton jet algebra

## i. Overview

The formal total spacetime derivative extends from the component functions to the
whole jet algebra as an even derivation. It is constructed by lifting the
generator map `ι x ↦ (ι x, ι (∂_μ x))` to an algebra homomorphism into the
trivial square-zero extension of the jet algebra.

## ii. Key results

- `JetAlgebra.jetDeriv` : the formal total spacetime derivative.
- `JetAlgebra.jetDeriv_ofGenerator` : the derivative of a generator.
- `JetAlgebra.jetDeriv_mul` : the Leibniz rule.
- `JetAlgebra.jetDeriv_comm` : total derivatives commute.

## iii. Table of contents

- A. The formal total derivative on the jet algebra
- B. Gauge transformations and total derivatives

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

namespace JetAlgebra

/-!

## A. The formal total derivative on the jet algebra

The formal total spacetime derivative extends from the component functions to
the whole jet algebra as an even derivation:
`∂_μ (x y) = (∂_μ x) y + x (∂_μ y)`, with no Koszul signs. It is constructed by
lifting the generator map `ι x ↦ (ι x, ι (∂_μ x))` to an algebra homomorphism
into the trivial square-zero extension of the jet algebra; the square-zero
condition holds because degree-one elements of the exterior algebra
anticommute.

-/

/-- The generator map of the total derivative into the trivial square-zero
  extension of the jet algebra: `ι x ↦ (ι x, ι (∂_μ x))`. -/
noncomputable def jetDerivGen (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace →ₗ[ℂ] TrivSqZeroExt JetAlgebra JetAlgebra where
  toFun x := (ExteriorAlgebra.ι ℂ x,
    ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x))
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma jetDerivGen_fst (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    (jetDerivGen μ x).fst = ExteriorAlgebra.ι ℂ x := rfl

@[simp]
lemma jetDerivGen_snd (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    (jetDerivGen μ x).snd = ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x) := rfl

/-- The generator map squares to zero: degree-one elements of the exterior
  algebra anticommute. -/
lemma jetDerivGen_mul_self (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDerivGen μ x * jetDerivGen μ x = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, jetDerivGen_fst, ExteriorAlgebra.ι_sq_zero,
      TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, jetDerivGen_fst, jetDerivGen_snd, TrivSqZeroExt.snd_zero,
      smul_eq_mul, op_smul_eq_mul]
    exact ExteriorAlgebra.ι_add_mul_swap x (JetComponentSpace.jetDeriv μ x)

/-- The lift of the total derivative to the trivial square-zero extension of the
  jet algebra: the algebra homomorphism `x ↦ (x, ∂_μ x)`. -/
noncomputable def jetDerivHom (μ : Fin 1 ⊕ Fin 3) :
    JetAlgebra →ₐ[ℂ] TrivSqZeroExt JetAlgebra JetAlgebra :=
  ExteriorAlgebra.lift ℂ ⟨jetDerivGen μ, jetDerivGen_mul_self μ⟩

@[simp]
lemma jetDerivHom_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDerivHom μ (ExteriorAlgebra.ι ℂ x) = jetDerivGen μ x := by
  rw [jetDerivHom, ExteriorAlgebra.lift_ι_apply]

/-- The first component of the square-zero lift is the identity. -/
@[simp]
lemma jetDerivHom_fst (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    (jetDerivHom μ x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ JetAlgebra JetAlgebra).comp (jetDerivHom μ) =
      AlgHom.id ℂ JetAlgebra := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp
  exact DFunLike.congr_fun h x

/-- The formal total spacetime derivative on the jet algebra of the
  charged-lepton singlet in the direction `μ`: the even derivation extending the
  shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the component functions. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra where
  toFun x := (jetDerivHom μ x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (jetDerivHom μ) x y)
  map_smul' c x := congrArg TrivSqZeroExt.snd (map_smul (jetDerivHom μ) c x)

lemma jetDeriv_apply (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv μ x = (jetDerivHom μ x).snd := rfl

@[simp]
lemma jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDeriv μ (ExteriorAlgebra.ι ℂ x) =
      ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x) := by
  rw [jetDeriv_apply, jetDerivHom_ι, jetDerivGen_snd]

/-- The total derivative appends the derivative index to each component
  function. -/
@[simp]
lemma jetDeriv_ofGenerator (μ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    jetDeriv μ (ofGenerator j) = ofGenerator (JetGenerators.shift μ j) := by
  rw [ofGenerator, jetDeriv_ι, JetComponentSpace.jetDeriv_basis]
  rfl

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv μ (1 : JetAlgebra) = 0 :=
  congrArg TrivSqZeroExt.snd (map_one (jetDerivHom μ))

/-- The total derivative is an even derivation: the Leibniz rule holds on the
  jet algebra with no Koszul signs. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  have h : jetDeriv μ (x * y) =
      (jetDerivHom μ x).fst * jetDeriv μ y + jetDeriv μ x * (jetDerivHom μ y).fst :=
    congrArg TrivSqZeroExt.snd (map_mul (jetDerivHom μ) x y)
  rw [jetDerivHom_fst, jetDerivHom_fst] at h
  exact h.trans (add_comm _ _)

lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv μ (jetDeriv ν x) = jetDeriv ν (jetDeriv μ x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    simp [JetComponentSpace.jetDeriv_comm]
  | mul x y hx hy =>
    simp only [jetDeriv_mul, map_add, hx, hy]
    abel
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-!

## B. Gauge transformations and total derivatives

Let ∂_s be the derivative with respect to the multi-index s.
On the action of the gauge group `∂_s (g • ψ) ≠ g • ∂_s ψ`.
The RHS of this properly takes account of derivatives of the gauge transformation,
while the LHS does not.

What we want to show is that
`g • ∂_s ψ = ∑_{p + q = s}  q ^ {|p|} • (∂_p g) • ∂_q ψ`.
where `q` is the charge of the field.

-/

end JetAlgebra

end LeptonSinglet

end StandardModel
