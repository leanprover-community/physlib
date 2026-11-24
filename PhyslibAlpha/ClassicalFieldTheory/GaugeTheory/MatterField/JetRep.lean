/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.DerivRep
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.JetOperations
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Jet
/-!
# The jet representation of a matter field

The continuous representation `ρ : G → GL(V)` of a matter field, extended to the jets
of gauge transformations and to the Lie algebra jets.

## i. Overview

A matter field `M` transforms under the representation `ρ = M.rep` of the global
gauge group `G` on its target space `V`. A gauge transformation `U(x)` acts on it through
`ρ(U(x))`, a function valued in the linear maps on `V`. Its jets are the jets of
`V →L[ℂ] V`-valued functions, `M.EndJet = SpaceTimeAlgebra ⊗[ℂ] (V →L[ℂ] V)`, an algebra. On
jets, a gauge jet `U` acts through the jet `ρ(U)` of `x ↦ ρ(U(x))`, and a Lie algebra jet `A`
through the jet `dρ(A)` of `x ↦ dρ(A(x))`, with `dρ` the Lie algebra representation of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.DerivRep`.

The jet action is built from the Lie algebra action and the Maurer–Cartan form, and not by
applying `ρ` to the power series entries of `U`, because `ρ` is only defined on the group `G`
itself. A jet is formal, so there is no group element `U(x)` to which `ρ` could be applied
and no formula for the jet of `ρ(U(x))` in terms of the entries of `U`. What is available is
the Lie algebra representation `dρ`, which acts on the Lie algebra jets, and the Maurer–Cartan
form `ω_μ = (∂_μ U) U⁻¹`, which carries a gauge jet into them. The derivative of `ρ(U(x))` is
`dρ(ω_μ) ρ(U(x))`, so the jet is recovered as the unique solution of this equation with the
right base-point value.

The jet `dρ(A)` is defined by its base-point derivatives, those of `A` with `dρ` applied, each
lying in the Lie algebra. It commutes with the derivatives, sends constant jets to constant
jets and preserves the commutator, the base-point derivatives of a commutator being sums of
commutators of base-point derivatives.

The jet `ρ(U)` is characterised by its value `ρ(U(0))` and the derivative identity
`∂_μ ρ(U) = dρ(ω_μ) ρ(U)`, with `ω_μ = (∂_μ U) U⁻¹` the Maurer–Cartan form. The flatness of
the Maurer–Cartan form, `∂_μ ω_ν − ∂_ν ω_μ = [ω_μ, ω_ν]`, carries over to `dρ(ω_μ)`, so the
derivative identity has a unique solution with any prescribed value, by the theory of flat
families of jets in `PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Jet`.
Uniqueness then gives `ρ(U V) = ρ(U) ρ(V)` and the equivariance
`dρ(U A U⁻¹) ρ(U) = ρ(U) dρ(A)`.

## ii. Key results

- `GlobalGaugeGroup.MatterField.EndJet` : the jets of linear maps on the target space.
- `GlobalGaugeGroup.MatterField.jetLieAlgebraRep` : the jet `dρ(A)` of a Lie algebra
  jet.
- `GlobalGaugeGroup.MatterField.jetRep` : the jet `ρ(U)` of a gauge jet, as a
  homomorphism.
- `GlobalGaugeGroup.MatterField.jetDeriv_jetRep` : the derivative identity
  `∂_μ ρ(U) = dρ(ω_μ) ρ(U)`.
- `GlobalGaugeGroup.MatterField.jetLieAlgebraRep_adjoint_mul_jetRep` : the equivariance
  `dρ(U A U⁻¹) ρ(U) = ρ(U) dρ(A)`.

## iii. Table of contents

- A. The Lie algebra representation on Lie algebra jets
- B. The jet of a representation along a gauge jet
  - B.1. The flat family `dρ(ω)`
  - B.2. The jet of the representation along a gauge jet
  - B.3. Equivariance and multiplicativity
  - B.4. The jet representation

## iv. References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

/- The jets `SpaceTimeAlgebra ⊗[ℂ] (V →L[ℂ] V)` are formed with the module structure of the
algebra `V →L[ℂ] V`, so that the derivatives of jets and the product of jets act on the same
tensor product. -/
attribute [local instance 2000] Algebra.toModule

namespace GlobalGaugeGroup.MatterField

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}
  (M : G.MatterField)

/-!

## A. The Lie algebra representation on Lie algebra jets

-/

/-- The jets of linear maps on the target space, an algebra. -/
abbrev EndJet : Type := SpaceTimeAlgebra ⊗[ℂ] (M.V →L[ℂ] M.V)

/-- `dρ` depends on a generator only through its matrix. -/
lemma lieAlgebraRepFun_congr {X Y : G.lieAlgebra} (h : (X : Matrix κ κ ℂ) = Y) :
    lieAlgebraRepFun M X = lieAlgebraRepFun M Y :=
  congrArg _ (Subtype.ext h)

/-- The jet `dρ(A)` of a Lie algebra jet `A`, whose base-point derivative along `s` is `dρ` of
  that of `A`. -/
noncomputable def jetLieAlgebraRepFun (A : G.jetLieSubalgebra) : M.EndJet :=
  ofJetDerivValues fun s => lieAlgebraRepFun M ⟨derivValueMatrix s A.1, A.2 s⟩

@[simp]
lemma jetDerivValue_jetLieAlgebraRepFun (A : G.jetLieSubalgebra) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    jetDerivValue s (jetLieAlgebraRepFun M A) =
      lieAlgebraRepFun M ⟨derivValueMatrix s A.1, A.2 s⟩ :=
  jetDerivValue_ofJetDerivValues _ s

/-- The jet `dρ(A)` of a Lie algebra jet, as a real-linear map. -/
noncomputable def jetLieAlgebraRep : G.jetLieSubalgebra →ₗ[ℝ] M.EndJet where
  toFun := jetLieAlgebraRepFun M
  map_add' A B := jet_ext_of_jetDerivValue fun s => by
    rw [map_add, jetDerivValue_jetLieAlgebraRepFun, jetDerivValue_jetLieAlgebraRepFun,
      jetDerivValue_jetLieAlgebraRepFun, ← lieAlgebraRepFun_add]
    exact lieAlgebraRepFun_congr M (derivValueMatrix_add s _ _)
  map_smul' r A := jet_ext_of_jetDerivValue fun s => by
    rw [RingHom.id_apply, (jetDerivValue s).map_smul_of_tower, jetDerivValue_jetLieAlgebraRepFun,
      jetDerivValue_jetLieAlgebraRepFun, ← lieAlgebraRepFun_smul]
    exact lieAlgebraRepFun_congr M (derivValueMatrix_real_smul s r _)

@[simp]
lemma jetDerivValue_jetLieAlgebraRep (A : G.jetLieSubalgebra) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    jetDerivValue s (jetLieAlgebraRep M A) = lieAlgebraRepFun M ⟨derivValueMatrix s A.1, A.2 s⟩ :=
  jetDerivValue_jetLieAlgebraRepFun M A s

/-- The jet `dρ(A)` of a constant Lie algebra jet `A = a` is the constant jet `dρ(a)`. -/
lemma jetLieAlgebraRep_ofConstantLie (a : G.lieSubalgebra) :
    jetLieAlgebraRep M (G.ofConstantLie a) = jetOfConstant (lieAlgebraRep M a) := by
  refine jet_ext_of_jetDerivValue fun s => ?_
  rw [jetDerivValue_jetLieAlgebraRep, jetDerivValue_jetOfConstant]
  split_ifs with hs
  · subst hs
    refine lieAlgebraRepFun_congr M ?_
    ext i j
    simp [RingHom.mapMatrix_apply, constantCoeff_C]
  · rw [show lieAlgebraRepFun M ⟨derivValueMatrix s (G.ofConstantLie a).1, _⟩ =
      lieAlgebraRepFun M 0 from lieAlgebraRepFun_congr M (by
        ext i j
        simp [derivValueMatrix, RingHom.mapMatrix_apply, iteratedPDeriv_C_of_ne_zero hs])]
    exact (lieAlgebraRepLinear M).map_zero

/-- The jet `dρ(A)` commutes with the formal derivatives, `∂_μ dρ(A) = dρ(∂_μ A)`. -/
lemma jetDeriv_jetLieAlgebraRep (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    jetDeriv μ (jetLieAlgebraRep M A) = jetLieAlgebraRep M (G.derivJ μ A) := by
  refine jet_ext_of_jetDerivValue fun s => ?_
  rw [← jetDerivValue_cons, jetDerivValue_jetLieAlgebraRep, jetDerivValue_jetLieAlgebraRep]
  exact lieAlgebraRepFun_congr M (derivValueMatrix_cons μ s A.1)

/-- The jet `dρ` on Lie algebra jets preserves the commutator. The base-point derivatives of
  a commutator are sums of commutators of base-point derivatives, each preserved by `dρ`. -/
lemma jetLieAlgebraRep_lie (A B : G.jetLieSubalgebra) :
    jetLieAlgebraRep M ⁅A, B⁆ =
      jetLieAlgebraRep M A * jetLieAlgebraRep M B -
        jetLieAlgebraRep M B * jetLieAlgebraRep M A := by
  refine jet_ext_of_jetDerivValue fun s => ?_
  have hA := A.2
  have hB := B.2
  let T : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3) → G.lieAlgebra := fun p =>
    ⟨derivValueMatrix p.1 A.1 * derivValueMatrix p.2 B.1 -
      derivValueMatrix p.2 B.1 * derivValueMatrix p.1 A.1,
      commutator_mem_lieAlgebraOfIsClosed (hA p.1) (hB p.2)⟩
  have hsum : lieAlgebraRepFun M ⟨derivValueMatrix s (⁅A, B⁆ : G.jetLieSubalgebra).1, ⁅A, B⁆.2 s⟩
      = (s.antidiagonal.map fun p => lieAlgebraRepFun M (T p)).sum := by
    rw [lieAlgebraRepFun_congr M (Y := (s.antidiagonal.map T).sum) (by
        show derivValueMatrix s (A.1 * B.1 - B.1 * A.1) = G.lieAlgebra.subtype _
        rw [map_multiset_sum, Multiset.map_map]
        exact matrix_constantCoeff_iteratedPDeriv_commutator s A.1 B.1)]
    have h := map_multiset_sum (lieAlgebraRepLinear M) (s.antidiagonal.map T)
    rw [Multiset.map_map] at h
    exact h
  rw [jetDerivValue_jetLieAlgebraRep, hsum, jetDerivValue_commutator]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [jetDerivValue_jetLieAlgebraRep]
  exact lieAlgebraRepFun_commutator M ⟨_, hA p.1⟩ ⟨_, hB p.2⟩

/-!

## B. The jet of a representation along a gauge jet

### B.1. The flat family `dρ(ω)`

-/

/-- The structure equation for `dρ(ω)`, `∂_μ dρ(ω_ν) − ∂_ν dρ(ω_μ) = [dρ(ω_μ), dρ(ω_ν)]`,
  so the family `dρ(ω_μ)` is flat. -/
lemma jetDeriv_jetLieAlgebraRep_maurerCartan_sub (U : G.gaugeJetGroup) (μ ν : Fin 1 ⊕ Fin 3) :
    jetDeriv μ (jetLieAlgebraRep M (G.maurerCartan U ν)) -
        jetDeriv ν (jetLieAlgebraRep M (G.maurerCartan U μ)) =
      jetLieAlgebraRep M (G.maurerCartan U μ) * jetLieAlgebraRep M (G.maurerCartan U ν) -
        jetLieAlgebraRep M (G.maurerCartan U ν) * jetLieAlgebraRep M (G.maurerCartan U μ) := by
  rw [jetDeriv_jetLieAlgebraRep, jetDeriv_jetLieAlgebraRep, ← map_sub, ← jetLieAlgebraRep_lie]
  congr 1
  exact Subtype.ext (G.map_pderiv_maurerCartan_sub U μ ν)

/-!

### B.2. The jet of the representation along a gauge jet

-/

/-- The jet `ρ(U)` of the representation along a gauge jet `U`, the solution of the
  derivative identity `∂_μ ρ(U) = dρ(ω_μ) ρ(U)` with value `ρ(U(0))`, which exists since the
  family `dρ(ω_μ)` is flat. -/
noncomputable def jetRepFun (U : G.gaugeJetGroup) : M.EndJet :=
  (exists_jetDeriv_eq_mul (fun μ => jetLieAlgebraRep M (G.maurerCartan U μ))
    (jetDeriv_jetLieAlgebraRep_maurerCartan_sub M U)
    ((M.rep (G.evalGaugeJet U) : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V)).choose

/-- The value of `ρ(U)` at the base point is `ρ(U(0))`. -/
lemma jetEval_jetRepFun (U : G.gaugeJetGroup) :
    jetEval (jetRepFun M U) = ((M.rep (G.evalGaugeJet U) : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V) :=
  (exists_jetDeriv_eq_mul (fun μ => jetLieAlgebraRep M (G.maurerCartan U μ))
    (jetDeriv_jetLieAlgebraRep_maurerCartan_sub M U) _).choose_spec.1

/-- The derivative identity `∂_μ ρ(U) = dρ(ω_μ) ρ(U)`. -/
lemma jetDeriv_jetRepFun (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv μ (jetRepFun M U) = jetLieAlgebraRep M (G.maurerCartan U μ) * jetRepFun M U :=
  (exists_jetDeriv_eq_mul (fun μ => jetLieAlgebraRep M (G.maurerCartan U μ))
    (jetDeriv_jetLieAlgebraRep_maurerCartan_sub M U) _).choose_spec.2 μ

/-- The jet `ρ(U)` is the only jet with value `ρ(U(0))` satisfying the derivative identity. -/
lemma eq_jetRepFun {U : G.gaugeJetGroup} {Y : M.EndJet}
    (hY : ∀ μ, jetDeriv μ Y = jetLieAlgebraRep M (G.maurerCartan U μ) * Y)
    (hY0 : jetEval Y = ((M.rep (G.evalGaugeJet U) : (M.V →L[ℂ] M.V)ˣ) : M.V →L[ℂ] M.V)) :
    Y = jetRepFun M U :=
  eq_of_jetDeriv_eq_mul _ hY (jetDeriv_jetRepFun M U) (by rw [hY0, jetEval_jetRepFun])

lemma jetRepFun_one : jetRepFun M 1 = 1 := by
  refine (eq_jetRepFun M (fun μ => ?_) ?_).symm
  · rw [maurerCartan_one, map_zero, zero_mul, Algebra.TensorProduct.one_def, jetDeriv_tmul,
      show (1 : SpaceTimeAlgebra) = C 1 from (map_one _).symm, pderiv_C, TensorProduct.zero_tmul]
  · rw [jetEval_one, map_one, map_one, Units.val_one]

/-!

### B.3. Equivariance and multiplicativity

-/

/-- The derivative of `dρ(U A U⁻¹)` is `dρ(U (∂_μ A) U⁻¹) + [dρ(ω_μ), dρ(U A U⁻¹)]`. -/
lemma jetDeriv_jetLieAlgebraRep_adjointJ (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra)
    (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv μ (jetLieAlgebraRep M (G.adjointJ U A)) =
      jetLieAlgebraRep M (G.adjointJ U (G.derivJ μ A)) +
        (jetLieAlgebraRep M (G.maurerCartan U μ) *
            jetLieAlgebraRep M (G.adjointJ U A) -
          jetLieAlgebraRep M (G.adjointJ U A) *
            jetLieAlgebraRep M (G.maurerCartan U μ)) := by
  rw [jetDeriv_jetLieAlgebraRep, G.derivJ_adjointJ, map_add, jetLieAlgebraRep_lie]

/-- The equivariance defect `dρ(U A U⁻¹) ρ(U) − ρ(U) dρ(A)` vanishes at the base point, by
  `dρ(g X g⁻¹) = ρ(g) dρ(X) ρ(g)⁻¹`. -/
lemma jetEval_adjointDefect (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra) :
    jetEval (jetLieAlgebraRep M (G.adjointJ U A) * jetRepFun M U -
        jetRepFun M U * jetLieAlgebraRep M A) = 0 := by
  rw [map_sub, jetEval_mul, jetEval_mul, jetEval_jetRepFun, ← jetDerivValue_zero,
    jetDerivValue_jetLieAlgebraRep, jetDerivValue_jetLieAlgebraRep,
    lieAlgebraRepFun_congr M (Y := G.adjoint (G.evalGaugeJet U) ⟨_, A.2 0⟩) (by
      show derivValueMatrix 0 ((G.adjointJ U A : G.jetLieSubalgebra) :
          Matrix κ κ SpaceTimeAlgebra) = ((G.evalGaugeJet U).1 : Matrix κ κ ℂ) *
        derivValueMatrix 0 A.1 * (↑(G.evalGaugeJet U).1⁻¹ : Matrix κ κ ℂ)
      rw [derivValueMatrix_zero, derivValueMatrix_zero, adjointJ_val, map_mul,
        map_mul]
      rfl), lieAlgebraRepFun_adjoint, mul_assoc, Units.inv_mul, mul_one, sub_self]

/-- The equivariance `dρ(U A U⁻¹) ρ(U) = ρ(U) dρ(A)`. The defect vanishes at the base point
  and its derivative is the defect of the derivative plus `dρ(ω_μ)` times the defect, so it
  vanishes. -/
lemma jetLieAlgebraRep_adjoint_mul_jetRepFun (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra) :
    jetLieAlgebraRep M (G.adjointJ U A) * jetRepFun M U =
      jetRepFun M U * jetLieAlgebraRep M A :=
  sub_eq_zero.mp <| eq_zero_of_jetDeriv_eq_add_mul
    (fun μ => jetLieAlgebraRep M (G.maurerCartan U μ))
    (fun A => jetLieAlgebraRep M (G.adjointJ U A) * jetRepFun M U -
      jetRepFun M U * jetLieAlgebraRep M A)
    (fun μ => G.derivJ μ)
    (fun μ A => by
      rw [jetDeriv_mul_sub_mul μ (jetDeriv_jetLieAlgebraRep_adjointJ M U A μ)
        (jetDeriv_jetRepFun M U μ), jetDeriv_jetLieAlgebraRep])
    (jetEval_adjointDefect M U) A

/-- The jet of a representation is multiplicative, `ρ(U V) = ρ(U) ρ(V)`. -/
lemma jetRepFun_mul (U V : G.gaugeJetGroup) :
    jetRepFun M (U * V) = jetRepFun M U * jetRepFun M V := by
  refine (eq_jetRepFun M (fun μ => ?_) ?_).symm
  · have hmc : G.maurerCartan (U * V) μ =
        G.maurerCartan U μ + G.adjointJ U (G.maurerCartan V μ) :=
      Subtype.ext (by rw [maurerCartan_mul]; rfl)
    rw [jetDeriv_mul, jetDeriv_jetRepFun, jetDeriv_jetRepFun, hmc, map_add, add_mul,
      ← mul_assoc (jetLieAlgebraRep M (G.adjointJ U (G.maurerCartan V μ))),
      jetLieAlgebraRep_adjoint_mul_jetRepFun]
    simp only [mul_assoc]
  · rw [jetEval_mul, jetEval_jetRepFun, jetEval_jetRepFun, map_mul, map_mul, Units.val_mul]

/-!

### B.4. The jet representation

-/

/-- The jet representation `U ↦ ρ(U)` of the jet gauge group. -/
noncomputable def jetRep : G.gaugeJetGroup →* M.EndJet where
  toFun := jetRepFun M
  map_one' := jetRepFun_one M
  map_mul' := jetRepFun_mul M

@[simp]
lemma jetRep_apply (U : G.gaugeJetGroup) : jetRep M U = jetRepFun M U := rfl

/-- The derivative identity `∂_μ ρ(U) = dρ(ω_μ) ρ(U)` of the jet representation. -/
lemma jetDeriv_jetRep (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv μ (jetRep M U) = jetLieAlgebraRep M (G.maurerCartan U μ) * jetRep M U :=
  jetDeriv_jetRepFun M U μ

/-- The equivariance `dρ(U A U⁻¹) ρ(U) = ρ(U) dρ(A)` of the jet representation. -/
lemma jetLieAlgebraRep_adjoint_mul_jetRep (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra) :
    jetLieAlgebraRep M (G.adjointJ U A) * jetRep M U =
      jetRep M U * jetLieAlgebraRep M A :=
  jetLieAlgebraRep_adjoint_mul_jetRepFun M U A

end GlobalGaugeGroup.MatterField
