/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.JetOperations
public import Mathlib.Algebra.Lie.OfAssociative
/-!
# The Taylor coefficients of the adjoint action

The base-point derivatives of the adjoint action of a gauge jet on the Lie algebra.

## i. Overview

A gauge jet `U` acts on the gauge algebra of jets by the adjoint action `Ad_U`. What the
transformation law of a gauge field `A_μ ↦ Ad_U A_μ + ω_μ(U)` sees of `Ad_U`, after differentiating
`x` times and evaluating at the base point, is the physicists' `∂_x (Ad_U)^a_b|₀`, a linear map
`adjointCoeff U x : G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra` on the constant gauge algebra, and its
transpose `adjointDualCoeff U x` on the dual index carried by the field symbols. This file develops
these coefficients for any global gauge group `G`, through its jet operations `G.evalLie`,
`G.iteratedDerivJ`, `G.adjointJ` and `G.ofConstantLie`.

The central result is the Taylor–Leibniz theorem `evalLie_iteratedDerivJ_adjointJ`. The
base-point Taylor coefficients of `Ad_U Y` for an arbitrary jet `Y` are the antidiagonal
convolution of the coefficients of `Ad_U` with those of `Y`. For a matrix group it is the Leibniz
rule for products of matrices of power series. Here it is derived from the Leibniz rule
`derivJ_adjointJ` for a single derivative, by induction on the number of derivatives. Its
corollaries are the multiplicativity `adjointCoeff_mul` of the coefficients up to convolution,
and the recursion `adjointCoeff_cons` expressing one more derivative of a coefficient through the
Maurer–Cartan form.

## ii. Key results

- `GlobalGaugeGroup.adjointCoeff` : the coefficient `∂_x (Ad_U)|₀`, with its values
  `adjointCoeff_zero` at the base point and `adjointCoeff_one` on the identity jet.
- `GlobalGaugeGroup.adjointCoeff_cons` : one more derivative of a coefficient is minus the
  antidiagonal convolution of `ad` of the derived form `−ω` against lower coefficients, where
  `ω = (∂_μ U) U⁻¹` is the Maurer–Cartan form.
- `GlobalGaugeGroup.evalLie_iteratedDerivJ_adjointJ` : the Taylor–Leibniz theorem.
- `GlobalGaugeGroup.adjointCoeff_mul` : the coefficients of a product are the convolution
  of the coefficients of the factors.
- `GlobalGaugeGroup.adjointDualCoeff` : the transposed coefficients, with
  `adjointDualCoeff_singleton`, `adjointDualCoeff_pair` and `adjointDualCoeff_cons`.

## iii. Table of contents

- A. The adjoint Taylor coefficients
- B. The recursion through the Maurer–Cartan form
- C. The Taylor–Leibniz theorem
- D. The dual coefficients

## iv. References

* None.

-/

@[expose] public section

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The adjoint Taylor coefficients

-/

/-- The physicists' `∂_x (Ad_U)^a_b|₀`. Include a constant gauge algebra element into
  jets, act by the adjoint of `U`, differentiate `x` times, and evaluate at the base
  point. For `x = 0` this is the adjoint action of the value of `U`, and for `x ≠ 0` it sees
  the derivatives of the gauge transformation. -/
noncomputable def adjointCoeff (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra :=
  G.evalLie.toLinearMap ∘ₗ G.iteratedDerivJ x ∘ₗ
    G.adjointJ U ∘ₗ G.ofConstantLie

lemma adjointCoeff_eq_evalLie (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3))
    (a : G.lieSubalgebra) :
    G.adjointCoeff U x a =
      G.evalLie (G.iteratedDerivJ x
        (G.adjointJ U (G.ofConstantLie a))) := rfl

/-- The zeroth coefficient is the adjoint action of the value of the jet. -/
@[simp]
lemma adjointCoeff_zero (U : G.gaugeJetGroup) : G.adjointCoeff U 0 = G.adjointRep
    (G.evalGaugeJet U) := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff_eq_evalLie, iteratedDerivJ_zero, LinearMap.id_apply,
    evalLie_adjointJ_ofConstantLie]

/-- A jet with trivial value has trivial zeroth coefficient. -/
lemma adjointCoeff_zero_of_eval_eq_one {U : G.gaugeJetGroup} (hU : G.evalGaugeJet U = 1) :
    G.adjointCoeff U 0 = LinearMap.id := by
  rw [adjointCoeff_zero, hU, map_one, Module.End.one_eq_id]

/-- The coefficients of the identity jet, of which only the base point survives. -/
lemma adjointCoeff_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    G.adjointCoeff (1 : G.gaugeJetGroup) p = if p = 0 then LinearMap.id else 0 := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff_eq_evalLie, map_one, one_apply_eq_self]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [iteratedDerivJ_zero, LinearMap.id_apply, evalLie_ofConstantLie, ite_eq_left rfl,
      LinearMap.id_apply]
  · rw [G.iteratedDerivJ_ofConstantLie_of_ne_zero hp, map_zero, ite_eq_right hp,
      LinearMap.zero_apply]

/-- The coefficients are derivations of the bracket up to convolution, by the iterated
  Leibniz rule for the jet bracket. -/
lemma adjointCoeff_lie (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3))
    (a b : G.lieSubalgebra) :
    G.adjointCoeff U x ⁅a, b⁆ =
      (x.antidiagonal.map fun p => ⁅G.adjointCoeff U p.1 a, G.adjointCoeff U p.2 b⁆).sum := by
  simp only [adjointCoeff_eq_evalLie]
  rw [G.ofConstantLie.map_lie, G.adjointJ_bracket,
    iteratedDerivJ_bracket, map_multiset_sum,
    Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LieHom.map_lie])

/-!

## B. The recursion through the Maurer–Cartan form

-/

/-- One more derivative of a coefficient. Differentiating the adjoint once produces minus
  `ad` of the Maurer–Cartan form, and the remaining derivatives distribute over the bracket
  by the Leibniz rule. -/
lemma adjointCoeff_cons (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    G.adjointCoeff U (μ ::ₘ x) =
      -((x.antidiagonal.map fun p =>
        LieAlgebra.ad ℝ G.lieSubalgebra (G.evalLie
          (G.iteratedDerivJ p.1 (-G.maurerCartan U μ))) ∘ₗ
          G.adjointCoeff U p.2).sum) := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff_eq_evalLie, iteratedDerivJ_cons_eq_comp_derivJ, LinearMap.comp_apply,
    derivJ_adjointJ_ofConstantLie, iteratedDerivJ_bracket, map_multiset_sum, Multiset.map_map,
    LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
    ← Multiset.sum_map_neg'']
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply, LinearMap.comp_apply, LieHom.map_lie, LieAlgebra.ad_apply,
    adjointCoeff_eq_evalLie, map_neg, LinearMap.neg_apply, neg_neg]

/-!

## C. The Taylor–Leibniz theorem

-/

/-- The convolution of the adjoint coefficients with one more derivative. Splitting the
  antidiagonal of `μ ::ₘ s` by where `μ` goes, the terms with `μ` on the right are the
  convolution over `s` with `μ` added on the right, and those with `μ` on the left unfold by
  `adjointCoeff_cons`. -/
lemma sum_antidiagonal_cons_adjointCoeff (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (y : Multiset (Fin 1 ⊕ Fin 3) → G.lieSubalgebra) :
    ((μ ::ₘ s).antidiagonal.map fun p => G.adjointCoeff U p.1 (y p.2)).sum =
      (s.antidiagonal.map fun p => G.adjointCoeff U p.1 (y (μ ::ₘ p.2))).sum
      - (s.antidiagonal.map fun p => (p.1.antidiagonal.map fun q =>
          ⁅G.evalLie (G.iteratedDerivJ q.1 (-G.maurerCartan U μ)),
            G.adjointCoeff U q.2 (y p.2)⁆).sum).sum := by
  rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Multiset.map_map, sub_eq_add_neg, ← Multiset.sum_map_neg'']
  congr 1
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, adjointCoeff_cons,
    LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_))
  rw [Function.comp_apply, LinearMap.comp_apply, LieAlgebra.ad_apply]

/-- The inductive step of the Taylor–Leibniz theorem. The rule for `μ ::ₘ s` derivatives
  follows from the rule for every sub-multiset of `s`. Peeling off `∂_μ` by the Leibniz
  rule `derivJ_adjointJ` leaves `Ad_U (∂_μ Y)`, handled by the rule for `s`, and a bracket
  with the Maurer–Cartan form, handled by the rule for the parts of `s`. On the other side
  the coefficients at `μ ::ₘ p` unfold by `sum_antidiagonal_cons_adjointCoeff`, and the two
  triple sums agree by coassociativity of the antidiagonal. -/
lemma evalLie_iteratedDerivJ_adjoint_cons (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (Y : G.jetLieSubalgebra)
    (ih : ∀ t ≤ s, ∀ Z : G.jetLieSubalgebra, G.evalLie
      (G.iteratedDerivJ t (G.adjointJ U Z)) =
      (t.antidiagonal.map fun p =>
        G.adjointCoeff U p.1 (G.evalLie
          (G.iteratedDerivJ p.2 Z))).sum) :
    G.evalLie (G.iteratedDerivJ (μ ::ₘ s)
      (G.adjointJ U Y)) =
      ((μ ::ₘ s).antidiagonal.map fun p =>
        G.adjointCoeff U p.1 (G.evalLie
          (G.iteratedDerivJ p.2 Y))).sum := by
  have hneg : ⁅G.maurerCartan U μ, G.adjointJ U Y⁆ =
      -⁅-G.maurerCartan U μ, G.adjointJ U Y⁆ := by rw [neg_lie, neg_neg]
  have hL : G.evalLie (G.iteratedDerivJ (μ ::ₘ s)
    (G.adjointJ U Y)) =
      (s.antidiagonal.map fun p =>
        G.adjointCoeff U p.1 (G.evalLie
          (G.iteratedDerivJ (μ ::ₘ p.2) Y))).sum
      - (s.antidiagonal.map fun p => (p.2.antidiagonal.map fun q =>
          ⁅G.evalLie (G.iteratedDerivJ p.1
            (-G.maurerCartan U μ)),
            G.adjointCoeff U q.1 (G.evalLie
              (G.iteratedDerivJ q.2 Y))⁆).sum).sum := by
    rw [iteratedDerivJ_cons_eq_comp_derivJ, LinearMap.comp_apply,
      G.derivJ_adjointJ, hneg, ← sub_eq_add_neg, map_sub,
      map_sub, ih s le_rfl, iteratedDerivJ_bracket, map_multiset_sum, Multiset.map_map]
    congr 1
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
      rw [iteratedDerivJ_cons_eq_comp_derivJ, LinearMap.comp_apply]
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
      rw [Function.comp_apply, LieHom.map_lie, ih p.2 (Multiset.snd_le_of_mem_antidiagonal hp),
        ← LieAlgebra.ad_apply (R := ℝ), map_multiset_sum, Multiset.map_map]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
      simp only [Function.comp_apply, LieAlgebra.ad_apply]
  have hR := G.sum_antidiagonal_cons_adjointCoeff U μ s fun t =>
    G.evalLie (G.iteratedDerivJ t Y)
  beta_reduce at hR
  rw [hL, hR]
  congr 1
  exact (Multiset.sum_antidiagonal_assoc s fun a b c =>
    ⁅G.evalLie (G.iteratedDerivJ a
      (-G.maurerCartan U μ)),
      G.adjointCoeff U b (G.evalLie (G.iteratedDerivJ c Y))⁆).symm

/-- The Taylor–Leibniz theorem for the adjoint action. The base-point Taylor coefficients
  of `Ad_U Y` are the antidiagonal convolution of the coefficients `adjointCoeff U` of
  `Ad_U` with those of `Y`. For a matrix group this is the Leibniz rule for products of
  matrices of power series. Here it follows from the single-derivative Leibniz rule
  `derivJ_adjointJ` by strong induction on the number of derivatives. -/
lemma evalLie_iteratedDerivJ_adjointJ (U : G.gaugeJetGroup)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (Y : G.jetLieSubalgebra) :
    G.evalLie (G.iteratedDerivJ x (G.adjointJ U Y)) =
      (x.antidiagonal.map fun p =>
        G.adjointCoeff U p.1 (G.evalLie
          (G.iteratedDerivJ p.2 Y))).sum := by
  suffices h : ∀ (n : ℕ) (x : Multiset (Fin 1 ⊕ Fin 3)), x.card = n → ∀ Y : G.jetLieSubalgebra,
      G.evalLie (G.iteratedDerivJ x (G.adjointJ U Y)) =
        (x.antidiagonal.map fun p =>
          G.adjointCoeff U p.1 (G.evalLie
            (G.iteratedDerivJ p.2 Y))).sum from
    h x.card x rfl Y
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx Y
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [Multiset.antidiagonal_zero, G.evalLie_adjointJ]
    · obtain ⟨μ, hμ⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr hx0)
      rw [← Multiset.cons_erase hμ]
      refine G.evalLie_iteratedDerivJ_adjoint_cons U μ (x.erase μ) Y fun t ht Z => ?_
      refine ih t.card ?_ t rfl Z
      have h1 := Multiset.card_le_card ht
      have h2 := Multiset.card_erase_lt_of_mem hμ
      omega

/-- The base-point Taylor data of `Ad_U Y` vanish up to a given order whenever those of
  `Y` do. -/
lemma evalLie_iteratedDerivJ_adjoint_eq_zero (U : G.gaugeJetGroup)
    {Y : G.jetLieSubalgebra} {s : Multiset (Fin 1 ⊕ Fin 3)}
    (h : ∀ q ≤ s, G.evalLie (G.iteratedDerivJ q Y) = 0) :
    G.evalLie (G.iteratedDerivJ s (G.adjointJ U Y))
      = 0 := by
  rw [evalLie_iteratedDerivJ_adjointJ]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
  rw [h p.2 (Multiset.snd_le_of_mem_antidiagonal hp), map_zero]

/-- The coefficients are multiplicative up to convolution. The coefficient of a product of
  jets is the antidiagonal convolution of the coefficients of the factors. -/
lemma adjointCoeff_mul (U V : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    G.adjointCoeff (U * V) x =
      (x.antidiagonal.map fun p => G.adjointCoeff U p.1 ∘ₗ G.adjointCoeff V p.2).sum := by
  refine LinearMap.ext fun a => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map, adjointCoeff_eq_evalLie, map_mul,
    mul_apply_eq_comp, evalLie_iteratedDerivJ_adjointJ]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LinearMap.comp_apply]
    rfl)

/-!

## D. The dual coefficients

-/

/-- The physicists' `∂_x (Ad_U)^a_b|₀` acting on the dual adjoint index of a gauge-field
  symbol, the transpose of `adjointCoeff U x`. -/
noncomputable def adjointDualCoeff (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] Module.Dual ℝ G.lieSubalgebra :=
  (G.adjointCoeff U x).dualMap

lemma adjointDualCoeff_apply (U : G.gaugeJetGroup) (x : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ G.lieSubalgebra)
    (a : G.lieSubalgebra) : G.adjointDualCoeff U x φ a = φ (G.adjointCoeff U x a) := rfl

/-- The zeroth dual coefficient is the dual of the adjoint action of the value of the
  jet. -/
lemma adjointDualCoeff_zero_evalGaugeJet (U : G.gaugeJetGroup) :
    G.adjointDualCoeff U 0 = (G.adjointRep (G.evalGaugeJet U)).dualMap := by
  rw [adjointDualCoeff, adjointCoeff_zero]

/-- A jet with trivial value has trivial zeroth dual coefficient. -/
lemma adjointDualCoeff_zero_of_evalGaugeJet_eq_one {U : G.gaugeJetGroup}
    (hU : G.evalGaugeJet U = 1) :
    G.adjointDualCoeff U 0 = LinearMap.id := by
  rw [adjointDualCoeff, G.adjointCoeff_zero_of_eval_eq_one hU, LinearMap.dualMap_id]

/-- The dual form of `adjointCoeff_cons`. One more derivative of a dual coefficient is
  minus the antidiagonal convolution of lower dual coefficients against `ad` of the derived
  Maurer–Cartan form. -/
lemma adjointDualCoeff_cons (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    G.adjointDualCoeff U (μ ::ₘ x) φ =
      -((x.antidiagonal.map fun p =>
        G.adjointDualCoeff U p.2 (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra
          (G.evalLie (G.iteratedDerivJ p.1
            (-G.maurerCartan U μ))))).sum) := by
  refine LinearMap.ext fun a => ?_
  rw [adjointDualCoeff_apply, adjointCoeff_cons, LinearMap.neg_apply, map_neg,
    Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum, Multiset.map_map,
    LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_))
  rfl

/-- The dual coefficient at a single derivative is minus the underived coefficient
  precomposed with `ad` of the base-point Maurer–Cartan form. This is what cancels the
  Leibniz cross terms of the gauge law against the commutator cross terms in the field
  strength. -/
lemma adjointDualCoeff_singleton (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    G.adjointDualCoeff U {μ} φ =
      -G.adjointDualCoeff U 0 (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra
        (G.evalLie (-G.maurerCartan U μ))) := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, adjointDualCoeff_cons]
  simp [Multiset.antidiagonal_zero]

/-- The dual coefficient at two derivatives, the underived coefficient against `ad` of the
  derived Maurer–Cartan form, and the once-derived coefficient against `ad` of the
  Maurer–Cartan form itself. -/
lemma adjointDualCoeff_pair (U : G.gaugeJetGroup) (ρ μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    G.adjointDualCoeff U (ρ ::ₘ {μ}) φ =
      -G.adjointDualCoeff U 0 (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra
        (G.evalLie (G.derivJ ρ (-G.maurerCartan U μ))))
      - G.adjointDualCoeff U {ρ} (φ ∘ₗ LieAlgebra.ad ℝ G.lieSubalgebra
        (G.evalLie (-G.maurerCartan U μ))) := by
  have hanti : ({ρ} : Multiset (Fin 1 ⊕ Fin 3)).antidiagonal =
      {((0 : Multiset (Fin 1 ⊕ Fin 3)), ({ρ} : Multiset (Fin 1 ⊕ Fin 3))),
        (({ρ} : Multiset (Fin 1 ⊕ Fin 3)), (0 : Multiset (Fin 1 ⊕ Fin 3)))} := by
    rw [show ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) = ρ ::ₘ 0 from rfl,
      Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
    simp
  rw [show (ρ ::ₘ {μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ {ρ} from Multiset.cons_swap ρ μ 0,
    adjointDualCoeff_cons, hanti]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, iteratedDerivJ_zero, iteratedDerivJ_singleton,
    LinearMap.id_apply]
  abel

end GlobalGaugeGroup
