/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Basic
/-!
# The Taylor coefficients of the adjoint action

## i. Overview

A gauge jet `U` acts on the gauge algebra of jets by the adjoint action `Ad_U`. What the
transformation law of a gauge field `A_μ ↦ Ad_U A_μ + ω_μ(U)` sees of `Ad_U`, after
differentiating `x` times and evaluating at the base point, is the physicists'
`∂_x (Ad_U)^a_b|₀`: a linear map `adjointCoeff U x : 𝔤 →ₗ[ℝ] 𝔤` on the constant gauge
algebra, and its transpose `adjointDualCoeff U x` on the dual index carried by the field
symbols. This file develops these coefficients for any package `jets`.

The central result is the Taylor–Leibniz theorem `evalLie_iteratedDeriv_adjoint`: the
base-point Taylor coefficients of `Ad_U Y` for an arbitrary jet `Y` are the antidiagonal
convolution of the coefficients of `Ad_U` with those of `Y`. For a matrix group it is the
Leibniz rule for products of matrices of power series; here it is derived from the Leibniz
rule `deriv_adjoint` for a single derivative, by induction on the number of derivatives.
Its corollaries are the multiplicativity `adjointCoeff_mul` of the coefficients up to
convolution, and the recursion `adjointCoeff_cons` expressing one more derivative of a
coefficient through the Maurer–Cartan form.

## ii. Key results

- `LocalGaugeData.adjointCoeff` : the coefficient `∂_x (Ad_U)|₀`, with its values
  `adjointCoeff_zero` at the base point and `adjointCoeff_one` on the identity jet.
- `LocalGaugeData.adjointCoeff_cons` : one more derivative of a coefficient is minus the
  antidiagonal convolution of `ad` of the derived Maurer–Cartan form against lower
  coefficients.
- `LocalGaugeData.evalLie_iteratedDeriv_adjoint` : the Taylor–Leibniz theorem.
- `LocalGaugeData.adjointCoeff_mul` : the coefficients of a product are the convolution
  of the coefficients of the factors.
- `LocalGaugeData.adjointDualCoeff` : the transposed coefficients, with
  `adjointDualCoeff_singleton`, `adjointDualCoeff_pair` and `adjointDualCoeff_cons`.

## iii. Table of contents

- A. The adjoint Taylor coefficients
- B. The recursion through the Maurer–Cartan form
- C. The Taylor–Leibniz theorem
- D. The dual coefficients

-/

@[expose] public section

namespace LocalGaugeData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  (jets : LocalGaugeData G 𝔤 G₀ 𝔤J)

/-!

## A. The adjoint Taylor coefficients

-/

/-- The physicists' `∂_x (Ad_U)^a_b|₀`: include a constant gauge algebra element into
  jets, act by the adjoint of `U`, differentiate `x` times, and evaluate at the base
  point. For `x = 0` this is the adjoint action of the value of `U`; for `x ≠ 0` it sees
  the derivatives of the gauge transformation. -/
noncomputable def adjointCoeff (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) : 𝔤 →ₗ[ℝ] 𝔤 :=
  jets.evalLie.toLinearMap ∘ₗ jets.iteratedDeriv x ∘ₗ jets.adjoint U ∘ₗ jets.ofConstantLie

lemma adjointCoeff_apply (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤) :
    jets.adjointCoeff U x a =
      jets.evalLie (jets.iteratedDeriv x (jets.adjoint U (jets.ofConstantLie a))) := rfl

/-- The zeroth coefficient is the adjoint action of the value of the jet. -/
@[simp]
lemma adjointCoeff_zero (U : G) : jets.adjointCoeff U 0 = jets.adjointValue (jets.eval U) := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff_apply, iteratedDeriv_zero, LinearMap.id_apply, evalLie_adjoint_ofConstantLie]

/-- A jet with trivial value has trivial zeroth coefficient. -/
lemma adjointCoeff_zero_of_eval_eq_one {U : G} (hU : jets.eval U = 1) :
    jets.adjointCoeff U 0 = LinearMap.id := by
  rw [adjointCoeff_zero, hU, map_one, Module.End.one_eq_id]

/-- The coefficients of the identity jet: only the base point survives. -/
lemma adjointCoeff_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.adjointCoeff (1 : G) p = if p = 0 then LinearMap.id else 0 := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff_apply, map_one, Module.End.one_apply]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [iteratedDeriv_zero, LinearMap.id_apply, evalLie_ofConstantLie, if_pos rfl,
      LinearMap.id_apply]
  · rw [jets.iteratedDeriv_ofConstantLie_of_ne_zero hp, map_zero, if_neg hp,
      LinearMap.zero_apply]

/-- The coefficients are derivations of the bracket up to convolution, by the iterated
  Leibniz rule for the jet bracket. -/
lemma adjointCoeff_lie (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) (a b : 𝔤) :
    jets.adjointCoeff U x ⁅a, b⁆ =
      (x.antidiagonal.map fun p => ⁅jets.adjointCoeff U p.1 a, jets.adjointCoeff U p.2 b⁆).sum := by
  simp only [adjointCoeff_apply]
  rw [jets.ofConstantLie_lie, jets.adjoint_lie, iteratedDeriv_bracket, map_multiset_sum,
    Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LieHom.map_lie])

/-!

## B. The recursion through the Maurer–Cartan form

-/

/-- One derivative of the adjoint action on a constant is minus the bracket with the
  Maurer–Cartan form: the Leibniz rule `deriv_adjoint` with the constant's derivative
  killed. -/
lemma deriv_adjoint_ofConstantLie (U : G) (μ : Fin 1 ⊕ Fin 3) (a : 𝔤) :
    jets.deriv μ (jets.adjoint U (jets.ofConstantLie a)) =
      -⁅jets.maurerCartan U μ, jets.adjoint U (jets.ofConstantLie a)⁆ := by
  rw [jets.deriv_adjoint, jets.deriv_ofConstantLie, map_zero, zero_sub]

/-- One more derivative of a coefficient: differentiating the adjoint once produces minus
  `ad` of the Maurer–Cartan form, and the remaining derivatives distribute over the bracket
  by the Leibniz rule. -/
lemma adjointCoeff_cons (U : G) (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.adjointCoeff U (μ ::ₘ x) =
      -((x.antidiagonal.map fun p =>
        LieAlgebra.ad ℝ 𝔤 (jets.evalLie (jets.iteratedDeriv p.1 (jets.maurerCartan U μ))) ∘ₗ
          jets.adjointCoeff U p.2).sum) := by
  refine LinearMap.ext fun a => ?_
  rw [adjointCoeff_apply, iteratedDeriv_cons_eq_comp_deriv, LinearMap.comp_apply,
    deriv_adjoint_ofConstantLie, map_neg, iteratedDeriv_bracket, map_neg, map_multiset_sum,
    Multiset.map_map, LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_))
  simp only [Function.comp_apply, LinearMap.comp_apply, LieHom.map_lie, LieAlgebra.ad_apply,
    adjointCoeff_apply]

/-!

## C. The Taylor–Leibniz theorem

-/

/-- The inductive step of the Taylor–Leibniz theorem: the rule for `μ ::ₘ s` derivatives
  follows from the rule for every sub-multiset of `s`. Peeling off `∂_μ` by the Leibniz
  rule `deriv_adjoint` leaves `Ad_U (∂_μ Y)`, handled by the rule for `s`, and a bracket
  with the Maurer–Cartan form, handled by the rule for the parts of `s`; on the other side
  the coefficients at `μ ::ₘ p` unfold by `adjointCoeff_cons`, and the two triple sums
  agree by coassociativity of the antidiagonal. -/
lemma evalLie_iteratedDeriv_adjoint_cons (U : G) (μ : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (Y : 𝔤J)
    (ih : ∀ t ≤ s, ∀ Z : 𝔤J, jets.evalLie (jets.iteratedDeriv t (jets.adjoint U Z)) =
      (t.antidiagonal.map fun p =>
        jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv p.2 Z))).sum) :
    jets.evalLie (jets.iteratedDeriv (μ ::ₘ s) (jets.adjoint U Y)) =
      ((μ ::ₘ s).antidiagonal.map fun p =>
        jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv p.2 Y))).sum := by
  have hL : jets.evalLie (jets.iteratedDeriv (μ ::ₘ s) (jets.adjoint U Y)) =
      (s.antidiagonal.map fun p =>
        jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv (μ ::ₘ p.2) Y))).sum
      - (s.antidiagonal.map fun p => (p.2.antidiagonal.map fun q =>
          ⁅jets.evalLie (jets.iteratedDeriv p.1 (jets.maurerCartan U μ)),
            jets.adjointCoeff U q.1 (jets.evalLie (jets.iteratedDeriv q.2 Y))⁆).sum).sum := by
    rw [iteratedDeriv_cons_eq_comp_deriv, LinearMap.comp_apply, jets.deriv_adjoint, map_sub,
      map_sub, ih s le_rfl, iteratedDeriv_bracket, map_multiset_sum, Multiset.map_map]
    congr 1
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
      rw [iteratedDeriv_cons_eq_comp_deriv, LinearMap.comp_apply]
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
      rw [Function.comp_apply, LieHom.map_lie, ih p.2 (Multiset.snd_le_of_mem_antidiagonal hp),
        ← LieAlgebra.ad_apply (R := ℝ), map_multiset_sum, Multiset.map_map]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
      simp only [Function.comp_apply, LieAlgebra.ad_apply]
  have hR : ((μ ::ₘ s).antidiagonal.map fun p =>
        jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv p.2 Y))).sum =
      (s.antidiagonal.map fun p =>
        jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv (μ ::ₘ p.2) Y))).sum
      - (s.antidiagonal.map fun p => (p.1.antidiagonal.map fun q =>
          ⁅jets.evalLie (jets.iteratedDeriv q.1 (jets.maurerCartan U μ)),
            jets.adjointCoeff U q.2 (jets.evalLie (jets.iteratedDeriv p.2 Y))⁆).sum).sum := by
    rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map, sub_eq_add_neg, ← Multiset.sum_map_neg'']
    congr 1
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, adjointCoeff_cons,
      LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_))
    rw [Function.comp_apply, LinearMap.comp_apply, LieAlgebra.ad_apply]
  rw [hL, hR]
  congr 1
  exact (Multiset.sum_antidiagonal_assoc s fun a b c =>
    ⁅jets.evalLie (jets.iteratedDeriv a (jets.maurerCartan U μ)),
      jets.adjointCoeff U b (jets.evalLie (jets.iteratedDeriv c Y))⁆).symm

/-- The Taylor–Leibniz theorem for the adjoint action: the base-point Taylor coefficients
  of `Ad_U Y` are the antidiagonal convolution of the coefficients `adjointCoeff U` of
  `Ad_U` with those of `Y`. For a matrix group this is the Leibniz rule for products of
  matrices of power series; here it follows from the single-derivative Leibniz rule
  `deriv_adjoint` by strong induction on the number of derivatives. -/
theorem evalLie_iteratedDeriv_adjoint (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) (Y : 𝔤J) :
    jets.evalLie (jets.iteratedDeriv x (jets.adjoint U Y)) =
      (x.antidiagonal.map fun p =>
        jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv p.2 Y))).sum := by
  suffices h : ∀ (n : ℕ) (x : Multiset (Fin 1 ⊕ Fin 3)), x.card = n → ∀ Y : 𝔤J,
      jets.evalLie (jets.iteratedDeriv x (jets.adjoint U Y)) =
        (x.antidiagonal.map fun p =>
          jets.adjointCoeff U p.1 (jets.evalLie (jets.iteratedDeriv p.2 Y))).sum from
    h x.card x rfl Y
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx Y
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [Multiset.antidiagonal_zero, jets.evalLie_adjoint]
    · obtain ⟨μ, hμ⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr hx0)
      rw [← Multiset.cons_erase hμ]
      refine jets.evalLie_iteratedDeriv_adjoint_cons U μ (x.erase μ) Y fun t ht Z => ?_
      refine ih t.card ?_ t rfl Z
      have h1 := Multiset.card_le_card ht
      have h2 := Multiset.card_erase_lt_of_mem hμ
      omega

/-- The base-point Taylor data of `Ad_U Y` vanish up to a given order whenever those of
  `Y` do. -/
lemma evalLie_iteratedDeriv_adjoint_eq_zero (U : G) {Y : 𝔤J} {s : Multiset (Fin 1 ⊕ Fin 3)}
    (h : ∀ q ≤ s, jets.evalLie (jets.iteratedDeriv q Y) = 0) :
    jets.evalLie (jets.iteratedDeriv s (jets.adjoint U Y)) = 0 := by
  rw [evalLie_iteratedDeriv_adjoint]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
  rw [h p.2 (Multiset.snd_le_of_mem_antidiagonal hp), map_zero]

/-- The coefficients are multiplicative up to convolution: the coefficient of a product of
  jets is the antidiagonal convolution of the coefficients of the factors. -/
lemma adjointCoeff_mul (U V : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.adjointCoeff (U * V) x =
      (x.antidiagonal.map fun p => jets.adjointCoeff U p.1 ∘ₗ jets.adjointCoeff V p.2).sum := by
  refine LinearMap.ext fun a => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map, adjointCoeff_apply, map_mul,
    Module.End.mul_apply, evalLie_iteratedDeriv_adjoint]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, LinearMap.comp_apply]
    rfl)

/-!

## D. The dual coefficients

-/

/-- The physicists' `∂_x (Ad_U)^a_b|₀` acting on the dual adjoint index of a gauge-field
  symbol: the transpose of `adjointCoeff U x`. -/
noncomputable def adjointDualCoeff (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] Module.Dual ℝ 𝔤 :=
  (jets.adjointCoeff U x).dualMap

lemma adjointDualCoeff_apply (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤)
    (a : 𝔤) : jets.adjointDualCoeff U x φ a = φ (jets.adjointCoeff U x a) := rfl

/-- The zeroth dual coefficient is the dual of the adjoint action of the value of the
  jet. -/
lemma adjointDualCoeff_zero (U : G) :
    jets.adjointDualCoeff U 0 = (jets.adjointValue (jets.eval U)).dualMap := by
  rw [adjointDualCoeff, adjointCoeff_zero]

/-- A jet with trivial value has trivial zeroth dual coefficient. -/
lemma adjointDualCoeff_zero_of_eval_eq_one {U : G} (hU : jets.eval U = 1) :
    jets.adjointDualCoeff U 0 = LinearMap.id := by
  rw [adjointDualCoeff, jets.adjointCoeff_zero_of_eval_eq_one hU, LinearMap.dualMap_id]

/-- The dual form of `adjointCoeff_cons`: one more derivative of a dual coefficient is
  minus the antidiagonal convolution of lower dual coefficients against `ad` of the derived
  Maurer–Cartan form. -/
lemma adjointDualCoeff_cons (U : G) (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ 𝔤) :
    jets.adjointDualCoeff U (μ ::ₘ x) φ =
      -((x.antidiagonal.map fun p =>
        jets.adjointDualCoeff U p.2 (φ ∘ₗ LieAlgebra.ad ℝ 𝔤
          (jets.evalLie (jets.iteratedDeriv p.1 (jets.maurerCartan U μ))))).sum) := by
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
lemma adjointDualCoeff_singleton (U : G) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    jets.adjointDualCoeff U {μ} φ =
      -jets.adjointDualCoeff U 0 (φ ∘ₗ LieAlgebra.ad ℝ 𝔤
        (jets.evalLie (jets.maurerCartan U μ))) := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, adjointDualCoeff_cons]
  simp [Multiset.antidiagonal_zero]

/-- The dual coefficient at two derivatives: the underived coefficient against `ad` of the
  derived Maurer–Cartan form, and the once-derived coefficient against `ad` of the
  Maurer–Cartan form itself. -/
lemma adjointDualCoeff_pair (U : G) (ρ μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    jets.adjointDualCoeff U (ρ ::ₘ {μ}) φ =
      -jets.adjointDualCoeff U 0 (φ ∘ₗ LieAlgebra.ad ℝ 𝔤
        (jets.evalLie (jets.deriv ρ (jets.maurerCartan U μ))))
      - jets.adjointDualCoeff U {ρ} (φ ∘ₗ LieAlgebra.ad ℝ 𝔤
        (jets.evalLie (jets.maurerCartan U μ))) := by
  have hanti : ({ρ} : Multiset (Fin 1 ⊕ Fin 3)).antidiagonal =
      {((0 : Multiset (Fin 1 ⊕ Fin 3)), ({ρ} : Multiset (Fin 1 ⊕ Fin 3))),
        (({ρ} : Multiset (Fin 1 ⊕ Fin 3)), (0 : Multiset (Fin 1 ⊕ Fin 3)))} := by
    rw [show ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) = ρ ::ₘ 0 from rfl,
      Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
    simp
  rw [show (ρ ::ₘ {μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ {ρ} from Multiset.cons_swap ρ μ 0,
    adjointDualCoeff_cons, hanti]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, iteratedDeriv_zero, iteratedDeriv_singleton,
    LinearMap.id_apply]
  abel

end LocalGaugeData
