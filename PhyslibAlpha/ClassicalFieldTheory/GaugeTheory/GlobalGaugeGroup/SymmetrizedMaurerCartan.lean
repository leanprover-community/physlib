/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.JetOperations
/-!
# The symmetrized Maurer–Cartan form of a global gauge group

The average of the derivatives of the Maurer–Cartan form over its directions.

## i. Overview

The Maurer–Cartan form `ω_μ(U) = (∂_μ U) U⁻¹` of a gauge jet `U` of a global gauge group `G` is
`G.maurerCartan`, subject to the cocycle law `maurerCartan_cocycle`, its value
`maurerCartan_gaugeJetOfConstant` on constants, and the flatness (structure) equation
`maurerCartan_structure`. This file develops what follows from those laws alone, for any global
gauge group. The statements are about the form `−ω_μ(U) = −(∂_μ U) U⁻¹`, the sign in which the
transformation laws of gauge fields use it.

The main construction is the *symmetrized* Maurer–Cartan form

  `ω̄_r(U) = (1 / |r|) ∑_{μ ∈ r} ∂_{r − {μ}} ω_μ(U)`,

the average over which direction of the multiset `r` is carried by the form itself rather than by a
derivative. Its point is `iteratedDerivJ_maurerCartan_eq_symmetrized_add`: an iterated
derivative `∂_s ω_μ(U)` is the symmetrized form at `μ ::ₘ s` plus an average of iterated derivatives
of *brackets* of Maurer–Cartan forms in strictly fewer directions. This is the structural
equation used to trade an antisymmetric part for lower-order data. It gives the inductive step
`evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq`, and iterating it,
`evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq_all`, the base-point Taylor
data of `ω` are determined by the base-point symmetrized data. How this determines a pure jet, and
the truncation filtration it defines, is the subject of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Truncation`.

## ii. Key results

- `GlobalGaugeGroup.evalLie_iteratedDerivJ_maurerCartan_structure` : the structural
  equation at the base point, to all orders.
- `GlobalGaugeGroup.symmetrizedMaurerCartanForm` : the symmetrized Maurer–Cartan form, with
  `symmetrizedMaurerCartanForm_singleton` and the recursion
  `symmetrizedMaurerCartanForm_cons`.
- `GlobalGaugeGroup.iteratedDerivJ_maurerCartan_eq_symmetrized_add` : the
  symmetrization defect is an average of brackets in fewer directions.
- `GlobalGaugeGroup.evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq_all` :
  the base-point symmetrized data determine the base-point Taylor data of `ω`, with the inductive
  step `evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq`.
- `GlobalGaugeGroup.evalLie_iteratedDerivJ_maurerCartan_eq_zero_of_symmetrized_eq_zero` : the
  base-point half of Maurer–Cartan triangularity.
- `GlobalGaugeGroup.maurerCartan_eq_zero_iff` : the Maurer–Cartan form vanishes
  exactly on the constant jets.

## iii. Table of contents

- A. The structural equation at the base point
- B. The symmetrized Maurer–Cartan form
- C. Determination of the Maurer–Cartan form by its symmetrized coefficients
- D. Vanishing of the Maurer–Cartan form

## iv. References

* None.

-/

@[expose] public section

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The structural equation at the base point

-/

/-- The structure equation for the form `−ω`, `∂_μ (−ω_ν) − ∂_ν (−ω_μ) + ⁅−ω_μ, −ω_ν⁆ = 0`. -/
private lemma structure_neg (U : G.gaugeJetGroup) (μ ν : Fin 1 ⊕ Fin 3) :
    G.derivJ μ (-G.maurerCartan U ν) - G.derivJ ν (-G.maurerCartan U μ) +
      ⁅-G.maurerCartan U μ, -G.maurerCartan U ν⁆ = 0 := by
  rw [map_neg, map_neg, neg_lie, lie_neg, neg_neg, ← G.maurerCartan_structure U μ ν]
  abel

/-- The all-orders structural equation of the Maurer–Cartan form `−ω`, at the base point.
  It is the `s`-th derivative of `∂_μ (−ω_ν) − ∂_ν (−ω_μ) + ⁅−ω_μ, −ω_ν⁆ = 0`, with the bracket
  expanded by the iterated Leibniz rule. -/
lemma evalLie_iteratedDerivJ_maurerCartan_structure
    (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    G.evalLie (G.iteratedDerivJ (μ ::ₘ s) (-G.maurerCartan U ν)) =
      G.evalLie (G.iteratedDerivJ (ν ::ₘ s) (-G.maurerCartan U μ))
      - (s.antidiagonal.map fun p =>
          ⁅G.evalLie (G.iteratedDerivJ p.1 (-G.maurerCartan U μ)),
            G.evalLie (G.iteratedDerivJ p.2 (-G.maurerCartan U ν))⁆).sum := by
  have h0 := congrArg (fun z => G.evalLie (G.iteratedDerivJ s z))
    (G.structure_neg U μ ν)
  simp only [map_add, map_sub, map_zero] at h0
  rw [← LinearMap.comp_apply, ← iteratedDerivJ_cons_eq_comp_derivJ, ← LinearMap.comp_apply,
    ← iteratedDerivJ_cons_eq_comp_derivJ, iteratedDerivJ_bracket, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by rw [Function.comp_apply, LieHom.map_lie])] at h0
  exact eq_sub_of_add_eq (sub_eq_zero.mp (by rw [← h0]; abel))

/-!

## B. The symmetrized Maurer–Cartan form

-/

/-- The symmetrized Maurer–Cartan form `ω̄_r(U) = (1/|r|) ∑_{μ ∈ r} ∂_{r − {μ}} ω_μ(U)`,
  the average, over the directions of `r`, of the Maurer–Cartan form in one direction
  differentiated along the remaining ones. -/
noncomputable def symmetrizedMaurerCartanForm (U : G.gaugeJetGroup) (r : Multiset (Fin 1 ⊕ Fin 3)) :
    G.jetLieSubalgebra :=
  ((1/(r.card : ℝ) : ℝ) • (r.map fun μ =>
    (G.iteratedDerivJ (r - {μ}) (-G.maurerCartan U μ))).sum)

@[simp]
lemma symmetrizedMaurerCartanForm_zero (U : G.gaugeJetGroup) :
    G.symmetrizedMaurerCartanForm U 0 = 0 := by
  simp [symmetrizedMaurerCartanForm]

@[simp]
lemma symmetrizedMaurerCartanForm_singleton (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    G.symmetrizedMaurerCartanForm U {μ} = (-G.maurerCartan U μ) := by
  simp [symmetrizedMaurerCartanForm, iteratedDerivJ_zero]

/-- The recursion for the symmetrized Maurer–Cartan form, peeling one direction off the
  multiset. -/
lemma symmetrizedMaurerCartanForm_cons (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3)
    (r : Multiset (Fin 1 ⊕ Fin 3)) : G.symmetrizedMaurerCartanForm U (μ ::ₘ r) =
    (1/(r.card + 1 : ℝ) : ℝ) • (G.iteratedDerivJ r (-G.maurerCartan U μ))
    + ((r.card : ℝ)/(r.card + 1 : ℝ)) •
      G.derivJ μ (G.symmetrizedMaurerCartanForm U r) := by
  by_cases hr : r = 0
  · subst hr
    simp
  · have hn : (r.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun h => hr (Multiset.card_eq_zero.mp h)
    rw [symmetrizedMaurerCartanForm, symmetrizedMaurerCartanForm, Multiset.map_cons,
      Multiset.sum_cons, Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
      Multiset.map_congr rfl fun ν hν => by
        rw [Multiset.sub_singleton, Multiset.erase_cons_tail_of_mem hν, iteratedDerivJ_cons,
          LinearMap.comp_apply,
          ← Multiset.sub_singleton],
      show (r.map fun ν =>
            G.derivJ μ (G.iteratedDerivJ (r - {ν}) (-G.maurerCartan U ν))) =
          (r.map fun ν =>
            G.iteratedDerivJ (r - {ν}) (-G.maurerCartan U ν)).map
              (G.derivJ μ) from
        (Multiset.map_map _ _ _).symm,
      ← map_multiset_sum, smul_add, map_smul, smul_smul,
      show ((r.card + 1 : ℕ) : ℝ) = (r.card : ℝ) + 1 by push_cast; ring,
      show (r.card : ℝ)/((r.card : ℝ) + 1) * (1/(r.card : ℝ)) = 1/((r.card : ℝ) + 1) by
        field_simp]

/-!

## C. Determination of the Maurer–Cartan form by its symmetrized coefficients

-/

/-- The symmetrization defect of the Maurer–Cartan form. An iterated derivative of
  `ω` is the corresponding symmetrized form plus an average of iterated derivatives
  of brackets of `ω` in strictly fewer directions. This is the structural equation
  `maurerCartan_structure` used to trade the antisymmetric part for lower-order data. -/
lemma iteratedDerivJ_maurerCartan_eq_symmetrized_add (U : G.gaugeJetGroup)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    G.iteratedDerivJ s (-G.maurerCartan U μ) =
      G.symmetrizedMaurerCartanForm U (μ ::ₘ s) +
      (1/(s.card + 1 : ℝ)) • (s.map fun ν =>
        G.iteratedDerivJ (s.erase ν)
          ⁅-G.maurerCartan U μ, -G.maurerCartan U ν⁆).sum := by
  -- each bracket term is a difference of two iterated derivatives of `ω`
  have hswap : ∀ ν ∈ s,
      G.iteratedDerivJ (s.erase ν) ⁅-G.maurerCartan U μ, -G.maurerCartan U ν⁆ =
        G.iteratedDerivJ s (-G.maurerCartan U μ) -
          G.iteratedDerivJ (μ ::ₘ s.erase ν) (-G.maurerCartan U ν) := by
    intro ν hν
    have hb : ⁅-G.maurerCartan U μ, -G.maurerCartan U ν⁆ =
        G.derivJ ν (-G.maurerCartan U μ) - G.derivJ μ
          (-G.maurerCartan U ν) := by
      have h1 : G.derivJ μ (-G.maurerCartan U ν) -
        G.derivJ ν (-G.maurerCartan U μ) =
          -⁅-G.maurerCartan U μ, -G.maurerCartan U ν⁆ :=
        eq_neg_of_add_eq_zero_left (G.structure_neg U μ ν)
      rw [← neg_sub, h1, neg_neg]
    rw [hb, map_sub]
    congr 1
    · conv_rhs => rw [← Multiset.cons_erase hν]
      rw [iteratedDerivJ_cons_eq_comp_derivJ, LinearMap.comp_apply]
    · rw [iteratedDerivJ_cons_eq_comp_derivJ, LinearMap.comp_apply]
  rw [symmetrizedMaurerCartanForm, Multiset.map_cons, Multiset.sum_cons,
    Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
    Multiset.map_congr rfl fun ν hν => by
      rw [Multiset.sub_singleton, Multiset.erase_cons_tail_of_mem hν],
    Multiset.map_congr rfl hswap, Multiset.sum_map_sub, Multiset.map_const',
    Multiset.sum_replicate, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  match_scalars <;> field_simp <;> ring

/-- Maurer–Cartan triangularity, base-point half. If the base-point symmetrized
  Maurer–Cartan data of `U` vanish in every nonempty multiset of at most `n` directions,
  then so do all its base-point Maurer–Cartan Taylor coefficients below order `n`. The
  induction is on the order. The symmetrization defect
  `iteratedDerivJ_maurerCartan_eq_symmetrized_add` expresses `∂_s ω_μ` through the
  symmetrized form, which vanishes by hypothesis, and brackets of `ω`s differentiated
  strictly fewer times, which vanish by the inductive hypothesis through
  `evalLie_iteratedDerivJ_bracket_congr`. -/
lemma evalLie_iteratedDerivJ_maurerCartan_eq_zero_of_symmetrized_eq_zero
    (U : G.gaugeJetGroup) {n : ℕ}
    (h : ∀ r : Multiset (Fin 1 ⊕ Fin 3), r ≠ 0 → r.card ≤ n →
      G.evalLie (G.symmetrizedMaurerCartanForm U r) = 0)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (hs : s.card < n) :
    G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ))
      = 0 := by
  have hall : ∀ (k : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = k →
      k < n → G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ)) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s μ hs hk
      rw [iteratedDerivJ_maurerCartan_eq_symmetrized_add G U s μ, map_add, map_smul]
      have h1 : G.evalLie (G.symmetrizedMaurerCartanForm U (μ ::ₘ s)) = 0 := by
        refine h (μ ::ₘ s) Multiset.cons_ne_zero ?_
        rw [Multiset.card_cons, hs]
        omega
      have h2 : G.evalLie ((s.map fun ν => G.iteratedDerivJ (s.erase ν)
          ⁅-G.maurerCartan U μ, -G.maurerCartan U ν⁆).sum) = 0 := by
        rw [map_multiset_sum, Multiset.map_map]
        refine Multiset.sum_eq_zero fun x hx => ?_
        obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hx
        have hzero : ∀ (ρ : Fin 1 ⊕ Fin 3) (p : Multiset (Fin 1 ⊕ Fin 3)), p ≤ s.erase ν →
            G.evalLie (G.iteratedDerivJ p (-G.maurerCartan U ρ)) =
              G.evalLie (G.iteratedDerivJ p
                (0 : G.jetLieSubalgebra)) := by
          intro ρ p hp
          have hcard : p.card < k := by
            have h3 := Multiset.card_le_card hp
            have h4 := Multiset.card_erase_add_one hν
            omega
          rw [ih p.card hcard p ρ rfl (hcard.trans hk), map_zero, map_zero]
        simp only [Function.comp_apply]
        rw [G.evalLie_iteratedDerivJ_bracket_congr (s.erase ν) _ _ 0 0
          (hzero μ) (hzero ν)]
        simp
      rw [h1, h2]
      simp
  exact hall s.card s μ rfl hs

/-- The determination step. If the base-point symmetrized Maurer–Cartan data of `U` and
  `V` agree, and their Maurer–Cartan Taylor data agree in fewer than `n` directions,
  then they agree in `n` directions. -/
lemma evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq
    (U V : G.gaugeJetGroup) (n : ℕ)
    (hsym : ∀ r, G.evalLie (G.symmetrizedMaurerCartanForm U r) =
      G.evalLie (G.symmetrizedMaurerCartanForm V r))
    (ih : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card < n →
      G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ)) =
        G.evalLie (G.iteratedDerivJ s
          (-G.maurerCartan V μ)))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (hs : s.card = n) :
    G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ)) =
      G.evalLie (G.iteratedDerivJ s
        (-G.maurerCartan V μ)) := by
  rw [iteratedDerivJ_maurerCartan_eq_symmetrized_add G U s μ,
    iteratedDerivJ_maurerCartan_eq_symmetrized_add G V s μ,
    map_add, map_add, map_smul, map_smul, hsym]
  refine congrArg (fun z => G.evalLie (G.symmetrizedMaurerCartanForm V (μ ::ₘ s)) +
    (1/(s.card + 1 : ℝ)) • z) ?_
  rw [map_multiset_sum, map_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun ν hν => ?_)
  have hlt : ∀ p : Multiset (Fin 1 ⊕ Fin 3), p ≤ s.erase ν → p.card < n := by
    intro p hp
    have h1 := Multiset.card_le_card hp
    have h2 := Multiset.card_erase_add_one hν
    omega
  exact G.evalLie_iteratedDerivJ_bracket_congr (s.erase ν) _ _ _ _
    (fun p hp => ih p μ (hlt p hp)) (fun p hp => ih p ν (hlt p hp))

/-- The symmetrized data determine the Maurer–Cartan Taylor data. If the base-point
  symmetrized Maurer–Cartan data of `U` and `V` agree, so do all base-point Taylor
  coefficients of their Maurer–Cartan forms. Strong induction on the order, with
  `evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq` as the step. -/
lemma evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq_all
    (U V : G.gaugeJetGroup)
    (hsym : ∀ r, G.evalLie (G.symmetrizedMaurerCartanForm U r) =
      G.evalLie (G.symmetrizedMaurerCartanForm V r))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ)) =
      G.evalLie (G.iteratedDerivJ s
        (-G.maurerCartan V μ)) := by
  have hall : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = n →
      G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ)) =
        G.evalLie (G.iteratedDerivJ s
          (-G.maurerCartan V μ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro s μ hs
        exact G.evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq U V n hsym
          (fun p ν hp => ih p.card hp p ν rfl) s μ hs
  exact hall s.card s μ rfl

/-!

## D. Vanishing of the Maurer–Cartan form

-/

/-- The Maurer–Cartan form of a gauge jet vanishes exactly when the jet is constant. -/
lemma maurerCartan_eq_zero_iff (U : G.gaugeJetGroup) :
    G.maurerCartan U = 0 ↔ U = G.gaugeJetOfConstant (G.evalGaugeJet U) := by
  refine ⟨fun h => G.eq_gaugeJetOfConstant_of_maurerCartan_eq_zero (congrFun h), fun h => ?_⟩
  funext μ
  rw [h, G.maurerCartan_gaugeJetOfConstant]
  rfl

end GlobalGaugeGroup
