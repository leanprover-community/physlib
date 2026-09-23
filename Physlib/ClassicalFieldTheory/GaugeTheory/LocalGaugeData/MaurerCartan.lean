/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Basic
/-!
# The Maurer–Cartan form of a local gauge data package

## i. Overview

The Maurer–Cartan form `ω_μ(U) = i (∂_μ U) U⁻¹` of a package
`jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J` is the field `jets.maurerCartan`, subject to the cocycle
law `maurerCartan_cocycle`, its value `maurerCartan_ofConstant` on constants, and the
flatness (structural) equation `maurerCartan_structure`. This file develops what follows
from those laws alone, for any package: nothing here mentions a particular gauge group.

The main construction is the *symmetrized* Maurer–Cartan form

  `ω̄_r(U) = (1 / |r|) ∑_{μ ∈ r} ∂_{r − {μ}} ω_μ(U)`,

the average over which direction of the multiset `r` is carried by the form itself rather
than by a derivative. Its point is `iteratedDeriv_maurerCartan_eq_symmetrized_add`: an
iterated derivative `∂_s ω_μ(U)` is the symmetrized form at `μ ::ₘ s` plus an average of
iterated derivatives of *brackets* of Maurer–Cartan forms in strictly fewer directions —
the structural equation used to trade an antisymmetric part for lower-order data. Iterating
that gives `evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq`: the base-point Taylor
data of `ω` is determined by the base-point symmetrized data. How this determines a pure
jet, and the truncation filtration it defines, is the subject of
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Truncation`.

## ii. Key results

- `LocalGaugeData.evalLie_iteratedDeriv_maurerCartan_structure` : the structural equation
  at the base point, to all orders.
- `LocalGaugeData.symmetrizedMaurerCartanForm` : the symmetrized Maurer–Cartan form, with
  `symmetrizedMaurerCartanForm_singleton` and the recursion
  `symmetrizedMaurerCartanForm_cons`.
- `LocalGaugeData.iteratedDeriv_maurerCartan_eq_symmetrized_add` : the symmetrization
  defect is an average of brackets in fewer directions.
- `LocalGaugeData.evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq` : the base-point
  symmetrized data determines the base-point Taylor data of `ω`.
- `LocalGaugeData.evalLie_iteratedDeriv_maurerCartan_eq_zero_of_symmetrized_eq_zero` : the
  base-point half of Maurer–Cartan triangularity.
- `LocalGaugeData.maurerCartan_eq_zero_iff` : in a faithful package, the Maurer–Cartan form
  vanishes exactly on the constant jets.

## iii. Table of contents

- A. The structural equation at the base point
- B. The symmetrized Maurer–Cartan form
- C. Determination of the Maurer–Cartan form by its symmetrized coefficients
- D. Faithful packages and the Maurer–Cartan form

-/

@[expose] public section

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J)

/-!

## A. The structural equation at the base point

-/

/-- The all-orders structural equation of the Maurer–Cartan form, at the base point:
  the `s`-th derivative of `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`, with the bracket
  expanded by the iterated Leibniz rule. -/
lemma evalLie_iteratedDeriv_maurerCartan_structure
    (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    jets.evalLie (jets.iteratedDeriv (μ ::ₘ s) (jets.maurerCartan U ν)) =
      jets.evalLie (jets.iteratedDeriv (ν ::ₘ s) (jets.maurerCartan U μ))
      - (s.antidiagonal.map fun p =>
          ⁅jets.evalLie (jets.iteratedDeriv p.1 (jets.maurerCartan U μ)),
            jets.evalLie (jets.iteratedDeriv p.2 (jets.maurerCartan U ν))⁆).sum := by
  have h0 := congrArg (fun z => jets.evalLie (jets.iteratedDeriv s z))
    (jets.maurerCartan_structure U μ ν)
  simp only [map_add, map_sub, map_zero] at h0
  rw [← LinearMap.comp_apply, ← iteratedDeriv_cons_eq_comp_deriv, ← LinearMap.comp_apply,
    ← iteratedDeriv_cons_eq_comp_deriv, iteratedDeriv_bracket, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by rw [Function.comp_apply, LieHom.map_lie])] at h0
  exact eq_sub_of_add_eq (sub_eq_zero.mp (by rw [← h0]; abel))

/-!

## B. The symmetrized Maurer–Cartan form

-/

/-- The symmetrized Maurer–Cartan form `ω̄_r(U) = (1/|r|) ∑_{μ ∈ r} ∂_{r − {μ}} ω_μ(U)`:
  the average, over the directions of `r`, of the Maurer–Cartan form in one direction
  differentiated along the remaining ones. -/
noncomputable def symmetrizedMaurerCartanForm (U : GJ) (r : Multiset (Fin 1 ⊕ Fin 3)) : 𝔤J :=
  ((1/(r.card : ℝ) : ℝ) • (r.map fun μ =>
    (jets.iteratedDeriv (r - {μ}) (jets.maurerCartan U μ))).sum)

@[simp]
lemma symmetrizedMaurerCartanForm_apply_zero (U : GJ) :
    jets.symmetrizedMaurerCartanForm U 0 = 0 := by
  simp [symmetrizedMaurerCartanForm]

@[simp]
lemma symmetrizedMaurerCartanForm_one : jets.symmetrizedMaurerCartanForm 1 = 0 := by
  funext r
  simp [symmetrizedMaurerCartanForm, jets.maurerCartan_one]

@[simp]
lemma symmetrizedMaurerCartanForm_ofConstant (g : G₀) :
    jets.symmetrizedMaurerCartanForm (jets.ofConstant g) = 0 := by
  funext r
  simp [symmetrizedMaurerCartanForm, jets.maurerCartan_ofConstant]

@[simp]
lemma symmetrizedMaurerCartanForm_singleton (U : GJ) (μ : Fin 1 ⊕ Fin 3) :
    jets.symmetrizedMaurerCartanForm U {μ} = jets.maurerCartan U μ := by
  simp [symmetrizedMaurerCartanForm, iteratedDeriv_zero]

/-- The recursion for the symmetrized Maurer–Cartan form: peeling one direction off the
  multiset. -/
lemma symmetrizedMaurerCartanForm_cons (U : GJ) (μ : Fin 1 ⊕ Fin 3)
    (r : Multiset (Fin 1 ⊕ Fin 3)) : jets.symmetrizedMaurerCartanForm U (μ ::ₘ r) =
    (1/(r.card + 1 : ℝ) : ℝ) • (jets.iteratedDeriv r (jets.maurerCartan U μ))
    + ((r.card : ℝ)/(r.card + 1 : ℝ)) •
      jets.deriv μ (jets.symmetrizedMaurerCartanForm U r) := by
  by_cases hr : r = 0
  · subst hr
    simp
  · have hn : (r.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun h => hr (Multiset.card_eq_zero.mp h)
    have herase : ∀ ν ∈ r, (μ ::ₘ r).erase ν = μ ::ₘ r.erase ν := by
      intro ν hν
      rcases eq_or_ne ν μ with rfl | h
      · rw [Multiset.erase_cons_head, Multiset.cons_erase hν]
      · rw [Multiset.erase_cons_tail _ h.symm]
    rw [symmetrizedMaurerCartanForm, symmetrizedMaurerCartanForm, Multiset.map_cons,
      Multiset.sum_cons, Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
      Multiset.map_congr rfl fun ν hν => by
        rw [Multiset.sub_singleton, herase ν hν, iteratedDeriv_cons, LinearMap.comp_apply,
          ← Multiset.sub_singleton],
      show (r.map fun ν =>
            jets.deriv μ (jets.iteratedDeriv (r - {ν}) (jets.maurerCartan U ν))) =
          (r.map fun ν =>
            jets.iteratedDeriv (r - {ν}) (jets.maurerCartan U ν)).map (jets.deriv μ) from
        (Multiset.map_map _ _ _).symm,
      ← map_multiset_sum, smul_add, map_smul, smul_smul,
      show ((r.card + 1 : ℕ) : ℝ) = (r.card : ℝ) + 1 by push_cast; ring,
      show (r.card : ℝ)/((r.card : ℝ) + 1) * (1/(r.card : ℝ)) = 1/((r.card : ℝ) + 1) by
        field_simp]

/-!

## C. Determination of the Maurer–Cartan form by its symmetrized coefficients

-/

/-- The symmetrization defect of the Maurer–Cartan form: an iterated derivative of
  `ω` is the corresponding symmetrized form plus an average of iterated derivatives
  of brackets of `ω` in strictly fewer directions. This is the structural equation
  `maurerCartan_structure` used to trade the antisymmetric part for lower-order data. -/
lemma iteratedDeriv_maurerCartan_eq_symmetrized_add (U : GJ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    jets.iteratedDeriv s (jets.maurerCartan U μ) =
      jets.symmetrizedMaurerCartanForm U (μ ::ₘ s) +
      (1/(s.card + 1 : ℝ)) • (s.map fun ν =>
        jets.iteratedDeriv (s.erase ν)
          ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆).sum := by
  -- each bracket term is a difference of two iterated derivatives of `ω`
  have hswap : ∀ ν ∈ s,
      jets.iteratedDeriv (s.erase ν) ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆ =
        jets.iteratedDeriv s (jets.maurerCartan U μ) -
          jets.iteratedDeriv (μ ::ₘ s.erase ν) (jets.maurerCartan U ν) := by
    intro ν hν
    have hb : ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆ =
        jets.deriv ν (jets.maurerCartan U μ) - jets.deriv μ (jets.maurerCartan U ν) := by
      have h1 : jets.deriv μ (jets.maurerCartan U ν) - jets.deriv ν (jets.maurerCartan U μ) =
          -⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆ :=
        eq_neg_of_add_eq_zero_left (jets.maurerCartan_structure U μ ν)
      rw [← neg_sub, h1, neg_neg]
    rw [hb, map_sub]
    congr 1
    · conv_rhs => rw [← Multiset.cons_erase hν]
      rw [show (ν ::ₘ s.erase ν : Multiset (Fin 1 ⊕ Fin 3)) = s.erase ν + {ν} from by
          rw [add_comm, Multiset.singleton_add],
        iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
    · rw [show (μ ::ₘ s.erase ν : Multiset (Fin 1 ⊕ Fin 3)) = s.erase ν + {μ} from by
          rw [add_comm, Multiset.singleton_add],
        iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
  have herase : ∀ ν ∈ s, (μ ::ₘ s).erase ν = μ ::ₘ s.erase ν := by
    intro ν hν
    rcases eq_or_ne ν μ with rfl | hne
    · rw [Multiset.erase_cons_head, Multiset.cons_erase hν]
    · rw [Multiset.erase_cons_tail _ hne.symm]
  rw [symmetrizedMaurerCartanForm, Multiset.map_cons, Multiset.sum_cons,
    Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
    Multiset.map_congr rfl fun ν hν => by rw [Multiset.sub_singleton, herase ν hν],
    Multiset.map_congr rfl hswap, Multiset.sum_map_sub, Multiset.map_const',
    Multiset.sum_replicate, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  match_scalars <;> field_simp <;> ring

/-- Maurer–Cartan triangularity, base-point half: if the base-point symmetrized
  Maurer–Cartan data of `U` vanish in every nonempty multiset of at most `n` directions,
  then so do all its base-point Maurer–Cartan Taylor coefficients below order `n`. The
  induction is on the order: the symmetrization defect
  `iteratedDeriv_maurerCartan_eq_symmetrized_add` expresses `∂_s ω_μ` through the
  symmetrized form, which vanishes by hypothesis, and brackets of `ω`s differentiated
  strictly fewer times, which vanish by the inductive hypothesis through
  `evalLie_iteratedDeriv_bracket_congr`. -/
lemma evalLie_iteratedDeriv_maurerCartan_eq_zero_of_symmetrized_eq_zero (U : GJ) {n : ℕ}
    (h : ∀ r : Multiset (Fin 1 ⊕ Fin 3), r ≠ 0 → r.card ≤ n →
      jets.evalLie (jets.symmetrizedMaurerCartanForm U r) = 0)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (hs : s.card < n) :
    jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) = 0 := by
  have hall : ∀ (k : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = k →
      k < n → jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s μ hs hk
      rw [iteratedDeriv_maurerCartan_eq_symmetrized_add jets U s μ, map_add, map_smul]
      have h1 : jets.evalLie (jets.symmetrizedMaurerCartanForm U (μ ::ₘ s)) = 0 := by
        refine h (μ ::ₘ s) Multiset.cons_ne_zero ?_
        rw [Multiset.card_cons, hs]
        omega
      have h2 : jets.evalLie ((s.map fun ν => jets.iteratedDeriv (s.erase ν)
          ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆).sum) = 0 := by
        rw [map_multiset_sum, Multiset.map_map]
        refine Multiset.sum_eq_zero fun x hx => ?_
        obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hx
        have hzero : ∀ (ρ : Fin 1 ⊕ Fin 3) (p : Multiset (Fin 1 ⊕ Fin 3)), p ≤ s.erase ν →
            jets.evalLie (jets.iteratedDeriv p (jets.maurerCartan U ρ)) =
              jets.evalLie (jets.iteratedDeriv p (0 : 𝔤J)) := by
          intro ρ p hp
          have hcard : p.card < k := by
            have h3 := Multiset.card_le_card hp
            have h4 := Multiset.card_erase_add_one hν
            omega
          rw [ih p.card hcard p ρ rfl (hcard.trans hk), map_zero, map_zero]
        simp only [Function.comp_apply]
        rw [jets.evalLie_iteratedDeriv_bracket_congr (s.erase ν) _ _ 0 0
          (hzero μ) (hzero ν)]
        simp
      rw [h1, h2]
      simp
  exact hall s.card s μ rfl hs

/-- Determination step: if the base-point symmetrized Maurer–Cartan data of `U` and
  `V` agree, and their Maurer–Cartan Taylor data agree in fewer than `n` directions,
  then they agree in `n` directions. -/
lemma evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq (U V : GJ) (n : ℕ)
    (hsym : ∀ r, jets.evalLie (jets.symmetrizedMaurerCartanForm U r) =
      jets.evalLie (jets.symmetrizedMaurerCartanForm V r))
    (ih : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card < n →
      jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) =
        jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan V μ)))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (hs : s.card = n) :
    jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) =
      jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan V μ)) := by
  rw [iteratedDeriv_maurerCartan_eq_symmetrized_add jets U s μ,
    iteratedDeriv_maurerCartan_eq_symmetrized_add jets V s μ,
    map_add, map_add, map_smul, map_smul, hsym]
  refine congrArg (fun z => jets.evalLie (jets.symmetrizedMaurerCartanForm V (μ ::ₘ s)) +
    (1/(s.card + 1 : ℝ)) • z) ?_
  rw [map_multiset_sum, map_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun ν hν => ?_)
  have hlt : ∀ p : Multiset (Fin 1 ⊕ Fin 3), p ≤ s.erase ν → p.card < n := by
    intro p hp
    have h1 := Multiset.card_le_card hp
    have h2 := Multiset.card_erase_add_one hν
    omega
  exact jets.evalLie_iteratedDeriv_bracket_congr (s.erase ν) _ _ _ _
    (fun p hp => ih p μ (hlt p hp)) (fun p hp => ih p ν (hlt p hp))

/-!

## D. Faithful packages and the Maurer–Cartan form

-/

/-- In a faithful package, the Maurer–Cartan form vanishes exactly on the constant jets. -/
lemma maurerCartan_eq_zero_iff [jets.Faithful] (U : GJ) :
    jets.maurerCartan U = 0 ↔ U = jets.ofConstant (jets.eval U) := by
  refine ⟨Faithful.eq_ofConstant_of_maurerCartan_eq_zero, fun h => ?_⟩
  funext μ
  rw [h, jets.maurerCartan_ofConstant]
  rfl

end LocalGaugeData
