/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.AdjointCoeff
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SymmetrizedMaurerCartan
/-!
# The truncation filtration of the jet gauge group

The normal subgroups of gauge jets that are trivial up to a given order.

## i. Overview

A jet of gauge transformations is *trivial to order `n`* when it agrees with the identity up to and
including its `n`-th derivatives. For a matrix group this is a statement about Taylor coefficients
of matrix entries. It is phrased here through two things given at the base point, the value
`G.evalGaugeJet U` and the Maurer–Cartan form: `U` is trivial to order `n` when
`G.evalGaugeJet U = 1` and the base-point Taylor coefficients of `ω_μ(U)` vanish below order
`n`. The Taylor–Leibniz theorem makes these jets a subgroup `truncationKer n`, normal in
`G.gaugeJetGroup`, and the subgroups decrease with `n`.

The zeroth member, the *pure jets* with `G.evalGaugeJet U = 1`, is the complement of the constant
jets. Every jet factors uniquely as a pure jet times the constant jet of its value,
`truncationProjZero` and `eq_truncationProjZero_mul_ofConstant`. A pure jet is determined by its
Maurer–Cartan form, and hence by the base-point values of the symmetrized Maurer–Cartan form,
`symmetrizedMaurerCartanCoeff`. Membership in `truncationKer n` is exactly the vanishing of those
symmetrized data up to order `n`.

What a jet trivial to order `n` does to the fields is the point of the filtration: all its
adjoint Taylor coefficients of order between `1` and `n` vanish,
`adjointCoeff_eq_zero_of_mem_truncationKer`, so it acts on the gauge-field symbols with at
most `n` derivatives by a pure translation.

## ii. Key results

- `GlobalGaugeGroup.truncationKer` : the jets trivial to order `n`, as a subgroup.
- `GlobalGaugeGroup.mem_truncationKer_zero_iff_evalGaugeJet` : the pure jets.
- `GlobalGaugeGroup.adjointCoeff_eq_zero_of_mem_truncationKer` : deep jets kill the positive
  adjoint coefficients.
- `GlobalGaugeGroup.truncationKer_normal` : the filtration is by normal subgroups.
- `GlobalGaugeGroup.truncationProjZero` : the projection of a jet onto the pure jets.
- `GlobalGaugeGroup.maurerCartan_injOn_truncationKer_zero` : a pure jet is determined by its
  Maurer–Cartan form.
- `GlobalGaugeGroup.symmetrizedMaurerCartanCoeff_injective` : and by its symmetrized
  Maurer–Cartan data.
- `GlobalGaugeGroup.mem_truncationKer_iff_symmetrizedMaurerCartanCoeff_eq_zero` : the
  filtration through the symmetrized data.
- `GlobalGaugeGroup.radial` : the radial component `−∑_μ x_μ ω_μ` of the Maurer–Cartan form,
  whose Taylor data are the symmetrized data.
- `GlobalGaugeGroup.exists_radial_eq` : radial integrability, which with the realisation of
  Taylor data makes the symmetrized data free coordinates on the pure jets,
  `GlobalGaugeGroup.symmetrizedMaurerCartanCoeff_bijective`.
- `GlobalGaugeGroup.truncation` : the `n`-th truncation of a gauge jet, a matrix of
  polynomials.
- `GlobalGaugeGroup.truncation_eq_one_of_mem_truncationKer` : jets trivial to order `n`
  truncate to the identity.

## iii. Table of contents

- A. The truncation filtration
- B. The adjoint coefficients of a deep jet
- C. Normality
- D. The projection onto the pure jets
- E. Pure jets and their Maurer–Cartan data
- F. The radial component of the Maurer–Cartan form
- G. Radial integrability
- H. Truncation of a gauge jet

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The truncation filtration

-/

/-- The jets trivial to order `n`, with value the identity and with the base-point Taylor
  coefficients of the Maurer–Cartan form vanishing below order `n`. Closure under products and
  inverses is the cocycle law together with the Taylor–Leibniz theorem for the adjoint action. -/
noncomputable def truncationKer (n : ℕ) : Subgroup G.gaugeJetGroup where
  carrier := {U | G.evalGaugeJet U = 1 ∧ ∀ (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3),
    s.card < n → G.evalLie (G.iteratedDerivJ s (G.maurerCartan U μ)) = 0}
  one_mem' := ⟨map_one _, fun s μ _ => by rw [maurerCartan_one, map_zero, map_zero]⟩
  mul_mem' := by
    intro U V hU hV
    refine ⟨by rw [map_mul, hU.1, hV.1, one_mul], fun s μ hs => ?_⟩
    rw [maurerCartan_cocycle, map_add, map_add, hU.2 s μ hs, zero_add]
    exact G.evalLie_iteratedDerivJ_adjoint_eq_zero U fun q hq =>
      hV.2 q μ (lt_of_le_of_lt (Multiset.card_le_card hq) hs)
  inv_mem' := by
    intro U hU
    refine ⟨by rw [map_inv, hU.1, inv_one], fun s μ hs => ?_⟩
    rw [maurerCartan_inv_adjointJ, map_neg, map_neg, neg_eq_zero]
    exact G.evalLie_iteratedDerivJ_adjoint_eq_zero U⁻¹ fun q hq =>
      hU.2 q μ (lt_of_le_of_lt (Multiset.card_le_card hq) hs)

/-- The zeroth truncation kernel is the group of pure jets, those with identity value. -/
lemma mem_truncationKer_zero_iff_evalGaugeJet {U : G.gaugeJetGroup} : U ∈ G.truncationKer 0 ↔
    G.evalGaugeJet U = 1 :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ hs => absurd hs (Nat.not_lt_zero _)⟩⟩

/-!

## B. The adjoint coefficients of a deep jet

-/

/-- Deep jets kill the positive adjoint coefficients. For a jet trivial to order `n`, the
  adjoint coefficients of order between `1` and `n` vanish. One derivative of the adjoint
  is `ad` of the Maurer–Cartan form, whose base-point data vanish below order `n`. -/
lemma adjointCoeff_eq_zero_of_mem_truncationKer {n : ℕ} {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n)
    {x : Multiset (Fin 1 ⊕ Fin 3)} (hx : x ≠ 0) (hxn : x.card ≤ n) :
    G.adjointCoeff U x = 0 := by
  obtain ⟨μ, hμ⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr hx)
  rw [← Multiset.cons_erase hμ, adjointCoeff_cons, neg_eq_zero]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
  have h1 := Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)
  have h2 := Multiset.card_erase_add_one hμ
  rw [map_neg, map_neg, hU.2 p.1 μ (by omega), neg_zero, map_zero, LinearMap.zero_comp]

/-- The dual form of `adjointCoeff_eq_zero_of_mem_truncationKer`. -/
lemma adjointDualCoeff_eq_zero_of_mem_truncationKer {n : ℕ} {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hx : x ≠ 0)
    (hxn : x.card ≤ n) : G.adjointDualCoeff U x = 0 := by
  rw [adjointDualCoeff, G.adjointCoeff_eq_zero_of_mem_truncationKer hU hx hxn]
  exact LinearMap.ext fun φ => LinearMap.ext fun a => map_zero φ

/-- Up to order `n`, a jet trivial to order `n` is invisible on the right of a product. -/
lemma adjointCoeff_mul_of_mem_truncationKer_right (g : G.gaugeJetGroup) {n : ℕ}
    {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hxn : x.card ≤ n) :
    G.adjointCoeff (g * U) x = G.adjointCoeff g x := by
  rw [adjointCoeff_mul, Multiset.sum_antidiagonal_eq_of_snd_ne_zero x _ fun p hp hp2 => ?_]
  · rw [G.adjointCoeff_zero_of_eval_eq_one hU.1, LinearMap.comp_id]
  · rw [G.adjointCoeff_eq_zero_of_mem_truncationKer hU hp2
      ((Multiset.card_le_card (Multiset.snd_le_of_mem_antidiagonal hp)).trans hxn),
      LinearMap.comp_zero]

/-- Up to order `n`, a conjugate of a jet trivial to order `n` has the adjoint
  coefficients of the identity. -/
lemma adjointCoeff_conj_of_mem_truncationKer (g : G.gaugeJetGroup) {n : ℕ} {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hxn : x.card ≤ n) :
    G.adjointCoeff (g * U * g⁻¹) x = G.adjointCoeff 1 x := by
  rw [adjointCoeff_mul, Multiset.map_congr rfl (fun p hp => by
      rw [G.adjointCoeff_mul_of_mem_truncationKer_right g hU
        ((Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)).trans hxn)]),
    ← adjointCoeff_mul, mul_inv_cancel]

/-- Up to order `n`, a conjugate of a jet trivial to order `n` acts trivially on the
  base-point Taylor data of the jet Lie algebra. -/
lemma evalLie_iteratedDerivJ_adjoint_conj_of_mem_truncationKer (g : G.gaugeJetGroup) {n : ℕ}
    {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n) {s : Multiset (Fin 1 ⊕ Fin 3)} (hs : s.card ≤ n)
    (Y : G.jetLieSubalgebra) : G.evalLie
      (G.iteratedDerivJ s (G.adjointJ (g * U * g⁻¹) Y)) =
      G.evalLie (G.iteratedDerivJ s Y) := by
  rw [evalLie_iteratedDerivJ_adjointJ, Multiset.sum_antidiagonal_eq_of_fst_ne_zero s _
    fun p hp hp1 => ?_]
  · rw [G.adjointCoeff_conj_of_mem_truncationKer g hU (by simp), adjointCoeff_one,
      ite_eq_left rfl, LinearMap.id_apply]
  · rw [G.adjointCoeff_conj_of_mem_truncationKer g hU
      ((Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)).trans hs),
      adjointCoeff_one, ite_eq_right hp1, LinearMap.zero_apply]

/-!

## C. Normality

-/

/-- The truncation kernels are normal subgroups, since conjugating a jet trivial to order `n`
  gives a jet trivial to order `n`. -/
instance truncationKer_normal (n : ℕ) : (G.truncationKer n).Normal where
  conj_mem U hU g := by
    refine ⟨by rw [map_mul, map_mul, hU.1, mul_one, map_inv, mul_inv_cancel], fun s μ hs => ?_⟩
    rw [maurerCartan_conj, map_sub, map_add, map_sub, map_add,
      G.evalLie_iteratedDerivJ_adjoint_conj_of_mem_truncationKer g hU hs.le,
      G.evalLie_iteratedDerivJ_adjoint_eq_zero g fun q hq =>
        hU.2 q μ (lt_of_le_of_lt (Multiset.card_le_card hq) hs),
      add_zero, sub_self]

/-!

## D. The projection onto the pure jets

-/

/-- The projection `U ↦ U · (U₀)⁻¹` of a jet onto the pure jets, stripping its value.
  This is not a group homomorphism. It is the cocycle of the splitting of `G.gaugeJetGroup` by
  the constant jets. -/
noncomputable def truncationProjZero (U : G.gaugeJetGroup) : G.truncationKer 0 :=
  ⟨U * (G.gaugeJetOfConstant (G.evalGaugeJet U))⁻¹, G.mem_truncationKer_zero_iff_evalGaugeJet.mpr
    (by rw [map_mul, map_inv, evalGaugeJet_gaugeJetOfConstant, mul_inv_cancel])⟩

@[simp]
lemma coe_truncationProjZero (U : G.gaugeJetGroup) :
    (G.truncationProjZero U : G.gaugeJetGroup) = U *
      (G.gaugeJetOfConstant (G.evalGaugeJet U))⁻¹ := rfl

/-- Every jet is its pure part times the constant jet of its value. -/
lemma eq_truncationProjZero_mul_ofConstant (U : G.gaugeJetGroup) :
    U = G.truncationProjZero U * G.gaugeJetOfConstant (G.evalGaugeJet U) := by
  simp

/-!

## E. Pure jets and their Maurer–Cartan data

-/

/-- The symmetrized Maurer–Cartan data of a pure jet, the base-point values of its
  symmetrized Maurer–Cartan forms, indexed by nonempty multisets of directions. Total
  symmetry is automatic from the multiset indexing. -/
noncomputable def symmetrizedMaurerCartanCoeff (U : G.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) : G.lieSubalgebra :=
  G.evalLie (G.symmetrizedMaurerCartanForm U.1 r.1)

lemma symmetrizedMaurerCartanCoeff_apply (U : G.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) :
    G.symmetrizedMaurerCartanCoeff U r =
      G.evalLie (G.symmetrizedMaurerCartanForm U.1 r.1) := rfl

/-- Maurer–Cartan triangularity. A pure jet whose symmetrized Maurer–Cartan data vanish
  up to order `n` is trivial to order `n`. The symmetrized data control the Taylor data of
  the Maurer–Cartan form through the symmetrization defect. -/
lemma mem_truncationKer_of_symmetrizedMaurerCartanCoeff_eq_zero (U : G.truncationKer 0)
    (n : ℕ) (h : ∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0), r.card ≤ n →
      G.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0) :
    U.1 ∈ G.truncationKer n :=
  ⟨U.2.1, fun s μ hs => by
    have h0 := G.evalLie_iteratedDerivJ_maurerCartan_eq_zero_of_symmetrized_eq_zero
      U.1 (fun r hr hrn => h r hr hrn) s μ hs
    rwa [map_neg, map_neg, neg_eq_zero] at h0⟩

/-- Conversely, the symmetrized Maurer–Cartan data of a jet trivial to order `n` vanish
  up to order `n`, since each term of the symmetrized form carries fewer than `n`
  derivatives. -/
lemma symmetrizedMaurerCartanCoeff_eq_zero_of_mem_truncationKer {U : G.truncationKer 0}
    {n : ℕ} (hU : U.1 ∈ G.truncationKer n) {r : Multiset (Fin 1 ⊕ Fin 3)} (hr : r ≠ 0)
    (hrn : r.card ≤ n) : G.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0 := by
  change G.evalLie (G.symmetrizedMaurerCartanForm U.1 r) = 0
  rw [symmetrizedMaurerCartanForm, map_smul, map_multiset_sum, Multiset.map_map]
  refine smul_eq_zero_of_right _ (Multiset.sum_eq_zero fun z hz => ?_)
  obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hz
  show G.evalLie (G.iteratedDerivJ (r - {μ}) (-G.maurerCartan U.1 μ)) = 0
  rw [map_neg, map_neg, neg_eq_zero]
  refine hU.2 _ μ ?_
  have h1 := Multiset.card_pos.mpr hr
  rw [Multiset.sub_singleton, Multiset.card_erase_of_mem hμ, Nat.pred_eq_sub_one]
  omega

/-- The truncation filtration through the symmetrized Maurer–Cartan data. A pure jet is
  trivial to order `n` exactly when its symmetrized data vanish up to order `n`. -/
lemma mem_truncationKer_iff_symmetrizedMaurerCartanCoeff_eq_zero (U : G.truncationKer 0)
    (n : ℕ) : U.1 ∈ G.truncationKer n ↔
      ∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0), r.card ≤ n →
        G.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0 :=
  ⟨fun hU _ hr hrn => G.symmetrizedMaurerCartanCoeff_eq_zero_of_mem_truncationKer hU hr hrn,
    G.mem_truncationKer_of_symmetrizedMaurerCartanCoeff_eq_zero U n⟩

/-- A pure jet is determined by its Maurer–Cartan form. By the
  cocycle and inverse laws `ω(V⁻¹ U) = Ad_{V⁻¹}(ω(U) − ω(V)) = 0`, so `V⁻¹ U` is the
  constant jet of its value, which is the identity. -/
lemma maurerCartan_injOn_truncationKer_zero {U V : G.gaugeJetGroup} (hU : U ∈ G.truncationKer 0)
    (hV : V ∈ G.truncationKer 0) (h : G.maurerCartan U = G.maurerCartan V) :
    U = V := by
  have h1 : G.maurerCartan (V⁻¹ * U) = 0 := by
    funext μ
    rw [maurerCartan_cocycle, maurerCartan_inv_adjointJ, congrFun h μ, neg_add_cancel,
      Pi.zero_apply]
  have h2 := (G.maurerCartan_eq_zero_iff _).mp h1
  rw [map_mul, map_inv, G.mem_truncationKer_zero_iff_evalGaugeJet.mp hU,
    G.mem_truncationKer_zero_iff_evalGaugeJet.mp hV, inv_one, one_mul, map_one] at h2
  exact (inv_mul_eq_one.mp h2).symm

/-- A pure jet is determined by its symmetrized Maurer–Cartan data. The symmetrized data determine
  all base-point Taylor data of the Maurer–Cartan form
  (`evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq_all`), hence the form
  itself by Taylor determinacy, hence the jet by `maurerCartan_injOn_truncationKer_zero`. -/
lemma symmetrizedMaurerCartanCoeff_injective :
    Function.Injective G.symmetrizedMaurerCartanCoeff := by
  intro U V h
  have hsym : ∀ r, G.evalLie (G.symmetrizedMaurerCartanForm U.1 r) =
      G.evalLie (G.symmetrizedMaurerCartanForm V.1 r) := by
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · exact congrFun h ⟨r, hr⟩
  refine Subtype.ext (G.maurerCartan_injOn_truncationKer_zero U.2 V.2 (funext fun μ => ?_))
  exact G.ext_of_evalLie_iteratedDerivJ fun s => by
    have h0 := G.evalLie_iteratedDerivJ_maurerCartan_eq_of_symmetrized_eq_all U.1 V.1 hsym s μ
    simpa only [map_neg, neg_inj] using h0

/-!

## F. The radial component of the Maurer–Cartan form

The symmetrized Maurer–Cartan data of a pure jet are, up to the normalization by the
order, the base-point Taylor data of a single element of `G.jetLieSubalgebra`, the radial
component `ρ(U) = −∑_μ x_μ ω_μ(U)` of the Maurer–Cartan form. This is the Euler identity applied
to each summand.

-/

/-- The radial component `−∑_μ x_μ ω_μ(U)` of the Maurer–Cartan form of a jet. It collects the
  Maurer–Cartan forms in all directions into a single Lie algebra jet, whose base-point Taylor
  data are the symmetrized Maurer–Cartan data. A pure jet is reconstructed from its
  Maurer–Cartan form by solving the radial system for this jet, and `exists_radial_eq` shows
  that every Lie algebra jet vanishing at the base point arises this way. -/
noncomputable def radial (U : G.gaugeJetGroup) : G.jetLieSubalgebra :=
  ∑ μ, G.mulCoordJ μ (-G.maurerCartan U μ)

/-- The symmetrized Maurer–Cartan data are the Taylor data of the radial component,
  `sym(ω(U))_r|₀ = (1/|r|) (∂_r ρ(U))|₀`. -/
lemma symmetrizedMaurerCartanCoeff_eq_evalLie_iteratedDeriv_radial (U : G.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) :
    G.symmetrizedMaurerCartanCoeff U r =
      (1 / (r.1.card : ℝ)) • G.evalLie
        (G.iteratedDerivJ r.1 (G.radial U.1)) := by
  classical
  rw [symmetrizedMaurerCartanCoeff_apply, symmetrizedMaurerCartanForm, map_smul,
    map_multiset_sum, Multiset.map_map, radial, map_sum, map_sum,
    Finset.sum_congr rfl fun μ _ => G.evalLie_iteratedDerivJ_mulCoordJ μ r.1 _,
    Finset.sum_multiset_map_count,
    Finset.sum_subset (Finset.subset_univ r.1.toFinset) fun μ _ hμ => by
      rw [Multiset.count_eq_zero.mpr fun h => hμ (Multiset.mem_toFinset.mpr h), zero_smul]]
  exact congrArg _ (Finset.sum_congr rfl fun μ _ => by
    rw [Function.comp_apply, Multiset.sub_singleton])

/-!

## G. Radial integrability

Every Lie algebra jet vanishing at the base point is the radial component of the
Maurer–Cartan form of a pure jet, the jet `U` solving `E U = −A U` with `U(0) = 1`, from
`GlobalGaugeGroup.exists_sum_X_smul_maurerCartan_eq`. With the realisation of Taylor data,
`GlobalGaugeGroup.exists_evalLie_iteratedDerivJ_eq`, this makes the symmetrized Maurer–Cartan
data free coordinates on the pure jets.

-/

/-- The radial component `−∑_μ x_μ ω_μ` of the Maurer–Cartan form of a gauge jet, as a matrix,
  `−∑_μ x_μ (∂_μ U) U⁻¹`. -/
lemma radial_val (U : G.gaugeJetGroup) :
    (G.radial U).1 =
      ∑ μ, (X μ : SpaceTimeAlgebra) • -((U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
        (U.1⁻¹).1) := by
  simp only [radial, AddSubmonoidClass.coe_finsetSum, mulCoordJ_val, NegMemClass.coe_neg,
    maurerCartan_val]

/-- Every Lie algebra jet vanishing at the base point is the radial component of the
  Maurer–Cartan form of a pure jet. -/
lemma exists_radial_eq {A : G.jetLieSubalgebra} (hA : G.evalLie A = 0) :
    ∃ U : G.truncationKer 0, G.radial U.1 = A := by
  have hA0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1 = 0 := by
    simpa using congrArg Subtype.val hA
  obtain ⟨U, hU1, hUrad⟩ := G.exists_sum_X_smul_maurerCartan_eq A.2 hA0
  refine ⟨⟨U, (G.mem_truncationKer_zero_iff_evalGaugeJet).2 hU1⟩, Subtype.ext ?_⟩
  rw [radial_val]
  simp only [smul_neg, Finset.sum_neg_distrib]
  simp only [maurerCartan_val] at hUrad
  rw [hUrad, neg_neg]

/-- Every family of symmetrized Maurer–Cartan data is realized by a pure jet. Realize the
  data, rescaled by the order, as the Taylor data of an element `ρ` vanishing at the base
  point, and integrate `ρ` to a pure jet. -/
lemma symmetrizedMaurerCartanCoeff_surjective :
    Function.Surjective G.symmetrizedMaurerCartanCoeff := by
  intro c
  obtain ⟨ρ, hρ⟩ := G.exists_evalLie_iteratedDerivJ_eq fun s =>
    if hs : s = 0 then 0 else (s.card : ℝ) • c ⟨s, hs⟩
  obtain ⟨U, hU⟩ := G.exists_radial_eq (A := ρ) (by
    simpa [iteratedDerivJ_zero] using hρ 0)
  refine ⟨U, funext fun r => ?_⟩
  have hcard : (r.1.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => r.2 (Multiset.card_eq_zero.mp h)
  rw [symmetrizedMaurerCartanCoeff_eq_evalLie_iteratedDeriv_radial, hU, hρ, dite_eq_right r.2,
    smul_smul, one_div, inv_mul_cancel₀ hcard, one_smul]

/-- The symmetrized Maurer–Cartan data are free coordinates on the pure jets. -/
lemma symmetrizedMaurerCartanCoeff_bijective :
    Function.Bijective G.symmetrizedMaurerCartanCoeff :=
  ⟨G.symmetrizedMaurerCartanCoeff_injective, G.symmetrizedMaurerCartanCoeff_surjective⟩

/-!

## H. Truncation of a gauge jet

Truncating a gauge jet at order `n` sets to zero, in every matrix entry, the Taylor
coefficients of total degree above `n`. This is a plain function into matrices, not a
homomorphism, since deleting the coefficients above order `n` breaks multiplicativity
between orders `n + 1` and `2n`. A jet trivial to order `n` in the sense of `truncationKer`
truncates to the identity, by the Euler vanishing principle applied to
`∂_ρ U = ω_ρ(U) U`.

-/

/-- The `n`-th truncation of a gauge jet, entrywise, all Taylor coefficients of total degree
  greater than `n` are set to zero. -/
noncomputable def truncation (n : ℕ) (U : G.gaugeJetGroup) : Matrix κ κ SpaceTimeAlgebra :=
  (U.1 : Matrix κ κ SpaceTimeAlgebra).map (SpaceTimeAlgebra.truncation n)

/-- Truncation of the identity jet is the identity matrix. -/
@[simp]
lemma truncation_one (n : ℕ) : G.truncation n 1 = 1 :=
  Matrix.map_one _ (SpaceTimeAlgebra.truncation_zero n) (SpaceTimeAlgebra.truncation_one n)

/-- The base-point Taylor coefficients of the Maurer–Cartan form of a jet trivial to order
  `n` vanish below degree `n`. -/
lemma coeff_maurerCartan_eq_zero_of_mem_truncationKer {n : ℕ} {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n) (ρ : Fin 1 ⊕ Fin 3) {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (hm : Finsupp.degree m < n) (i j : κ) :
    coeff m ((G.maurerCartan U ρ : Matrix κ κ SpaceTimeAlgebra) i j) = 0 := by
  have h0 := hU.2 (Finsupp.toMultiset m) ρ (by
    rw [Finsupp.card_toMultiset]
    exact hm)
  have h1 := congrArg (fun A : G.lieSubalgebra => (A : Matrix κ κ ℂ) i j) h0
  simp only [evalLie_iteratedDerivJ_val, derivValueMatrix, Matrix.map_apply,
    ZeroMemClass.coe_zero, Matrix.zero_apply] at h1
  rw [constantCoeff_iteratedPDeriv, Finsupp.toMultiset_toFinsupp] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _))

/-- A jet trivial to order `n` in the sense of the truncation filtration truncates to the
  identity at order `n`. The radial relation `∂_ρ U = ω_ρ(U) U` and the Euler vanishing
  principle propagate the vanishing of the Maurer–Cartan coefficients below degree `n` to
  the vanishing of the coefficients of `U` in nonzero degree up to `n`. -/
lemma truncation_eq_one_of_mem_truncationKer {n : ℕ} {U : G.gaugeJetGroup}
    (hU : U ∈ G.truncationKer n) : G.truncation n U = 1 := by
  rw [← G.truncation_one n]
  exact matrix_map_truncation_eq_one
    (by simpa using congrArg (fun g => (g.1 : Matrix κ κ ℂ)) hU.1) fun i j p hp hpn =>
      coeff_entry_eq_zero_of_map_pderiv_eq_mul
      (G.map_pderiv_eq_maurerCartan_mul U)
      (fun ρ q hq i j => G.coeff_maurerCartan_eq_zero_of_mem_truncationKer hU ρ hq i j) i j hp hpn

end GlobalGaugeGroup
