/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.AdjointCoeff
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MaurerCartan
/-!
# The truncation filtration of the jet gauge group

## i. Overview

A jet of gauge transformations is *trivial to order `n`* when it agrees with the identity
up to and including its `n`-th derivatives. For a matrix group this is a statement about
Taylor coefficients of matrix entries; for an abstract package `jets` it is phrased through
the two things the package provides at the base point, the value `eval U` and the
Maurer–Cartan form: `U` is trivial to order `n` when `eval U = 1` and the base-point Taylor
coefficients of `ω_μ(U)` vanish below order `n`. The Taylor–Leibniz theorem makes these
jets a subgroup `truncationKer n`, normal in `G`, and the subgroups decrease with `n`.

The zeroth member, the *pure jets* with `eval U = 1`, is the complement of the constant
jets: every jet factors uniquely as a pure jet times the constant jet of its value,
`truncationProjZero`. When the package is `Faithful`, a pure jet is determined by its
Maurer–Cartan form, and hence by the base-point values of the symmetrized Maurer–Cartan
form, `symmetrizedMaurerCartanCoeff`; and membership in `truncationKer n` is exactly the
vanishing of those symmetrized data up to order `n`.

What a jet trivial to order `n` does to the fields is the point of the filtration: all its
adjoint Taylor coefficients of order between `1` and `n` vanish,
`adjointCoeff_eq_zero_of_mem_truncationKer`, so it acts on the gauge-field symbols with at
most `n` derivatives by a pure translation.

## ii. Key results

- `LocalGaugeData.truncationKer` : the jets trivial to order `n`, as a subgroup.
- `LocalGaugeData.mem_truncationKer_zero_iff` : the pure jets.
- `LocalGaugeData.adjointCoeff_eq_zero_of_mem_truncationKer` : deep jets kill the positive
  adjoint coefficients.
- `LocalGaugeData.truncationKer_normal` : the filtration is by normal subgroups.
- `LocalGaugeData.truncationProjZero` : the projection of a jet onto the pure jets.
- `LocalGaugeData.maurerCartan_injOn_truncationKer_zero` : a pure jet of a faithful package
  is determined by its Maurer–Cartan form.
- `LocalGaugeData.symmetrizedMaurerCartanCoeff_injective` : and by its symmetrized
  Maurer–Cartan data.
- `LocalGaugeData.mem_truncationKer_iff_symmetrizedMaurerCartanCoeff_eq_zero` : the
  filtration through the symmetrized data.
- `LocalGaugeData.radial` : the radial component `∑_μ x_μ ω_μ` of the Maurer–Cartan form,
  whose Taylor data are the symmetrized data.
- `LocalGaugeData.Free` : Taylor completeness and radial integrability, which make the
  symmetrized data free coordinates on the pure jets,
  `LocalGaugeData.symmetrizedMaurerCartanCoeff_surjective`.

## iii. Table of contents

- A. The truncation filtration
- B. The adjoint coefficients of a deep jet
- C. Normality
- D. The projection onto the pure jets
- E. Pure jets and their Maurer–Cartan data
- F. The radial component of the Maurer–Cartan form
- G. Free packages

-/

@[expose] public section

namespace LocalGaugeData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  (jets : LocalGaugeData G 𝔤 G₀ 𝔤J)

/-!

## A. The truncation filtration

-/

/-- The jets trivial to order `n`: value the identity, and base-point Taylor coefficients
  of the Maurer–Cartan form vanishing below order `n`. Closure under products and inverses
  is the cocycle law together with the Taylor–Leibniz theorem for the adjoint action. -/
noncomputable def truncationKer (n : ℕ) : Subgroup G where
  carrier := {U | jets.eval U = 1 ∧ ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3),
    s.card < n → jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) = 0}
  one_mem' := ⟨map_one _, fun s μ _ => by rw [maurerCartan_one, map_zero, map_zero]⟩
  mul_mem' := by
    intro U V hU hV
    refine ⟨by rw [map_mul, hU.1, hV.1, one_mul], fun s μ hs => ?_⟩
    rw [maurerCartan_cocycle, map_add, map_add, hU.2 s μ hs, zero_add]
    exact jets.evalLie_iteratedDeriv_adjoint_eq_zero U fun q hq =>
      hV.2 q μ (lt_of_le_of_lt (Multiset.card_le_card hq) hs)
  inv_mem' := by
    intro U hU
    refine ⟨by rw [map_inv, hU.1, inv_one], fun s μ hs => ?_⟩
    rw [maurerCartan_inv, map_neg, map_neg, neg_eq_zero]
    exact jets.evalLie_iteratedDeriv_adjoint_eq_zero U⁻¹ fun q hq =>
      hU.2 q μ (lt_of_le_of_lt (Multiset.card_le_card hq) hs)

lemma mem_truncationKer_iff {n : ℕ} {U : G} :
    U ∈ jets.truncationKer n ↔ jets.eval U = 1 ∧
      ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card < n →
        jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) = 0 := Iff.rfl

lemma eval_eq_one_of_mem_truncationKer {n : ℕ} {U : G} (hU : U ∈ jets.truncationKer n) :
    jets.eval U = 1 := hU.1

lemma evalLie_iteratedDeriv_maurerCartan_eq_zero_of_mem_truncationKer {n : ℕ} {U : G}
    (hU : U ∈ jets.truncationKer n) {s : Multiset (Fin 1 ⊕ Fin 3)} (hs : s.card < n)
    (μ : Fin 1 ⊕ Fin 3) : jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) = 0 :=
  hU.2 s μ hs

/-- The filtration decreases: a jet trivial to order `n` is trivial to every lower order. -/
lemma truncationKer_antitone : Antitone jets.truncationKer :=
  fun _ _ hmn _ hU => ⟨hU.1, fun s μ hs => hU.2 s μ (lt_of_lt_of_le hs hmn)⟩

/-- The zeroth truncation kernel is the group of pure jets, those with identity value. -/
lemma mem_truncationKer_zero_iff {U : G} : U ∈ jets.truncationKer 0 ↔ jets.eval U = 1 :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ hs => absurd hs (Nat.not_lt_zero _)⟩⟩

/-!

## B. The adjoint coefficients of a deep jet

-/

/-- Deep jets kill the positive adjoint coefficients: for a jet trivial to order `n`, the
  adjoint coefficients of order between `1` and `n` vanish. One derivative of the adjoint
  is `ad` of the Maurer–Cartan form, whose base-point data vanish below order `n`. -/
lemma adjointCoeff_eq_zero_of_mem_truncationKer {n : ℕ} {U : G} (hU : U ∈ jets.truncationKer n)
    {x : Multiset (Fin 1 ⊕ Fin 3)} (hx : x ≠ 0) (hxn : x.card ≤ n) :
    jets.adjointCoeff U x = 0 := by
  obtain ⟨μ, hμ⟩ := Multiset.card_pos_iff_exists_mem.mp (Multiset.card_pos.mpr hx)
  rw [← Multiset.cons_erase hμ, adjointCoeff_cons, neg_eq_zero]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
  have h1 := Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)
  have h2 := Multiset.card_erase_add_one hμ
  rw [hU.2 p.1 μ (by omega), map_zero, LinearMap.zero_comp]

/-- The dual form of `adjointCoeff_eq_zero_of_mem_truncationKer`. -/
lemma adjointDualCoeff_eq_zero_of_mem_truncationKer {n : ℕ} {U : G}
    (hU : U ∈ jets.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hx : x ≠ 0)
    (hxn : x.card ≤ n) : jets.adjointDualCoeff U x = 0 := by
  rw [adjointDualCoeff, jets.adjointCoeff_eq_zero_of_mem_truncationKer hU hx hxn]
  exact LinearMap.ext fun φ => LinearMap.ext fun a => map_zero φ

/-- Up to order `n`, a jet trivial to order `n` has the adjoint coefficients of the
  identity. -/
lemma adjointCoeff_eq_one_of_mem_truncationKer {n : ℕ} {U : G} (hU : U ∈ jets.truncationKer n)
    {x : Multiset (Fin 1 ⊕ Fin 3)} (hxn : x.card ≤ n) :
    jets.adjointCoeff U x = jets.adjointCoeff 1 x := by
  rw [adjointCoeff_one]
  split_ifs with h
  · subst h
    exact jets.adjointCoeff_zero_of_eval_eq_one hU.1
  · exact jets.adjointCoeff_eq_zero_of_mem_truncationKer hU h hxn

/-- Up to order `n`, a jet trivial to order `n` is invisible on the right of a product. -/
lemma adjointCoeff_mul_of_mem_truncationKer_right (g : G) {n : ℕ} {U : G}
    (hU : U ∈ jets.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hxn : x.card ≤ n) :
    jets.adjointCoeff (g * U) x = jets.adjointCoeff g x := by
  rw [adjointCoeff_mul, Multiset.sum_antidiagonal_eq_of_snd_ne_zero x _ fun p hp hp2 => ?_]
  · rw [jets.adjointCoeff_zero_of_eval_eq_one hU.1, LinearMap.comp_id]
  · rw [jets.adjointCoeff_eq_zero_of_mem_truncationKer hU hp2
      ((Multiset.card_le_card (Multiset.snd_le_of_mem_antidiagonal hp)).trans hxn),
      LinearMap.comp_zero]

/-- Up to order `n`, a jet trivial to order `n` is invisible on the left of a product. -/
lemma adjointCoeff_mul_of_mem_truncationKer_left (g : G) {n : ℕ} {U : G}
    (hU : U ∈ jets.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hxn : x.card ≤ n) :
    jets.adjointCoeff (U * g) x = jets.adjointCoeff g x := by
  rw [adjointCoeff_mul, Multiset.sum_antidiagonal_eq_of_fst_ne_zero x _ fun p hp hp1 => ?_]
  · rw [jets.adjointCoeff_zero_of_eval_eq_one hU.1, LinearMap.id_comp]
  · rw [jets.adjointCoeff_eq_zero_of_mem_truncationKer hU hp1
      ((Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)).trans hxn),
      LinearMap.zero_comp]

/-- Up to order `n`, a conjugate of a jet trivial to order `n` has the adjoint
  coefficients of the identity. -/
lemma adjointCoeff_conj_of_mem_truncationKer (g : G) {n : ℕ} {U : G}
    (hU : U ∈ jets.truncationKer n) {x : Multiset (Fin 1 ⊕ Fin 3)} (hxn : x.card ≤ n) :
    jets.adjointCoeff (g * U * g⁻¹) x = jets.adjointCoeff 1 x := by
  rw [adjointCoeff_mul, Multiset.map_congr rfl (fun p hp => by
      rw [jets.adjointCoeff_mul_of_mem_truncationKer_right g hU
        ((Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)).trans hxn)]),
    ← adjointCoeff_mul, mul_inv_cancel]

/-- Up to order `n`, a conjugate of a jet trivial to order `n` acts trivially on the
  base-point Taylor data of the jet Lie algebra. -/
lemma evalLie_iteratedDeriv_adjoint_conj_of_mem_truncationKer (g : G) {n : ℕ} {U : G}
    (hU : U ∈ jets.truncationKer n) {s : Multiset (Fin 1 ⊕ Fin 3)} (hs : s.card ≤ n)
    (Y : 𝔤J) : jets.evalLie (jets.iteratedDeriv s (jets.adjoint (g * U * g⁻¹) Y)) =
      jets.evalLie (jets.iteratedDeriv s Y) := by
  rw [evalLie_iteratedDeriv_adjoint, Multiset.sum_antidiagonal_eq_of_fst_ne_zero s _
    fun p hp hp1 => ?_]
  · rw [jets.adjointCoeff_conj_of_mem_truncationKer g hU (by simp), adjointCoeff_one,
      if_pos rfl, LinearMap.id_apply]
  · rw [jets.adjointCoeff_conj_of_mem_truncationKer g hU
      ((Multiset.card_le_card (Multiset.fst_le_of_mem_antidiagonal hp)).trans hs),
      adjointCoeff_one, if_neg hp1, LinearMap.zero_apply]

/-!

## C. Normality

-/

/-- The Maurer–Cartan form of a conjugate, by the cocycle law: the conjugating jet
  contributes its own form and its transport by the conjugate. -/
lemma maurerCartan_conj (g U : G) (μ : Fin 1 ⊕ Fin 3) :
    jets.maurerCartan (g * U * g⁻¹) μ =
      jets.maurerCartan g μ + jets.adjoint g (jets.maurerCartan U μ)
        - jets.adjoint (g * U * g⁻¹) (jets.maurerCartan g μ) := by
  rw [jets.maurerCartan_cocycle (g * U) g⁻¹, jets.maurerCartan_cocycle g U, maurerCartan_inv,
    map_neg, map_mul jets.adjoint (g * U) g⁻¹, Module.End.mul_apply, sub_eq_add_neg]

/-- The truncation kernels are normal subgroups: conjugating a jet trivial to order `n`
  gives a jet trivial to order `n`. -/
instance truncationKer_normal (n : ℕ) : (jets.truncationKer n).Normal where
  conj_mem U hU g := by
    refine ⟨by rw [map_mul, map_mul, hU.1, mul_one, map_inv, mul_inv_cancel], fun s μ hs => ?_⟩
    rw [maurerCartan_conj, map_sub, map_add, map_sub, map_add,
      jets.evalLie_iteratedDeriv_adjoint_conj_of_mem_truncationKer g hU hs.le,
      jets.evalLie_iteratedDeriv_adjoint_eq_zero g fun q hq =>
        hU.2 q μ (lt_of_le_of_lt (Multiset.card_le_card hq) hs),
      add_zero, sub_self]

/-!

## D. The projection onto the pure jets

-/

/-- The projection of a jet onto the pure jets, stripping its value: `U ↦ U · (U₀)⁻¹`.
  This is not a group homomorphism; it is the cocycle of the splitting of `G` by the
  constant jets. -/
noncomputable def truncationProjZero (U : G) : jets.truncationKer 0 :=
  ⟨U * (jets.ofConstant (jets.eval U))⁻¹, jets.mem_truncationKer_zero_iff.mpr
    (by rw [map_mul, map_inv, eval_ofConstant, mul_inv_cancel])⟩

@[simp]
lemma coe_truncationProjZero (U : G) :
    (jets.truncationProjZero U : G) = U * (jets.ofConstant (jets.eval U))⁻¹ := rfl

/-- Every jet is its pure part times the constant jet of its value. -/
lemma eq_truncationProjZero_mul_ofConstant (U : G) :
    U = jets.truncationProjZero U * jets.ofConstant (jets.eval U) := by
  simp

lemma truncationProjZero_surjective : Function.Surjective jets.truncationProjZero := by
  intro V
  refine ⟨V, Subtype.ext ?_⟩
  rw [coe_truncationProjZero, jets.mem_truncationKer_zero_iff.mp V.2, map_one, inv_one,
    mul_one]

/-- The pure part of a jet is trivial exactly when the jet is constant. -/
lemma truncationProjZero_eq_one_iff {U : G} :
    jets.truncationProjZero U = 1 ↔ U = jets.ofConstant (jets.eval U) := by
  rw [← Subtype.coe_inj, coe_truncationProjZero, Subgroup.coe_one, mul_inv_eq_one]

@[simp]
lemma truncationProjZero_ofConstant (g : G₀) :
    jets.truncationProjZero (jets.ofConstant g) = 1 := by
  rw [truncationProjZero_eq_one_iff, eval_ofConstant]

/-- Stripping the value of a jet does not change its Maurer–Cartan form: by the cocycle
  law, right multiplication by a constant jet drops out. -/
@[simp]
lemma maurerCartan_truncationProjZero (U : G) (μ : Fin 1 ⊕ Fin 3) :
    jets.maurerCartan (jets.truncationProjZero U) μ = jets.maurerCartan U μ := by
  rw [coe_truncationProjZero, ← map_inv, maurerCartan_cocycle, maurerCartan_ofConstant,
    map_zero, add_zero]

/-!

## E. Pure jets and their Maurer–Cartan data

-/

/-- The symmetrized Maurer–Cartan data of a pure jet: the base-point values of its
  symmetrized Maurer–Cartan forms, indexed by nonempty multisets of directions. Total
  symmetry is automatic from the multiset indexing. -/
noncomputable def symmetrizedMaurerCartanCoeff (U : jets.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) : 𝔤 :=
  jets.evalLie (jets.symmetrizedMaurerCartanForm U.1 r.1)

lemma symmetrizedMaurerCartanCoeff_apply (U : jets.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) :
    jets.symmetrizedMaurerCartanCoeff U r =
      jets.evalLie (jets.symmetrizedMaurerCartanForm U.1 r.1) := rfl

/-- Maurer–Cartan triangularity: a pure jet whose symmetrized Maurer–Cartan data vanish
  up to order `n` is trivial to order `n`. The symmetrized data control the Taylor data of
  the Maurer–Cartan form through the symmetrization defect. -/
lemma mem_truncationKer_of_symmetrizedMaurerCartanCoeff_eq_zero (U : jets.truncationKer 0)
    (n : ℕ) (h : ∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0), r.card ≤ n →
      jets.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0) :
    U.1 ∈ jets.truncationKer n :=
  ⟨U.2.1, fun s μ hs => jets.evalLie_iteratedDeriv_maurerCartan_eq_zero_of_symmetrized_eq_zero
    U.1 (fun r hr hrn => h r hr hrn) s μ hs⟩

/-- Conversely, the symmetrized Maurer–Cartan data of a jet trivial to order `n` vanish
  up to order `n`: each term of the symmetrized form carries fewer than `n` derivatives. -/
lemma symmetrizedMaurerCartanCoeff_eq_zero_of_mem_truncationKer {U : jets.truncationKer 0}
    {n : ℕ} (hU : U.1 ∈ jets.truncationKer n) {r : Multiset (Fin 1 ⊕ Fin 3)} (hr : r ≠ 0)
    (hrn : r.card ≤ n) : jets.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0 := by
  change jets.evalLie (jets.symmetrizedMaurerCartanForm U.1 r) = 0
  rw [symmetrizedMaurerCartanForm, map_smul, map_multiset_sum, Multiset.map_map]
  refine smul_eq_zero_of_right _ (Multiset.sum_eq_zero fun z hz => ?_)
  obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hz
  refine hU.2 _ μ ?_
  have h1 := Multiset.card_pos.mpr hr
  rw [Multiset.sub_singleton, Multiset.card_erase_of_mem hμ, Nat.pred_eq_sub_one]
  omega

/-- The truncation filtration through the symmetrized Maurer–Cartan data: a pure jet is
  trivial to order `n` exactly when its symmetrized data vanish up to order `n`. -/
lemma mem_truncationKer_iff_symmetrizedMaurerCartanCoeff_eq_zero (U : jets.truncationKer 0)
    (n : ℕ) : U.1 ∈ jets.truncationKer n ↔
      ∀ (r : Multiset (Fin 1 ⊕ Fin 3)) (hr : r ≠ 0), r.card ≤ n →
        jets.symmetrizedMaurerCartanCoeff U ⟨r, hr⟩ = 0 :=
  ⟨fun hU _ hr hrn => jets.symmetrizedMaurerCartanCoeff_eq_zero_of_mem_truncationKer hU hr hrn,
    jets.mem_truncationKer_of_symmetrizedMaurerCartanCoeff_eq_zero U n⟩

section Faithful

variable [jets.Faithful]

/-- A pure jet of a faithful package is determined by its Maurer–Cartan form. By the
  cocycle and inverse laws `ω(V⁻¹ U) = Ad_{V⁻¹}(ω(U) − ω(V)) = 0`, so `V⁻¹ U` is the
  constant jet of its value, which is the identity. -/
lemma maurerCartan_injOn_truncationKer_zero {U V : G} (hU : U ∈ jets.truncationKer 0)
    (hV : V ∈ jets.truncationKer 0) (h : jets.maurerCartan U = jets.maurerCartan V) :
    U = V := by
  have h1 : jets.maurerCartan (V⁻¹ * U) = 0 := by
    funext μ
    rw [maurerCartan_cocycle, maurerCartan_inv, congrFun h μ, neg_add_cancel, Pi.zero_apply]
  have h2 := (jets.maurerCartan_eq_zero_iff _).mp h1
  rw [map_mul, map_inv, jets.mem_truncationKer_zero_iff.mp hU,
    jets.mem_truncationKer_zero_iff.mp hV, inv_one, one_mul, map_one] at h2
  exact (inv_mul_eq_one.mp h2).symm

/-- A pure jet of a faithful package is determined by its symmetrized Maurer–Cartan data.
  The symmetrized data determine all base-point Taylor data of the Maurer–Cartan form by
  strong induction on the order, hence the form itself by Taylor determinacy, hence the
  jet by `maurerCartan_injOn_truncationKer_zero`. -/
lemma symmetrizedMaurerCartanCoeff_injective :
    Function.Injective jets.symmetrizedMaurerCartanCoeff := by
  intro U V h
  have hsym : ∀ r, jets.evalLie (jets.symmetrizedMaurerCartanForm U.1 r) =
      jets.evalLie (jets.symmetrizedMaurerCartanForm V.1 r) := by
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · exact congrFun h ⟨r, hr⟩
  have hall : ∀ (n : ℕ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card = n →
      jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U.1 μ)) =
        jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan V.1 μ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro s μ hs
        exact jets.evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq U.1 V.1 n hsym
          (fun p ν hp => ih p.card hp p ν rfl) s μ hs
  refine Subtype.ext (jets.maurerCartan_injOn_truncationKer_zero U.2 V.2 (funext fun μ => ?_))
  exact jets.ext_of_evalLie_iteratedDeriv fun s => hall s.card s μ rfl

end Faithful

/-!

## F. The radial component of the Maurer–Cartan form

The symmetrized Maurer–Cartan data of a pure jet are, up to the normalization by the
order, the base-point Taylor data of a single element of `𝔤J`: the radial component
`ρ(U) = ∑_μ x_μ ω_μ(U)` of the Maurer–Cartan form. This is the Euler identity applied
to each summand.

-/

/-- The radial component `∑_μ x_μ ω_μ(U)` of the Maurer–Cartan form of a jet. -/
noncomputable def radial (U : G) : 𝔤J :=
  ∑ μ, jets.coord μ (jets.maurerCartan U μ)

/-- The symmetrized Maurer–Cartan data are the Taylor data of the radial component:
  `sym(ω(U))_r|₀ = (1/|r|) (∂_r ρ(U))|₀`. -/
lemma symmetrizedMaurerCartanCoeff_eq_evalLie_iteratedDeriv_radial (U : jets.truncationKer 0)
    (r : {r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0}) :
    jets.symmetrizedMaurerCartanCoeff U r =
      (1 / (r.1.card : ℝ)) • jets.evalLie (jets.iteratedDeriv r.1 (jets.radial U.1)) := by
  classical
  rw [symmetrizedMaurerCartanCoeff_apply, symmetrizedMaurerCartanForm, map_smul,
    map_multiset_sum, Multiset.map_map, radial, map_sum, map_sum,
    Finset.sum_congr rfl fun μ _ => jets.evalLie_iteratedDeriv_coord μ r.1 _,
    Finset.sum_multiset_map_count,
    Finset.sum_subset (Finset.subset_univ r.1.toFinset) fun μ _ hμ => by
      rw [Multiset.count_eq_zero.mpr fun h => hμ (Multiset.mem_toFinset.mpr h), zero_smul]]
  exact congrArg _ (Finset.sum_congr rfl fun μ _ => by
    rw [Function.comp_apply, Multiset.sub_singleton])

/-!

## G. Free packages

-/

/-- A package is free when it is faithful and its jets are honest formal power series in
  the coordinates: every family of base-point Taylor data is realized by an element of
  `𝔤J` (Taylor completeness), and every element vanishing at the base point is the radial
  component of the Maurer–Cartan form of a pure jet (radial integrability, the solution of
  the Euler equation `∑_μ x_μ ∂_μ U = −i ρ U` with `U(0) = 1`). Both hold for the full jet
  group of any matrix group. Freeness makes the symmetrized Maurer–Cartan data free
  coordinates on the pure jets, `symmetrizedMaurerCartanCoeff_bijective`; like `Faithful`
  it is recorded separately from the structure because the covariance theory does not
  need it, only the classification of invariants does. -/
class Free (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) : Prop extends Faithful jets where
  exists_evalLie_iteratedDeriv_eq : ∀ c : Multiset (Fin 1 ⊕ Fin 3) → 𝔤,
    ∃ Y : 𝔤J, ∀ s, jets.evalLie (jets.iteratedDeriv s Y) = c s
  exists_radial_eq : ∀ ρ : 𝔤J, jets.evalLie ρ = 0 → ∃ U : jets.truncationKer 0, jets.radial U.1 = ρ

section Free

variable [jets.Free]

/-- Taylor completeness of a free package. -/
lemma exists_evalLie_iteratedDeriv_eq (c : Multiset (Fin 1 ⊕ Fin 3) → 𝔤) :
    ∃ Y : 𝔤J, ∀ s, jets.evalLie (jets.iteratedDeriv s Y) = c s :=
  Free.exists_evalLie_iteratedDeriv_eq c

/-- Radial integrability of a free package. -/
lemma exists_radial_eq {ρ : 𝔤J} (hρ : jets.evalLie ρ = 0) :
    ∃ U : jets.truncationKer 0, jets.radial U.1 = ρ :=
  Free.exists_radial_eq ρ hρ

/-- Every family of symmetrized Maurer–Cartan data is realized by a pure jet: realize the
  data, rescaled by the order, as the Taylor data of an element `ρ` vanishing at the base
  point, and integrate `ρ` to a pure jet. -/
theorem symmetrizedMaurerCartanCoeff_surjective :
    Function.Surjective jets.symmetrizedMaurerCartanCoeff := by
  intro c
  obtain ⟨ρ, hρ⟩ := jets.exists_evalLie_iteratedDeriv_eq fun s =>
    if hs : s = 0 then 0 else (s.card : ℝ) • c ⟨s, hs⟩
  obtain ⟨U, hU⟩ := jets.exists_radial_eq (ρ := ρ) (by
    simpa [iteratedDeriv_zero] using hρ 0)
  refine ⟨U, funext fun r => ?_⟩
  have hcard : (r.1.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => r.2 (Multiset.card_eq_zero.mp h)
  rw [symmetrizedMaurerCartanCoeff_eq_evalLie_iteratedDeriv_radial, hU, hρ, dif_neg r.2,
    smul_smul, one_div, inv_mul_cancel₀ hcard, one_smul]

/-- The symmetrized Maurer–Cartan data are free coordinates on the pure jets of a free
  package. -/
lemma symmetrizedMaurerCartanCoeff_bijective :
    Function.Bijective jets.symmetrizedMaurerCartanCoeff :=
  ⟨jets.symmetrizedMaurerCartanCoeff_injective, jets.symmetrizedMaurerCartanCoeff_surjective⟩

end Free

end LocalGaugeData
