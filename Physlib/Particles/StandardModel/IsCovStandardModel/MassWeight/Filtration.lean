/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.MassWeight.Invariants
/-!
# The mass-weight filtration and the constant term

The grading of the field algebra by mass weight answers one weight at a time. A
Lagrangian is not graded: it is a sum of terms of every weight up to a cut-off, and the
object that holds such a sum is the filtration `massWeightSubmoduleLE w`, the join of the
weight pieces of weight at most `w`.

Passing from the grading to the filtration adds exactly one thing, and it is the thing the
graded statement had to exclude. `Invariants.lean` classifies the invariants of
`massWeightSubmodule w` for `0 < w ≤ 8`, and the lower bound is not an artefact: at weight
zero the field algebra contains the scalars, which are fixed by both groups and lie in no
given `S`, so no classification into a span plus a remainder in `S` can hold there. The
filtration contains weight zero, so the scalars have to be met rather than avoided — and
they are a genuine invariant, the constant term of mass dimension zero, the cosmological
term.

Section B settles what the weight-zero piece is: the only word of total weight zero is the
empty word, every generator carrying positive weight, so `massWeightSubmodule 0` is exactly
the scalars, and the unit is fixed by both groups because both act by algebra maps.

The classification then runs as it does for the grading. `Peels` is closed under joins in
its source, and the filtration is a join: each weight from one to eight peels to the
Standard-Model span of that weight by `peels_massWeightSubmodule`, weight zero peels to
itself, and the join of the nine is a peeling of the filtration. No independence of the
sectors, and none of the weights, is used anywhere.

The answer at bound eight is the whole of the Standard Model below and at mass dimension
four: the constant term, the Higgs mass term `H† H`, and the dimension-four Lagrangian.

- A. The mass-weight filtration
- B. The constant term at weight zero
- C. The span of the filtration
- D. Peeling the filtration
- E. The classification up to mass dimension four
- F. The Standard Model Lagrangian with its constant and mass terms

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-!

## A. The mass-weight filtration

-/

/-- The elements of the field algebra of mass weight at most `w`: the join of the
  mass-weight submodules of weight `0` through `w`. This is where a Lagrangian lives, a
  sum of terms of every mass dimension up to a cut-off rather than of a single one. -/
noncomputable def massWeightSubmoduleLE (w : ℕ) : Submodule ℂ B :=
  ⨆ k ∈ Finset.range (w + 1), h.massWeightSubmodule k

/-- Each graded piece of weight at most `w` sits inside the filtration at `w`. -/
lemma massWeightSubmodule_le_massWeightSubmoduleLE {k w : ℕ} (hk : k ≤ w) :
    h.massWeightSubmodule k ≤ h.massWeightSubmoduleLE w :=
  le_iSup₂_of_le k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) le_rfl

/-- An element of a graded piece of weight at most `w` lies in the filtration at `w`. -/
lemma mem_massWeightSubmoduleLE {k w : ℕ} (hk : k ≤ w) {x : B}
    (hx : x ∈ h.massWeightSubmodule k) : x ∈ h.massWeightSubmoduleLE w :=
  h.massWeightSubmodule_le_massWeightSubmoduleLE hk hx

/-- A submodule containing every graded piece of weight at most `w` contains the
  filtration at `w`: the join is taken over exactly those pieces. -/
lemma massWeightSubmoduleLE_le {w : ℕ} {V : Submodule ℂ B}
    (hV : ∀ k ≤ w, h.massWeightSubmodule k ≤ V) : h.massWeightSubmoduleLE w ≤ V :=
  iSup₂_le fun k hk => hV k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

/-- The filtration grows with the bound. -/
lemma massWeightSubmoduleLE_mono {w w' : ℕ} (hw : w ≤ w') :
    h.massWeightSubmoduleLE w ≤ h.massWeightSubmoduleLE w' :=
  h.massWeightSubmoduleLE_le fun _ hk =>
    h.massWeightSubmodule_le_massWeightSubmoduleLE (hk.trans hw)

/-- The filtration as a join over a finite index type, which is the form in which the
  peeling of a join consumes it. -/
lemma massWeightSubmoduleLE_eq_iSup (w : ℕ) :
    h.massWeightSubmoduleLE w = ⨆ k : Fin (w + 1), h.massWeightSubmodule (k : ℕ) :=
  le_antisymm
    (h.massWeightSubmoduleLE_le fun k hk =>
      le_iSup_of_le ⟨k, Nat.lt_succ_of_le hk⟩ le_rfl)
    (iSup_le fun k =>
      h.massWeightSubmodule_le_massWeightSubmoduleLE (Nat.lt_succ_iff.1 k.isLt))

/-- The filtration is carried into itself by both groups: each graded piece is, and a
  join of stable submodules is stable. -/
lemma isStableUnder_massWeightSubmoduleLE (w : ℕ) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.massWeightSubmoduleLE w) :=
  isStableUnder_iSup fun _ => isStableUnder_iSup fun _ =>
    isStableUnder_gaugeLorentzMaps_iff.2
      ⟨fun g _ hy => h.repGauge_mem_massWeightSubmodule g hy,
        fun Λ _ hy => h.repLorentz_mem_massWeightSubmodule Λ hy⟩

/-!

## B. The constant term at weight zero

-/

/-- The weight-zero part of the field algebra is the scalars. Every covariant generator
  carries positive mass weight, so the only word of total weight zero is the empty one,
  whose value is the unit. This is the constant term of the Lagrangian, of mass dimension
  zero — the cosmological term. -/
lemma massWeightSubmodule_zero : h.massWeightSubmodule 0 = 1 := by
  rw [h.massWeightSubmodule_eq_span, Submodule.one_eq_span]
  congr 1
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨[], rfl, rfl⟩, ?_⟩
  rintro x ⟨gl, hw, rfl⟩
  cases gl with
  | nil => rfl
  | cons g t =>
    rw [List.map_cons, List.sum_cons] at hw
    have hg := g.weight_pos
    omega

/-- The scalars are fixed by both groups: each acts by an algebra map, so each fixes the
  unit. This is what makes the constant term an invariant, and it is what the backward
  direction of the classification needs of the weight-zero part of the span. -/
lemma isFixedBy_massWeightSubmodule_zero :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) (h.massWeightSubmodule 0) := by
  rw [h.massWeightSubmodule_zero, Submodule.one_eq_span]
  refine isFixedBy_span_singleton ?_
  rintro (g | Λ)
  · exact h.repGauge_one g
  · exact h.repLorentz_one Λ

/-!

## C. The span of the filtration

-/

/-- The gauge- and Lorentz-invariant content of the Standard Model up to mass weight `w`:
  the weight-zero part of the field algebra, which is the constant term, joined with the
  Standard-Model span of every weight up to `w`. -/
noncomputable def standardModelSpanLE (w : ℕ) : Submodule ℂ B :=
  h.massWeightSubmodule 0 ⊔ ⨆ k ∈ Finset.range (w + 1), h.standardModelSpan k

/-- The constant term lies in the span of the filtration, at every bound. -/
lemma massWeightSubmodule_zero_le_standardModelSpanLE (w : ℕ) :
    h.massWeightSubmodule 0 ≤ h.standardModelSpanLE w := by
  rw [standardModelSpanLE]
  exact le_sup_left

/-- The graded span of a weight at most `w` lies in the span of the filtration at `w`. -/
lemma standardModelSpan_le_standardModelSpanLE {k w : ℕ} (hk : k ≤ w) :
    h.standardModelSpan k ≤ h.standardModelSpanLE w := by
  rw [standardModelSpanLE]
  exact le_sup_of_le_right (le_iSup₂_of_le k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) le_rfl)

/-- The span of the filtration at `w` has mass weight at most `w`: the constant term has
  weight zero and each graded span has its own weight. -/
lemma standardModelSpanLE_le_massWeightSubmoduleLE (w : ℕ) :
    h.standardModelSpanLE w ≤ h.massWeightSubmoduleLE w :=
  sup_le (h.massWeightSubmodule_le_massWeightSubmoduleLE (Nat.zero_le w))
    (iSup₂_le fun k hk => (h.standardModelSpan_le_massWeightSubmodule k).trans
      (h.massWeightSubmodule_le_massWeightSubmoduleLE
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))))

/-- The span of the filtration is fixed pointwise by the gauge and Lorentz groups
  together. At positive weight this is the fixedness of the graded spans; at weight zero
  it is the fixedness of the unit, and that is the only new content of the filtration. -/
lemma isFixedBy_standardModelSpanLE (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) (h.standardModelSpanLE w) :=
  h.isFixedBy_massWeightSubmodule_zero.sup
    (isFixedBy_iSup fun k => isFixedBy_iSup fun _ => h.isFixedBy_standardModelSpan k)

/-- Every element of the span of the filtration is a gauge invariant. -/
lemma repGauge_of_mem_standardModelSpanLE (w : ℕ) (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.standardModelSpanLE w) : repGauge g y = y :=
  h.isFixedBy_standardModelSpanLE w (Sum.inl g) y hy

/-- Every element of the span of the filtration is a Lorentz invariant. -/
lemma repLorentz_of_mem_standardModelSpanLE (w : ℕ) (Λ : SL(2,ℂ)) {y : B}
    (hy : y ∈ h.standardModelSpanLE w) : repLorentz Λ y = y :=
  h.isFixedBy_standardModelSpanLE w (Sum.inr Λ) y hy

/-- The span of the filtration at bound eight in reduced form. Of the nine graded spans
  only two are non-trivial, the Higgs mass term at weight four and the dimension-four
  Lagrangian at weight eight, so what survives up to mass dimension four is the constant
  term, the Higgs mass term, and the Lagrangian. -/
lemma standardModelSpanLE_eight :
    h.standardModelSpanLE 8 = (1 : Submodule ℂ B) ⊔ (h.isHiggsSector.dotSpan 0 0
      ⊔ (h.isGaugeSector.lorentzContractionEightSpan
            ⊔ h.isHiggsSector.lorentzContractionEightSpan
          ⊔ (h.isFermionSector.kineticSpan ⊔ h.yukawaSpan))) := by
  rw [standardModelSpanLE, h.massWeightSubmodule_zero, ← h.standardModelSpan_eight,
    ← h.standardModelSpan_four]
  congr 1
  refine le_antisymm (iSup₂_le fun k hk => ?_) (sup_le ?_ ?_)
  · rw [Finset.mem_range] at hk
    by_cases hk8 : k = 8
    · subst hk8
      exact le_sup_right
    by_cases hk4 : k = 4
    · subst hk4
      exact le_sup_left
    · rw [h.standardModelSpan_eq_bot hk8 hk4]
      exact bot_le
  · exact le_iSup₂_of_le 4 (by decide) le_rfl
  · exact le_iSup₂_of_le 8 (by decide) le_rfl

/-!

## D. Peeling the filtration

-/

/-- The filtration peels to its span, at every bound up to eight. The filtration is a
  join of the graded pieces, each of them stable under both groups, and `Peels` is closed
  under joins in its source: the weights are taken one at a time, each in turn joining the
  error term of the others. At positive weight the graded peeling of `Invariants.lean` is
  used; at weight zero a submodule peels to itself, the constant term being carried in the
  span. -/
lemma peels_massWeightSubmoduleLE {w : ℕ} (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.massWeightSubmoduleLE w)
      (h.standardModelSpanLE w) := by
  rw [h.massWeightSubmoduleLE_eq_iSup]
  refine Peels.iSup (fun k => ?_) (fun _ => ?_)
    (h.isFixedBy_standardModelSpanLE w).isStableUnder
  · have hkw : (k : ℕ) ≤ w := Nat.lt_succ_iff.1 k.isLt
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hk0
    · rw [hk0]
      exact peels_of_le (h.massWeightSubmodule_zero_le_standardModelSpanLE w)
    · exact (h.peels_massWeightSubmodule hk0 (hkw.trans hw)).mono_right
        (h.standardModelSpan_le_standardModelSpanLE hkw)
  · exact isStableUnder_gaugeLorentzMaps_iff.2
      ⟨fun g _ hy => h.repGauge_mem_massWeightSubmodule g hy,
        fun Λ _ hy => h.repLorentz_mem_massWeightSubmodule Λ hy⟩

/-!

## E. The classification up to mass dimension four

-/

/-- The gauge and Lorentz invariants of mass weight at most `w`, for `w ≤ 8`, modulo a
  submodule `S` stable under both groups: such an invariant is a combination of the
  constant term and the Standard-Model terms of weight at most `w`, plus a remainder in
  `S`, and the remainder is fixed by both groups as well, being the difference of two
  invariants. -/
theorem exists_mem_standardModelSpanLE_of_gauge_and_lorentz_invariant (w : ℕ) (hw : w ≤ 8)
    (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmoduleLE w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.standardModelSpanLE w := by
  obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1
    (h.peels_massWeightSubmoduleLE hw S (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩)
      x hx (forall_gaugeLorentzMaps_eq_self_iff.2 ⟨hG, hL⟩))
  refine ⟨y, hy, fun g => ?_, fun g => ?_, by simpa using hz⟩
  · have hstep := hG g
    rw [map_add, h.repGauge_of_mem_standardModelSpanLE w g hz, add_right_inj] at hstep
    exact hstep
  · have hstep := hL g
    rw [map_add, h.repLorentz_of_mem_standardModelSpanLE w g hz, add_right_inj] at hstep
    exact hstep

/-- The classification of the Standard Model up to mass weight `w ≤ 8` as an equivalence,
  in the shape every sector uses: an element of `massWeightSubmoduleLE w ⊔ S`, with `S`
  stable under both groups, is fixed by both groups exactly when it is a combination of
  the constant term and the Standard-Model terms of weight at most `w`, up to a remainder
  in `S` fixed by both groups. -/
theorem mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff (w : ℕ) (hw : w ≤ 8)
    (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmoduleLE w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.standardModelSpanLE w := by
  refine ⟨fun hx => h.exists_mem_standardModelSpanLE_of_gauge_and_lorentz_invariant w hw
    S hS hSL hx.1 hx.2.1 hx.2.2, ?_⟩
  rintro ⟨y, hyS, hyG, hyL, hxy⟩
  refine ⟨?_, fun g => ?_, fun g => ?_⟩
  · have hsum : x - y + y ∈ h.massWeightSubmoduleLE w ⊔ S :=
      Submodule.add_mem _
        (Submodule.mem_sup_left (h.standardModelSpanLE_le_massWeightSubmoduleLE w hxy))
        (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : repGauge g (x - y + y) = x - y + y := by
      rw [map_add, h.repGauge_of_mem_standardModelSpanLE w g hxy, hyG g]
    simpa using hstep
  · have hstep : repLorentz g (x - y + y) = x - y + y := by
      rw [map_add, h.repLorentz_of_mem_standardModelSpanLE w g hxy, hyL g]
    simpa using hstep

/-- The same classification without the existential: at every bound up to eight an element
  of `massWeightSubmoduleLE w ⊔ S` fixed by both groups is an element of the span of the
  filtration joined with `S` fixed by both groups, and conversely. -/
theorem mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw : w ≤ 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmoduleLE w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ h.standardModelSpanLE w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) := by
  constructor
  · rintro ⟨hxm, hG, hL⟩
    obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.exists_mem_standardModelSpanLE_of_gauge_and_lorentz_invariant w hw S hS hSL hxm hG hL
    refine ⟨?_, hG, hL⟩
    have hsum : x - y + y ∈ h.standardModelSpanLE w ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hxy) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · rintro ⟨hxm, hG, hL⟩
    exact ⟨sup_le_sup_right (h.standardModelSpanLE_le_massWeightSubmoduleLE w) S hxm, hG, hL⟩

/-!

## F. The Standard Model Lagrangian with its constant and mass terms

-/

/-- The classification at bound eight, that is at mass dimension at most four, as an
  equivalence: an element of `massWeightSubmoduleLE 8 ⊔ S`, with `S` stable under both
  groups, is fixed by both groups exactly when it lies in the span of the filtration up to
  a remainder in `S` fixed by both groups. -/
theorem mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmoduleLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.standardModelSpanLE 8 :=
  h.mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff 8 le_rfl S hS hSL x

/-- The same at bound eight without the existential. -/
theorem mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff_mem
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmoduleLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ h.standardModelSpanLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  h.mem_massWeightSubmoduleLE_sup_and_gauge_lorentz_invariant_iff_mem 8 le_rfl S hS hSL x

/-- The invariant content of the Standard Model up to mass dimension four. An element of
  `massWeightSubmoduleLE 8 ⊔ S`, for `S` a submodule stable under both groups, is fixed by
  the gauge group and the Lorentz group exactly when it is a combination of
  the constant term, of mass dimension zero,
  the Higgs mass term `H† H`, of mass dimension two (`IsHiggsSector.dotSpan`),
  and the Standard-Model Lagrangian of mass dimension four — the gauge kinetic and theta
  terms of the three gauge groups (`IsGaugeSector.lorentzContractionEightSpan`), the Higgs
  kinetic term, its quartic potential and its two box terms
  (`IsHiggsSector.lorentzContractionEightSpan`), the kinetic terms of the ten fermion
  species over the nine family pairs (`IsFermionSector.kineticSpan`), and the six Yukawa
  couplings over the nine family pairs (`yukawaSpan`) —
  up to a remainder in `S` fixed by both groups, and nothing else. -/
theorem mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmoduleLE 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ (1 : Submodule ℂ B) ⊔ (h.isHiggsSector.dotSpan 0 0
              ⊔ (h.isGaugeSector.lorentzContractionEightSpan
                    ⊔ h.isHiggsSector.lorentzContractionEightSpan
                  ⊔ (h.isFermionSector.kineticSpan ⊔ h.yukawaSpan))) := by
  rw [← h.standardModelSpanLE_eight]
  exact h.mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff S hS hSL x

end IsCovStandardModel

end StandardModel
