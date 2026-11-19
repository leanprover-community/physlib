/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.GaugeHiggsSector.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.GaugeSector.MassWeight.MassDimLTEight
/-!
# The gauge-Higgs invariants below mass weight nine

The gauge-Higgs sector of the Standard Model's covariant field algebra carries no invariant.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

The mixed `{gauge, scalar}` sector is small, and none of it is invariant. A field-strength
tower weighs at least four and a Higgs tower at least two, and both weights are even, so
the sector vanishes below weight six and at every odd weight, weight seven included. What
is left is weight six, the underived field strength against the underived Higgs, and
weight eight, that same field strength against the weight-four Higgs terms, together with
the once-derived field strength against the underived Higgs.

None of it can carry an invariant, and the reason is an index count. The Higgs is a Lorentz
scalar, so an underived Higgs symbol has no covector index at all and is fixed by the whole
Lorentz group, while a once-derived one carries a single index, its derivative slot. The
covector indices of these products are therefore those of the field strength — two when it
is underived and three when it is once derived — plus at most one from the Higgs.

Two indices admit exactly one invariant contraction, the metric trace, and it vanishes, since the
metric is symmetric in the pair of indices in which `GaugeSector.F_antisymm` says the
field strength is antisymmetric. Three indices admit no invariant contraction at all, the
metric tying two and the Levi-Civita symbol four. Weight six and the two-Higgs term of
weight eight are of the first kind and the other two terms of weight eight of the second,
so at no weight below nine does the sector add an invariant to what is already there.

Neither count needs the gauge group, and neither needs a basis of the Higgs. The families
being peeled are indexed by a covector of the gauge algebra together with a piece of Higgs
material, and neither index is finite; section A peels a join over an arbitrary index type
by passing to a finite subset of it, which is all an element of a join ever needs.

The bound is `w < 9` rather than the gauge sector's `w < 8`, weight eight being as empty of
invariants as the weights below it. No lower bound on `w` is needed either. The sector is
the two-class sector of the gauge and Higgs generators, so both classes must be present
with a non-zero weight and the scalars, which force `0 < w` in the gauge-sector statement,
never appear.

## ii. Key results

- `mem_of_lorentz_invariant_iSup_rankTwo_span` : a Lorentz invariant of a join, over an arbitrary
  index type, of the spans of bi-Lorentz families with vanishing metric traces lies in the stable
  submodule it is taken modulo.
- `mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_six_sup`,
  `mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_eight_sup` : mass weights six and eight
  carry no Lorentz invariant.
- `mem_sectorMassWeight_gauge_higgs_lt_nine_sup_and_gauge_lorentz_invariant_iff` : the
  classification below mass weight nine as an equivalence.

## iii. Table of contents

- A. Peeling a join over an arbitrary index
- B. The underived Higgs is Lorentz inert
- C. Field strengths against Higgs material
- D. Mass weights six and eight
- E. The classification below mass weight nine

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz

section Peeling

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## A. Peeling a join over an arbitrary index

The gauge sector combines the reductions of a join of spans indexed by a finite set, which
is what its twelve directions of the gauge algebra need. Here the families are indexed by a
covector of the gauge algebra together with a piece of Higgs material, and neither index is
finite. Nothing is lost: an element of a join lies in the join over finitely many of the
summands, so `ReducesInvariantsTo.iSup` combines the reductions over the whole join, by
way of `ReducesInvariantsTo.iSup_of_biSup`. The rest of the section collects the
stability and the inertness of products and joins that section D consumes.

-/

/-- A Lorentz invariant of a join, over an arbitrary index type, of the spans of
  bi-Lorentz families with vanishing metric traces lies in the stable submodule it is taken
  modulo. Each span reduces to the line through its metric contraction, which is zero; the
  reductions combine over every finite set of indices, and so over the whole join. -/
lemma mem_of_lorentz_invariant_iSup_rankTwo_span {ι : Type}
    {T : ι → (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentz
      (liftComponents (T i)))
    (hzero : ∀ i, liftComponents (T i) RankTwo.metric = 0) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, Submodule.span ℂ (Set.range (T i))) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  simp_rw [← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 2 => .up)] at hx
  simpa using ReducesInvariantsTo.iSup
    (fun i => (ComplexVector.reducesInvariantsTo_span_metric (hT i)).mono_right
      (Submodule.span_singleton_eq_bot.2 (hzero i)).le)
    (fun i => (hT i).isStableUnder_range) isStableUnder_bot S hS x hx hinv

/-- A Lorentz invariant of a join, over an arbitrary index type, of the spans of triple Lorentz
  families lies in the stable submodule it is taken modulo, since three covector indices admit no
  invariant contraction at all, so each span reduces to `⊥`, and the reductions combine over every
  finite set of indices, and so over the whole join. -/
lemma mem_of_lorentz_invariant_iSup_rankThree_span {ι : Type}
    {T : ι → (Fin 3 → Fin 1 ⊕ Fin 3) → B}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentz
      (liftComponents (T i)))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, Submodule.span ℂ (Set.range (T i))) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  simp_rw [← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 3 => .up)] at hx
  simpa using ReducesInvariantsTo.iSup
    (fun i => ComplexVector.reducesInvariantsTo_bot_of_odd ⟨1, rfl⟩ (hT i))
    (fun i => (hT i).isStableUnder_range) isStableUnder_bot S hS x hx hinv

/-- A product of two pointwise Lorentz-inert submodules is pointwise Lorentz inert. -/
lemma repLorentz_eq_self_of_mem_mul
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {V W : Submodule ℂ B} (hV : ∀ (g : SL(2,ℂ)), ∀ y ∈ V, repLorentz g y = y)
    (hW : ∀ (g : SL(2,ℂ)), ∀ y ∈ W, repLorentz g y = y) (g : SL(2,ℂ)) :
    ∀ y ∈ V * W, repLorentz g y = y := by
  intro y hy
  refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => ?_
  · rw [hmul, hV g a ha, hW g b hb]
  · rw [map_add, ha, hb]

/-- A product of two Lorentz-stable submodules is Lorentz stable. -/
lemma repLorentz_mem_mul_of_stable
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {V W : Submodule ℂ B} (hV : ∀ (g : SL(2,ℂ)), ∀ y ∈ V, repLorentz g y ∈ V)
    (hW : ∀ (g : SL(2,ℂ)), ∀ y ∈ W, repLorentz g y ∈ W) (g : SL(2,ℂ)) :
    ∀ y ∈ V * W, repLorentz g y ∈ V * W := by
  intro y hy
  refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => ?_
  · rw [hmul]
    exact Submodule.mul_mem_mul (hV g a ha) (hW g b hb)
  · rw [map_add]
    exact add_mem ha hb

/-- A pointwise Lorentz-inert submodule is Lorentz stable. -/
lemma repLorentz_mem_of_fixed {V : Submodule ℂ B}
    (hV : ∀ (g : SL(2,ℂ)), ∀ y ∈ V, repLorentz g y = y) (g : SL(2,ℂ)) :
    ∀ y ∈ V, repLorentz g y ∈ V := fun y hy => by rw [hV g y hy]; exact hy

/-- A join of two Lorentz-stable submodules is Lorentz stable. -/
lemma repLorentz_mem_sup_of_stable {V W : Submodule ℂ B}
    (hV : ∀ (g : SL(2,ℂ)), ∀ y ∈ V, repLorentz g y ∈ V)
    (hW : ∀ (g : SL(2,ℂ)), ∀ y ∈ W, repLorentz g y ∈ W) (g : SL(2,ℂ)) :
    ∀ y ∈ V ⊔ W, repLorentz g y ∈ V ⊔ W := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hV g a ha))
    (Submodule.mem_sup_right (hW g b hb))

end Peeling

namespace LocalCovFieldAlgebra

/-!

## B. The underived Higgs is Lorentz inert

The Higgs is a Lorentz scalar, and an underived symbol has no derivative slot for the
Lorentz matrix to act on, so it is fixed outright — and with it every element of the
submodule the underived symbols span.

-/

/-- The underived Higgs and conjugate-Higgs symbols are Lorentz scalars with no derivative
  slot to rotate, so every element of the weight-two Higgs submodule is fixed by the whole
  Lorentz group. -/
lemma repLorentz_eq_self_of_mem_higgs_derivSubmodule_zero (g : SL(2,ℂ))
    {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ ScalarSector.derivSubmodule 0) : repLorentzGroup g y = y := by
  have key : ScalarSector.derivSubmodule 0
      ≤ LinearMap.ker (repLorentzGroup g - LinearMap.id) := by
    rw [ScalarSector.derivSubmodule]
    refine sup_le ?_ ?_
    · rw [ScalarSector.higgsSubmodule]
      refine iSup_le fun l => ?_
      rintro _ ⟨φ, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rw [ScalarSector.repLorentz_H_apply g φ 0 l,
        Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
          (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
          (fun hb => absurd (Finset.mem_univ _) hb),
        Fin.prod_univ_zero, one_smul, Subsingleton.elim l ![]]
    · rw [ScalarSector.barHiggsSubmodule]
      refine iSup_le fun l => ?_
      rintro _ ⟨φ, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rw [ScalarSector.repLorentz_barH_apply g φ 0 l,
        Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
          (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
          (fun hb => absurd (Finset.mem_univ _) hb),
        Fin.prod_univ_zero, one_smul, Subsingleton.elim l ![]]
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    using key hy

/-!

## C. Field strengths against Higgs material

Three products have to be classified. An underived field strength against inert material is
a bi-Lorentz family whose metric trace vanishes with the antisymmetry of the field strength;
a once-derived one against inert material is a triple Lorentz family; and an underived one
against a once-derived Higgs is a triple Lorentz family as well, the Higgs supplying the
third index. The last is the only one in which a Higgs index moves at all.

-/

/-- An underived field strength against Lorentz-inert material carries no Lorentz
  invariant modulo a Lorentz-stable submodule. -/
lemma mem_of_lorentz_invariant_derivSubmodule_zero_mul_fixed_sup
    (C : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hC : ∀ (g : SL(2,ℂ)), ∀ y ∈ C, repLorentzGroup g y = y)
      (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ GaugeSector.derivSubmodule 0 * C ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  let T : Module.Dual ℝ GaugeAlgebra × C → (Fin 2 → Fin 1 ⊕ Fin 3) →
      fieldData.LocalCovFieldAlgebra :=
    fun i l => gaugeFieldStrength ![] (l 0) (l 1) i.1 * (i.2 : fieldData.LocalCovFieldAlgebra)
  have hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentzGroup
      (liftComponents (T i)) :=
    fun i => isEquivariant_liftComponents_up_mul_fixed repLorentzGroup_mul
      (GaugeSector.isEquivariant_up_F_underived i.1)
      fun g => hC g (i.2 : fieldData.LocalCovFieldAlgebra) i.2.2
  have hzero : ∀ i, liftComponents (T i) RankTwo.metric = 0 := by
    intro i
    refine GaugeSector.liftComponents_metric_eq_zero_of_antisymm fun a b => ?_
    simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [GaugeSector.F_antisymm ![] a b i.1, neg_mul]
  refine mem_of_lorentz_invariant_iSup_rankTwo_span hT hzero S hSL ?_ hinv
  refine sup_le_sup_right ?_ S hx
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have key : GaugeSector.derivSubmodule 0
      ≤ Submodule.comap (LinearMap.mulRight ℂ b) (⨆ i, Submodule.span ℂ (Set.range (T i))) := by
    rw [GaugeSector.derivSubmodule]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    rw [Subsingleton.elim l ![]]
    refine Submodule.mem_iSup_of_mem (φ, ⟨b, hb⟩) (Submodule.subset_span ⟨![μ, ν], ?_⟩)
    simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact key ha

/-- A once-derived field strength against Lorentz-inert material carries no Lorentz
  invariant modulo a Lorentz-stable submodule. -/
lemma mem_of_lorentz_invariant_derivSubmodule_one_mul_fixed_sup
    (C : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hC : ∀ (g : SL(2,ℂ)), ∀ y ∈ C, repLorentzGroup g y = y)
      (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ GaugeSector.derivSubmodule 1 * C ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  let T : Module.Dual ℝ GaugeAlgebra × C → (Fin 3 → Fin 1 ⊕ Fin 3) →
      fieldData.LocalCovFieldAlgebra :=
    fun i l => gaugeFieldStrength ![l 0] (l 1) (l 2) i.1 * (i.2 : fieldData.LocalCovFieldAlgebra)
  have hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentzGroup
      (liftComponents (T i)) :=
    fun i => isEquivariant_liftComponents_up_mul_fixed repLorentzGroup_mul
      (GaugeSector.isEquivariant_up_F_deriv_one i.1)
      fun g => hC g (i.2 : fieldData.LocalCovFieldAlgebra) i.2.2
  refine mem_of_lorentz_invariant_iSup_rankThree_span hT S hSL ?_ hinv
  refine sup_le_sup_right ?_ S hx
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have key : GaugeSector.derivSubmodule 1
      ≤ Submodule.comap (LinearMap.mulRight ℂ b) (⨆ i, Submodule.span ℂ (Set.range (T i))) := by
    rw [GaugeSector.derivSubmodule]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    refine Submodule.mem_iSup_of_mem (φ, ⟨b, hb⟩) (Submodule.subset_span ⟨![l 0, μ, ν], ?_⟩)
    simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Lorentz.vecCons_fin_one_eta]
  exact key ha

/-- The once-derived Higgs and conjugate-Higgs symbols, read as one family indexed by the
  derivative direction, transform as a Lorentz vector. -/
lemma repLorentzGroup_higgsOrConj_deriv_one
    (j : Module.Dual ℂ HiggsVec ⊕ Module.Dual ℂ (ConjModule HiggsVec))
    (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup g (Sum.elim (fun φ => higgsField ![μ] φ)
      (fun ψ => conjHiggsField ![μ] ψ) j)
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) •
          Sum.elim (fun φ => higgsField ![ν] φ)
            (fun ψ => conjHiggsField ![ν] ψ) j := by
  rcases j with φ | ψ
  · simp only [Sum.elim_inl]
    rw [show higgsField ![μ] φ = ScalarSector.covH 1 ![μ] φ from rfl,
      ScalarSector.repLorentz_H_apply g φ 1 ![μ], Lorentz.sum_pi_fin_one]
    exact Finset.sum_congr rfl fun ν _ => by simp [ScalarSector.covH]
  · simp only [Sum.elim_inr]
    rw [show conjHiggsField ![μ] ψ = ScalarSector.covBarH 1 ![μ] ψ from rfl,
      ScalarSector.repLorentz_barH_apply g ψ 1 ![μ], Lorentz.sum_pi_fin_one]
    exact Finset.sum_congr rfl fun ν _ => by simp [ScalarSector.covBarH]

/-- The underived field strength against a once-derived Higgs or conjugate-Higgs symbol, as a
  family of three covector indices, the two of the field strength and the derivative direction
  of the Higgs. -/
noncomputable def fieldStrengthHiggsDerivFamily
    (i : Module.Dual ℝ GaugeAlgebra ×
      (Module.Dual ℂ HiggsVec ⊕ Module.Dual ℂ (ConjModule HiggsVec)))
    (l : Fin 3 → Fin 1 ⊕ Fin 3) : fieldData.LocalCovFieldAlgebra :=
  gaugeFieldStrength ![] (l 0) (l 1) i.1 *
    Sum.elim (fun φ => higgsField ![l 2] φ) (fun ψ => conjHiggsField ![l 2] ψ) i.2

/-- The underived field strength against a once-derived Higgs is a triple Lorentz tensor. -/
lemma isEquivariant_up_fieldStrengthHiggsDerivFamily
    (i : Module.Dual ℝ GaugeAlgebra ×
      (Module.Dual ℂ HiggsVec ⊕ Module.Dual ℂ (ConjModule HiggsVec))) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentzGroup
      (liftComponents (fieldStrengthHiggsDerivFamily i)) := by
  have h1 := isEquivariant_liftComponents_up_mul_vector repLorentzGroup_mul
    (GaugeSector.isEquivariant_up_F_underived i.1) (repLorentzGroup_higgsOrConj_deriv_one i.2)
  convert h1 using 3
  simp only [fieldStrengthHiggsDerivFamily, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- An underived field-strength symbol times the once-derived Higgs submodule lies in the join
  of the spans of the families `fieldStrengthHiggsDerivFamily`. -/
lemma mul_derivSubmodule_one_le_iSup_span (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    ScalarSector.derivSubmodule 1
      ≤ Submodule.comap (LinearMap.mulLeft ℂ (gaugeFieldStrength ![] μ ν φ))
        (⨆ i, Submodule.span ℂ (Set.range (fieldStrengthHiggsDerivFamily i))) := by
  rw [ScalarSector.derivSubmodule]
  refine sup_le ?_ ?_
  · rw [ScalarSector.higgsSubmodule]
    refine iSup_le fun dd => ?_
    obtain ⟨ρ, rfl⟩ : ∃ ρ, dd = ![ρ] := ⟨dd 0, (Lorentz.vecCons_fin_one_eta dd).symm⟩
    rintro _ ⟨ψ, rfl⟩
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.mem_iSup_of_mem (φ, Sum.inl ψ)
      (Submodule.subset_span ⟨![μ, ν, ρ], ?_⟩)
    simp only [fieldStrengthHiggsDerivFamily, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Sum.elim_inl]
    rfl
  · rw [ScalarSector.barHiggsSubmodule]
    refine iSup_le fun dd => ?_
    obtain ⟨ρ, rfl⟩ : ∃ ρ, dd = ![ρ] := ⟨dd 0, (Lorentz.vecCons_fin_one_eta dd).symm⟩
    rintro _ ⟨ψ, rfl⟩
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.mem_iSup_of_mem (φ, Sum.inr ψ)
      (Submodule.subset_span ⟨![μ, ν, ρ], ?_⟩)
    simp only [fieldStrengthHiggsDerivFamily, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Sum.elim_inr]
    rfl

/-- An underived field strength against a once-derived Higgs carries no Lorentz invariant
  modulo a Lorentz-stable submodule, since three covector indices admit no contraction. -/
lemma mem_of_lorentz_invariant_derivSubmodule_zero_mul_higgs_one_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ GaugeSector.derivSubmodule 0 * ScalarSector.derivSubmodule 1 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_iSup_rankThree_span
    isEquivariant_up_fieldStrengthHiggsDerivFamily S hSL ?_ hinv
  refine sup_le_sup_right ?_ S hx
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hA : GaugeSector.derivSubmodule 0 ≤ Submodule.comap (LinearMap.mulRight ℂ b)
      (⨆ i, Submodule.span ℂ (Set.range (fieldStrengthHiggsDerivFamily i))) := by
    rw [GaugeSector.derivSubmodule]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    rw [Subsingleton.elim l ![]]
    exact mul_derivSubmodule_one_le_iSup_span μ ν φ hb
  exact hA ha

/-!

## D. Mass weights six and eight

Weight six is a single product and section C settles it outright. Weight eight is a join of
three, and they are peeled one at a time, the two not yet peeled joining the error term —
which asks that they be Lorentz stable. The gauge and Higgs derivative submodules are, and
so are their products and joins.

-/

/-- Mass weight six carries no Lorentz invariant modulo a Lorentz-stable submodule. A
  Lorentz invariant of `fieldData.sectorMassWeight {gauge, scalar} 6 ⊔ S` lies in `S`. The weight is
  the underived field strength against the underived Higgs, whose two covector indices are
  contracted only by the metric, and that trace vanishes. -/
lemma mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_six_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} 6 ⊔
      S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  rw [LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_six] at hx
  exact LocalCovFieldAlgebra.mem_of_lorentz_invariant_derivSubmodule_zero_mul_fixed_sup _
    (fun g y hy => LocalCovFieldAlgebra.repLorentz_eq_self_of_mem_higgs_derivSubmodule_zero g hy) S
      hSL hx hinv

/-- Mass weight eight carries no Lorentz invariant modulo a Lorentz-stable submodule. A
  Lorentz invariant of `fieldData.sectorMassWeight {gauge, scalar} 8 ⊔ S` lies in `S`. The three
  products making up the weight are peeled off one at a time, the two carrying three
  covector indices by the absence of any contraction and the one carrying two by the
  vanishing of the metric trace. -/
lemma mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_eight_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} 8 ⊔
      S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  have hH0 : ∀ (g : SL(2,ℂ)), ∀ y ∈ ScalarSector.derivSubmodule 0, repLorentzGroup g y
    = y :=
    fun g y hy => LocalCovFieldAlgebra.repLorentz_eq_self_of_mem_higgs_derivSubmodule_zero g hy
  have hH0H0 : ∀ (g : SL(2,ℂ)), ∀ y ∈ ScalarSector.derivSubmodule 0 *
      ScalarSector.derivSubmodule 0, repLorentzGroup g y = y :=
    repLorentz_eq_self_of_mem_mul repLorentzGroup_mul hH0 hH0
  have hGst : ∀ (n : ℕ) (g : SL(2,ℂ)), ∀ y ∈ GaugeSector.derivSubmodule n,
      repLorentzGroup g y ∈ GaugeSector.derivSubmodule n :=
    fun n g y hy => GaugeSector.derivSubmodule_map_repLorentz_le n g ⟨y, hy, rfl⟩
  have hBst := repLorentz_mem_mul_of_stable repLorentzGroup_mul (hGst 0)
    (repLorentz_mem_of_fixed hH0H0)
  have hCst := repLorentz_mem_mul_of_stable repLorentzGroup_mul (hGst 1)
    (repLorentz_mem_of_fixed hH0)
  rw [LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_eight, mul_assoc, sup_assoc,
    sup_assoc] at hx
  exact LocalCovFieldAlgebra.mem_of_lorentz_invariant_derivSubmodule_one_mul_fixed_sup _ hH0 S hSL
    (LocalCovFieldAlgebra.mem_of_lorentz_invariant_derivSubmodule_zero_mul_fixed_sup _ hH0H0 _
      (repLorentz_mem_sup_of_stable hCst hSL)
      (LocalCovFieldAlgebra.mem_of_lorentz_invariant_derivSubmodule_zero_mul_higgs_one_sup _
        (repLorentz_mem_sup_of_stable hBst (repLorentz_mem_sup_of_stable hCst hSL)) hx hinv)
      hinv) hinv

/-!

## E. The classification below mass weight nine

The nine weights below nine are now settled: the sector vanishes below weight six and at
weight seven, and weights six and eight are section D. So below weight nine the gauge-Higgs
sector supplies no invariant beyond what `S` already carries, and the equivalences record it
in the shape the other sectors carry, so that all of them can be combined.

-/

/-- Below mass weight nine the gauge-Higgs sector carries no Lorentz invariant. A Lorentz
  invariant of `fieldData.sectorMassWeight {gauge, scalar} w ⊔ S` for `w < 9` lies in `S`. Weights
  below six and weight seven are trivial submodules, and weights six and eight are the two
  index counts. -/
lemma mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup (w : ℕ) (hw : w < 9)
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y
      ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w ⊔
      S)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  rcases lt_or_ge w 6 with hw6 | hw6
  · rwa [LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_eq_bot_of_lt_six hw6, bot_sup_eq] at hx
  interval_cases w
  · exact LocalCovFieldAlgebra.mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_six_sup S hSL
      hx hL
  · rwa [LocalCovFieldAlgebra.sectorMassWeight_gauge_higgs_seven, bot_sup_eq] at hx
  · exact LocalCovFieldAlgebra.mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_eight_sup S hSL
      hx hL

/-- The classification below mass weight nine as an equivalence, in the shape of the gauge-
  and Yukawa-sector statements. An element of `fieldData.sectorMassWeight {gauge, scalar} w ⊔ S` for
  `w < 9` is fixed by both groups exactly when it is itself an element of `S` fixed by both
  groups. Gauge stability of `S` is not needed, and neither is gauge invariance of `x`, since the
  forward direction is the index count, which uses the Lorentz group alone. -/
lemma mem_sectorMassWeight_gauge_higgs_lt_nine_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x) ∧ ∀ g : SL(2,ℂ),
          repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, LocalCovFieldAlgebra.mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w hw S
      hSL hx hL,
      hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

/-- The same classification without the existential. Below mass weight nine an element of
  `fieldData.sectorMassWeight {gauge, scalar} w ⊔ S` fixed by both groups is an element of `S`
  fixed by both groups, and conversely. -/
lemma mem_sectorMassWeight_gauge_higgs_lt_nine_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x) ∧ ∀ g : SL(2,ℂ),
          repLorentzGroup g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  ⟨fun hx => ⟨LocalCovFieldAlgebra.mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w hw S
    hSL
    hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end LocalCovFieldAlgebra

end StandardModel
