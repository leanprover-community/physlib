/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.GaugeHiggsSector.Basic
public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.MassDimLTEight
/-!
# The gauge-Higgs invariants below mass weight nine

The mixed `{gauge, higgs}` sector is small, and none of it is invariant. A field-strength
tower weighs at least four and a Higgs tower at least two, and both weights are even, so
the sector vanishes below weight six and at every odd weight, weight seven included. What
is left is weight six, the underived field strength against the underived Higgs, and
weight eight: that same field strength against the weight-four Higgs terms, together with
the once-derived field strength against the underived Higgs.

None of it can carry an invariant, and the reason is an index count. The Higgs is a Lorentz
scalar, so an underived Higgs symbol has no covector index at all and is fixed by the whole
Lorentz group, while a once-derived one carries a single index, its derivative slot. The
covector indices of these products are therefore those of the field strength — two when it
is underived and three when it is once derived — plus at most one from the Higgs.

Two indices admit exactly one invariant contraction, the metric trace, and it vanishes: the
metric is symmetric in the pair of indices in which `IsGaugeSector.F_antisymm` says the
field strength is antisymmetric. Three indices admit no invariant contraction at all, the
metric tying two and the Levi-Civita symbol four. Weight six and the two-Higgs term of
weight eight are of the first kind and the other two terms of weight eight of the second,
so at no weight below nine does the sector add an invariant to what is already there.

Neither count needs the gauge group, and neither needs a basis of the Higgs. The families
being peeled are indexed by a covector of the gauge algebra together with a piece of Higgs
material, and neither index is finite; section B peels a join over an arbitrary index type
by passing to a finite subset of it, which is all an element of a join ever needs.

- A. Field strengths against Lorentz-inert material
- B. Peeling a join over an arbitrary index
- C. The underived Higgs is Lorentz inert
- D. Field strengths against Higgs material
- E. Mass weights six and eight
- F. The classification below mass weight nine

The bound is `w < 9` rather than the gauge sector's `w < 8`, weight eight being as empty of
invariants as the weights below it. No lower bound on `w` is needed either: the sector is
the two-class sector of the gauge and Higgs generators, so both classes must be present
with a non-zero weight and the scalars, which force `0 < w` in the gauge-sector statement,
never appear.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

variable {B : Type*} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## A. Field strengths against Lorentz-inert material

A family transforming as a Lorentz tensor stays one when multiplied by an element the
Lorentz group fixes, and its metric trace is multiplied by that element too. So a field
strength against an underived Higgs is a tensor of the same two or three indices as the
field strength alone. A once-derived Higgs contributes an index of its own, and a
bi-Lorentz family against a Lorentz vector is a triple Lorentz family.

-/

/-- Multiplying a bi-Lorentz family by a Lorentz-inert element gives a bi-Lorentz family:
  the element rides through the transformation law untouched. -/
lemma IsBiLorentz.mul_fixed
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B} (hT : IsBiLorentz B repLorentz T) {y : B}
    (hy : ∀ g : SL(2,ℂ), repLorentz g y = y) :
    IsBiLorentz B repLorentz fun d => T d * y where
  repLorentz_T g l := by
    rw [hmul, hT.repLorentz_T g l, hy g, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- The metric trace of a family multiplied on the right by a fixed element is the metric
  trace of the family, multiplied by that element. -/
lemma IsBiLorentz.metricContraction_mul (T : (Fin 2 → Fin 1 ⊕ Fin 3) → B) (y : B) :
    IsBiLorentz.metricContraction (T := fun d => T d * y)
      = IsBiLorentz.metricContraction (T := T) * y := by
  rw [IsBiLorentz.metricContraction, IsBiLorentz.metricContraction, Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => (smul_mul_assoc _ _ _).symm

/-- Multiplying a triple Lorentz family by a Lorentz-inert element gives a triple Lorentz
  family. -/
lemma IsTriLorentz.mul_fixed
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin 3 → Fin 1 ⊕ Fin 3) → B} (hT : IsTriLorentz B repLorentz T) {y : B}
    (hy : ∀ g : SL(2,ℂ), repLorentz g y = y) :
    IsTriLorentz B repLorentz fun d => T d * y where
  repLorentz_T g l := by
    rw [hmul, hT.repLorentz_T g l, hy g, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- A bi-Lorentz family against a Lorentz vector is a triple Lorentz family: the two
  covector indices of the first factor and the single index of the second make three. -/
lemma IsBiLorentz.isTriLorentz_mul_vector
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B} (hT : IsBiLorentz B repLorentz T)
    {U : (Fin 1 ⊕ Fin 3) → B}
    (hU : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3), repLorentz g (U μ)
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) • U ν) :
    IsTriLorentz B repLorentz fun d : Fin 3 → Fin 1 ⊕ Fin 3 => T ![d 0, d 1] * U (d 2) where
  repLorentz_T g l := by
    rw [hmul, hT.repLorentz_T g ![l 0, l 1], hU g (l 2),
      StandardModel.IsGaugeSector.sum_cov_two, StandardModel.IsGaugeSector.sum_cov_three,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    all_goals simp [Fin.prod_univ_two, Fin.prod_univ_three, mul_assoc]

end Lorentz

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

section Peeling

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## B. Peeling a join over an arbitrary index

The gauge sector peels a join of spans indexed by a finite set, which is what its twelve
directions of the gauge algebra need. Here the families are indexed by a covector of the
gauge algebra together with a piece of Higgs material, and neither index is finite. Nothing
is lost: an element of a join lies in the join over finitely many of the summands, so the
finite peeling applies to it as it stands. The rest of the section collects the stability
and the inertness of products and joins that the peeling consumes.

-/

/-- A Lorentz invariant of a join, over an arbitrary index type, of the spans of
  bi-Lorentz families with vanishing metric traces lies in the stable submodule it is taken
  modulo. An element of a join lies in a join over finitely many of the summands, so the
  finite peeling of the gauge sector suffices. -/
lemma mem_of_lorentz_invariant_iSup_isBiLorentz_span {ι : Type}
    {T : ι → (Fin 2 → Fin 1 ⊕ Fin 3) → B} (hT : ∀ i, IsBiLorentz B repLorentz (T i))
    (hzero : ∀ i, IsBiLorentz.metricContraction (T := T i) = 0) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, (hT i).span) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  classical
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hu
  exact IsGaugeSector.mem_of_lorentz_invariant_biSup_isBiLorentz_span hT hzero S hS s
    (Submodule.mem_sup.2 ⟨u, hs, z, hz, rfl⟩) hinv

/-- A Lorentz invariant of a join, over an arbitrary index type, of the spans of triple
  Lorentz families lies in the stable submodule it is taken modulo: three covector indices
  admit no invariant contraction at all. -/
lemma mem_of_lorentz_invariant_iSup_isTriLorentz_span {ι : Type}
    {T : ι → (Fin 3 → Fin 1 ⊕ Fin 3) → B} (hT : ∀ i, IsTriLorentz B repLorentz (T i))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, (hT i).span) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  classical
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hu
  exact IsGaugeSector.mem_of_lorentz_invariant_biSup_isTriLorentz_span hT S hS s
    (Submodule.mem_sup.2 ⟨u, hs, z, hz, rfl⟩) hinv

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
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
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

## C. The underived Higgs is Lorentz inert

The Higgs is a Lorentz scalar, and an underived symbol has no derivative slot for the
Lorentz matrix to act on, so it is fixed outright — and with it every element of the
submodule the underived symbols span.

-/

/-- The underived Higgs and conjugate-Higgs symbols are Lorentz scalars with no derivative
  slot to rotate, so every element of the weight-two Higgs submodule is fixed by the whole
  Lorentz group. -/
lemma repLorentz_eq_self_of_mem_higgs_derivSubmodule_zero (g : SL(2,ℂ)) {y : B}
    (hy : y ∈ h.isHiggsSector.derivSubmodule 0) : repLorentz g y = y := by
  have key : h.isHiggsSector.derivSubmodule 0
      ≤ LinearMap.ker (repLorentz g - LinearMap.id) := by
    rw [IsHiggsSector.derivSubmodule]
    refine sup_le ?_ ?_
    · rw [IsHiggsSector.higgsSubmodule]
      refine iSup_le fun l => ?_
      rintro _ ⟨φ, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rw [h.isHiggsSector.repLorentz_H_apply g φ 0 l,
        Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
          (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
          (fun hb => absurd (Finset.mem_univ _) hb),
        Fin.prod_univ_zero, one_smul, Subsingleton.elim l ![]]
    · rw [IsHiggsSector.barHiggsSubmodule]
      refine iSup_le fun l => ?_
      rintro _ ⟨φ, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rw [h.isHiggsSector.repLorentz_barH_apply g φ 0 l,
        Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
          (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
          (fun hb => absurd (Finset.mem_univ _) hb),
        Fin.prod_univ_zero, one_smul, Subsingleton.elim l ![]]
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    using key hy

/-!

## D. Field strengths against Higgs material

Three products have to be classified. An underived field strength against inert material is
a bi-Lorentz family whose metric trace vanishes with the antisymmetry of the field strength;
a once-derived one against inert material is a triple Lorentz family; and an underived one
against a once-derived Higgs is a triple Lorentz family as well, the Higgs supplying the
third index. The last is the only one in which a Higgs index moves at all.

-/

/-- An underived field strength against Lorentz-inert material carries no Lorentz
  invariant modulo a Lorentz-stable submodule. -/
theorem mem_of_lorentz_invariant_derivSubmodule_zero_mul_fixed_sup (C : Submodule ℂ B)
    (hC : ∀ (g : SL(2,ℂ)), ∀ y ∈ C, repLorentz g y = y) (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.isGaugeSector.derivSubmodule 0 * C ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hT : ∀ i : Module.Dual ℝ GaugeAlgebra × C, IsBiLorentz B repLorentz
      (fun l : Fin 2 → Fin 1 ⊕ Fin 3 => F ![] (l 0) (l 1) i.1 * (i.2 : B)) :=
    fun i => (h.isGaugeSector.isBiLorentz_F_underived i.1).mul_fixed hrepLorentz_mul
      fun g => hC g (i.2 : B) i.2.2
  have hzero : ∀ i : Module.Dual ℝ GaugeAlgebra × C,
      IsBiLorentz.metricContraction
        (T := fun l : Fin 2 → Fin 1 ⊕ Fin 3 => F ![] (l 0) (l 1) i.1 * (i.2 : B)) = 0 := by
    intro i
    refine IsGaugeSector.metricContraction_eq_zero_of_antisymm fun a b => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h.isGaugeSector.F_antisymm ![] a b i.1, neg_mul]
  refine mem_of_lorentz_invariant_iSup_isBiLorentz_span hT hzero S hSL ?_ hinv
  refine sup_le_sup_right ?_ S hx
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have key : h.isGaugeSector.derivSubmodule 0
      ≤ Submodule.comap (LinearMap.mulRight ℂ b) (⨆ i, (hT i).span) := by
    rw [IsGaugeSector.derivSubmodule]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    rw [Subsingleton.elim l ![]]
    refine Submodule.mem_iSup_of_mem (φ, ⟨b, hb⟩) (Submodule.mem_iSup_of_mem ![μ, ν] ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Submodule.mem_span_singleton_self _
  exact key ha

/-- A once-derived field strength against Lorentz-inert material carries no Lorentz
  invariant modulo a Lorentz-stable submodule. -/
theorem mem_of_lorentz_invariant_derivSubmodule_one_mul_fixed_sup (C : Submodule ℂ B)
    (hC : ∀ (g : SL(2,ℂ)), ∀ y ∈ C, repLorentz g y = y) (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.isGaugeSector.derivSubmodule 1 * C ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hT : ∀ i : Module.Dual ℝ GaugeAlgebra × C, IsTriLorentz B repLorentz
      (fun l : Fin 3 → Fin 1 ⊕ Fin 3 => F ![l 0] (l 1) (l 2) i.1 * (i.2 : B)) :=
    fun i => (h.isGaugeSector.isTriLorentz_F_deriv_one i.1).mul_fixed hrepLorentz_mul
      fun g => hC g (i.2 : B) i.2.2
  refine mem_of_lorentz_invariant_iSup_isTriLorentz_span hT S hSL ?_ hinv
  refine sup_le_sup_right ?_ S hx
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have key : h.isGaugeSector.derivSubmodule 1
      ≤ Submodule.comap (LinearMap.mulRight ℂ b) (⨆ i, (hT i).span) := by
    rw [IsGaugeSector.derivSubmodule]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    refine Submodule.mem_iSup_of_mem (φ, ⟨b, hb⟩) (Submodule.mem_iSup_of_mem ![l 0, μ, ν] ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, IsGaugeSector.etaExpand_cov_one]
    exact Submodule.mem_span_singleton_self _
  exact key ha

/-- An underived field strength against a once-derived Higgs carries no Lorentz invariant
  modulo a Lorentz-stable submodule: three covector indices admit no contraction. -/
theorem mem_of_lorentz_invariant_derivSubmodule_zero_mul_higgs_one_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.isGaugeSector.derivSubmodule 0 * h.isHiggsSector.derivSubmodule 1 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hU : ∀ (j : Module.Dual ℂ HiggsVec ⊕ Module.Dual ℂ (ConjModule HiggsVec))
      (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3),
      repLorentz g (Sum.elim (fun φ => H ![μ] φ) (fun ψ => barH ![μ] ψ) j)
        = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) •
            Sum.elim (fun φ => H ![ν] φ) (fun ψ => barH ![ν] ψ) j := by
    rintro (φ | ψ) g μ
    · simp only [Sum.elim_inl]
      rw [h.isHiggsSector.repLorentz_H_apply g φ 1 ![μ], IsGaugeSector.sum_cov_one]
      exact Finset.sum_congr rfl fun ν _ => by simp
    · simp only [Sum.elim_inr]
      rw [h.isHiggsSector.repLorentz_barH_apply g ψ 1 ![μ], IsGaugeSector.sum_cov_one]
      exact Finset.sum_congr rfl fun ν _ => by simp
  have hT : ∀ i : Module.Dual ℝ GaugeAlgebra ×
      (Module.Dual ℂ HiggsVec ⊕ Module.Dual ℂ (ConjModule HiggsVec)),
      IsTriLorentz B repLorentz (fun l : Fin 3 → Fin 1 ⊕ Fin 3 => F ![] (l 0) (l 1) i.1 *
        Sum.elim (fun φ => H ![l 2] φ) (fun ψ => barH ![l 2] ψ) i.2) :=
    fun i => (h.isGaugeSector.isBiLorentz_F_underived i.1).isTriLorentz_mul_vector
      hrepLorentz_mul (hU i.2)
  refine mem_of_lorentz_invariant_iSup_isTriLorentz_span hT S hSL ?_ hinv
  refine sup_le_sup_right ?_ S hx
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have key : ∀ (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra),
      h.isHiggsSector.derivSubmodule 1
        ≤ Submodule.comap (LinearMap.mulLeft ℂ (F ![] μ ν φ)) (⨆ i, (hT i).span) := by
    intro μ ν φ
    rw [IsHiggsSector.derivSubmodule]
    refine sup_le ?_ ?_
    · rw [IsHiggsSector.higgsSubmodule]
      refine iSup_le fun dd => ?_
      obtain ⟨ρ, rfl⟩ : ∃ ρ, dd = ![ρ] := ⟨dd 0, (IsGaugeSector.etaExpand_cov_one dd).symm⟩
      rintro _ ⟨ψ, rfl⟩
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      refine Submodule.mem_iSup_of_mem (φ, Sum.inl ψ)
        (Submodule.mem_iSup_of_mem ![μ, ν, ρ] ?_)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Sum.elim_inl]
      exact Submodule.mem_span_singleton_self _
    · rw [IsHiggsSector.barHiggsSubmodule]
      refine iSup_le fun dd => ?_
      obtain ⟨ρ, rfl⟩ : ∃ ρ, dd = ![ρ] := ⟨dd 0, (IsGaugeSector.etaExpand_cov_one dd).symm⟩
      rintro _ ⟨ψ, rfl⟩
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      refine Submodule.mem_iSup_of_mem (φ, Sum.inr ψ)
        (Submodule.mem_iSup_of_mem ![μ, ν, ρ] ?_)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Sum.elim_inr]
      exact Submodule.mem_span_singleton_self _
  have hA : h.isGaugeSector.derivSubmodule 0
      ≤ Submodule.comap (LinearMap.mulRight ℂ b) (⨆ i, (hT i).span) := by
    rw [IsGaugeSector.derivSubmodule]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    rw [Subsingleton.elim l ![]]
    exact key μ ν φ hb
  exact hA ha

/-!

## E. Mass weights six and eight

Weight six is a single product and section D settles it outright. Weight eight is a join of
three, and they are peeled one at a time, the two not yet peeled joining the error term —
which asks that they be Lorentz stable. The gauge and Higgs derivative submodules are, and
so are their products and joins.

-/

/-- Mass weight six carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {gauge, higgs} 6 ⊔ S` lies in `S`. The weight is
  the underived field strength against the underived Higgs, whose two covector indices are
  contracted only by the metric, and that trace vanishes. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_six_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} 6 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_gauge_higgs_six] at hx
  exact h.mem_of_lorentz_invariant_derivSubmodule_zero_mul_fixed_sup _
    (fun g y hy => h.repLorentz_eq_self_of_mem_higgs_derivSubmodule_zero g hy) S hSL hx hinv

/-- Mass weight eight carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {gauge, higgs} 8 ⊔ S` lies in `S`. The three
  products making up the weight are peeled off one at a time, the two carrying three
  covector indices by the absence of any contraction and the one carrying two by the
  vanishing of the metric trace. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_eight_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} 8 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hH0 : ∀ (g : SL(2,ℂ)), ∀ y ∈ h.isHiggsSector.derivSubmodule 0, repLorentz g y = y :=
    fun g y hy => h.repLorentz_eq_self_of_mem_higgs_derivSubmodule_zero g hy
  have hH0H0 : ∀ (g : SL(2,ℂ)), ∀ y ∈ h.isHiggsSector.derivSubmodule 0 *
      h.isHiggsSector.derivSubmodule 0, repLorentz g y = y :=
    repLorentz_eq_self_of_mem_mul hrepLorentz_mul hH0 hH0
  have hGst : ∀ (n : ℕ) (g : SL(2,ℂ)), ∀ y ∈ h.isGaugeSector.derivSubmodule n,
      repLorentz g y ∈ h.isGaugeSector.derivSubmodule n :=
    fun n g y hy => h.isGaugeSector.derivSubmodule_map_repLorentz_le n g ⟨y, hy, rfl⟩
  have hBst := repLorentz_mem_mul_of_stable hrepLorentz_mul (hGst 0)
    (repLorentz_mem_of_fixed hH0H0)
  have hCst := repLorentz_mem_mul_of_stable hrepLorentz_mul (hGst 1)
    (repLorentz_mem_of_fixed hH0)
  rw [h.sectorMassWeight_gauge_higgs_eight, mul_assoc, sup_assoc, sup_assoc] at hx
  exact h.mem_of_lorentz_invariant_derivSubmodule_one_mul_fixed_sup _ hH0 S hSL
    (h.mem_of_lorentz_invariant_derivSubmodule_zero_mul_fixed_sup _ hH0H0 _
      (repLorentz_mem_sup_of_stable hCst hSL)
      (h.mem_of_lorentz_invariant_derivSubmodule_zero_mul_higgs_one_sup _
        (repLorentz_mem_sup_of_stable hBst (repLorentz_mem_sup_of_stable hCst hSL)) hx hinv)
      hinv) hinv

/-!

## F. The classification below mass weight nine

The nine weights below nine are now settled: the sector vanishes below weight six and at
weight seven, and weights six and eight are section E. So below weight nine the gauge-Higgs
sector supplies no invariant beyond what `S` already carries, and the equivalences record it
in the shape the other sectors carry, so that all of them can be combined.

-/

/-- Below mass weight nine the gauge-Higgs sector carries no Lorentz invariant: a Lorentz
  invariant of `sectorMassWeight {gauge, higgs} w ⊔ S` for `w < 9` lies in `S`. Weights
  below six and weight seven are trivial submodules, and weights six and eight are the two
  index counts. -/
theorem mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup (w : ℕ) (hw : w < 9)
    (S : Submodule ℂ B) (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rcases lt_or_ge w 6 with hw6 | hw6
  · rwa [h.sectorMassWeight_gauge_higgs_eq_bot_of_lt_six hw6, bot_sup_eq] at hx
  interval_cases w
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_six_sup S hSL hx hL
  · rwa [h.sectorMassWeight_gauge_higgs_seven, bot_sup_eq] at hx
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_gauge_higgs_eight_sup S hSL hx hL

set_option linter.unusedVariables false in
/-- The classification below mass weight nine as an equivalence, in the shape of the gauge-
  and Yukawa-sector statements: an element of `sectorMassWeight {gauge, higgs} w ⊔ S` for
  `w < 9` is fixed by both groups exactly when it is itself an element of `S` fixed by both
  groups. Gauge stability of `S` is not needed, and neither is gauge invariance of `x`: the
  forward direction is the index count, which uses the Lorentz group alone. -/
theorem mem_sectorMassWeight_gauge_higgs_lt_nine_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w hw S hSL hx hL,
      hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

set_option linter.unusedVariables false in
/-- The same classification without the existential: below mass weight nine an element of
  `sectorMassWeight {gauge, higgs} w ⊔ S` fixed by both groups is an element of `S` fixed by
  both groups, and conversely. -/
theorem mem_sectorMassWeight_gauge_higgs_lt_nine_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w hw S hSL
    hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end IsCovStandardModel

end StandardModel
