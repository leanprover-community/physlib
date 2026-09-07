/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.FermionGaugeSector.Basic
public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.MassDimLTEight
public import Physlib.Particles.StandardModel.IsGaugeSector.DerivSubmodule.BoostWeightDecomposition
-- The fermion boost weights enter only inside the proofs below, so this import is kept
-- private: its public form is one character over the line-length limit.
import Physlib.Particles.StandardModel.IsFermionSector.DerivSubmodule.BoostWeightDecomposition
/-!
# The gauge-fermion invariants below mass weight nine

The mixed `{gauge, fermion}` sector is almost empty below weight nine, and what little
there is cannot be invariant. A field-strength tower weighs at least four and a fermion
tower at least three, so the sector vanishes below weight seven; at weight eight the two
splittings that arithmetic allows are `4 + 4` and `6 + 2`, and the fermion sector is
trivial at both four and two, so weight eight vanishes too. That leaves weight seven, the
single product `F ψ` of the underived field strength against the underived fermion towers.

Weight seven is barred from carrying an invariant by a parity count on boost weight, the
same one that empties the Yukawa sector at weights five and seven. Along a spatial axis a
field-strength symbol carries even boost weight, its two covector indices and its
derivative slots each contributing `±2` or `0` and its adjoint index nothing, while a
fermion symbol carries odd boost weight, the Weyl-spinor value index contributing the
extra `±1`. The one product at weight seven has exactly one fermion factor, so its boost
weight is odd along every axis; and a Lorentz invariant has boost weight zero, which is
even.

The machinery is the Yukawa sector's: `WeightDecomposition.mulOfMul` convolves the two
factors' boost decompositions using multiplicativity of the Lorentz representation alone,
`not_two_dvd_of_mem_mulOfMul_supp` does the parity bookkeeping, and
`mem_of_invariant_of_mem_sup_of_odd_supp` turns an odd support into the absence of
invariants modulo a Lorentz-stable submodule. Only the left-hand factor changes: the
Higgs decomposition of even support is replaced by the gauge one, which is even for the
same reason.

- A. Even field strength against odd fermion
- B. Mass weight seven
- C. The classification below mass weight nine

The bound is `w < 9` rather than `w < 8`: weight eight is as empty as the weights below
seven, so nothing is gained by stopping short of the first weight the sector can occupy.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.BoostWeight

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

## A. Even field strength against odd fermion

The two boost weight decompositions of the factors are already proved: the field-strength
derivative submodules carry even weights, the covector and derivative slots contributing
`±2` or `0` and the adjoint index nothing, and the fermion ones carry odd weights, the
Weyl-spinor value index adding `±1`. Convolving them gives a boost weight decomposition of
their product, and even plus odd is odd.

-/

/-- The boost weight decomposition of a product of a field-strength and a fermion
  derivative submodule, obtained by convolving the two factors' decompositions. -/
private noncomputable def gaugeFermionBoostWeight (a b : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (h.isGaugeSector.derivSubmodule a * h.isFermionSector.derivSubmodule b) :=
  WeightDecomposition.mulOfMul hrepLorentz_mul
    (h.isGaugeSector.derivSubmoduleBoostWeight a i)
    (h.isFermionSector.derivSubmoduleBoostWeight b i)

/-- One field-strength factor against one fermion factor is odd: even plus odd. -/
private lemma odd_gaugeFermionBoostWeight_supp (a b : ℕ) (i : Fin 3) :
    ∀ k ∈ (h.gaugeFermionBoostWeight a b i).supp, ¬ (2 : ℤ) ∣ k :=
  fun _ hk => WeightDecomposition.not_two_dvd_of_mem_mulOfMul_supp
    (fun _ hp => h.isGaugeSector.two_dvd_of_mem_derivSubmoduleBoostWeight_supp a i hp)
    (fun _ hq => h.isFermionSector.not_two_dvd_of_mem_derivSubmoduleBoostWeight_supp b i hq) hk

/-!

## B. Mass weight seven

Weight seven is the single product `F ψ`, the underived field strength against the
underived fermion towers. It has exactly one fermion factor, so section A makes every one
of its boost weights odd, and an invariant of odd boost weight is zero modulo a
Lorentz-stable submodule. The axis is immaterial; the first one will do.

-/

/-- Mass weight seven carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {gauge, fermion} 7 ⊔ S` lies in `S`. The weight is
  the underived field strength against the underived fermion towers, of odd boost
  weight. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_gauge_fermion_seven_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} 7 ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_gauge_fermion_seven] at hx
  exact WeightDecomposition.mem_of_invariant_of_mem_sup_of_odd_supp
    (h.gaugeFermionBoostWeight 0 0 0) (h.odd_gaugeFermionBoostWeight_supp 0 0 0) S hSL hx hL

/-!

## C. The classification below mass weight nine

The nine weights below nine are now settled: the sector vanishes below weight seven and
again at weight eight, and weight seven is section B. So below weight nine the
gauge-fermion sector supplies no invariant beyond what `S` already carries, and the
equivalences record it in the shape the other sectors carry, so that all of them can be
combined.

No lower bound on the weight is needed. The sector is the two-class sector of the gauge
and fermion generators, so both classes must be present with a non-zero weight and the
sector is already trivial at weight zero; the scalars, which force `0 < w` in the
gauge-sector statement, never appear.

-/

/-- Below mass weight nine the gauge-fermion sector carries no Lorentz invariant: a
  Lorentz invariant of `sectorMassWeight {gauge, fermion} w ⊔ S` for `w < 9` lies in `S`.
  Weights below seven and weight eight are trivial submodules, and weight seven is section
  B. -/
theorem mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup (w : ℕ) (hw : w < 9)
    (S : Submodule ℂ B) (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rcases lt_or_ge w 7 with hw7 | hw7
  · rwa [h.sectorMassWeight_gauge_fermion_eq_bot_of_lt_seven hw7, bot_sup_eq] at hx
  interval_cases w
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_gauge_fermion_seven_sup S hSL hx hL
  · rwa [h.sectorMassWeight_gauge_fermion_eight, bot_sup_eq] at hx

set_option linter.unusedVariables false in
/-- The classification below mass weight nine as an equivalence, in the shape of the gauge-
  and Yukawa-sector statements: an element of `sectorMassWeight {gauge, fermion} w ⊔ S` for
  `w < 9` is fixed by both groups exactly when it is itself an element of `S` fixed by both
  groups. Gauge stability of `S` is not needed, and neither is gauge invariance of `x`: the
  forward direction is the boost-weight parity argument, which uses the Lorentz group
  alone. -/
theorem mem_sectorMassWeight_gauge_fermion_lt_nine_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w hw S hSL hx hL,
      hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

set_option linter.unusedVariables false in
/-- The same classification without the existential: below mass weight nine an element of
  `sectorMassWeight {gauge, fermion} w ⊔ S` fixed by both groups is an element of `S` fixed
  by both groups, and conversely. -/
theorem mem_sectorMassWeight_gauge_fermion_lt_nine_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w hw S hSL
    hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end IsCovStandardModel

end StandardModel
