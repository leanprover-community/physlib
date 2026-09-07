/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.KineticTerms
public import Mathlib.RepresentationTheory.Invariants
/-!
# The kinetic terms at mass weight eight

Mass weight eight is the first weight at which the fermion sector carries an invariant,
and what it carries is the kinetic terms. The submodule is
`derivSubmodule 0 * derivSubmodule 1`, one underived tower against one once-derived one,
and the single derivative is exactly what mass weight six was missing: it supplies a
four-vector index, and a four-vector index together with a dotted and an undotted spinor
index has one invariant contraction, against the conjugate Pauli matrices. That
contraction is `ψ̄ σ̄^μ ∂_μ ψ`.

The classification runs the four stages every sector runs. Hypercharge first, through the
gauge weight decomposition: `massWeightSubmoduleGaugeWeightEight_piece_zero` cuts the
hundred pairings of two fermion symbols down to the ten conjugate ones, every other
pairing having hypercharges that cannot cancel. Then colour, then isospin, then Lorentz,
one classification each, chained by the `Peels` relation of `StandardModel.Peeling` and
supplied by the `KineticBlock` packages of `KineticTerms`. What is left is the kinetic
span: one term for each of the ten pairings and each of the nine pairs of generations.

- A. Symbol ranges and their stability
- B. The block submodules
- C. The symbol ranges inside the derivative submodules, and the mass weight
- D. The kinetic span
- E. The blocks peel to the kinetic terms
- F. The classification as an equivalence

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
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
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

/-!

## A. Symbol ranges and their stability

The peeling asks two things of the submodule a block is read from: that the two groups
carry it into itself, and that it lies in the span of the block's components. Both come
from the symbol maps. A gauge transformation moves only the covector a symbol is evaluated
at, so a symbol range is gauge stable at any number of derivative slots. The Lorentz group
moves the covector too, but it also mixes the derivative slots, so an underived range is
Lorentz stable on its own while a once-derived one is stable only after joining over the
derivative direction — which is why a block submodule carries that join.

-/

/-- The two groups read as one family of maps respect multiplication, each of the two
  representations doing so. -/
lemma gaugeLorentzMaps_mul
    (hG : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    (p : GaugeGroupI ⊕ SL(2,ℂ)) (a b : B) :
    gaugeLorentzMaps repGauge repLorentz p (a * b)
      = gaugeLorentzMaps repGauge repLorentz p a
        * gaugeLorentzMaps repGauge repLorentz p b := by
  cases p with
  | inl g => exact hG g a b
  | inr Λ => exact hL Λ a b

/-- The join, over the derivative direction, of the ranges of a once-derived symbol map is
  carried into itself by the Lorentz group: a Lorentz transformation mixes the derivative
  slot into the other directions and moves the covector, and both stay inside the join. -/
lemma isStableUnder_iSup_range_deriv_one {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] B}
    (hF : IsLorentzCovDerivTransforms repLorentz ρ F) (Λ : SL(2,ℂ)) :
    ∀ y ∈ (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ])),
      repLorentz Λ y ∈ ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ]) := by
  intro y hy
  have key : (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ]))
      ≤ Submodule.comap (repLorentz Λ)
        (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ])) := by
    refine iSup_le fun μ => ?_
    rintro _ ⟨φ, rfl⟩
    rw [Submodule.mem_comap, repLorentz_symbol_deriv_one hF Λ μ φ]
    exact Submodule.sum_mem _ fun ν _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem ν ⟨_, rfl⟩)
  exact key hy

/-- The range of an underived symbol map is carried into itself by both groups. -/
lemma isStableUnder_range_underived {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρG : Representation ℂ GaugeGroupI M} {ρL : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] B}
    (hG : ∀ (g : GaugeGroupI) (φ : Module.Dual ℂ M),
      repGauge g (F (![] : Fin 0 → Fin 1 ⊕ Fin 3) φ)
        = F (![] : Fin 0 → Fin 1 ⊕ Fin 3) (ρG.dual g φ))
    (hL : IsLorentzCovDerivTransforms repLorentz ρL F) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (LinearMap.range (F (![] : Fin 0 → Fin 1 ⊕ Fin 3))) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_range_repGauge hG, fun Λ => isStableUnder_range_repLorentz hL Λ⟩

/-- The join, over the derivative direction, of the ranges of a once-derived symbol map is
  carried into itself by both groups. -/
lemma isStableUnder_iSup_range_derived {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρG : Representation ℂ GaugeGroupI M} {ρL : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] B}
    (hG : ∀ (g : GaugeGroupI) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ M),
      repGauge g (F ![μ] φ) = F ![μ] (ρG.dual g φ))
    (hL : IsLorentzCovDerivTransforms repLorentz ρL F) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (F ![μ])) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨isStableUnder_iSup fun μ => isStableUnder_range_repGauge (hG · μ),
      isStableUnder_iSup_range_deriv_one hL⟩

/-!

## B. The block submodules

Each of the ten conjugate pairings gives one submodule per pair of generations: the
underived range of one species against the once-derived ranges of its conjugate, joined
over the derivative direction so that the Lorentz group has somewhere to move it. Each is
carried into itself by both groups and lies in the span of the components of the matching
kinetic block, which is all the peeling asks.

-/

set_option linter.unusedVariables false in
/-- The submodule of the `d ∂ bard` block of a generation pair: an underived
  down-singlet range against the once-derived conjugate down-singlet ranges,
  joined over the derivative direction. -/
noncomputable def dbardPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (d f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (bard f' ![μ])

include h in
/-- The `d ∂ bard` block submodule is carried into itself by both groups. -/
lemma isStableUnder_dbardPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.dbardPairSubmodule f f') := by
  rw [dbardPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := d f) (fun g φ => h.repGauge_d g f ![] φ)
      (h.repLorentz_d f))
    (isStableUnder_iSup_range_derived (F := bard f')
      (fun g μ φ => h.repGauge_bard g f' ![μ] φ) (h.repLorentz_bard f'))

include h in
/-- The `d ∂ bard` block submodule lies in the span of the block's components. -/
lemma dbardPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.dbardPairSubmodule f f' ≤ (h.dbardKineticBlock f f').blockSpan := by
  rw [dbardPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => d f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (DownSinglet.basis.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      bard f' ![k.1] (DownSinglet.basis.conj.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis DownSinglet.basis _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis DownSinglet.basis.conj (bard f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (0, 0))
      (Submodule.mem_iSup_of_mem ![j.2.2, i.2] (Submodule.mem_span_singleton_self _))

include h in
/-- The `d ∂ bard` block peels to its kinetic term. -/
lemma peels_dbard (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.dbardPairSubmodule f f')
      (ℂ ∙ (h.dbardKineticBlock f f').kineticTerm) :=
  ((h.dbardKineticBlock f f').peels).mono_left (h.dbardPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `bard ∂ d` block of a generation pair: an underived
  conjugate down-singlet range against the once-derived down-singlet ranges,
  joined over the derivative direction. -/
noncomputable def barddPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (d f' ![μ])

include h in
/-- The `bard ∂ d` block submodule is carried into itself by both groups. -/
lemma isStableUnder_barddPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barddPairSubmodule f f') := by
  rw [barddPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := bard f) (fun g φ => h.repGauge_bard g f ![] φ)
      (h.repLorentz_bard f))
    (isStableUnder_iSup_range_derived (F := d f')
      (fun g μ φ => h.repGauge_d g f' ![μ] φ) (h.repLorentz_d f'))

include h in
/-- The `bard ∂ d` block submodule lies in the span of the block's components. -/
lemma barddPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.barddPairSubmodule f f' ≤ (h.barddKineticBlock f f').blockSpan := by
  rw [barddPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => bard f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (DownSinglet.basis.conj.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      d f' ![k.1] (DownSinglet.basis.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis DownSinglet.basis.conj _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis DownSinglet.basis (d f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (0, 0))
      (Submodule.mem_iSup_of_mem ![i.2, j.2.2] (Submodule.mem_span_singleton_self _))

include h in
/-- The `bard ∂ d` block peels to its kinetic term. -/
lemma peels_bardd (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.barddPairSubmodule f f')
      (ℂ ∙ (h.barddKineticBlock f f').kineticTerm) :=
  ((h.barddKineticBlock f f').peels).mono_left (h.barddPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `u ∂ baru` block of a generation pair: an underived
  up-singlet range against the once-derived conjugate up-singlet ranges,
  joined over the derivative direction. -/
noncomputable def ubaruPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (u f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (baru f' ![μ])

include h in
/-- The `u ∂ baru` block submodule is carried into itself by both groups. -/
lemma isStableUnder_ubaruPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.ubaruPairSubmodule f f') := by
  rw [ubaruPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := u f) (fun g φ => h.repGauge_u g f ![] φ)
      (h.repLorentz_u f))
    (isStableUnder_iSup_range_derived (F := baru f')
      (fun g μ φ => h.repGauge_baru g f' ![μ] φ) (h.repLorentz_baru f'))

include h in
/-- The `u ∂ baru` block submodule lies in the span of the block's components. -/
lemma ubaruPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.ubaruPairSubmodule f f' ≤ (h.ubaruKineticBlock f f').blockSpan := by
  rw [ubaruPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => u f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (UpSinglet.basis.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      baru f' ![k.1] (UpSinglet.basis.conj.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis UpSinglet.basis _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis UpSinglet.basis.conj (baru f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (0, 0))
      (Submodule.mem_iSup_of_mem ![j.2.2, i.2] (Submodule.mem_span_singleton_self _))

include h in
/-- The `u ∂ baru` block peels to its kinetic term. -/
lemma peels_ubaru (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.ubaruPairSubmodule f f')
      (ℂ ∙ (h.ubaruKineticBlock f f').kineticTerm) :=
  ((h.ubaruKineticBlock f f').peels).mono_left (h.ubaruPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `baru ∂ u` block of a generation pair: an underived
  conjugate up-singlet range against the once-derived up-singlet ranges,
  joined over the derivative direction. -/
noncomputable def baruuPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (u f' ![μ])

include h in
/-- The `baru ∂ u` block submodule is carried into itself by both groups. -/
lemma isStableUnder_baruuPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.baruuPairSubmodule f f') := by
  rw [baruuPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := baru f) (fun g φ => h.repGauge_baru g f ![] φ)
      (h.repLorentz_baru f))
    (isStableUnder_iSup_range_derived (F := u f')
      (fun g μ φ => h.repGauge_u g f' ![μ] φ) (h.repLorentz_u f'))

include h in
/-- The `baru ∂ u` block submodule lies in the span of the block's components. -/
lemma baruuPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.baruuPairSubmodule f f' ≤ (h.baruuKineticBlock f f').blockSpan := by
  rw [baruuPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => baru f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (UpSinglet.basis.conj.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3) =>
      u f' ![k.1] (UpSinglet.basis.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis UpSinglet.basis.conj _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis UpSinglet.basis (u f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (0, 0))
      (Submodule.mem_iSup_of_mem ![i.2, j.2.2] (Submodule.mem_span_singleton_self _))

include h in
/-- The `baru ∂ u` block peels to its kinetic term. -/
lemma peels_baruu (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.baruuPairSubmodule f f')
      (ℂ ∙ (h.baruuKineticBlock f f').kineticTerm) :=
  ((h.baruuKineticBlock f f').peels).mono_left (h.baruuPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `Q ∂ barQ` block of a generation pair: an underived
  quark-doublet range against the once-derived conjugate quark-doublet ranges,
  joined over the derivative direction. -/
noncomputable def QbarQPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (Q f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (barQ f' ![μ])

include h in
/-- The `Q ∂ barQ` block submodule is carried into itself by both groups. -/
lemma isStableUnder_QbarQPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.QbarQPairSubmodule f f') := by
  rw [QbarQPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := Q f) (fun g φ => h.repGauge_Q g f ![] φ)
      (h.repLorentz_Q f))
    (isStableUnder_iSup_range_derived (F := barQ f')
      (fun g μ φ => h.repGauge_barQ g f' ![μ] φ) (h.repLorentz_barQ f'))

include h in
/-- The `Q ∂ barQ` block submodule lies in the span of the block's components. -/
lemma QbarQPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.QbarQPairSubmodule f f' ≤ (h.QbarQKineticBlock f f').blockSpan := by
  rw [QbarQPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => Q f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (QuarkDoublet.basis.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3 × Fin 2) =>
      barQ f' ![k.1] (QuarkDoublet.basis.conj.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis QuarkDoublet.basis _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis QuarkDoublet.basis.conj (barQ f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (j.2.2.2, i.2.2))
      (Submodule.mem_iSup_of_mem ![j.2.2.1, i.2.1] (Submodule.mem_span_singleton_self _))

include h in
/-- The `Q ∂ barQ` block peels to its kinetic term. -/
lemma peels_QbarQ (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.QbarQPairSubmodule f f')
      (ℂ ∙ (h.QbarQKineticBlock f f').kineticTerm) :=
  ((h.QbarQKineticBlock f f').peels).mono_left (h.QbarQPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `barQ ∂ Q` block of a generation pair: an underived
  conjugate quark-doublet range against the once-derived quark-doublet ranges,
  joined over the derivative direction. -/
noncomputable def barQQPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (barQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (Q f' ![μ])

include h in
/-- The `barQ ∂ Q` block submodule is carried into itself by both groups. -/
lemma isStableUnder_barQQPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barQQPairSubmodule f f') := by
  rw [barQQPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := barQ f) (fun g φ => h.repGauge_barQ g f ![] φ)
      (h.repLorentz_barQ f))
    (isStableUnder_iSup_range_derived (F := Q f')
      (fun g μ φ => h.repGauge_Q g f' ![μ] φ) (h.repLorentz_Q f'))

include h in
/-- The `barQ ∂ Q` block submodule lies in the span of the block's components. -/
lemma barQQPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.barQQPairSubmodule f f' ≤ (h.barQQKineticBlock f f').blockSpan := by
  rw [barQQPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => barQ f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (QuarkDoublet.basis.conj.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 3 × Fin 2) =>
      Q f' ![k.1] (QuarkDoublet.basis.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis QuarkDoublet.basis.conj _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis QuarkDoublet.basis (Q f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (i.2.2, j.2.2.2))
      (Submodule.mem_iSup_of_mem ![i.2.1, j.2.2.1] (Submodule.mem_span_singleton_self _))

include h in
/-- The `barQ ∂ Q` block peels to its kinetic term. -/
lemma peels_barQQ (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.barQQPairSubmodule f f')
      (ℂ ∙ (h.barQQKineticBlock f f').kineticTerm) :=
  ((h.barQQKineticBlock f f').peels).mono_left (h.barQQPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `L ∂ barL` block of a generation pair: an underived
  lepton-doublet range against the once-derived conjugate lepton-doublet ranges,
  joined over the derivative direction. -/
noncomputable def LbarLPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (L f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (barL f' ![μ])

include h in
/-- The `L ∂ barL` block submodule is carried into itself by both groups. -/
lemma isStableUnder_LbarLPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.LbarLPairSubmodule f f') := by
  rw [LbarLPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := L f) (fun g φ => h.repGauge_L g f ![] φ)
      (h.repLorentz_L f))
    (isStableUnder_iSup_range_derived (F := barL f')
      (fun g μ φ => h.repGauge_barL g f' ![μ] φ) (h.repLorentz_barL f'))

include h in
/-- The `L ∂ barL` block submodule lies in the span of the block's components. -/
lemma LbarLPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.LbarLPairSubmodule f f' ≤ (h.LbarLKineticBlock f f').blockSpan := by
  rw [LbarLPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => L f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (LeptonDoublet.basis.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) =>
      barL f' ![k.1] (LeptonDoublet.basis.conj.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis LeptonDoublet.basis _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis LeptonDoublet.basis.conj (barL f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i.1, j.2.1), (j.2.2, i.2))
      (Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _))

include h in
/-- The `L ∂ barL` block peels to its kinetic term. -/
lemma peels_LbarL (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.LbarLPairSubmodule f f')
      (ℂ ∙ (h.LbarLKineticBlock f f').kineticTerm) :=
  ((h.LbarLKineticBlock f f').peels).mono_left (h.LbarLPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `barL ∂ L` block of a generation pair: an underived
  conjugate lepton-doublet range against the once-derived lepton-doublet ranges,
  joined over the derivative direction. -/
noncomputable def barLLPairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (L f' ![μ])

include h in
/-- The `barL ∂ L` block submodule is carried into itself by both groups. -/
lemma isStableUnder_barLLPairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.barLLPairSubmodule f f') := by
  rw [barLLPairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := barL f) (fun g φ => h.repGauge_barL g f ![] φ)
      (h.repLorentz_barL f))
    (isStableUnder_iSup_range_derived (F := L f')
      (fun g μ φ => h.repGauge_L g f' ![μ] φ) (h.repLorentz_L f'))

include h in
/-- The `barL ∂ L` block submodule lies in the span of the block's components. -/
lemma barLLPairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.barLLPairSubmodule f f' ≤ (h.barLLKineticBlock f f').blockSpan := by
  rw [barLLPairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => barL f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (LeptonDoublet.basis.conj.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2 × Fin 2) =>
      L f' ![k.1] (LeptonDoublet.basis.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis LeptonDoublet.basis.conj _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis LeptonDoublet.basis (L f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2.1, i.1), (i.2, j.2.2))
      (Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _))

include h in
/-- The `barL ∂ L` block peels to its kinetic term. -/
lemma peels_barLL (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.barLLPairSubmodule f f')
      (ℂ ∙ (h.barLLKineticBlock f f').kineticTerm) :=
  ((h.barLLKineticBlock f f').peels).mono_left (h.barLLPairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `e ∂ bare` block of a generation pair: an underived
  lepton-singlet range against the once-derived conjugate lepton-singlet ranges,
  joined over the derivative direction. -/
noncomputable def ebarePairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (e f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (bare f' ![μ])

include h in
/-- The `e ∂ bare` block submodule is carried into itself by both groups. -/
lemma isStableUnder_ebarePairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.ebarePairSubmodule f f') := by
  rw [ebarePairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := e f) (fun g φ => h.repGauge_e g f ![] φ)
      (h.repLorentz_e f))
    (isStableUnder_iSup_range_derived (F := bare f')
      (fun g μ φ => h.repGauge_bare g f' ![μ] φ) (h.repLorentz_bare f'))

include h in
/-- The `e ∂ bare` block submodule lies in the span of the block's components. -/
lemma ebarePairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.ebarePairSubmodule f f' ≤ (h.ebareKineticBlock f f').blockSpan := by
  rw [ebarePairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => e f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (LeptonSinglet.basis.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2) =>
      bare f' ![k.1] (LeptonSinglet.basis.conj.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis LeptonSinglet.basis _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis LeptonSinglet.basis.conj (bare f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (j.2, i), (0, 0))
      (Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _))

include h in
/-- The `e ∂ bare` block peels to its kinetic term. -/
lemma peels_ebare (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.ebarePairSubmodule f f')
      (ℂ ∙ (h.ebareKineticBlock f f').kineticTerm) :=
  ((h.ebareKineticBlock f f').peels).mono_left (h.ebarePairSubmodule_le_blockSpan f f')

set_option linter.unusedVariables false in
/-- The submodule of the `bare ∂ e` block of a generation pair: an underived
  conjugate lepton-singlet range against the once-derived lepton-singlet ranges,
  joined over the derivative direction. -/
noncomputable def bareePairSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) (f f' : Fin 3) :
    Submodule ℂ B :=
  LinearMap.range (bare f (![] : Fin 0 → Fin 1 ⊕ Fin 3))
    * ⨆ μ : Fin 1 ⊕ Fin 3, LinearMap.range (e f' ![μ])

include h in
/-- The `bare ∂ e` block submodule is carried into itself by both groups. -/
lemma isStableUnder_bareePairSubmodule (f f' : Fin 3) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.bareePairSubmodule f f') := by
  rw [bareePairSubmodule]
  exact IsStableUnder.mul (gaugeLorentzMaps_mul hrepGauge_mul hrepLorentz_mul)
    (isStableUnder_range_underived (F := bare f) (fun g φ => h.repGauge_bare g f ![] φ)
      (h.repLorentz_bare f))
    (isStableUnder_iSup_range_derived (F := e f')
      (fun g μ φ => h.repGauge_e g f' ![μ] φ) (h.repLorentz_e f'))

include h in
/-- The `bare ∂ e` block submodule lies in the span of the block's components. -/
lemma bareePairSubmodule_le_blockSpan (f f' : Fin 3) :
    h.bareePairSubmodule f f' ≤ (h.bareeKineticBlock f f').blockSpan := by
  rw [bareePairSubmodule, KineticBlock.blockSpan]
  refine mul_le_of_le
    (A := fun k => bare f (![] : Fin 0 → Fin 1 ⊕ Fin 3) (LeptonSinglet.basis.conj.dualBasis k))
    (C := fun k : (Fin 1 ⊕ Fin 3) × (Fin 2) =>
      e f' ![k.1] (LeptonSinglet.basis.dualBasis k.2))
    (le_of_eq (range_eq_iSup_span_dualBasis LeptonSinglet.basis.conj _)) (iSup_le fun μ => ?_) ?_
  · rw [range_eq_iSup_span_dualBasis LeptonSinglet.basis (e f' ![μ])]
    exact iSup_le fun k => le_iSup_of_le (μ, k) le_rfl
  · intro i j
    exact Submodule.mem_iSup_of_mem (j.1, (i, j.2), (0, 0))
      (Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _))

include h in
/-- The `bare ∂ e` block peels to its kinetic term. -/
lemma peels_baree (f f' : Fin 3) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.bareePairSubmodule f f')
      (ℂ ∙ (h.bareeKineticBlock f f').kineticTerm) :=
  ((h.bareeKineticBlock f f').peels).mono_left (h.bareePairSubmodule_le_blockSpan f f')

/-!

## C. The symbol ranges inside the derivative submodules, and the mass weight

An underived symbol range lies in `derivSubmodule 0` and a once-derived one in
`derivSubmodule 1`, so every component of a kinetic block is a product of the two, which
is `massWeightSubmodule 8`. Each stage of a block's classification stays inside the span
of the stage before it, so the kinetic term is there too.

-/

/-- A family of one derivative direction is the tuple of its own entry. -/
lemma etaExpand_deriv_one (l : Fin 1 → Fin 1 ⊕ Fin 3) : ![l 0] = l := by
  funext i
  fin_cases i
  rfl

include h in
/-- The range of the down-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_d_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (d f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_rfl)))))))))

include h in
/-- The range of the conjugate down-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_bard_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bard f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))))))

include h in
/-- The range of the up-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_u_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (u f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
    (le_rfl))))))))

include h in
/-- The range of the conjugate up-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_baru_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (baru f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))))))

include h in
/-- The range of the quark-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_Q_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (Q f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))))

include h in
/-- The range of the conjugate quark-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_barQ_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barQ f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))

include h in
/-- The range of the lepton-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_L_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (L f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))

include h in
/-- The range of the conjugate lepton-doublet symbols lies in the derivative
  submodule of its slots. -/
lemma range_barL_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barL f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))

include h in
/-- The range of the lepton-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_e_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (e f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_left (le_sup_of_le_right (le_rfl))

include h in
/-- The range of the conjugate lepton-singlet symbols lies in the derivative
  submodule of its slots. -/
lemma range_bare_le_derivSubmodule {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bare f l) ≤ h.derivSubmodule n := by
  rw [derivSubmodule]
  refine le_iSup_of_le f (le_iSup_of_le l ?_)
  exact le_sup_of_le_right (le_rfl)

include h in
/-- The kinetic term of the `d ∂ bard` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma dbardKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.dbardKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_d_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_bard_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `bard ∂ d` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma barddKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.barddKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_bard_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_d_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `u ∂ baru` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma ubaruKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.ubaruKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_u_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_baru_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `baru ∂ u` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma baruuKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.baruuKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_baru_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_u_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `Q ∂ barQ` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma QbarQKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.QbarQKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_Q_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_barQ_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `barQ ∂ Q` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma barQQKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.barQQKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_barQ_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_Q_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `L ∂ barL` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma LbarLKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.LbarLKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_L_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_barL_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `barL ∂ L` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma barLLKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.barLLKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_barL_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_L_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `e ∂ bare` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma ebareKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.ebareKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_e_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_bare_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

include h in
/-- The kinetic term of the `bare ∂ e` block has mass weight eight: every component of the
  block is an underived tower against a once-derived one. -/
lemma bareeKineticTerm_mem_massWeightSubmodule (f f' : Fin 3) :
    (h.bareeKineticBlock f f').kineticTerm ∈ h.massWeightSubmodule 8 := by
  refine KineticBlock.kineticTerm_mem _ fun q l c c' w w' => ?_
  rw [h.massWeightSubmodule_eight_eq]
  exact Submodule.mul_mem_mul (h.range_bare_le_derivSubmodule f ![] ⟨_, rfl⟩)
    (h.range_e_le_derivSubmodule f' ![q] ⟨_, rfl⟩)

/-!

## D. The kinetic span

The kinetic span of the fermion sector at mass weight eight: the join, over the ten
conjugate pairings and the nine pairs of generations, of the lines through the kinetic
terms. Each generator is a gauge and Lorentz invariant of mass weight eight, which is the
easy direction of the classification and what makes it an equivalence rather than an
inclusion.

-/

set_option linter.unusedVariables false in
/-- The kinetic span of the fermion sector at mass weight eight: the join of the ten
  conjugate pairings, each over the nine pairs of generations. -/
noncomputable def kineticSpan (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3),
      ℂ ∙ (h.dbardKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.barddKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.ubaruKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.baruuKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.QbarQKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.barQQKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.LbarLKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.barLLKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.ebareKineticBlock f f').kineticTerm
        ⊔ ℂ ∙ (h.bareeKineticBlock f f').kineticTerm

include h in
/-- The line through the `dbard` kinetic term lies in the kinetic span. -/
lemma span_dbard_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.dbardKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_rfl)))))))))

include h in
/-- The line through the `bardd` kinetic term lies in the kinetic span. -/
lemma span_bardd_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.barddKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))))))

include h in
/-- The line through the `ubaru` kinetic term lies in the kinetic span. -/
lemma span_ubaru_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.ubaruKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))))))

include h in
/-- The line through the `baruu` kinetic term lies in the kinetic span. -/
lemma span_baruu_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.baruuKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))))))

include h in
/-- The line through the `QbarQ` kinetic term lies in the kinetic span. -/
lemma span_QbarQ_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.QbarQKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))))

include h in
/-- The line through the `barQQ` kinetic term lies in the kinetic span. -/
lemma span_barQQ_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.barQQKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_right (le_rfl)))))

include h in
/-- The line through the `LbarL` kinetic term lies in the kinetic span. -/
lemma span_LbarL_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.LbarLKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl))))

include h in
/-- The line through the `barLL` kinetic term lies in the kinetic span. -/
lemma span_barLL_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.barLLKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_rfl)))

include h in
/-- The line through the `ebare` kinetic term lies in the kinetic span. -/
lemma span_ebare_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.ebareKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_left (le_sup_of_le_right (le_rfl))

include h in
/-- The line through the `baree` kinetic term lies in the kinetic span. -/
lemma span_baree_le_kineticSpan (f f' : Fin 3) :
    ℂ ∙ (h.bareeKineticBlock f f').kineticTerm ≤ h.kineticSpan := by
  rw [kineticSpan]
  refine le_iSup₂_of_le f f' ?_
  exact le_sup_of_le_right (le_rfl)

include h in
/-- The kinetic span is fixed pointwise by both groups, each of its generators being a
  gauge and Lorentz invariant. -/
lemma isFixedBy_kineticSpan :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) h.kineticSpan := by
  rw [kineticSpan]
  refine isFixedBy_iSup fun f => isFixedBy_iSup fun f' => ?_
  exact IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (IsFixedBy.sup
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.dbardKineticBlock f f').repGauge_kineticTerm,
        (h.dbardKineticBlock f f').repLorentz_kineticTerm⟩))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.barddKineticBlock f f').repGauge_kineticTerm,
        (h.barddKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.ubaruKineticBlock f f').repGauge_kineticTerm,
        (h.ubaruKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.baruuKineticBlock f f').repGauge_kineticTerm,
        (h.baruuKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.QbarQKineticBlock f f').repGauge_kineticTerm,
        (h.QbarQKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.barQQKineticBlock f f').repGauge_kineticTerm,
        (h.barQQKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.LbarLKineticBlock f f').repGauge_kineticTerm,
        (h.LbarLKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.barLLKineticBlock f f').repGauge_kineticTerm,
        (h.barLLKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.ebareKineticBlock f f').repGauge_kineticTerm,
        (h.ebareKineticBlock f f').repLorentz_kineticTerm⟩)))
    (isFixedBy_span_singleton (forall_gaugeLorentzMaps_eq_self_iff.2
      ⟨(h.bareeKineticBlock f f').repGauge_kineticTerm,
        (h.bareeKineticBlock f f').repLorentz_kineticTerm⟩))

include h in
/-- The kinetic span lies at mass weight eight. -/
lemma kineticSpan_le_massWeightSubmodule : h.kineticSpan ≤ h.massWeightSubmodule 8 := by
  rw [kineticSpan]
  refine iSup_le fun f => iSup_le fun f' => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.dbardKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.barddKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.ubaruKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.baruuKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.QbarQKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.barQQKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.LbarLKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.barLLKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.ebareKineticTerm_mem_massWeightSubmodule f f')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      (h.bareeKineticTerm_mem_massWeightSubmodule f f')

include h in
/-- The kinetic span is a space of gauge invariants. -/
lemma kineticSpan_le_invariants : h.kineticSpan ≤ repGauge.invariants := by
  rw [kineticSpan]
  refine iSup_le fun f => iSup_le fun f' => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.dbardKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.barddKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.ubaruKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.baruuKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.QbarQKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.barQQKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.LbarLKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.barLLKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.ebareKineticBlock f f').repGauge_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.bareeKineticBlock f f').repGauge_kineticTerm)

include h in
/-- The kinetic span is a space of Lorentz invariants. -/
lemma kineticSpan_le_lorentzInvariants : h.kineticSpan ≤ repLorentz.invariants := by
  rw [kineticSpan]
  refine iSup_le fun f => iSup_le fun f' => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.dbardKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.barddKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.ubaruKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.baruuKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.QbarQKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.barQQKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.LbarLKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.barLLKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.ebareKineticBlock f f').repLorentz_kineticTerm)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2
      (h.bareeKineticBlock f f').repLorentz_kineticTerm)

/-!

## E. The blocks peel to the kinetic terms

The weight-zero piece of the gauge weight decomposition lies in the join of the ten block
submodules, hypercharge having already cut the hundred pairings down to ten; and each
block peels to its kinetic term, by the three stages its `KineticBlock` package supplies.
Joining the ten and then the nine generation pairs is `Peels.sup` and `Peels.iSup`, which
is where the stability of the blocks and of the kinetic span is spent.

-/

set_option linter.unusedVariables false in
/-- The join of the ten block submodules over the nine pairs of generations. -/
noncomputable def kineticBlockSubmodule (h : IsFermionSector B repGauge hrepGauge_mul
      repLorentz hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly) :
    Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3),
      h.dbardPairSubmodule f f'
        ⊔ h.barddPairSubmodule f f'
        ⊔ h.ubaruPairSubmodule f f'
        ⊔ h.baruuPairSubmodule f f'
        ⊔ h.QbarQPairSubmodule f f'
        ⊔ h.barQQPairSubmodule f f'
        ⊔ h.LbarLPairSubmodule f f'
        ⊔ h.barLLPairSubmodule f f'
        ⊔ h.ebarePairSubmodule f f'
        ⊔ h.bareePairSubmodule f f'

include h in
/-- The weight-zero piece at mass weight eight lies in the join of the ten block
  submodules: each of the ten conjugate pairings of
  `massWeightSubmoduleGaugeWeightEight_piece_zero` is an underived range against a
  once-derived one, and the derivative direction is joined over. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero_le :
    (h.massWeightSubmoduleGaugeWeightEight).piece 0 ≤ h.kineticBlockSubmodule := by
  rw [h.massWeightSubmoduleGaugeWeightEight_piece_zero, kineticBlockSubmodule]
  simp only [dbardPairSubmodule,
    barddPairSubmodule,
    ubaruPairSubmodule,
    baruuPairSubmodule,
    QbarQPairSubmodule,
    barQQPairSubmodule,
    LbarLPairSubmodule,
    barLLPairSubmodule,
    ebarePairSubmodule,
    bareePairSubmodule]
  refine iSup_le fun f => iSup_le fun f' => iSup_le fun l' => ?_
  obtain ⟨μ, rfl⟩ : ∃ μ, l' = ![μ] := ⟨l' 0, (etaExpand_deriv_one l').symm⟩
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range
      (bard f' ![ν])) μ))))))))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range
      (d f' ![ν])) μ))))))))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (mul_le_mul'
      le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range (baru f' ![ν])) μ)))))))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup
      (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range (u f' ![ν])) μ))))))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3
      => LinearMap.range (barQ f' ![ν])) μ)))))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range
      (Q f' ![ν])) μ))))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
      (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range (barL f' ![ν]))
      μ)))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup
      (fun ν : Fin 1 ⊕ Fin 3 => LinearMap.range (L f' ![ν])) μ))))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_left (le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕
      Fin 3 => LinearMap.range (bare f' ![ν])) μ)))
  · refine (GaugeWeightDecomposition.piece_le_self _ 0).trans
      (le_iSup₂_of_le f f' ?_)
    exact le_sup_of_le_right (mul_le_mul' le_rfl (le_iSup (fun ν : Fin 1 ⊕ Fin 3 =>
      LinearMap.range (e f' ![ν])) μ))

include h in
/-- The join of the ten block submodules peels to the kinetic span. -/
lemma peels_kineticBlockSubmodule :
    Peels (gaugeLorentzMaps repGauge repLorentz) h.kineticBlockSubmodule h.kineticSpan := by
  have hW : IsStableUnder (gaugeLorentzMaps repGauge repLorentz) h.kineticSpan :=
    h.isFixedBy_kineticSpan.isStableUnder
  have hS : ∀ f f' : Fin 3, IsStableUnder (gaugeLorentzMaps repGauge repLorentz)
      (
        h.dbardPairSubmodule f f'
          ⊔ h.barddPairSubmodule f f'
          ⊔ h.ubaruPairSubmodule f f'
          ⊔ h.baruuPairSubmodule f f'
          ⊔ h.QbarQPairSubmodule f f'
          ⊔ h.barQQPairSubmodule f f'
          ⊔ h.LbarLPairSubmodule f f'
          ⊔ h.barLLPairSubmodule f f'
          ⊔ h.ebarePairSubmodule f f'
          ⊔ h.bareePairSubmodule f f') := fun f f' =>
    IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (IsStableUnder.sup
      (h.isStableUnder_dbardPairSubmodule f f')
      (h.isStableUnder_barddPairSubmodule f f'))
      (h.isStableUnder_ubaruPairSubmodule f f'))
      (h.isStableUnder_baruuPairSubmodule f f'))
      (h.isStableUnder_QbarQPairSubmodule f f'))
      (h.isStableUnder_barQQPairSubmodule f f'))
      (h.isStableUnder_LbarLPairSubmodule f f'))
      (h.isStableUnder_barLLPairSubmodule f f'))
      (h.isStableUnder_ebarePairSubmodule f f'))
      (h.isStableUnder_bareePairSubmodule f f')
  have hP : ∀ f f' : Fin 3, Peels (gaugeLorentzMaps repGauge repLorentz)
      (
        h.dbardPairSubmodule f f'
          ⊔ h.barddPairSubmodule f f'
          ⊔ h.ubaruPairSubmodule f f'
          ⊔ h.baruuPairSubmodule f f'
          ⊔ h.QbarQPairSubmodule f f'
          ⊔ h.barQQPairSubmodule f f'
          ⊔ h.LbarLPairSubmodule f f'
          ⊔ h.barLLPairSubmodule f f'
          ⊔ h.ebarePairSubmodule f f'
          ⊔ h.bareePairSubmodule f f') h.kineticSpan := fun f f' =>
    Peels.sup
      (Peels.sup
      (Peels.sup
      (Peels.sup
      (Peels.sup
      (Peels.sup
      (Peels.sup
      (Peels.sup
      (Peels.sup
      ((h.peels_dbard f f').mono_right (h.span_dbard_le_kineticSpan f f'))
      ((h.peels_bardd f f').mono_right (h.span_bardd_le_kineticSpan f f'))
      (h.isStableUnder_barddPairSubmodule f f') hW)
      ((h.peels_ubaru f f').mono_right (h.span_ubaru_le_kineticSpan f f'))
      (h.isStableUnder_ubaruPairSubmodule f f') hW)
      ((h.peels_baruu f f').mono_right (h.span_baruu_le_kineticSpan f f'))
      (h.isStableUnder_baruuPairSubmodule f f') hW)
      ((h.peels_QbarQ f f').mono_right (h.span_QbarQ_le_kineticSpan f f'))
      (h.isStableUnder_QbarQPairSubmodule f f') hW)
      ((h.peels_barQQ f f').mono_right (h.span_barQQ_le_kineticSpan f f'))
      (h.isStableUnder_barQQPairSubmodule f f') hW)
      ((h.peels_LbarL f f').mono_right (h.span_LbarL_le_kineticSpan f f'))
      (h.isStableUnder_LbarLPairSubmodule f f') hW)
      ((h.peels_barLL f f').mono_right (h.span_barLL_le_kineticSpan f f'))
      (h.isStableUnder_barLLPairSubmodule f f') hW)
      ((h.peels_ebare f f').mono_right (h.span_ebare_le_kineticSpan f f'))
      (h.isStableUnder_ebarePairSubmodule f f') hW)
      ((h.peels_baree f f').mono_right (h.span_baree_le_kineticSpan f f'))
      (h.isStableUnder_bareePairSubmodule f f') hW
  rw [kineticBlockSubmodule]
  exact Peels.iSup (fun f => Peels.iSup (hP f) (hS f) hW)
    (fun f => isStableUnder_iSup fun f' => hS f f') hW

/-!

## F. The classification as an equivalence

The two directions meet. Forwards: hypercharge puts a gauge invariant in the weight-zero
piece, section E peels that down to the kinetic span, and what is left over is in `S` and
is itself invariant, the kinetic span being made of invariants. Backwards: the kinetic
span is a space of gauge and Lorentz invariants of mass weight eight, so splitting `x` as
`(x - y) + y` puts it back together.

So the fermion sector at mass weight eight carries exactly the kinetic terms — one for
each species, each pair of generations and each placement of the derivative — and nothing
else. Compare mass weight six, where the same argument leaves nothing at all: without a
derivative there is no four-vector index for the conjugate Pauli matrices to carry, and
the Dirac mass term does not exist.

-/

include h in
/-- The classification of the mass-weight eight invariants: an element of
  `massWeightSubmodule 8 ⊔ S` fixed by both groups is a combination of the kinetic terms
  up to a remainder in `S` that is itself fixed by both groups. -/
theorem exists_mem_of_gauge_and_lorentz_invariant (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8 ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentz g y = y) ∧ x - y ∈ h.kineticSpan := by
  have hzero : x ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 ⊔ S :=
    mem_piece_zero_sup_of_invariant _ (fun i y hy => hS _ y hy) hx hG
  have hblk : x ∈ h.kineticBlockSubmodule ⊔ S :=
    sup_le_sup_right h.massWeightSubmoduleGaugeWeightEight_piece_zero_le S hzero
  have hSstab : IsStableUnder (gaugeLorentzMaps repGauge repLorentz) S :=
    isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩
  have hxinv : ∀ p, gaugeLorentzMaps repGauge repLorentz p x = x :=
    forall_gaugeLorentzMaps_eq_self_iff.2 ⟨hG, hL⟩
  obtain ⟨z, hz, y, hy, hzy⟩ := Submodule.mem_sup.1
    (h.peels_kineticBlockSubmodule S hSstab x hblk hxinv)
  have hzG := (Representation.mem_invariants _ _).1 (h.kineticSpan_le_invariants hz)
  have hzL := (Representation.mem_invariants _ _).1 (h.kineticSpan_le_lorentzInvariants hz)
  refine ⟨y, hy, fun g => ?_, fun g => ?_, ?_⟩
  · have hxg := hG g
    rw [← hzy, map_add, hzG g] at hxg
    exact add_left_cancel hxg
  · have hxg := hL g
    rw [← hzy, map_add, hzL g] at hxg
    exact add_left_cancel hxg
  · rw [← hzy]
    simpa using hz

include h in
/-- The classification of mass weight eight as an equivalence, in the shape of the
  sibling sectors: an element of `massWeightSubmodule 8 ⊔ S` is fixed by both groups
  exactly when it is a combination of the kinetic terms up to a remainder in `S` fixed by
  both groups. Forwards this is `exists_mem_of_gauge_and_lorentz_invariant`; backwards it
  splits `x` as `(x - y) + y`, the first summand an invariant of mass weight eight by
  section D. -/
theorem mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.kineticSpan := by
  refine ⟨fun hx =>
    h.exists_mem_of_gauge_and_lorentz_invariant S hS hSL hx.1 hx.2.1 hx.2.2, ?_⟩
  rintro ⟨y, hyS, hyG, hyL, hxy⟩
  have hmem := h.kineticSpan_le_massWeightSubmodule hxy
  have hzG := (Representation.mem_invariants _ _).1 (h.kineticSpan_le_invariants hxy)
  have hzL := (Representation.mem_invariants _ _).1 (h.kineticSpan_le_lorentzInvariants hxy)
  refine ⟨?_, fun g => ?_, fun g => ?_⟩
  · have hsum : x - y + y ∈ h.massWeightSubmodule 8 ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : repGauge g (x - y + y) = x - y + y := by rw [map_add, hzG g, hyG g]
    simpa using hstep
  · have hstep : repLorentz g (x - y + y) = x - y + y := by rw [map_add, hzL g, hyL g]
    simpa using hstep


end IsFermionSector

end StandardModel
