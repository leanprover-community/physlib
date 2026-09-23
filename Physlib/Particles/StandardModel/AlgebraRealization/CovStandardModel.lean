/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.AlgebraRealization.CovFieldAlgebra.Basic
public import Physlib.Particles.StandardModel.AlgebraRealization.MassWeight.Basic
/-!
# From the jet Standard Model to its covariant form

## i. Overview

`AlgebraRealization` records the Standard Model in terms of the *bare* symbols
`[∂_s A_μ^a]`, `[∂_s H^i]`, `[∂_s ψ^α]`, on which the whole jet gauge group
`JetGaugeGroupI` acts — a gauge transformation together with all of its derivatives at
the base point. The covariant form of the theory is written instead in terms of the
covariant towers `∇_l F_{μν}`, `∇_l H`, `∇_l ψ`, on which only the global gauge group
`GaugeGroupI` acts.

This file builds the bridge, in two halves. The first proves the *reduction theorem*:
inside the field algebra, invariance under the full jet gauge group is exactly
membership of the covariant subalgebra together with invariance under the global gauge
group; adjoining the Lorentz condition, which the reduction leaves untouched, gives the
form used for classifying Lagrangians. The second establishes the laws the towers
satisfy, which `CovAlgebraRealization` collects into the covariant form of the theory:
their global gauge equivariance, their mass weights and their statistics. The twelve
matter towers are treated uniformly: section B packages a matter species as its
gauge-algebra action, its bare family, and the two facts about the family every argument
uses — it commutes with the gauge field and it is a mass-weight eigenvector — and each
later law is proved once for an arbitrary species and read off twelve times. The Lorentz
laws of the matter towers are section L of [`CovariantDeriv.lean`](CovariantDeriv.lean);
the one for the field-strength tower closes this file.

## ii. Key results

- `AlgebraRealization.repGlobal` : the global gauge action, the jet action restricted
  along the constant jets.
- `AlgebraRealization.Species` : a matter species with the facts the laws below consume;
  `AlgebraRealization.speciesH`, `AlgebraRealization.speciesD` and their companions are
  the twelve matter families of the Standard Model.
- `AlgebraRealization.forall_repJet_eq_iff` and
  `AlgebraRealization.forall_repJet_and_repLorentz_eq_iff` : the reduction theorem, for
  the gauge group alone and together with the Lorentz group.
- `AlgebraRealization.repGlobal_covF`, `AlgebraRealization.repGlobal_covDerivH` and their
  companions : the covariant towers are equivariant for the global gauge group.
- `AlgebraRealization.covF_commute_of_mem_covAlgebra` : the field-strength tower is
  central in the covariant algebra.
- `AlgebraRealization.Species.massWeight_tower` and `AlgebraRealization.massWeight_covF` :
  a covariant tower is a mass-weight eigenvector of the weight its species and
  derivative order predict.
- `AlgebraRealization.Species.commute_tower_tower` and
  `AlgebraRealization.Species.anticomm_tower_tower` : the statistics of a pair of towers
  is the statistics of the pair of bare families.
- `AlgebraRealization.repLorentz_covF` : the Lorentz law of the field-strength tower.

## iii. Table of contents

- A. The global gauge action
- B. The twelve matter species
- C. Pure gauge jets fix the covariant algebra
- D. The reduction theorem
- E. The covariant generators are globally equivariant
- F. The field-strength tower is central in the covariant algebra
- G. Sums of products: the two family pairings
- H. The mass weights of the covariant towers
  - H.1. The mass weights, species by species
- I. The statistics of the covariant towers
  - I.1. The statistics, species by species
- J. The Lorentz law of the field-strength tower

## iv. References

The classification of jet-gauge invariants that section D consumes is
`AlgebraRealization.invariant_mem_adjoin_covDeriv` of
[`CovFieldAlgebra/Basic.lean`](CovFieldAlgebra/Basic.lean); the splitting of a gauge jet
into a pure jet and a constant jet is `localGaugeData.eq_truncationProjZero_mul_ofConstant`.
The laws of the second half are consumed by the three sector structures of
[`IsGaugeSector/Basic.lean`](../IsGaugeSector/Basic.lean),
[`HiggsAlgebraCovRealization/Basic.lean`](../HiggsAlgebraCovRealization/Basic.lean) and
[`IsFermionSector/Basic.lean`](../IsFermionSector/Basic.lean).

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace AlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-!

## A. The global gauge action

A global (constant) gauge transformation is a jet with no derivatives, so the global gauge
group sits inside the jet gauge group as the constant jets. Restricting the jet action along
that inclusion gives the global gauge action on the algebra, multiplicative like the jet action.

-/

/-- The action of the global gauge group on the algebra: the jet action restricted
  along the inclusion of the constant jets. -/
noncomputable def repGlobal (repJet : Representation ℂ JetGaugeGroupI B) :
    Representation ℂ GaugeGroupI B :=
  MonoidHom.comp repJet JetGaugeGroupI.ofConstant

/-- The global gauge action is the jet action at the corresponding constant jet. -/
@[simp]
lemma repGlobal_apply (repJet : Representation ℂ JetGaugeGroupI B) (g : GaugeGroupI)
    (b : B) : repGlobal repJet g b = repJet (JetGaugeGroupI.ofConstant g) b := rfl

include h in
/-- The global gauge action is multiplicative: it is the jet action at a constant jet,
  and the jet action is an algebra map. -/
lemma repGlobal_mul (g : GaugeGroupI) (b₁ b₂ : B) :
    repGlobal repJet g (b₁ * b₂) = repGlobal repJet g b₁ * repGlobal repJet g b₂ :=
  h.gaugeRealization.gauge_mul _ b₁ b₂

/-!

## B. The twelve matter species

Every matter tower is `GaugeAlgebraRealization.covDerivIter h.A act F n l 0` for the gauge-algebra
action `act` of its species and its bare family `F`, and every law proved below for a
matter tower uses only two facts about that family: its symbols commute with the
gauge-field symbols, and they are mass-weight eigenvectors of weight `c + 2 * |t|` at the
derivative multiset `t`. A `Species` records exactly this data, the twelve matter families
of the Standard Model are its twelve instances, and `matterTowers_induction_species` and
`covGenerators_cases` are the case splits that read a law proved for an arbitrary species
off for all of them.

-/

/-- A matter species of the Standard Model, as the laws of this file consume it: the
  gauge-algebra action on its value space, its bare family of derivative symbols, the
  mass weight `c` of its undifferentiated symbols, and the two facts that the family
  commutes with the gauge-field symbols and has mass weight `c + 2 * |t|` at the
  derivative multiset `t`. -/
structure Species (V : Type) [AddCommGroup V] [Module ℂ V] where
  /-- The action of the gauge algebra on the value space. -/
  act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V
  /-- The bare derivative symbols of the species. -/
  F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B
  /-- The mass weight of the undifferentiated symbols. -/
  c : ℕ
  /-- The gauge-field symbols commute with the bare symbols. -/
  A_comm : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V), Commute (h.A p μ ψ) (F t χ)
  /-- The bare symbol at the derivative multiset `t` has mass weight `c + 2 * |t|`. -/
  massWeight : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V),
    massWeightPoly (F t χ) = Polynomial.monomial (c + 2 * Multiset.card t) (F t χ)

namespace Species

variable {h} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (S : h.Species V)

/-- The covariant tower of the species, in the ordered-tuple indexing of the covariant
  form of the theory. -/
noncomputable def tower {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) : Module.Dual ℂ V →ₗ[ℂ] B :=
  GaugeAlgebraRealization.covDerivIter h.A S.act S.F n l 0

/-- The tower commutes with the gauge-field symbols: it is a polynomial in symbols that do. -/
lemma comm_A {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra) :
    Commute (S.tower l φ) (h.A p μ ψ) :=
  GaugeAlgebraRealization.commute_covDerivIter S.act S.F h.A_comm_A S.A_comm n l φ p μ ψ

end Species

/-- The Higgs field, of mass weight `2`. -/
noncomputable def speciesH : h.Species HiggsVec :=
  ⟨HiggsVec.gaugeAlgebraAction, h.H, 2, h.A_comm_H,
    fun t χ => (h.massWeight_H t χ).trans (by rw [mul_add, mul_one])⟩

/-- The conjugate Higgs field, of mass weight `2`. -/
noncomputable def speciesBarH : h.Species (ConjModule HiggsVec) :=
  ⟨LocalGaugeData.actionConj HiggsVec.gaugeAlgebraAction, h.barH, 2, h.A_comm_barH,
    fun t χ => (h.massWeight_barH t χ).trans (by rw [mul_add, mul_one])⟩

/-- The down-type quarks of generation `i`, of mass weight `3`. -/
noncomputable def speciesD (i : Fin 3) : h.Species DownSinglet :=
  ⟨DownSinglet.gaugeAlgebraAction, h.d i, 3, fun p μ ψ => h.A_comm_d p μ ψ i, h.massWeight_d i⟩

/-- The conjugate down-type quarks of generation `i`, of mass weight `3`. -/
noncomputable def speciesBarD (i : Fin 3) : h.Species (ConjModule DownSinglet) :=
  ⟨LocalGaugeData.actionConj DownSinglet.gaugeAlgebraAction, h.bard i, 3,
    fun p μ ψ => h.A_comm_bard p μ ψ i, h.massWeight_bard i⟩

/-- The up-type quarks of generation `i`, of mass weight `3`. -/
noncomputable def speciesU (i : Fin 3) : h.Species UpSinglet :=
  ⟨UpSinglet.gaugeAlgebraAction, h.u i, 3, fun p μ ψ => h.A_comm_u p μ ψ i, h.massWeight_u i⟩

/-- The conjugate up-type quarks of generation `i`, of mass weight `3`. -/
noncomputable def speciesBarU (i : Fin 3) : h.Species (ConjModule UpSinglet) :=
  ⟨LocalGaugeData.actionConj UpSinglet.gaugeAlgebraAction, h.baru i, 3,
    fun p μ ψ => h.A_comm_baru p μ ψ i, h.massWeight_baru i⟩

/-- The quark doublets of generation `i`, of mass weight `3`. -/
noncomputable def speciesQ (i : Fin 3) : h.Species QuarkDoublet :=
  ⟨QuarkDoublet.gaugeAlgebraAction, h.Q i, 3, fun p μ ψ => h.A_comm_Q p μ ψ i, h.massWeight_Q i⟩

/-- The conjugate quark doublets of generation `i`, of mass weight `3`. -/
noncomputable def speciesBarQ (i : Fin 3) : h.Species (ConjModule QuarkDoublet) :=
  ⟨LocalGaugeData.actionConj QuarkDoublet.gaugeAlgebraAction, h.barQ i, 3,
    fun p μ ψ => h.A_comm_barQ p μ ψ i, h.massWeight_barQ i⟩

/-- The lepton doublets of generation `i`, of mass weight `3`. -/
noncomputable def speciesL (i : Fin 3) : h.Species LeptonDoublet :=
  ⟨LeptonDoublet.gaugeAlgebraAction, h.L i, 3, fun p μ ψ => h.A_comm_L p μ ψ i, h.massWeight_L i⟩

/-- The conjugate lepton doublets of generation `i`, of mass weight `3`. -/
noncomputable def speciesBarL (i : Fin 3) : h.Species (ConjModule LeptonDoublet) :=
  ⟨LocalGaugeData.actionConj LeptonDoublet.gaugeAlgebraAction, h.barL i, 3,
    fun p μ ψ => h.A_comm_barL p μ ψ i, h.massWeight_barL i⟩

/-- The lepton singlets of generation `i`, of mass weight `3`. -/
noncomputable def speciesE (i : Fin 3) : h.Species LeptonSinglet :=
  ⟨LeptonSinglet.gaugeAlgebraAction, h.e i, 3, fun p μ ψ => h.A_comm_e p μ ψ i, h.massWeight_e i⟩

/-- The conjugate lepton singlets of generation `i`, of mass weight `3`. -/
noncomputable def speciesBarE (i : Fin 3) : h.Species (ConjModule LeptonSinglet) :=
  ⟨LocalGaugeData.actionConj LeptonSinglet.gaugeAlgebraAction, h.bare i, 3,
    fun p μ ψ => h.A_comm_bare p μ ψ i, h.massWeight_bare i⟩

/-- A property of every symbol of every matter tower is proved species by species: each
  matter tower is the tower of one of the twelve species. -/
lemma matterTowers_induction_species (P : B → Prop) {b : B} (hb : b ∈ h.matterTowers)
    (hS : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (S : h.Species V)
      (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V), P (S.tower l φ)) : P b :=
  h.matterTowers_induction P hb (hS h.speciesH) (hS h.speciesBarH) (fun i => hS (h.speciesD i))
    (fun i => hS (h.speciesBarD i)) (fun i => hS (h.speciesU i)) (fun i => hS (h.speciesBarU i))
    (fun i => hS (h.speciesQ i)) (fun i => hS (h.speciesBarQ i)) (fun i => hS (h.speciesL i))
    (fun i => hS (h.speciesBarL i)) (fun i => hS (h.speciesE i)) (fun i => hS (h.speciesBarE i))

/-- A property of every covariant generator is proved for the field-strength tower and
  for the matter towers. -/
lemma covGenerators_cases (P : B → Prop) {b : B} (hb : b ∈ h.covGenerators)
    (hF : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℝ GaugeAlgebra), P (h.covF l μ ν φ))
    (hM : ∀ b ∈ h.matterTowers, P b) : P b := by
  rw [covGenerators, Set.union_assoc] at hb
  rcases hb with hb | hb
  · simp only [Set.mem_iUnion, Set.mem_range] at hb
    obtain ⟨n, l, μ, ν, φ, rfl⟩ := hb
    exact hF n l μ ν φ
  · exact hM b hb

/-!

## C. Pure gauge jets fix the covariant algebra

Section M of `AlgebraRealization.CovariantDeriv` shows that a gauge jet with trivial
base-point value fixes every covariant generator. The jet action is multiplicative, so it
fixes the whole algebra those generators span.

-/

include h in
/-- Gauge jets fix the scalars: the action is multiplicative, hence unital, and
  complex-linear. -/
lemma repJet_algebraMap (U : JetGaugeGroupI) (c : ℂ) :
    repJet U (algebraMap ℂ B c) = algebraMap ℂ B c := by
  have hone := h.gaugeRealization.gauge_mul U (repJet U⁻¹ 1) 1
  rw [mul_one, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repJet,
    Module.End.one_apply, one_mul] at hone
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ← hone]

/-- Pure gauge jets fix the covariant generators: the thirteen cases are section L of
  `AlgebraRealization.CovariantDeriv`. -/
lemma repJet_eq_of_mem_covGenerators_of_mem_truncationKer_zero
    (U : localGaugeData.truncationKer 0) {x : B} (hx : x ∈ h.covGenerators) :
    repJet U.1 x = x :=
  h.covGenerators_cases (fun x => repJet U.1 x = x) hx
    (fun _ _ μ ν φ => h.repJet_covDerivFieldStrength_of_mem_truncationKer_zero U _ μ ν φ)
    fun _ hb => h.matterTowers_induction (fun x => repJet U.1 x = x) hb
      (fun _ l φ => h.repJet_covDerivH_of_mem_truncationKer_zero l U φ)
      (fun _ l φ => h.repJet_covDerivBarH_of_mem_truncationKer_zero l U φ)
      (fun i _ l φ => h.repJet_covDerivD_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivBarD_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivU_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivBarU_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivQ_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivBarQ_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivL_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivBarL_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivE_of_mem_truncationKer_zero i l U φ)
      (fun i _ l φ => h.repJet_covDerivBarE_of_mem_truncationKer_zero i l U φ)

/-- Pure gauge jets fix the covariant algebra pointwise: they fix its generators, and
  the jet action is an algebra map. -/
lemma repJet_eq_of_mem_covAlgebra_of_mem_truncationKer_zero
    (U : localGaugeData.truncationKer 0) {x : B} (hx : x ∈ h.covAlgebra) :
    repJet U.1 x = x := by
  induction hx using Algebra.adjoin_induction with
  | mem b hb => exact h.repJet_eq_of_mem_covGenerators_of_mem_truncationKer_zero U hb
  | algebraMap c => exact h.repJet_algebraMap U.1 c
  | add a b _ _ iha ihb => rw [map_add, iha, ihb]
  | mul a b _ _ iha ihb => rw [h.gaugeRealization.gauge_mul, iha, ihb]

/-!

## D. The reduction theorem

Every gauge jet splits as a pure jet times a constant jet. On the covariant algebra the
pure part acts trivially, so only the constant part — the global gauge group — is left.
In the other direction the classification `AlgebraRealization.invariant_mem_adjoin_covDeriv`
of `AlgebraRealization.CovFieldAlgebra.Basic` puts every jet-invariant of the field algebra
inside the covariant algebra. Together: on the field algebra, jet invariance is membership
of the covariant algebra plus global invariance.

-/

/-- The reduction of jet gauge invariance to global gauge invariance: an element of the
  field algebra is invariant under the whole jet gauge group exactly when it lies in
  the covariant algebra and is invariant under the global gauge group. -/
theorem forall_repJet_eq_iff {x : B} (hx : x ∈ h.fieldAlgebra) :
    (∀ U : JetGaugeGroupI, repJet U x = x) ↔
      x ∈ h.covAlgebra ∧ ∀ g : GaugeGroupI, repGlobal repJet g x = x := by
  refine ⟨fun hinv => ⟨h.invariant_mem_adjoin_covDeriv hx hinv, fun g => hinv _⟩, ?_⟩
  rintro ⟨hmem, hglob⟩ U
  rw [localGaugeData.eq_truncationProjZero_mul_ofConstant U, map_mul, Module.End.mul_apply]
  exact (congrArg (repJet (localGaugeData.truncationProjZero U).1) (hglob U.eval)).trans
    (h.repJet_eq_of_mem_covAlgebra_of_mem_truncationKer_zero _ hmem)

/-- The reduction theorem in the form used for Lagrangians: on the field algebra, invariance
  under the jet gauge group and the Lorentz group is membership of the covariant algebra
  with invariance under the global gauge group and the Lorentz group. -/
theorem forall_repJet_and_repLorentz_eq_iff {x : B} (hx : x ∈ h.fieldAlgebra) :
    ((∀ U : JetGaugeGroupI, repJet U x = x) ∧ ∀ Λ : SL(2,ℂ), repLorentz Λ x = x) ↔
      (x ∈ h.covAlgebra ∧ (∀ g : GaugeGroupI, repGlobal repJet g x = x) ∧
        ∀ Λ : SL(2,ℂ), repLorentz Λ x = x) := by
  rw [h.forall_repJet_eq_iff hx, and_assoc]

/-!

## E. The covariant generators are globally equivariant

Section L of `AlgebraRealization.CovariantDeriv` shows that a gauge jet acts on a covariant
tower through the base-point Taylor coefficient of its representation alone. Evaluated on
a constant jet, that coefficient is the corresponding action of the global gauge group,
so each covariant tower is equivariant for `repGlobal` in the (contragredient of the)
global representation of its species. These are exactly the `repGauge_*` obligations of
`IsGaugeSector`, `HiggsAlgebraCovRealization` and `IsFermionSector`: `repGlobal_covF` for the
field strength, and `repGlobal_covDerivH`, `repGlobal_covDerivD` and their companions for the
twelve matter towers, each an instance of `repGlobal_of_repJet` or of its conjugate form.

-/

/-- The zeroth Taylor coefficient of a jet representation at a constant jet is the
  underlying action of the global gauge group. -/
lemma repCoeff_zero_ofConstant {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repG : Representation ℂ GaugeGroupI V} {g : GaugeGroupI}
    (hg : rep (JetGaugeGroupI.ofConstant g) = TensorProduct.map LinearMap.id (repG g)) :
    GaugeAlgebraRealization.repCoeff rep (JetGaugeGroupI.ofConstant g) 0 = repG g := by
  refine LinearMap.ext fun v => ?_
  simp only [GaugeAlgebraRealization.repCoeff, LinearMap.coe_comp, Function.comp_apply,
    jetIteratedDeriv_zero, LinearMap.id_coe, id_eq, jetOfConstant_apply, hg,
    TensorProduct.map_tmul, LinearMap.id_apply, jetEval_tmul, map_one, one_smul]

/-- A tower that transforms through the base-point dual coefficient of a gauge jet is
  equivariant for the global gauge group, in the contragredient of the global
  representation. -/
lemma repGlobal_of_repJet {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repG : Representation ℂ GaugeGroupI V} {T : Module.Dual ℂ V →ₗ[ℂ] B}
    (hT : ∀ (U : JetGaugeGroupI) (φ : Module.Dual ℂ V),
      repJet U (T φ) = T (GaugeAlgebraRealization.repDualCoeff rep U⁻¹ 0 φ))
    (hg : ∀ g : GaugeGroupI,
      rep (JetGaugeGroupI.ofConstant g) = TensorProduct.map LinearMap.id (repG g))
    (g : GaugeGroupI) (φ : Module.Dual ℂ V) :
    repGlobal repJet g (T φ) = T (repG.dual g φ) := by
  rw [repGlobal_apply, hT, ← map_inv JetGaugeGroupI.ofConstant,
    GaugeAlgebraRealization.repDualCoeff,
    repCoeff_zero_ofConstant (hg g⁻¹)]
  rfl

/-- The conjugate form of `repGlobal_of_repJet`: a tower transforming through the dual
  coefficient of the conjugate representation is equivariant in its conjugate contragredient. -/
lemma repGlobal_of_repJet_conj {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repG : Representation ℂ GaugeGroupI V} {T : Module.Dual ℂ (ConjModule V) →ₗ[ℂ] B}
    (hT : ∀ (U : JetGaugeGroupI) (φ : Module.Dual ℂ (ConjModule V)), repJet U (T φ) =
      T (GaugeAlgebraRealization.repDualCoeff (JetComponentSpace.repConj rep) U⁻¹ 0 φ))
    (hg : ∀ g : GaugeGroupI,
      rep (JetGaugeGroupI.ofConstant g) = TensorProduct.map LinearMap.id (repG g))
    (g : GaugeGroupI) (φ : Module.Dual ℂ (ConjModule V)) :
    repGlobal repJet g (T φ) = T (repG.conj.dual g φ) := by
  rw [repGlobal_apply, hT, ← map_inv JetGaugeGroupI.ofConstant,
    GaugeAlgebraRealization.repDualCoeff,
    LocalGaugeData.repCoeff_repConj, repCoeff_zero_ofConstant (hg g⁻¹)]
  rfl

/-- At an inverse constant jet the dual adjoint coefficient is the contragredient
  adjoint action of the global gauge group. -/
lemma localGaugeData.adjointDualCoeff_zero_ofConstant_inv (g : GaugeGroupI) :
    localGaugeData.adjointDualCoeff (JetGaugeGroupI.ofConstant g)⁻¹ 0 =
      (GaugeAlgebra.adjointMap g⁻¹).dualMap := by
  rw [localGaugeData.adjointDualCoeff_zero, map_inv, localGaugeData_eval,
    JetGaugeGroupI.eval_ofConstant]
  rfl

section

variable (g : GaugeGroupI) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))

/-- The field-strength tower is equivariant for the global gauge group, in the
  contragredient adjoint representation. -/
lemma repGlobal_covF (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repGlobal repJet g (h.covF l μ ν φ) =
      h.covF l μ ν ((GaugeAlgebra.adjointMap g⁻¹).dualMap φ) := by
  rw [repGlobal_apply, ← localGaugeData.adjointDualCoeff_zero_ofConstant_inv]
  exact h.repJet_covDerivFieldStrength (JetGaugeGroupI.ofConstant g) (List.ofFn l) μ ν φ

lemma repGlobal_covDerivH (φ : Module.Dual ℂ HiggsVec) :
    repGlobal repJet g (h.covDerivH l φ) = h.covDerivH l (HiggsVec.repGaugeGroupI.dual g φ) :=
  repGlobal_of_repJet (h.repJet_covDerivH l) HiggsVec.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivBarH (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    repGlobal repJet g (h.covDerivBarH l φ) =
      h.covDerivBarH l (HiggsVec.repGaugeGroupI.conj.dual g φ) :=
  repGlobal_of_repJet_conj (h.repJet_covDerivBarH l) HiggsVec.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivD (φ : Module.Dual ℂ DownSinglet) :
    repGlobal repJet g (h.covDerivD i l φ) =
      h.covDerivD i l (DownSinglet.repGaugeGroupI.dual g φ) :=
  repGlobal_of_repJet (h.repJet_covDerivD i l) DownSinglet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivBarD (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    repGlobal repJet g (h.covDerivBarD i l φ) =
      h.covDerivBarD i l (DownSinglet.repGaugeGroupI.conj.dual g φ) :=
  repGlobal_of_repJet_conj (h.repJet_covDerivBarD i l) DownSinglet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivU (φ : Module.Dual ℂ UpSinglet) :
    repGlobal repJet g (h.covDerivU i l φ) = h.covDerivU i l (UpSinglet.repGaugeGroupI.dual g φ) :=
  repGlobal_of_repJet (h.repJet_covDerivU i l) UpSinglet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivBarU (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    repGlobal repJet g (h.covDerivBarU i l φ) =
      h.covDerivBarU i l (UpSinglet.repGaugeGroupI.conj.dual g φ) :=
  repGlobal_of_repJet_conj (h.repJet_covDerivBarU i l) UpSinglet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivQ (φ : Module.Dual ℂ QuarkDoublet) :
    repGlobal repJet g (h.covDerivQ i l φ) =
      h.covDerivQ i l (QuarkDoublet.repGaugeGroupI.dual g φ) :=
  repGlobal_of_repJet (h.repJet_covDerivQ i l) QuarkDoublet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivBarQ (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    repGlobal repJet g (h.covDerivBarQ i l φ) =
      h.covDerivBarQ i l (QuarkDoublet.repGaugeGroupI.conj.dual g φ) :=
  repGlobal_of_repJet_conj (h.repJet_covDerivBarQ i l) QuarkDoublet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivL (φ : Module.Dual ℂ LeptonDoublet) :
    repGlobal repJet g (h.covDerivL i l φ) =
      h.covDerivL i l (LeptonDoublet.repGaugeGroupI.dual g φ) :=
  repGlobal_of_repJet (h.repJet_covDerivL i l) LeptonDoublet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivBarL (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    repGlobal repJet g (h.covDerivBarL i l φ) =
      h.covDerivBarL i l (LeptonDoublet.repGaugeGroupI.conj.dual g φ) :=
  repGlobal_of_repJet_conj (h.repJet_covDerivBarL i l)
    LeptonDoublet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivE (φ : Module.Dual ℂ LeptonSinglet) :
    repGlobal repJet g (h.covDerivE i l φ) =
      h.covDerivE i l (LeptonSinglet.repGaugeGroupI.dual g φ) :=
  repGlobal_of_repJet (h.repJet_covDerivE i l) LeptonSinglet.repJetGaugeGroupI_ofConstant g φ

lemma repGlobal_covDerivBarE (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    repGlobal repJet g (h.covDerivBarE i l φ) =
      h.covDerivBarE i l (LeptonSinglet.repGaugeGroupI.conj.dual g φ) :=
  repGlobal_of_repJet_conj (h.repJet_covDerivBarE i l)
    LeptonSinglet.repJetGaugeGroupI_ofConstant g φ

end

/-!

## F. The field-strength tower is central in the covariant algebra

The gauge field is bosonic, so its symbols commute with each other and with every matter
symbol. Every covariant generator is a polynomial in those symbols, so the covariant
generators all commute with the gauge-field symbols; and the field-strength tower, being
itself a polynomial in the gauge-field symbols, therefore commutes with the whole covariant
algebra. This discharges the `F_comm_F` obligation of `IsGaugeSector` and the cross-sector
`F_comm_*` rules at once.

-/

/-- The covariant derivatives of the field strength are polynomials in the gauge-field
  symbols. -/
lemma covF_mem_adjoin_gaugeSymbols {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    h.covF l μ ν φ ∈ Algebra.adjoin ℂ {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
      (ρ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra), b = h.A s ρ ψ} :=
  GaugeAlgebraRealization.iteratedCovDerivAdjoint_fieldStrength_mem_adjoin_symbols
    (List.ofFn l) μ ν φ

/-- The field-strength tower commutes with anything the gauge-field symbols commute
  with. -/
lemma covF_comm_of_comm_A {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) {y : B}
    (hy : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3) (ψ' : Module.Dual ℝ GaugeAlgebra),
      Commute (h.A p ρ ψ') y) : Commute (h.covF l μ ν ψ) y := by
  refine GaugeAlgebraRealization.commute_of_mem_adjoin ?_ (h.covF_mem_adjoin_gaugeSymbols l μ ν ψ)
  rintro x ⟨p, ρ, ψ', rfl⟩
  exact hy p ρ ψ'

/-- Every covariant generator commutes with every gauge-field symbol: the covariant towers
  are polynomials in the gauge-field and matter symbols, and the gauge field is bosonic. -/
lemma commute_gaugeSymbol_of_mem_covGenerators (p : Multiset (Fin 1 ⊕ Fin 3))
    (ρ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra) {y : B}
    (hy : y ∈ h.covGenerators) : Commute y (h.A p ρ ψ) :=
  h.covGenerators_cases (fun y => Commute y (h.A p ρ ψ)) hy
    (fun _ l μ ν φ => h.covF_comm_of_comm_A l μ ν φ fun s' ρ' ψ' => h.A_comm_A s' p ρ' ρ ψ' ψ)
    fun _ hb => h.matterTowers_induction_species (fun y => Commute y (h.A p ρ ψ)) hb
      fun S _ l φ => S.comm_A l φ p ρ ψ

/-- The field-strength tower is central in the covariant algebra: it commutes with every
  covariant generator, and commutation extends to the algebra they generate. -/
lemma covF_commute_of_mem_covAlgebra {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra) {x : B}
    (hx : x ∈ h.covAlgebra) : Commute (h.covF l μ ν ψ) x :=
  (GaugeAlgebraRealization.commute_of_mem_adjoin (fun _ hb =>
    (h.covF_comm_of_comm_A l μ ν ψ fun p ρ ψ' =>
    (h.commute_gaugeSymbol_of_mem_covGenerators p ρ ψ' hb).symm).symm) hx).symm

/-!

## G. Sums of products: the two family pairings

Both correction terms of a covariant derivative — the action pairing `act` on a matter
family and the gauge-algebra bracket on an adjoint family — are, after expansion in a basis,
finite sums of scalar multiples of products of the two families' components. So each lands
in any submodule of `B` containing all those products, which is all sections H and I use.

-/

/-- The action pairing of two families lands in any submodule containing the products of
  their components: expanded in bases it is a finite sum of scalar multiples of them. -/
lemma actionFam_apply_mem_submodule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V} {M : Submodule ℂ B}
    {f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} {g : Module.Dual ℂ V →ₗ[ℂ] B}
    (hfg : ∀ ψ χ, f ψ * g χ ∈ M) (φ : Module.Dual ℂ V) :
    GaugeAlgebraRealization.actionFam act f g φ ∈ M := by
  rw [GaugeAlgebraRealization.actionFam,
    GaugeAlgebraRealization.dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) f,
    GaugeAlgebraRealization.dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) g]
  simp only [map_sum, LinearMap.sum_apply, GaugeAlgebraRealization.tensorAction_tmul,
    GaugeAlgebraRealization.dualPairEquivC_tmul]
  exact sum_mem fun i _ => sum_mem fun j _ => M.smul_mem _ (hfg _ _)

/-- The bracket pairing of two adjoint families lands in any submodule containing the
  products of their components: it is the sum of the structure constants against them. -/
lemma bracketFam_apply_mem_submodule {M : Submodule ℂ B}
    {f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    (hfg : ∀ ψ χ, f ψ * g χ ∈ M) (φ : Module.Dual ℝ GaugeAlgebra) :
    GaugeAlgebraRealization.bracketFam f g φ ∈ M := by
  rw [GaugeAlgebraRealization.bracketFam_apply_eq_sum]
  refine sum_mem fun j _ => sum_mem fun k _ => ?_
  rw [← algebraMap_smul ℂ]
  exact M.smul_mem _ (hfg _ _)

/-!

## H. The mass weights of the covariant towers

`massWeightPoly` is pinned down on the bare symbols only, while a covariant tower is a sum
of products of them. The weight-`w` eigenspace of `massWeightPoly` is a submodule, and the
product of a weight-`w` and a weight-`w'` element has weight `w + w'`; the recursion defining
a covariant derivative adds one derivative on one branch and one gauge-field factor on the
other, which cost the same two units of weight. Both towers are therefore eigenvectors, of
the weights `IsGaugeSector`, `HiggsAlgebraCovRealization` and `IsFermionSector` demand.

-/

/-- The weight-`w` part of the algebra: the elements on which the mass-weight algebra
  map is the monomial `X ^ w`. -/
noncomputable def massWeightEigenspace (massWeightPoly : B →ₐ[ℂ] Polynomial B) (w : ℕ) :
    Submodule ℂ B :=
  LinearMap.ker (massWeightPoly.toLinearMap
    - (Polynomial.monomial w : B →ₗ[B] Polynomial B).restrictScalars ℂ)

/-- Membership of the weight-`w` part is the eigenvector equation itself. -/
lemma mem_massWeightEigenspace_iff {w : ℕ} {b : B} :
    b ∈ massWeightEigenspace massWeightPoly w ↔
      massWeightPoly b = Polynomial.monomial w b := by
  rw [massWeightEigenspace, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars,
    sub_eq_zero]

/-- The mass weight is additive on products: `massWeightPoly` is an algebra map and
  monomials multiply by adding their degrees. -/
lemma mul_mem_massWeightEigenspace {w w' : ℕ} {b b' : B}
    (hb : b ∈ massWeightEigenspace massWeightPoly w)
    (hb' : b' ∈ massWeightEigenspace massWeightPoly w') :
    b * b' ∈ massWeightEigenspace massWeightPoly (w + w') := by
  rw [mem_massWeightEigenspace_iff] at hb hb' ⊢
  rw [map_mul, hb, hb', Polynomial.monomial_mul_monomial]

/-- A gauge-field symbol with `|p|` derivatives has mass weight `2 * (1 + |p|)`. -/
lemma A_mem_massWeightEigenspace (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) :
    h.A p μ ψ ∈ massWeightEigenspace massWeightPoly (2 * (1 + Multiset.card p)) :=
  mem_massWeightEigenspace_iff.mpr (h.massWeight_A p μ ψ)

namespace Species

variable {h} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (S : h.Species V)

/-- The mass weight of a matter covariant tower: the `n`-fold covariant derivative of the
  family at the derivative multiset `s` has weight `c + 2 * n + 2 * |s|`. Each covariant
  derivative costs two units, whether it lands on the derivative index or brings down a
  gauge-field factor. -/
lemma covDerivIter_mem_massWeightEigenspace {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    GaugeAlgebraRealization.covDerivIter h.A S.act S.F n l s φ ∈
      massWeightEigenspace massWeightPoly (S.c + 2 * n + 2 * Multiset.card s) := by
  induction n generalizing s φ with
  | zero =>
      rw [GaugeAlgebraRealization.covDerivIter_zero]
      simpa using mem_massWeightEigenspace_iff.mpr (S.massWeight s φ)
  | succ n ih =>
      rw [GaugeAlgebraRealization.covDerivIter_succ, GaugeAlgebraRealization.covDerivAction_apply]
      refine add_mem ?_ ?_
      · have hstep := ih (fun i => l i.succ) (l 0 ::ₘ s) φ
        rwa [Multiset.card_cons, show S.c + 2 * n + 2 * (Multiset.card s + 1)
            = S.c + 2 * (n + 1) + 2 * Multiset.card s by ring] at hstep
      · rw [GaugeAlgebraRealization.actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
        refine multiset_sum_mem _ fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
        have hle : Multiset.card p.1 + Multiset.card p.2 = Multiset.card s := by
          rw [← Multiset.card_add, Multiset.mem_antidiagonal.mp hp]
        simp only [Function.comp_apply]
        refine actionFam_apply_mem_submodule (fun ψ χ => ?_) _
        have hmul := mul_mem_massWeightEigenspace (h.A_mem_massWeightEigenspace p.1 (l 0) ψ)
          (ih (fun i => l i.succ) p.2 χ)
        rwa [show 2 * (1 + Multiset.card p.1) + (S.c + 2 * n + 2 * Multiset.card p.2)
          = S.c + 2 * (n + 1) + 2 * Multiset.card s by omega] at hmul

/-- The mass weight of the tower of a species is `c + 2 * n`: the form in which the
  sector structures ask for it. -/
lemma massWeight_tower {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    massWeightPoly (S.tower l φ) = Polynomial.monomial (S.c + 2 * n) (S.tower l φ) := by
  have hmem := S.covDerivIter_mem_massWeightEigenspace l 0 φ
  rwa [Multiset.card_zero, mul_zero, add_zero, mem_massWeightEigenspace_iff] at hmem

end Species

/-- The mass weight of the bare field strength: two gauge-field symbols, or one with an
  extra derivative, in either case weight `4 + 2 * |s|`. -/
lemma fieldStrength_mem_massWeightEigenspace (μ ν : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    GaugeAlgebraRealization.fieldStrength h.A μ ν s φ ∈
      massWeightEigenspace massWeightPoly (4 + 2 * Multiset.card s) := by
  rw [GaugeAlgebraRealization.fieldStrength_apply]
  refine add_mem (sub_mem ?_ ?_) ?_
  · have hstep := h.A_mem_massWeightEigenspace (μ ::ₘ s) ν φ
    rwa [Multiset.card_cons,
      show 2 * (1 + (Multiset.card s + 1)) = 4 + 2 * Multiset.card s by ring] at hstep
  · have hstep := h.A_mem_massWeightEigenspace (ν ::ₘ s) μ φ
    rwa [Multiset.card_cons,
      show 2 * (1 + (Multiset.card s + 1)) = 4 + 2 * Multiset.card s by ring] at hstep
  · rw [GaugeAlgebraRealization.commutatorFam, Multiset.sum_linearMap_apply, Multiset.map_map]
    refine multiset_sum_mem _ fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    have hle : Multiset.card p.1 + Multiset.card p.2 = Multiset.card s := by
      rw [← Multiset.card_add, Multiset.mem_antidiagonal.mp hp]
    simp only [Function.comp_apply]
    refine bracketFam_apply_mem_submodule (fun ψ χ => ?_) _
    have hmul := mul_mem_massWeightEigenspace (h.A_mem_massWeightEigenspace p.1 μ ψ)
      (h.A_mem_massWeightEigenspace p.2 ν χ)
    rwa [show 2 * (1 + Multiset.card p.1) + 2 * (1 + Multiset.card p.2)
      = 4 + 2 * Multiset.card s by omega] at hmul

/-- The mass weight of an adjoint covariant tower: the adjoint analogue of
  `Species.covDerivIter_mem_massWeightEigenspace`, with the bracket pairing in place of
  the action pairing. -/
lemma iteratedCovDerivAdjoint_mem_massWeightEigenspace (c : ℕ)
    (G : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (hG : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℝ GaugeAlgebra),
      G t χ ∈ massWeightEigenspace massWeightPoly (c + 2 * Multiset.card t))
    (l : List (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra) :
    GaugeAlgebraRealization.iteratedCovDerivAdjoint h.A l G s φ ∈
      massWeightEigenspace massWeightPoly (c + 2 * l.length + 2 * Multiset.card s) := by
  induction l generalizing s φ with
  | nil =>
      rw [show GaugeAlgebraRealization.iteratedCovDerivAdjoint h.A ([] : List (Fin 1 ⊕ Fin 3)) G = G
        from rfl]
      simpa using hG s φ
  | cons ρ l ih =>
      rw [show GaugeAlgebraRealization.iteratedCovDerivAdjoint h.A (ρ :: l) G
          = GaugeAlgebraRealization.covDerivAdjoint h.A
              (GaugeAlgebraRealization.iteratedCovDerivAdjoint h.A l G) ρ
        from rfl, GaugeAlgebraRealization.covDerivAdjoint_apply, List.length_cons]
      refine add_mem ?_ ?_
      · have hstep := ih (ρ ::ₘ s) φ
        rwa [Multiset.card_cons, show c + 2 * l.length + 2 * (Multiset.card s + 1)
            = c + 2 * (l.length + 1) + 2 * Multiset.card s by ring] at hstep
      · rw [GaugeAlgebraRealization.bracketFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
        refine multiset_sum_mem _ fun x hx => ?_
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
        have hle : Multiset.card p.1 + Multiset.card p.2 = Multiset.card s := by
          rw [← Multiset.card_add, Multiset.mem_antidiagonal.mp hp]
        simp only [Function.comp_apply]
        refine bracketFam_apply_mem_submodule (fun ψ χ => ?_) _
        have hmul := mul_mem_massWeightEigenspace (h.A_mem_massWeightEigenspace p.1 ρ ψ)
          (ih p.2 χ)
        rwa [show 2 * (1 + Multiset.card p.1) + (c + 2 * l.length + 2 * Multiset.card p.2)
          = c + 2 * (l.length + 1) + 2 * Multiset.card s by omega] at hmul

/-!

### H.1. The mass weights, species by species

The two towers of section H, evaluated at the empty derivative multiset, give the
mass weights that `IsGaugeSector`, `HiggsAlgebraCovRealization` and `IsFermionSector`
demand: `2 * (2 + n)` for the field strength (`massWeight_covF`), `2 * (1 + n)` for the
Higgs (`massWeight_covDerivH`) and `3 + 2 * n` for the fermions (`massWeight_covDerivD`
and its companions), the matter cases each being `Species.massWeight_tower` at the
corresponding species.

-/

section

variable (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))

/-- The mass weight of the field-strength tower is `2 * (2 + n)`: mass dimension `2 + n`. -/
lemma massWeight_covF (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    massWeightPoly (h.covF l μ ν φ) = Polynomial.monomial (2 * (2 + n)) (h.covF l μ ν φ) := by
  have hmem := h.iteratedCovDerivAdjoint_mem_massWeightEigenspace 4 _
    (h.fieldStrength_mem_massWeightEigenspace μ ν) (List.ofFn l) 0 φ
  rwa [List.length_ofFn, Multiset.card_zero, mul_zero, add_zero,
    show 4 + 2 * n = 2 * (2 + n) by ring, mem_massWeightEigenspace_iff] at hmem

lemma massWeight_covDerivH (φ : Module.Dual ℂ HiggsVec) :
    massWeightPoly (h.covDerivH l φ) = Polynomial.monomial (2 * (1 + n)) (h.covDerivH l φ) := by
  rw [mul_add, mul_one]
  exact h.speciesH.massWeight_tower l φ

lemma massWeight_covDerivBarH (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    massWeightPoly (h.covDerivBarH l φ) =
      Polynomial.monomial (2 * (1 + n)) (h.covDerivBarH l φ) := by
  rw [mul_add, mul_one]
  exact h.speciesBarH.massWeight_tower l φ

lemma massWeight_covDerivD (φ : Module.Dual ℂ DownSinglet) :
    massWeightPoly (h.covDerivD i l φ) = Polynomial.monomial (3 + 2 * n) (h.covDerivD i l φ) :=
  (h.speciesD i).massWeight_tower l φ

lemma massWeight_covDerivBarD (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    massWeightPoly (h.covDerivBarD i l φ) =
      Polynomial.monomial (3 + 2 * n) (h.covDerivBarD i l φ) :=
  (h.speciesBarD i).massWeight_tower l φ

lemma massWeight_covDerivU (φ : Module.Dual ℂ UpSinglet) :
    massWeightPoly (h.covDerivU i l φ) = Polynomial.monomial (3 + 2 * n) (h.covDerivU i l φ) :=
  (h.speciesU i).massWeight_tower l φ

lemma massWeight_covDerivBarU (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    massWeightPoly (h.covDerivBarU i l φ) =
      Polynomial.monomial (3 + 2 * n) (h.covDerivBarU i l φ) :=
  (h.speciesBarU i).massWeight_tower l φ

lemma massWeight_covDerivQ (φ : Module.Dual ℂ QuarkDoublet) :
    massWeightPoly (h.covDerivQ i l φ) = Polynomial.monomial (3 + 2 * n) (h.covDerivQ i l φ) :=
  (h.speciesQ i).massWeight_tower l φ

lemma massWeight_covDerivBarQ (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    massWeightPoly (h.covDerivBarQ i l φ) =
      Polynomial.monomial (3 + 2 * n) (h.covDerivBarQ i l φ) :=
  (h.speciesBarQ i).massWeight_tower l φ

lemma massWeight_covDerivL (φ : Module.Dual ℂ LeptonDoublet) :
    massWeightPoly (h.covDerivL i l φ) = Polynomial.monomial (3 + 2 * n) (h.covDerivL i l φ) :=
  (h.speciesL i).massWeight_tower l φ

lemma massWeight_covDerivBarL (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    massWeightPoly (h.covDerivBarL i l φ) =
      Polynomial.monomial (3 + 2 * n) (h.covDerivBarL i l φ) :=
  (h.speciesBarL i).massWeight_tower l φ

lemma massWeight_covDerivE (φ : Module.Dual ℂ LeptonSinglet) :
    massWeightPoly (h.covDerivE i l φ) = Polynomial.monomial (3 + 2 * n) (h.covDerivE i l φ) :=
  (h.speciesE i).massWeight_tower l φ

lemma massWeight_covDerivBarE (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    massWeightPoly (h.covDerivBarE i l φ) =
      Polynomial.monomial (3 + 2 * n) (h.covDerivBarE i l φ) :=
  (h.speciesBarE i).massWeight_tower l φ

end

/-!

## I. The statistics of the covariant towers

Every covariant tower is a polynomial in the gauge-field symbols and the bare symbols of
its own species, and each of its terms carries exactly one of the latter. So the statistics
of a pair of towers is decided by the statistics of the pair of bare families: two towers
whose bare symbols commute with the gauge field and with each other commute, and two whose
bare symbols commute with the gauge field and anticommute with each other anticommute. The
anticommutation is checked term by term, through the submodule of elements anticommuting
with a fixed one.

-/

/-- The elements of the algebra anticommuting with a fixed element. It is a submodule,
  which is what lets the anticommutation of a tower be checked term by term. -/
def anticommuteSubmodule (x : B) : Submodule ℂ B where
  carrier := {y : B | x * y = -(y * x)}
  add_mem' {a b} (ha : x * a = -(a * x)) (hb : x * b = -(b * x)) :=
    show x * (a + b) = -((a + b) * x) by rw [mul_add, add_mul, ha, hb, neg_add]
  zero_mem' := by simp
  smul_mem' c y (hy : x * y = -(y * x)) :=
    show x * (c • y) = -((c • y) * x) by rw [mul_smul_comm, hy, smul_neg, smul_mul_assoc]

/-- Membership of the anticommutant is the anticommutation relation itself. -/
lemma mem_anticommuteSubmodule_iff {x y : B} :
    y ∈ anticommuteSubmodule x ↔ x * y = -(y * x) := Iff.rfl

omit [Algebra ℂ B] in
/-- Anticommutation is symmetric in its two arguments. -/
lemma anticomm_symm {a b : B} (hab : a * b = -(b * a)) : b * a = -(a * b) := by
  rw [hab, neg_neg]

/-- Multiplying an anticommuting element on the left by a commuting one keeps it
  anticommuting. -/
lemma mul_mem_anticommuteSubmodule {x a b : B} (ha : Commute x a)
    (hb : b ∈ anticommuteSubmodule x) : a * b ∈ anticommuteSubmodule x := by
  rw [mem_anticommuteSubmodule_iff] at hb ⊢
  rw [← mul_assoc, ha.eq, mul_assoc, hb, mul_neg, mul_assoc]

namespace Species

variable {h} {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (S : h.Species V)

/-- Anything commuting with every gauge-field symbol and with every bare symbol of the
  species commutes with its tower. -/
lemma commute_tower {y : B}
    (hyA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra),
      Commute (h.A p μ ψ) y)
    (hyF : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V), Commute (S.F t χ) y)
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) : Commute (S.tower l φ) y := by
  refine GaugeAlgebraRealization.commute_of_mem_adjoin ?_
    (GaugeAlgebraRealization.covDerivIter_mem_adjoin_symbols S.act S.F n l 0 φ)
  rintro x (⟨p, μ, ψ, rfl⟩ | ⟨t, χ, rfl⟩)
  exacts [hyA p μ ψ, hyF t χ]

/-- The towers of two species whose bare families commute with each other commute. The
  hypothesis is stated in the shape of the bare laws `H_comm_d`. -/
lemma commute_tower_tower (T : h.Species W)
    (hST : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V) (t' : Multiset (Fin 1 ⊕ Fin 3))
      (χ' : Module.Dual ℂ W), Commute (S.F t χ) (T.F t' χ'))
    {n m : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V)
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ W) :
    Commute (S.tower l φ) (T.tower l' φ') :=
  S.commute_tower (fun p μ ψ => (T.comm_A l' φ' p μ ψ).symm)
    (fun t χ => (T.commute_tower (fun p μ ψ => S.A_comm p μ ψ t χ)
      (fun t' χ' => (hST t χ t' χ').symm) l' φ').symm) l φ

/-- Anything commuting with every gauge-field symbol and anticommuting with every bare
  symbol of the species anticommutes with its tower: each term of the tower is a product
  of gauge-field symbols with a single bare symbol. -/
lemma anticomm_tower {x : B}
    (hxA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ GaugeAlgebra),
      Commute x (h.A p μ ψ))
    (hxF : ∀ (t : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V), x * S.F t χ = -(S.F t χ * x))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    x * S.tower l φ = -(S.tower l φ * x) := by
  suffices key : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ V),
      GaugeAlgebraRealization.covDerivIter h.A S.act S.F n l s φ ∈ anticommuteSubmodule x
    from key n l 0 φ
  intro n
  induction n with
  | zero => exact fun l s φ => hxF s φ
  | succ n ih =>
      intro l s φ
      rw [GaugeAlgebraRealization.covDerivIter_succ, GaugeAlgebraRealization.covDerivAction_apply]
      refine add_mem (ih _ _ _) ?_
      rw [GaugeAlgebraRealization.actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map]
      refine multiset_sum_mem _ fun z hz => ?_
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hz
      simp only [Function.comp_apply]
      exact actionFam_apply_mem_submodule
        (fun ψ χ => mul_mem_anticommuteSubmodule (hxA p.1 (l 0) ψ) (ih _ p.2 χ)) _

/-- The towers of two species whose bare families anticommute with each other
  anticommute. The hypothesis is stated in the shape of the bare laws `d_anticomm_bard`. -/
lemma anticomm_tower_tower (T : h.Species W)
    (hST : ∀ (t t' : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V) (χ' : Module.Dual ℂ W),
      S.F t χ * T.F t' χ' = -(T.F t' χ' * S.F t χ))
    {n m : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V)
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ W) :
    S.tower l φ * T.tower l' φ' = -(T.tower l' φ' * S.tower l φ) :=
  anticomm_symm (S.anticomm_tower (fun p μ ψ => T.comm_A l' φ' p μ ψ)
    (fun t χ => anticomm_symm (T.anticomm_tower (fun p μ ψ => (S.A_comm p μ ψ t χ).symm)
      (fun t' χ' => hST t t' χ χ') l' φ')) l φ)

/-- The field-strength tower commutes with the tower of every species. -/
lemma covF_comm_tower {k n : ℕ} (l : Fin k → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    Commute (h.covF l μ ν ψ) (S.tower l' φ) :=
  h.covF_comm_of_comm_A l μ ν ψ fun p ρ ψ' => (S.comm_A l' φ p ρ ψ').symm

end Species

/-- Two field-strength towers commute: both are polynomials in the gauge-field symbols,
  and the gauge field is bosonic. -/
lemma covF_comm_covF {n m : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (μ ν μ' ν' : Fin 1 ⊕ Fin 3)
    (ψ ψ' : Module.Dual ℝ GaugeAlgebra) :
    Commute (h.covF l μ ν ψ) (h.covF l' μ' ν' ψ') :=
  h.covF_comm_of_comm_A l μ ν ψ fun p ρ ψ₁ =>
    (h.covF_comm_of_comm_A l' μ' ν' ψ' fun q σ ψ₂ => h.A_comm_A q p σ ρ ψ₂ ψ₁).symm

/-!

### I.1. The statistics, species by species

The field-strength tower is central; the Higgs towers are bosonic and commute with
everything; the fermion towers anticommute with one another. These are exactly the
commutation obligations of the three sector structures: `covF_comm_covX` for the
field-strength tower against the tower of the species `X`, `covH_comm_covX` and
`covBarH_comm_covX` for the two Higgs towers, and `covX_anticomm_covY` for each pair of
fermion species — each `Species.covF_comm_tower`, `Species.commute_tower_tower` or
`Species.anticomm_tower_tower` at the corresponding species, fed the bare law of the pair.

-/

section

variable {n m : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
  (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → (Fin 1 ⊕ Fin 3))

lemma covF_comm_covH (φ : Module.Dual ℂ HiggsVec) :
    Commute (h.covF l μ ν ψ) (h.covDerivH l' φ) :=
  h.speciesH.covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covBarH (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    Commute (h.covF l μ ν ψ) (h.covDerivBarH l' φ) :=
  h.speciesBarH.covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covD (φ : Module.Dual ℂ DownSinglet) :
    Commute (h.covF l μ ν ψ) (h.covDerivD i l' φ) :=
  (h.speciesD i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covBarD (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (h.covF l μ ν ψ) (h.covDerivBarD i l' φ) :=
  (h.speciesBarD i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covU (φ : Module.Dual ℂ UpSinglet) :
    Commute (h.covF l μ ν ψ) (h.covDerivU i l' φ) :=
  (h.speciesU i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covBarU (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (h.covF l μ ν ψ) (h.covDerivBarU i l' φ) :=
  (h.speciesBarU i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covQ (φ : Module.Dual ℂ QuarkDoublet) :
    Commute (h.covF l μ ν ψ) (h.covDerivQ i l' φ) :=
  (h.speciesQ i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covBarQ (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (h.covF l μ ν ψ) (h.covDerivBarQ i l' φ) :=
  (h.speciesBarQ i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covL (φ : Module.Dual ℂ LeptonDoublet) :
    Commute (h.covF l μ ν ψ) (h.covDerivL i l' φ) :=
  (h.speciesL i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covBarL (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (h.covF l μ ν ψ) (h.covDerivBarL i l' φ) :=
  (h.speciesBarL i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covE (φ : Module.Dual ℂ LeptonSinglet) :
    Commute (h.covF l μ ν ψ) (h.covDerivE i l' φ) :=
  (h.speciesE i).covF_comm_tower l μ ν ψ l' φ

lemma covF_comm_covBarE (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (h.covF l μ ν ψ) (h.covDerivBarE i l' φ) :=
  (h.speciesBarE i).covF_comm_tower l μ ν ψ l' φ

end

section

variable (i j : Fin 3) {n m : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (l' : Fin m → (Fin 1 ⊕ Fin 3))

lemma covH_comm_covH (φ φ' : Module.Dual ℂ HiggsVec) :
    Commute (h.covDerivH l φ) (h.covDerivH l' φ') :=
  h.speciesH.commute_tower_tower h.speciesH (fun t χ t' χ' => h.H_comm_H t t' χ χ') l φ l' φ'

lemma covH_comm_covBarH (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ (ConjModule HiggsVec)) :
    Commute (h.covDerivH l φ) (h.covDerivBarH l' φ') :=
  h.speciesH.commute_tower_tower h.speciesBarH (fun t χ t' χ' => h.H_comm_barH t t' χ χ') l φ l' φ'

lemma covBarH_comm_covBarH (φ φ' : Module.Dual ℂ (ConjModule HiggsVec)) :
    Commute (h.covDerivBarH l φ) (h.covDerivBarH l' φ') :=
  h.speciesBarH.commute_tower_tower h.speciesBarH
    (fun t χ t' χ' => h.barH_comm_barH t t' χ χ') l φ l' φ'

lemma covH_comm_covD (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ DownSinglet) :
    Commute (h.covDerivH l φ) (h.covDerivD i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesD i) (fun t χ => h.H_comm_d t χ i) l φ l' φ'

lemma covH_comm_covBarD (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (h.covDerivH l φ) (h.covDerivBarD i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesBarD i) (fun t χ => h.H_comm_bard t χ i) l φ l' φ'

lemma covH_comm_covU (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ UpSinglet) :
    Commute (h.covDerivH l φ) (h.covDerivU i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesU i) (fun t χ => h.H_comm_u t χ i) l φ l' φ'

lemma covH_comm_covBarU (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (h.covDerivH l φ) (h.covDerivBarU i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesBarU i) (fun t χ => h.H_comm_baru t χ i) l φ l' φ'

lemma covH_comm_covQ (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ QuarkDoublet) :
    Commute (h.covDerivH l φ) (h.covDerivQ i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesQ i) (fun t χ => h.H_comm_Q t χ i) l φ l' φ'

lemma covH_comm_covBarQ (φ : Module.Dual ℂ HiggsVec)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (h.covDerivH l φ) (h.covDerivBarQ i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesBarQ i) (fun t χ => h.H_comm_barQ t χ i) l φ l' φ'

lemma covH_comm_covL (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ LeptonDoublet) :
    Commute (h.covDerivH l φ) (h.covDerivL i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesL i) (fun t χ => h.H_comm_L t χ i) l φ l' φ'

lemma covH_comm_covBarL (φ : Module.Dual ℂ HiggsVec)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (h.covDerivH l φ) (h.covDerivBarL i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesBarL i) (fun t χ => h.H_comm_barL t χ i) l φ l' φ'

lemma covH_comm_covE (φ : Module.Dual ℂ HiggsVec) (φ' : Module.Dual ℂ LeptonSinglet) :
    Commute (h.covDerivH l φ) (h.covDerivE i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesE i) (fun t χ => h.H_comm_e t χ i) l φ l' φ'

lemma covH_comm_covBarE (φ : Module.Dual ℂ HiggsVec)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (h.covDerivH l φ) (h.covDerivBarE i l' φ') :=
  h.speciesH.commute_tower_tower (h.speciesBarE i) (fun t χ => h.H_comm_bare t χ i) l φ l' φ'

lemma covBarH_comm_covD (φ : Module.Dual ℂ (ConjModule HiggsVec)) (φ' : Module.Dual ℂ DownSinglet) :
    Commute (h.covDerivBarH l φ) (h.covDerivD i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesD i) (fun t χ => h.barH_comm_d t χ i) l φ l' φ'

lemma covBarH_comm_covBarD (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (h.covDerivBarH l φ) (h.covDerivBarD i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesBarD i) (fun t χ => h.barH_comm_bard t χ i) l φ l' φ'

lemma covBarH_comm_covU (φ : Module.Dual ℂ (ConjModule HiggsVec)) (φ' : Module.Dual ℂ UpSinglet) :
    Commute (h.covDerivBarH l φ) (h.covDerivU i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesU i) (fun t χ => h.barH_comm_u t χ i) l φ l' φ'

lemma covBarH_comm_covBarU (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (h.covDerivBarH l φ) (h.covDerivBarU i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesBarU i) (fun t χ => h.barH_comm_baru t χ i) l φ l' φ'

lemma covBarH_comm_covQ (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ QuarkDoublet) :
    Commute (h.covDerivBarH l φ) (h.covDerivQ i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesQ i) (fun t χ => h.barH_comm_Q t χ i) l φ l' φ'

lemma covBarH_comm_covBarQ (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (h.covDerivBarH l φ) (h.covDerivBarQ i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesBarQ i) (fun t χ => h.barH_comm_barQ t χ i) l φ l' φ'

lemma covBarH_comm_covL (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ LeptonDoublet) :
    Commute (h.covDerivBarH l φ) (h.covDerivL i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesL i) (fun t χ => h.barH_comm_L t χ i) l φ l' φ'

lemma covBarH_comm_covBarL (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (h.covDerivBarH l φ) (h.covDerivBarL i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesBarL i) (fun t χ => h.barH_comm_barL t χ i) l φ l' φ'

lemma covBarH_comm_covE (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ LeptonSinglet) :
    Commute (h.covDerivBarH l φ) (h.covDerivE i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesE i) (fun t χ => h.barH_comm_e t χ i) l φ l' φ'

lemma covBarH_comm_covBarE (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (h.covDerivBarH l φ) (h.covDerivBarE i l' φ') :=
  h.speciesBarH.commute_tower_tower (h.speciesBarE i) (fun t χ => h.barH_comm_bare t χ i) l φ l' φ'

lemma covD_anticomm_covD (φ φ' : Module.Dual ℂ DownSinglet) :
    h.covDerivD i l φ * h.covDerivD j l' φ' = -(h.covDerivD j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesD j) (h.d_anticomm_d i j) l φ l' φ'

lemma covD_anticomm_covBarD (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    h.covDerivD i l φ * h.covDerivBarD j l' φ' = -(h.covDerivBarD j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesBarD j) (h.d_anticomm_bard i j) l φ l' φ'

lemma covD_anticomm_covU (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ UpSinglet) :
    h.covDerivD i l φ * h.covDerivU j l' φ' = -(h.covDerivU j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesU j) (h.d_anticomm_u i j) l φ l' φ'

lemma covD_anticomm_covBarU (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    h.covDerivD i l φ * h.covDerivBarU j l' φ' = -(h.covDerivBarU j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesBarU j) (h.d_anticomm_baru i j) l φ l' φ'

lemma covD_anticomm_covQ (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ QuarkDoublet) :
    h.covDerivD i l φ * h.covDerivQ j l' φ' = -(h.covDerivQ j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesQ j) (h.d_anticomm_Q i j) l φ l' φ'

lemma covD_anticomm_covBarQ (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    h.covDerivD i l φ * h.covDerivBarQ j l' φ' = -(h.covDerivBarQ j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesBarQ j) (h.d_anticomm_barQ i j) l φ l' φ'

lemma covD_anticomm_covL (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivD i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesL j) (h.d_anticomm_L i j) l φ l' φ'

lemma covD_anticomm_covBarL (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivD i l φ * h.covDerivBarL j l' φ' = -(h.covDerivBarL j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesBarL j) (h.d_anticomm_barL i j) l φ l' φ'

lemma covD_anticomm_covE (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivD i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesE j) (h.d_anticomm_e i j) l φ l' φ'

lemma covD_anticomm_covBarE (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivD i l φ * h.covDerivBarE j l' φ' = -(h.covDerivBarE j l' φ' * h.covDerivD i l φ) :=
  (h.speciesD i).anticomm_tower_tower (h.speciesBarE j) (h.d_anticomm_bare i j) l φ l' φ'

lemma covBarD_anticomm_covBarD (φ φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    h.covDerivBarD i l φ * h.covDerivBarD j l' φ' =
      -(h.covDerivBarD j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesBarD j) (h.bard_anticomm_bard i j) l φ l' φ'

lemma covBarD_anticomm_covU (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ UpSinglet) :
    h.covDerivBarD i l φ * h.covDerivU j l' φ' = -(h.covDerivU j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesU j) (h.bard_anticomm_u i j) l φ l' φ'

lemma covBarD_anticomm_covBarU (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    h.covDerivBarD i l φ * h.covDerivBarU j l' φ' =
      -(h.covDerivBarU j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesBarU j) (h.bard_anticomm_baru i j) l φ l' φ'

lemma covBarD_anticomm_covQ (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ QuarkDoublet) :
    h.covDerivBarD i l φ * h.covDerivQ j l' φ' = -(h.covDerivQ j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesQ j) (h.bard_anticomm_Q i j) l φ l' φ'

lemma covBarD_anticomm_covBarQ (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    h.covDerivBarD i l φ * h.covDerivBarQ j l' φ' =
      -(h.covDerivBarQ j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesBarQ j) (h.bard_anticomm_barQ i j) l φ l' φ'

lemma covBarD_anticomm_covL (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivBarD i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesL j) (h.bard_anticomm_L i j) l φ l' φ'

lemma covBarD_anticomm_covBarL (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivBarD i l φ * h.covDerivBarL j l' φ' =
      -(h.covDerivBarL j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesBarL j) (h.bard_anticomm_barL i j) l φ l' φ'

lemma covBarD_anticomm_covE (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivBarD i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesE j) (h.bard_anticomm_e i j) l φ l' φ'

lemma covBarD_anticomm_covBarE (φ : Module.Dual ℂ (ConjModule DownSinglet))
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivBarD i l φ * h.covDerivBarE j l' φ' =
      -(h.covDerivBarE j l' φ' * h.covDerivBarD i l φ) :=
  (h.speciesBarD i).anticomm_tower_tower (h.speciesBarE j) (h.bard_anticomm_bare i j) l φ l' φ'

lemma covU_anticomm_covU (φ φ' : Module.Dual ℂ UpSinglet) :
    h.covDerivU i l φ * h.covDerivU j l' φ' = -(h.covDerivU j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesU j) (h.u_anticomm_u i j) l φ l' φ'

lemma covU_anticomm_covBarU (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    h.covDerivU i l φ * h.covDerivBarU j l' φ' = -(h.covDerivBarU j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesBarU j) (h.u_anticomm_baru i j) l φ l' φ'

lemma covU_anticomm_covQ (φ : Module.Dual ℂ UpSinglet) (φ' : Module.Dual ℂ QuarkDoublet) :
    h.covDerivU i l φ * h.covDerivQ j l' φ' = -(h.covDerivQ j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesQ j) (h.u_anticomm_Q i j) l φ l' φ'

lemma covU_anticomm_covBarQ (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    h.covDerivU i l φ * h.covDerivBarQ j l' φ' = -(h.covDerivBarQ j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesBarQ j) (h.u_anticomm_barQ i j) l φ l' φ'

lemma covU_anticomm_covL (φ : Module.Dual ℂ UpSinglet) (φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivU i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesL j) (h.u_anticomm_L i j) l φ l' φ'

lemma covU_anticomm_covBarL (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivU i l φ * h.covDerivBarL j l' φ' = -(h.covDerivBarL j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesBarL j) (h.u_anticomm_barL i j) l φ l' φ'

lemma covU_anticomm_covE (φ : Module.Dual ℂ UpSinglet) (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivU i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesE j) (h.u_anticomm_e i j) l φ l' φ'

lemma covU_anticomm_covBarE (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivU i l φ * h.covDerivBarE j l' φ' = -(h.covDerivBarE j l' φ' * h.covDerivU i l φ) :=
  (h.speciesU i).anticomm_tower_tower (h.speciesBarE j) (h.u_anticomm_bare i j) l φ l' φ'

lemma covBarU_anticomm_covBarU (φ φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    h.covDerivBarU i l φ * h.covDerivBarU j l' φ' =
      -(h.covDerivBarU j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesBarU j) (h.baru_anticomm_baru i j) l φ l' φ'

lemma covBarU_anticomm_covQ (φ : Module.Dual ℂ (ConjModule UpSinglet))
    (φ' : Module.Dual ℂ QuarkDoublet) :
    h.covDerivBarU i l φ * h.covDerivQ j l' φ' = -(h.covDerivQ j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesQ j) (h.baru_anticomm_Q i j) l φ l' φ'

lemma covBarU_anticomm_covBarQ (φ : Module.Dual ℂ (ConjModule UpSinglet))
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    h.covDerivBarU i l φ * h.covDerivBarQ j l' φ' =
      -(h.covDerivBarQ j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesBarQ j) (h.baru_anticomm_barQ i j) l φ l' φ'

lemma covBarU_anticomm_covL (φ : Module.Dual ℂ (ConjModule UpSinglet))
    (φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivBarU i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesL j) (h.baru_anticomm_L i j) l φ l' φ'

lemma covBarU_anticomm_covBarL (φ : Module.Dual ℂ (ConjModule UpSinglet))
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivBarU i l φ * h.covDerivBarL j l' φ' =
      -(h.covDerivBarL j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesBarL j) (h.baru_anticomm_barL i j) l φ l' φ'

lemma covBarU_anticomm_covE (φ : Module.Dual ℂ (ConjModule UpSinglet))
    (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivBarU i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesE j) (h.baru_anticomm_e i j) l φ l' φ'

lemma covBarU_anticomm_covBarE (φ : Module.Dual ℂ (ConjModule UpSinglet))
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivBarU i l φ * h.covDerivBarE j l' φ' =
      -(h.covDerivBarE j l' φ' * h.covDerivBarU i l φ) :=
  (h.speciesBarU i).anticomm_tower_tower (h.speciesBarE j) (h.baru_anticomm_bare i j) l φ l' φ'

lemma covQ_anticomm_covQ (φ φ' : Module.Dual ℂ QuarkDoublet) :
    h.covDerivQ i l φ * h.covDerivQ j l' φ' = -(h.covDerivQ j l' φ' * h.covDerivQ i l φ) :=
  (h.speciesQ i).anticomm_tower_tower (h.speciesQ j) (h.Q_anticomm_Q i j) l φ l' φ'

lemma covQ_anticomm_covBarQ (φ : Module.Dual ℂ QuarkDoublet)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    h.covDerivQ i l φ * h.covDerivBarQ j l' φ' = -(h.covDerivBarQ j l' φ' * h.covDerivQ i l φ) :=
  (h.speciesQ i).anticomm_tower_tower (h.speciesBarQ j) (h.Q_anticomm_barQ i j) l φ l' φ'

lemma covQ_anticomm_covL (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivQ i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivQ i l φ) :=
  (h.speciesQ i).anticomm_tower_tower (h.speciesL j) (h.Q_anticomm_L i j) l φ l' φ'

lemma covQ_anticomm_covBarL (φ : Module.Dual ℂ QuarkDoublet)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivQ i l φ * h.covDerivBarL j l' φ' = -(h.covDerivBarL j l' φ' * h.covDerivQ i l φ) :=
  (h.speciesQ i).anticomm_tower_tower (h.speciesBarL j) (h.Q_anticomm_barL i j) l φ l' φ'

lemma covQ_anticomm_covE (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivQ i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivQ i l φ) :=
  (h.speciesQ i).anticomm_tower_tower (h.speciesE j) (h.Q_anticomm_e i j) l φ l' φ'

lemma covQ_anticomm_covBarE (φ : Module.Dual ℂ QuarkDoublet)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivQ i l φ * h.covDerivBarE j l' φ' = -(h.covDerivBarE j l' φ' * h.covDerivQ i l φ) :=
  (h.speciesQ i).anticomm_tower_tower (h.speciesBarE j) (h.Q_anticomm_bare i j) l φ l' φ'

lemma covBarQ_anticomm_covBarQ (φ φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    h.covDerivBarQ i l φ * h.covDerivBarQ j l' φ' =
      -(h.covDerivBarQ j l' φ' * h.covDerivBarQ i l φ) :=
  (h.speciesBarQ i).anticomm_tower_tower (h.speciesBarQ j) (h.barQ_anticomm_barQ i j) l φ l' φ'

lemma covBarQ_anticomm_covL (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
    (φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivBarQ i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivBarQ i l φ) :=
  (h.speciesBarQ i).anticomm_tower_tower (h.speciesL j) (h.barQ_anticomm_L i j) l φ l' φ'

lemma covBarQ_anticomm_covBarL (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivBarQ i l φ * h.covDerivBarL j l' φ' =
      -(h.covDerivBarL j l' φ' * h.covDerivBarQ i l φ) :=
  (h.speciesBarQ i).anticomm_tower_tower (h.speciesBarL j) (h.barQ_anticomm_barL i j) l φ l' φ'

lemma covBarQ_anticomm_covE (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
    (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivBarQ i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivBarQ i l φ) :=
  (h.speciesBarQ i).anticomm_tower_tower (h.speciesE j) (h.barQ_anticomm_e i j) l φ l' φ'

lemma covBarQ_anticomm_covBarE (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivBarQ i l φ * h.covDerivBarE j l' φ' =
      -(h.covDerivBarE j l' φ' * h.covDerivBarQ i l φ) :=
  (h.speciesBarQ i).anticomm_tower_tower (h.speciesBarE j) (h.barQ_anticomm_bare i j) l φ l' φ'

lemma covL_anticomm_covL (φ φ' : Module.Dual ℂ LeptonDoublet) :
    h.covDerivL i l φ * h.covDerivL j l' φ' = -(h.covDerivL j l' φ' * h.covDerivL i l φ) :=
  (h.speciesL i).anticomm_tower_tower (h.speciesL j) (h.L_anticomm_L i j) l φ l' φ'

lemma covL_anticomm_covBarL (φ : Module.Dual ℂ LeptonDoublet)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivL i l φ * h.covDerivBarL j l' φ' = -(h.covDerivBarL j l' φ' * h.covDerivL i l φ) :=
  (h.speciesL i).anticomm_tower_tower (h.speciesBarL j) (h.L_anticomm_barL i j) l φ l' φ'

lemma covL_anticomm_covE (φ : Module.Dual ℂ LeptonDoublet) (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivL i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivL i l φ) :=
  (h.speciesL i).anticomm_tower_tower (h.speciesE j) (h.L_anticomm_e i j) l φ l' φ'

lemma covL_anticomm_covBarE (φ : Module.Dual ℂ LeptonDoublet)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivL i l φ * h.covDerivBarE j l' φ' = -(h.covDerivBarE j l' φ' * h.covDerivL i l φ) :=
  (h.speciesL i).anticomm_tower_tower (h.speciesBarE j) (h.L_anticomm_bare i j) l φ l' φ'

lemma covBarL_anticomm_covBarL (φ φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    h.covDerivBarL i l φ * h.covDerivBarL j l' φ' =
      -(h.covDerivBarL j l' φ' * h.covDerivBarL i l φ) :=
  (h.speciesBarL i).anticomm_tower_tower (h.speciesBarL j) (h.barL_anticomm_barL i j) l φ l' φ'

lemma covBarL_anticomm_covE (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
    (φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivBarL i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivBarL i l φ) :=
  (h.speciesBarL i).anticomm_tower_tower (h.speciesE j) (h.barL_anticomm_e i j) l φ l' φ'

lemma covBarL_anticomm_covBarE (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivBarL i l φ * h.covDerivBarE j l' φ' =
      -(h.covDerivBarE j l' φ' * h.covDerivBarL i l φ) :=
  (h.speciesBarL i).anticomm_tower_tower (h.speciesBarE j) (h.barL_anticomm_bare i j) l φ l' φ'

lemma covE_anticomm_covE (φ φ' : Module.Dual ℂ LeptonSinglet) :
    h.covDerivE i l φ * h.covDerivE j l' φ' = -(h.covDerivE j l' φ' * h.covDerivE i l φ) :=
  (h.speciesE i).anticomm_tower_tower (h.speciesE j) (h.e_anticomm_e i j) l φ l' φ'

lemma covE_anticomm_covBarE (φ : Module.Dual ℂ LeptonSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivE i l φ * h.covDerivBarE j l' φ' = -(h.covDerivBarE j l' φ' * h.covDerivE i l φ) :=
  (h.speciesE i).anticomm_tower_tower (h.speciesBarE j) (h.e_anticomm_bare i j) l φ l' φ'

lemma covBarE_anticomm_covBarE (φ φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    h.covDerivBarE i l φ * h.covDerivBarE j l' φ' =
      -(h.covDerivBarE j l' φ' * h.covDerivBarE i l φ) :=
  (h.speciesBarE i).anticomm_tower_tower (h.speciesBarE j) (h.bare_anticomm_bare i j) l φ l' φ'

end

/-!

## J. The Lorentz law of the field-strength tower

The Lorentz laws of the matter towers are section L of
[`CovariantDeriv.lean`](CovariantDeriv.lean); the one for the field-strength tower is
`repLorentz_covF` just below, which is
`GaugeAlgebraRealization.repLorentz_iteratedCovDerivAdjoint_fieldStrength` read in the
ordered-tuple indexing.

-/

/-- The Lorentz law of the covariant field-strength tower: the covariant derivative
  slots mix by their own columns of the Lorentz matrix, and the two covector indices
  of the field strength mix by theirs. -/
lemma repLorentz_covF (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (h.covF l μ ν φ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
      ∑ a, (((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
      ∑ b, (((SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) • h.covF p a b φ :=
  GaugeAlgebraRealization.repLorentz_iteratedCovDerivAdjoint_fieldStrength h.gaugeRealization
    Λ n l μ ν φ

end AlgebraRealization

end StandardModel
