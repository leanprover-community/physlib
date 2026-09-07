/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3FunAntiFun
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2AntiFundamental
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
public import Physlib.Relativity.LorentzGroup.Invariants.IsVectorLeftRightWeyl
/-!
# Peeling invariants off a stable submodule

Every sector of the Standard Model is classified the same way. A submodule of the algebra
is cut down by one index law at a time — colour, then isospin, then Lorentz — and at each
stage a classification theorem says that an invariant of the submodule is a multiple of a
single contraction, up to an error term in a submodule that the group carries into itself.
This file is the machinery that runs those stages, shared by every sector so that they all
tell the same story.

The relation is `Peels σ V W`: every `σ`-invariant of `V ⊔ S` lies in `W ⊔ S`, for every
`σ`-stable `S`. It is transitive, monotone in both arguments and closed under joins in its
source, and those four moves are all a sector-level argument ever needs: stages chain by
`Peels.trans`, a sum of blocks is handled by `Peels.sup`, and a family of blocks by
`Peels.biSup` and `Peels.iSup`.

The maps `σ` are a bare family of linear maps indexed by any type, not a representation.
That is what lets one relation serve three stages: colour is `fun U => repGauge (U, 1, 1)`,
isospin is `fun V => repGauge (1, V, 1)`, Lorentz is `fun Λ => repLorentz Λ`, and both
groups at once is the family indexed by `GaugeGroupI ⊕ SL(2,ℂ)`. A peeling for one of the
three transports to a peeling for all of them by `Peels.comp`.

A `Step` packages one classification theorem: the submodule, the contraction its invariants
are multiples of, and the three facts the peeling consumes. The constructors wrap the
classifiers of the colour, isospin and Lorentz index laws, together with `Step.ofFixed` for
a stage that has nothing to do — a lepton block has no colour index, and rather than making
it an exception it is given the trivial colour step.

Three further groups of shared facts ride along, for the same reason: they are used by
every sector and belong to none. A gauge transformation is a triple, so an element fixed by
its colour, isospin and hypercharge factors separately is gauge invariant, and each index
law constrains one factor and says nothing about the others (E). A contraction of one pair
of indices is a sum, or a difference, of components, so each index law has to be known
closed under those before the next contraction can be formed (F). And a weight piece lies
inside the submodule it decomposes, a symbol range is the span of its components, and a
product of stable submodules is stable (G).

- A. Stable and fixed submodules
- B. The peeling relation
- C. The classification steps
- D. The two groups at once
- E. The three factors of a gauge transformation
- F. Sums and differences of classified families
- G. Weight pieces, symbol ranges and stability

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

/-!

## A. Stable and fixed submodules

The peeling argument never uses a group structure, only a family of linear maps `σ` indexed
by a type `G`, and two properties of a submodule with respect to it: being carried into
itself, and being fixed pointwise.  Both are needed.  Stability is what lets a submodule be
adjoined to the error term `S` of a classification, and it is exactly the hypothesis the
classification theorems ask of `S`; fixedness is the stronger property the spans of the
contractions have, and it implies stability.

-/

section Stability

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {G : Type*}

/-- A submodule carried into itself by every map of the family `σ`. This is the hypothesis
  every classification modulo a submodule asks of that submodule. -/
def IsStableUnder (σ : G → B →ₗ[ℂ] B) (V : Submodule ℂ B) : Prop :=
  ∀ g, ∀ y ∈ V, σ g y ∈ V

/-- A submodule fixed pointwise by every map of the family `σ`. -/
def IsFixedBy (σ : G → B →ₗ[ℂ] B) (V : Submodule ℂ B) : Prop :=
  ∀ g, ∀ y ∈ V, σ g y = y

/-- Stability read as an inclusion of images, which is the form the lattice operations
  are handled in. -/
lemma isStableUnder_iff_map {σ : G → B →ₗ[ℂ] B} {V : Submodule ℂ B} :
    IsStableUnder σ V ↔ ∀ g, Submodule.map (σ g) V ≤ V := by
  constructor
  · rintro hV g _ ⟨y, hy, rfl⟩
    exact hV g y hy
  · exact fun hV g y hy => hV g ⟨y, hy, rfl⟩

/-- A submodule fixed pointwise is stable. -/
lemma IsFixedBy.isStableUnder {σ : G → B →ₗ[ℂ] B} {V : Submodule ℂ B} (hV : IsFixedBy σ V) :
    IsStableUnder σ V := fun g y hy => by rw [hV g y hy]; exact hy

/-- A join of two pointwise-fixed submodules is pointwise fixed. -/
lemma IsFixedBy.sup {σ : G → B →ₗ[ℂ] B} {V V' : Submodule ℂ B} (hV : IsFixedBy σ V)
    (hV' : IsFixedBy σ V') : IsFixedBy σ (V ⊔ V') := by
  intro g y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, hV g a ha, hV' g b hb]

/-- The zero submodule is stable. -/
lemma isStableUnder_bot {σ : G → B →ₗ[ℂ] B} : IsStableUnder σ (⊥ : Submodule ℂ B) := by
  intro g y hy
  rw [Submodule.mem_bot] at hy
  simp [hy]

/-- A join of two stable submodules is stable. -/
lemma IsStableUnder.sup {σ : G → B →ₗ[ℂ] B} {V V' : Submodule ℂ B} (hV : IsStableUnder σ V)
    (hV' : IsStableUnder σ V') : IsStableUnder σ (V ⊔ V') :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_sup]
    exact sup_le_sup (isStableUnder_iff_map.1 hV g) (isStableUnder_iff_map.1 hV' g)

/-- An indexed join of stable submodules is stable. The index is a `Sort`, so this covers
  the join over a proposition and with it the bounded join `⨆ i ∈ s, V i`. -/
lemma isStableUnder_iSup {σ : G → B →ₗ[ℂ] B} {ι : Sort*} {V : ι → Submodule ℂ B}
    (hV : ∀ i, IsStableUnder σ (V i)) : IsStableUnder σ (⨆ i, V i) :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => isStableUnder_iff_map.1 (hV i) g

/-- The line through a fixed vector is fixed, hence stable. -/
lemma isFixedBy_span_singleton {σ : G → B →ₗ[ℂ] B} {b : B} (hb : ∀ g, σ g b = b) :
    IsFixedBy σ (ℂ ∙ b) := by
  intro g y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [map_smul, hb]

/-- An indexed join of pointwise-fixed submodules is pointwise fixed. -/
lemma isFixedBy_iSup {σ : G → B →ₗ[ℂ] B} {ι : Sort*} {V : ι → Submodule ℂ B}
    (hV : ∀ i, IsFixedBy σ (V i)) : IsFixedBy σ (⨆ i, V i) := by
  intro g y hy
  refine Submodule.iSup_induction (motive := fun z => σ g z = z) V hy (fun i z hz => hV i g z hz)
    (map_zero _) fun z z' hz hz' => by rw [map_add, hz, hz']

/-- A join of lines through fixed vectors is pointwise fixed: the form in which a family of
  contractions supplies the fixedness of its span. -/
lemma isFixedBy_iSup_span_singleton {σ : G → B →ₗ[ℂ] B} {ι : Sort*} {T : ι → B}
    (hT : ∀ i g, σ g (T i) = T i) : IsFixedBy σ (⨆ i, ℂ ∙ T i) :=
  isFixedBy_iSup fun i => isFixedBy_span_singleton (hT i)

/-- The span of a family whose members transform into combinations of the family is
  stable. -/
lemma isStableUnder_iSup_span_singleton {σ : G → B →ₗ[ℂ] B} {ι : Type*} {T : ι → B}
    (hT : ∀ g i, σ g (T i) ∈ ⨆ j, ℂ ∙ T j) : IsStableUnder σ (⨆ i, ℂ ∙ T i) :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_iSup]
    exact iSup_le fun i => by
      rw [Submodule.map_span, Set.image_singleton, Submodule.span_singleton_le_iff_mem]
      exact hT g i

/-- The span of a family transforming by a finite combination of itself is stable: the
  form in which the three index laws supply stability. -/
lemma isStableUnder_iSup_span_singleton_of_sum {σ : G → B →ₗ[ℂ] B} {ι : Type*} [Fintype ι]
    {T : ι → B} (hT : ∀ g i, ∃ c : ι → ℂ, σ g (T i) = ∑ a, c a • T a) :
    IsStableUnder σ (⨆ i, ℂ ∙ T i) := by
  refine isStableUnder_iSup_span_singleton fun g i => ?_
  obtain ⟨c, hc⟩ := hT g i
  rw [hc]
  exact sum_mem fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _))

end Stability

/-!

## B. The peeling relation

`Peels σ V W` says that a `σ`-invariant of `V` joined with a `σ`-stable submodule `S` lies
in `W` joined with `S`, for every such `S`.  It is the shape every classification modulo a
stable submodule takes, and everything the argument does with those classifications is one
of four moves: enlarging the target, shrinking the source, composing two of them in
sequence, and — the one that does real work — joining two of them.

The join is where stability is spent.  To peel `V₁ ⊔ V₂` down to `W` the second summand is
put into the error term, which asks that `V₂` be stable; what comes back out is an element
of `W ⊔ (V₂ ⊔ S)`, and peeling `V₂` off that in turn asks that `W` be stable, since `W` is
now part of the error term.  Both hypotheses are met in practice, `V₂` being a span of
symbol components and `W` a span of invariants.

-/

section Peeling

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {G : Type*}

/-- The peeling relation: every `σ`-invariant of `V ⊔ S`, for `S` a `σ`-stable submodule,
  lies in `W ⊔ S`. This is the conclusion each classification modulo a stable submodule
  reaches, in a form that composes. -/
def Peels (σ : G → B →ₗ[ℂ] B) (V W : Submodule ℂ B) : Prop :=
  ∀ S : Submodule ℂ B, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) → x ∈ W ⊔ S

/-- An inclusion peels: nothing has to be classified. -/
lemma peels_of_le {σ : G → B →ₗ[ℂ] B} {V W : Submodule ℂ B} (hVW : V ≤ W) : Peels σ V W :=
  fun S _ _ hx _ => sup_le_sup_right hVW S hx

/-- Peeling a smaller source. -/
lemma Peels.mono_left {σ : G → B →ₗ[ℂ] B} {V V' W : Submodule ℂ B} (hP : Peels σ V' W)
    (hV : V ≤ V') : Peels σ V W :=
  fun S hS x hx hinv => hP S hS x (sup_le_sup_right hV S hx) hinv

/-- Peeling to a larger target. -/
lemma Peels.mono_right {σ : G → B →ₗ[ℂ] B} {V W W' : Submodule ℂ B} (hP : Peels σ V W')
    (hW : W' ≤ W) : Peels σ V W :=
  fun S hS x hx hinv => sup_le_sup_right hW S (hP S hS x hx hinv)

/-- Two peelings in sequence. This is what turns the colour, isospin and Lorentz
  classifications of a block into a single one. -/
lemma Peels.trans {σ : G → B →ₗ[ℂ] B} {V W W' : Submodule ℂ B} (hP : Peels σ V W)
    (hQ : Peels σ W W') : Peels σ V W' :=
  fun S hS x hx hinv => hQ S hS x (hP S hS x hx hinv) hinv

/-- Peeling a join, one summand at a time: the second summand joins the error term while
  the first is classified, and the roles are then exchanged. -/
lemma Peels.sup {σ : G → B →ₗ[ℂ] B} {V V' W : Submodule ℂ B} (hP : Peels σ V W)
    (hQ : Peels σ V' W) (hV' : IsStableUnder σ V') (hW : IsStableUnder σ W) :
    Peels σ (V ⊔ V') W := by
  intro S hS x hx hinv
  have h1 : x ∈ W ⊔ (V' ⊔ S) :=
    hP (V' ⊔ S) (hV'.sup hS) x (by rwa [← sup_assoc]) hinv
  have h2 : x ∈ V' ⊔ (W ⊔ S) := by
    have hcomm : W ⊔ (V' ⊔ S) = V' ⊔ (W ⊔ S) := sup_left_comm W V' S
    rwa [hcomm] at h1
  have h3 : x ∈ W ⊔ (W ⊔ S) := hQ (W ⊔ S) (hW.sup hS) x h2 hinv
  rwa [← sup_assoc, sup_idem] at h3

/-- Peeling a join over a finite set, by induction on the set. -/
lemma Peels.biSup {σ : G → B →ₗ[ℂ] B} {ι : Type*} [DecidableEq ι] {V : ι → Submodule ℂ B}
    {W : Submodule ℂ B} (hP : ∀ i, Peels σ (V i) W) (hV : ∀ i, IsStableUnder σ (V i))
    (hW : IsStableUnder σ W) : ∀ s : Finset ι, Peels σ (⨆ i ∈ s, V i) W := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine peels_of_le (le_trans (le_of_eq ?_) bot_le)
    simp
  | @insert a s _ ih =>
    rw [Finset.iSup_insert]
    exact (hP a).sup ih (isStableUnder_iSup fun i => isStableUnder_iSup fun _ => hV i) hW

/-- Peeling a join over a finite index type. -/
lemma Peels.iSup {σ : G → B →ₗ[ℂ] B} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Submodule ℂ B} {W : Submodule ℂ B} (hP : ∀ i, Peels σ (V i) W)
    (hV : ∀ i, IsStableUnder σ (V i)) (hW : IsStableUnder σ W) : Peels σ (⨆ i, V i) W := by
  have hs := Peels.biSup hP hV hW Finset.univ
  refine hs.mono_left (iSup_le fun i => le_iSup₂_of_le i (Finset.mem_univ i) le_rfl)

/-- Peeling under a reindexing of the family of maps: an invariant of the larger family is
  an invariant of the smaller one and a stable submodule for the larger is stable for the
  smaller, so a peeling for the smaller family is one for the larger. This is what lets the
  colour, isospin and Lorentz peelings, each stated for its own group, be read as peelings
  for the gauge and Lorentz groups together. -/
lemma Peels.comp {σ : G → B →ₗ[ℂ] B} {G' : Type*} (ι : G' → G) {V W : Submodule ℂ B}
    (hP : Peels (fun g' => σ (ι g')) V W) : Peels σ V W :=
  fun S hS x hx hinv => hP S (fun g' y hy => hS (ι g') y hy) x hx fun g' => hinv (ι g')

end Peeling

/-!

## C. The classification steps

A `Step` packages what one classification theorem provides: a submodule, the single
contraction its invariants are multiples of, and the three facts the peeling needs — that
the submodule is stable, that the contraction is fixed, and that an invariant of the
submodule joined with a stable error term is a multiple of the contraction plus an error.

Six constructors cover the file.  Five wrap the classification theorems of the colour,
isospin and Lorentz index laws.  The sixth wraps no theorem at all: a line through a fixed
vector is classified by that vector, and it is what stands in for the colour step of a
lepton block, whose three symbols carry no colour index between them.  With it the two
lepton couplings are peeled in the same three stages as the four quark ones.

-/

section Steps

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {G : Type*}

/-- One classification of the invariants of a submodule, in the form the peeling consumes:
  the submodule is stable, the contraction it classifies down to is fixed, and every
  invariant of the submodule joined with a stable error term is a multiple of the
  contraction up to an error. -/
structure Step (σ : G → B →ₗ[ℂ] B) (V : Submodule ℂ B) where
  /-- The single invariant the classification produces. -/
  contraction : B
  /-- The submodule being classified is carried into itself. -/
  stable : IsStableUnder σ V
  /-- The contraction is fixed by the whole family. -/
  contraction_fixed : ∀ g, σ g contraction = contraction
  /-- The classification itself, modulo a stable error term. -/
  classify : ∀ S : Submodule ℂ B, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) →
    ∃ c : ℂ, ∃ y ∈ S, x = c • contraction + y

/-- A step peels its submodule down to the line through its contraction. -/
lemma Step.peels {σ : G → B →ₗ[ℂ] B} {V : Submodule ℂ B} (st : Step σ V) :
    Peels σ V (ℂ ∙ st.contraction) := by
  intro S hS x hx hinv
  obtain ⟨c, y, hy, rfl⟩ := st.classify S hS x hx hinv
  exact Submodule.mem_sup.2 ⟨c • st.contraction,
    Submodule.mem_span_singleton.2 ⟨c, rfl⟩, y, hy, rfl⟩

/-- The line through a step's contraction is fixed, hence stable: the form in which a
  step supplies the stability of the target of a peeling. -/
lemma Step.span_contraction_stable {σ : G → B →ₗ[ℂ] B} {V : Submodule ℂ B}
    (st : Step σ V) : IsStableUnder σ (ℂ ∙ st.contraction) :=
  (isFixedBy_span_singleton st.contraction_fixed).isStableUnder

/-- A family of steps peels the join of their submodules down to the join of their
  contractions. This is the whole of one stage of a block's classification: one index law
  holds at each value of the indices it does not see, and the classification is applied at
  each of those values in turn. -/
lemma Peels.iSup_step {σ : G → B →ₗ[ℂ] B} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {V : κ → Submodule ℂ B} (st : ∀ k, Step σ (V k)) :
    Peels σ (⨆ k, V k) (⨆ k, ℂ ∙ (st k).contraction) :=
  Peels.iSup (fun k => ((st k).peels).mono_right
      (le_iSup (fun k' => ℂ ∙ (st k').contraction) k)) (fun k => (st k).stable)
    (isStableUnder_iSup fun k => (st k).span_contraction_stable)

/-- The trivial step: a line through a vector that the family fixes is already classified,
  by that vector itself. This is the colour step of a lepton block, whose symbols carry no
  colour index, and it is what makes those blocks a case of the general argument rather
  than an exception to it. -/
noncomputable def Step.ofFixed {σ : G → B →ₗ[ℂ] B} (b : B) (hb : ∀ g, σ g b = b) :
    Step σ (ℂ ∙ b) where
  contraction := b
  stable := (isFixedBy_span_singleton hb).isStableUnder
  contraction_fixed := hb
  classify S _ x hx _ := by
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    exact ⟨c, y, hy, rfl⟩

/-- The trivial step on a family that does not move at all: if every member of the family
  is the same fixed vector, the join of the lines through the family is the line through
  that vector, and it is classified by it. This is the colour step of a block whose symbols
  carry no colour index, and the isospin step of one whose symbols carry no isospin. -/
noncomputable def Step.ofFixedFamily {σ : G → B →ₗ[ℂ] B} {ι : Type*} [Nonempty ι]
    {T : ι → B} (b : B) (hTb : ∀ i, T i = b) (hb : ∀ g, σ g b = b) :
    Step σ (⨆ i, ℂ ∙ T i) where
  contraction := b
  stable := by
    refine (isFixedBy_iSup fun i => ?_).isStableUnder
    rw [hTb i]
    exact isFixedBy_span_singleton hb
  contraction_fixed := hb
  classify S _ x hx _ := by
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    have hspan : (⨆ i, ℂ ∙ T i) = ℂ ∙ b := by
      refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le (Classical.arbitrary ι) ?_)
      · rw [hTb i]
      · rw [hTb (Classical.arbitrary ι)]
    rw [hspan] at ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    exact ⟨c, y, hy, rfl⟩

end Steps

section GaugeSteps

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The colour step of a family carrying one fundamental and one anti-fundamental colour
  index: its invariants are the multiples of the delta contraction. -/
noncomputable def Step.ofSU3FunAntiFun {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
      (IsSU3FunAntiFun.span T) where
  contraction := IsSU3FunAntiFun.deltaContraction T
  stable := isStableUnder_iSup_span_singleton_of_sum fun U l => ⟨_, hT.repGauge_T U l⟩
  contraction_fixed U := IsSU3FunAntiFun.repGauge_deltaContraction hT U
  classify S hS x hx hinv := by
    obtain ⟨c, y, hy, hxy, _⟩ := hT.mem_span_sup_su3_invariant_iff x S hS hx hinv
    exact ⟨c, y, hy, hxy⟩

/-- The isospin step of a family carrying one fundamental and one anti-fundamental isospin
  index: its invariants are the multiples of the delta contraction. -/
noncomputable def Step.ofSU2FunAntiFun {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (IsSU2BiFundamental.span T) where
  contraction := IsSU2FunAntiFun.deltaContraction T
  stable := isStableUnder_iSup_span_singleton_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩
  contraction_fixed V := IsSU2FunAntiFun.repGauge_deltaContraction hT V
  classify S hS x hx hinv := by
    obtain ⟨c, y, hy, hxy, _⟩ := hT.mem_span_sup_su2_invariant_iff x S hS hx hinv
    exact ⟨c, y, hy, hxy⟩

/-- The isospin step of a family carrying two anti-fundamental isospin indices: its
  invariants are the multiples of the epsilon contraction, a pair of anti-fundamental
  indices admitting no trace. -/
noncomputable def Step.ofSU2BiAntiFun {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (IsSU2BiFundamental.span T) where
  contraction := IsSU2BiFundamental.epsilonContraction T
  stable := isStableUnder_iSup_span_singleton_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩
  contraction_fixed V := IsSU2BiAntiFun.repGauge_epsilonContraction hT V
  classify S hS x hx hinv := by
    obtain ⟨c, y, hy, hxy, _⟩ := hT.mem_span_sup_su2_invariant_iff x S hS hx hinv
    exact ⟨c, y, hy, hxy⟩

/-- The isospin step of a family carrying two fundamental isospin indices. -/
noncomputable def Step.ofSU2BiFundamental {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (IsSU2BiFundamental.span T) where
  contraction := IsSU2BiFundamental.epsilonContraction T
  stable := isStableUnder_iSup_span_singleton_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩
  contraction_fixed V := IsSU2BiFundamental.repGauge_epsilonContraction hT V
  classify S hS x hx hinv := by
    obtain ⟨c, y, hy, hxy, _⟩ := hT.mem_span_sup_su2_invariant_iff x S hS hx hinv
    exact ⟨c, y, hy, hxy⟩

/-- The Lorentz step of a family carrying two dual left-handed Weyl indices: its invariants
  are the multiples of the epsilon contraction. -/
noncomputable def Step.ofBiDualLeftWeyl {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualLeftWeyl B repLorentz T) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ) (⨆ l, ℂ ∙ T l) where
  contraction := IsBiLeftWeyl.epsilonContraction (T := T)
  stable := isStableUnder_iSup_span_singleton_of_sum fun Λ l => ⟨_, hT.repLorentz_T Λ l⟩
  contraction_fixed Λ := hT.repLorentz_epsilonContraction Λ
  classify S hS _ hx hinv :=
    hT.exists_smul_epsilonContraction_of_invariant_subset S hS hx hinv

/-- The Lorentz step of a family carrying two dual right-handed Weyl indices. -/
noncomputable def Step.ofBiDualRightWeyl {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualRightWeyl B repLorentz T) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ) (⨆ l, ℂ ∙ T l) where
  contraction := IsBiLeftWeyl.epsilonContraction (T := T)
  stable := isStableUnder_iSup_span_singleton_of_sum fun Λ l => ⟨_, hT.repLorentz_T Λ l⟩
  contraction_fixed Λ := hT.repLorentz_epsilonContraction Λ
  classify S hS _ hx hinv :=
    hT.exists_smul_epsilonContraction_of_invariant_subset S hS hx hinv

/-- The Lorentz step of a family carrying one four-vector index and a pair of dual
  opposite-chirality Weyl indices: its invariants are the multiples of the conjugate Pauli
  contraction. This is the kinetic term of a Weyl fermion. -/
noncomputable def Step.ofVectorDualLeftRightWeyl {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    {T : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 → B}
    (hT : IsVectorDualLeftRightWeyl B repLorentz T) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ) (⨆ q, ℂ ∙ T q) where
  contraction := IsVectorDualLeftRightWeyl.pauliBarContraction (T := T)
  stable := isStableUnder_iSup_span_singleton_of_sum fun Λ q => by
    refine ⟨fun a => ((((SL2C.toLorentzGroup Λ).1 a.1 q.1 : ℝ) : ℂ)
      * ((Λ.1⁻¹)ᵀ a.2.1 q.2.1 * (Λ.1⁻¹)ᴴ a.2.2 q.2.2)), ?_⟩
    rw [show q = (q.1, q.2) from rfl, hT.repLorentz_T, Fintype.sum_prod_type]
  contraction_fixed Λ := hT.repLorentz_pauliBarContraction Λ
  classify S hS _ hx hinv :=
    hT.exists_smul_pauliBarContraction_of_invariant_subset S hS hx hinv

end GaugeSteps

/-!

## D. The two groups at once

The three classifications of a block are read at three different groups, and the twelve
blocks have to be peeled apart under the gauge and Lorentz groups together.  Both are
handled by one device: the family of maps indexed by the disjoint union of the two groups,
whose invariants are the elements fixed by both and whose stable submodules are those
stable under both.  Each stage is then a peeling for a subfamily, transported by
`Peels.comp`.

-/

section BothGroups

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  (repGauge : Representation ℂ GaugeGroupI B)
  (repLorentz : Representation ℂ SL(2,ℂ) B)

/-- The gauge and Lorentz groups read as a single family of linear maps, indexed by their
  disjoint union. -/
def gaugeLorentzMaps : GaugeGroupI ⊕ SL(2,ℂ) → B →ₗ[ℂ] B :=
  Sum.elim (fun g => repGauge g) (fun Λ => repLorentz Λ)

variable {repGauge repLorentz}

/-- A submodule stable under both groups is stable under the combined family, and
  conversely. -/
lemma isStableUnder_gaugeLorentzMaps_iff {V : Submodule ℂ B} :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) V
      ↔ (∀ g : GaugeGroupI, ∀ y ∈ V, repGauge g y ∈ V)
        ∧ ∀ Λ : SL(2,ℂ), ∀ y ∈ V, repLorentz Λ y ∈ V := by
  constructor
  · exact fun hV => ⟨fun g => hV (Sum.inl g), fun Λ => hV (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- An element fixed by both groups is fixed by the combined family, and conversely. -/
lemma forall_gaugeLorentzMaps_eq_self_iff {x : B} :
    (∀ p, gaugeLorentzMaps repGauge repLorentz p x = x)
      ↔ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ Λ : SL(2,ℂ), repLorentz Λ x = x := by
  constructor
  · exact fun hx => ⟨fun g => hx (Sum.inl g), fun Λ => hx (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- A colour peeling is a peeling for the gauge and Lorentz groups together. -/
lemma Peels.ofSU3 {V W : Submodule ℂ B}
    (hP : Peels (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1)) V W) :
    Peels (gaugeLorentzMaps repGauge repLorentz) V W :=
  Peels.comp (fun U : specialUnitaryGroup (Fin 3) ℂ => Sum.inl ((U, 1, 1) : GaugeGroupI)) hP

/-- An isospin peeling is a peeling for the gauge and Lorentz groups together. -/
lemma Peels.ofSU2 {V W : Submodule ℂ B}
    (hP : Peels (fun U : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, U, 1)) V W) :
    Peels (gaugeLorentzMaps repGauge repLorentz) V W :=
  Peels.comp (fun U : specialUnitaryGroup (Fin 2) ℂ => Sum.inl ((1, U, 1) : GaugeGroupI)) hP

/-- A Lorentz peeling is a peeling for the gauge and Lorentz groups together. -/
lemma Peels.ofLorentz {V W : Submodule ℂ B}
    (hP : Peels (fun Λ : SL(2,ℂ) => repLorentz Λ) V W) :
    Peels (gaugeLorentzMaps repGauge repLorentz) V W :=
  Peels.comp (Sum.inr (α := GaugeGroupI)) hP

end BothGroups

/-!

## E. The three factors of a gauge transformation

A gauge transformation is a triple, and the three index laws below each constrain one
factor of it and say nothing about the other two.  This section reads a representation at
each factor separately: the entries of an inverse in the two unitary groups, the three
one-parameter embeddings `(U, 1, 1)`, `(1, V, 1)` and `(1, 1, t)` together with their
inverses, and the factorisation of an arbitrary gauge transformation into the three, which
is what turns three separate invariances into gauge invariance.

-/

/-- The entries of the inverse of an `SU(3)` element are the conjugated transposed
  entries, the inverse of a unitary matrix being its conjugate transpose. -/
lemma su3_inv_apply (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 3) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

/-- The entries of the inverse of an `SU(2)` element are the conjugated transposed
  entries. -/
lemma su2_inv_apply (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (U⁻¹).1 a b = conj (U.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

/-- The inverse of a unitary scalar is its conjugate. -/
lemma unitary_inv_coe (t : unitary ℂ) : ((t⁻¹ : unitary ℂ) : ℂ) = star (t : ℂ) := rfl

/-- The colour factor of a colour gauge transformation. -/
@[simp] lemma toSU3_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toSU3 ((U, 1, 1) : GaugeGroupI) = U := rfl

/-- The isospin factor of a colour gauge transformation is trivial. -/
@[simp] lemma toSU2_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI) = 1 := rfl

/-- The hypercharge factor of a colour gauge transformation is trivial. -/
@[simp] lemma toU1_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    GaugeGroupI.toU1 ((U, 1, 1) : GaugeGroupI) = 1 := rfl

/-- The inverse of a colour gauge transformation is the colour transformation of the
  inverse. -/
@[simp] lemma inv_su3Elt (U : specialUnitaryGroup (Fin 3) ℂ) :
    ((U, 1, 1) : GaugeGroupI)⁻¹ = ((U⁻¹, 1, 1) : GaugeGroupI) := by
  simp

/-- The colour factor of an isospin gauge transformation is trivial. -/
@[simp] lemma toSU3_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toSU3 ((1, V, 1) : GaugeGroupI) = 1 := rfl

/-- The isospin factor of an isospin gauge transformation. -/
@[simp] lemma toSU2_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toSU2 ((1, V, 1) : GaugeGroupI) = V := rfl

/-- The hypercharge factor of an isospin gauge transformation is trivial. -/
@[simp] lemma toU1_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    GaugeGroupI.toU1 ((1, V, 1) : GaugeGroupI) = 1 := rfl

/-- The inverse of an isospin gauge transformation is the isospin transformation of the
  inverse. -/
@[simp] lemma inv_su2Elt (V : specialUnitaryGroup (Fin 2) ℂ) :
    ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) := by
  simp


/-- The colour factor of a hypercharge gauge transformation is trivial. -/
@[simp] lemma toSU3_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toSU3 ((1, 1, t) : GaugeGroupI) = 1 := rfl

/-- The isospin factor of a hypercharge gauge transformation is trivial. -/
@[simp] lemma toSU2_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toSU2 ((1, 1, t) : GaugeGroupI) = 1 := rfl

/-- The hypercharge factor of a hypercharge gauge transformation. -/
@[simp] lemma toU1_u1Elt (t : unitary ℂ) :
    GaugeGroupI.toU1 ((1, 1, t) : GaugeGroupI) = t := rfl

/-- The inverse of a hypercharge gauge transformation is the hypercharge transformation of
  the inverse. -/
@[simp] lemma inv_u1Elt (t : unitary ℂ) :
    ((1, 1, t) : GaugeGroupI)⁻¹ = ((1, 1, t⁻¹) : GaugeGroupI) := by
  simp

/-- A gauge transformation is the product of its colour, isospin and hypercharge parts, so
  an element fixed by each of the three factors separately is gauge invariant. -/
lemma forall_repGauge_eq_self {B : Type*} [AddCommGroup B] [Module ℂ B]
    {rep : Representation ℂ GaugeGroupI B} {x : B}
    (h3 : ∀ U : specialUnitaryGroup (Fin 3) ℂ, rep (U, 1, 1) x = x)
    (h2 : ∀ V : specialUnitaryGroup (Fin 2) ℂ, rep (1, V, 1) x = x)
    (h1 : ∀ t : unitary ℂ, rep (1, 1, t) x = x) (g : GaugeGroupI) : rep g x = x := by
  have hg : g = ((g.1, 1, 1) : GaugeGroupI) * (((1, g.2.1, 1) : GaugeGroupI)
      * ((1, 1, g.2.2) : GaugeGroupI)) := by
    simp [Prod.ext_iff]
  rw [hg, map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, h1, h2, h3]

/-!

## F. Sums and differences of classified families

Contracting one pair of indices of a block leaves a family in the remaining pairs, and that
family is a finite sum — or, where the contraction is by the antisymmetric symbol, a
difference — of the block's own components.  So each index law has to be known closed under
those operations before the second and third contractions can be formed.

-/

/-- A finite sum of families carrying one fundamental and one anti-fundamental colour index
  is such a family again. -/
lemma IsSU3FunAntiFun.sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ GaugeGroupI M} {ι : Type} [Fintype ι]
    {T : ι → (Fin 2 → Fin 3) → M} (hT : ∀ i, IsSU3FunAntiFun M rep (T i)) :
    IsSU3FunAntiFun M rep (fun l => ∑ i, T i l) where
  repGauge_T U l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T U l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A finite sum of families carrying one fundamental and one anti-fundamental isospin
  index is such a family again. -/
lemma IsSU2FunAntiFun.sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ GaugeGroupI M} {ι : Type} [Fintype ι]
    {T : ι → (Fin 2 → Fin 2) → M} (hT : ∀ i, IsSU2FunAntiFun M rep (T i)) :
    IsSU2FunAntiFun M rep (fun l => ∑ i, T i l) where
  repGauge_T V l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T V l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A finite sum of families carrying two anti-fundamental isospin indices is such a family
  again. -/
lemma IsSU2BiAntiFun.sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ GaugeGroupI M} {ι : Type} [Fintype ι]
    {T : ι → (Fin 2 → Fin 2) → M} (hT : ∀ i, IsSU2BiAntiFun M rep (T i)) :
    IsSU2BiAntiFun M rep (fun l => ∑ i, T i l) where
  repGauge_T V l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T V l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A finite sum of families carrying two dual right-handed Weyl indices is such a family
  again. -/
lemma isBiDualRightWeyl_sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {ι : Type} [Fintype ι]
    {T : ι → Fin 2 × Fin 2 → M} (hT : ∀ i, IsBiDualRightWeyl M rep (T i)) :
    IsBiDualRightWeyl M rep (fun l => ∑ i, T i l) where
  repLorentz_T Λ l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repLorentz_T Λ l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A finite sum of families carrying two dual left-handed Weyl indices is such a family
  again. -/
lemma isBiDualLeftWeyl_sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {ι : Type} [Fintype ι]
    {T : ι → Fin 2 × Fin 2 → M} (hT : ∀ i, IsBiDualLeftWeyl M rep (T i)) :
    IsBiDualLeftWeyl M rep (fun l => ∑ i, T i l) where
  repLorentz_T Λ l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repLorentz_T Λ l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A difference of two families carrying two dual left-handed Weyl indices is such a
  family again. -/
lemma isBiDualLeftWeyl_sub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {T T' : Fin 2 × Fin 2 → M}
    (hT : IsBiDualLeftWeyl M rep T) (hT' : IsBiDualLeftWeyl M rep T') :
    IsBiDualLeftWeyl M rep (fun l => T l - T' l) where
  repLorentz_T Λ l := by
    rw [map_sub, hT.repLorentz_T Λ l, hT'.repLorentz_T Λ l, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm

/-- A finite sum of bi-fundamental isospin families is such a family again. -/
lemma IsSU2BiFundamental.sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ GaugeGroupI M} {ι : Type} [Fintype ι]
    {T : ι → (Fin 2 → Fin 2) → M} (hT : ∀ i, IsSU2BiFundamental M rep (T i)) :
    IsSU2BiFundamental M rep (fun l => ∑ i, T i l) where
  repGauge_T V l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T V l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- A difference of two families carrying two dual right-handed Weyl indices is such a
  family again. -/
lemma isBiDualRightWeyl_sub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {rep : Representation ℂ SL(2,ℂ) M} {T T' : Fin 2 × Fin 2 → M}
    (hT : IsBiDualRightWeyl M rep T) (hT' : IsBiDualRightWeyl M rep T') :
    IsBiDualRightWeyl M rep (fun l => T l - T' l) where
  repLorentz_T Λ l := by
    rw [map_sub, hT.repLorentz_T Λ l, hT'.repLorentz_T Λ l, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm

/-!

## G. Weight pieces, symbol ranges and stability

The last group of shared facts is about the objects a sector-level argument hands the
peeling: a weight piece of a gauge weight decomposition lies in the submodule it
decomposes, a symbol range is the span of the symbol's components against a dual basis, and
the product of two stable submodules is stable. None of them mentions a particular sector.

-/

section Bridges

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- A weight piece lies inside the submodule it decomposes. -/
lemma GaugeWeightDecomposition.piece_le_self {rep : Representation ℂ GaugeGroupI B}
    {V : Submodule ℂ B} (d : GaugeWeightDecomposition rep V) (w : GaugeWeight) :
    d.piece w ≤ V := le_trans (le_iSup d.piece w) (le_of_eq d.iSup_piece)

/-- The range of a symbol map is the span of its components against the dual basis of the
  value space. This is the companion of `range_eq_iSup_span`, which reads the same range off
  `Module.Basis.coord`; the two families of components are equal, but the components of the
  `Families` files are the ones written here. -/
lemma range_eq_iSup_span_dualBasis {V M : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (F : Module.Dual ℂ V →ₗ[ℂ] M) :
    LinearMap.range F = ⨆ j, ℂ ∙ F (b.dualBasis j) := by
  rw [LinearMap.range_eq_map, ← b.dualBasis.span_eq, Submodule.map_span, ← Set.range_comp,
    Submodule.span_range_eq_iSup]
  rfl

/-- The product of two lines is the line through the product. -/
lemma span_singleton_mul_span_singleton (a b : B) : (ℂ ∙ a) * (ℂ ∙ b) = ℂ ∙ (a * b) := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

/-- A product of three spans of families is the span of the products, which is the form in
  which a block submodule is compared with the span of its components. -/
lemma mul_mul_le_of_le {ιa ιb ιc : Type} {VA VB VC X : Submodule ℂ B} {A : ιa → B}
    {C : ιb → B} {D : ιc → B} (hA : VA ≤ ⨆ i, ℂ ∙ A i) (hC : VB ≤ ⨆ j, ℂ ∙ C j)
    (hD : VC ≤ ⨆ k, ℂ ∙ D k) (hX : ∀ i j k, A i * (C j * D k) ∈ X) :
    VA * (VB * VC) ≤ X := by
  refine le_trans (mul_le_mul' hA (mul_le_mul' hC hD)) ?_
  rw [Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  rw [Submodule.mul_iSup, Submodule.mul_iSup]
  refine iSup_le fun k => ?_
  rw [span_singleton_mul_span_singleton, span_singleton_mul_span_singleton,
    Submodule.span_singleton_le_iff_mem]
  exact hX i j k

/-- A product of two submodules, each inside the join of the lines through a family, lies
  in any submodule containing the products of the two families. -/
lemma mul_le_of_le {ιa ιb : Type} {VA VB X : Submodule ℂ B} {A : ιa → B} {C : ιb → B}
    (hA : VA ≤ ⨆ i, ℂ ∙ A i) (hC : VB ≤ ⨆ j, ℂ ∙ C j) (hX : ∀ i j, A i * C j ∈ X) :
    VA * VB ≤ X := by
  refine le_trans (mul_le_mul' hA hC) ?_
  rw [Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  rw [span_singleton_mul_span_singleton, Submodule.span_singleton_le_iff_mem]
  exact hX i j

/-- The range of a symbol map is carried into itself by the gauge group: the symbol is
  equivariant, so a gauge transformation only moves the dual vector it is evaluated at. -/
lemma isStableUnder_range_repGauge {M : Type} [AddCommGroup M] [Module ℂ M]
    {repGauge : Representation ℂ GaugeGroupI B} {ρ : Representation ℂ GaugeGroupI M}
    {F : Module.Dual ℂ M →ₗ[ℂ] B} (hF : ∀ g φ, repGauge g (F φ) = F (ρ.dual g φ)) :
    ∀ g : GaugeGroupI, ∀ y ∈ LinearMap.range F, repGauge g y ∈ LinearMap.range F := by
  rintro g _ ⟨φ, rfl⟩
  exact ⟨ρ.dual g φ, (hF g φ).symm⟩

/-- At zero derivative slots the assignments of derivative directions form a one-element
  type, so a sum over them has a single term. -/
lemma univ_deriv_slots_zero (l : Fin 0 → Fin 1 ⊕ Fin 3) :
    (Finset.univ : Finset (Fin 0 → Fin 1 ⊕ Fin 3)) = {l} :=
  Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.mem_univ l, fun x _ => Subsingleton.elim x l⟩

/-- The range of an underived symbol map is carried into itself by the Lorentz group: with
  no derivative slots to mix, the transformation law moves the dual vector alone. -/
lemma isStableUnder_range_repLorentz {M : Type} [AddCommGroup M] [Module ℂ M]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {ρ : Representation ℂ SL(2,ℂ) M}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ M →ₗ[ℂ] B}
    (hF : IsLorentzCovDerivTransforms repLorentz ρ F) (Λ : SL(2,ℂ)) :
    ∀ y ∈ LinearMap.range (F (![] : Fin 0 → Fin 1 ⊕ Fin 3)),
      repLorentz Λ y ∈ LinearMap.range (F (![] : Fin 0 → Fin 1 ⊕ Fin 3)) := by
  rintro _ ⟨φ, rfl⟩
  rw [hF Λ 0 ![] φ, univ_deriv_slots_zero (![] : Fin 0 → Fin 1 ⊕ Fin 3),
    Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  exact ⟨ρ.dual Λ φ, rfl⟩

/-- A product of two stable submodules is stable, the maps of the family respecting
  multiplication. -/
lemma IsStableUnder.mul {G : Type*} {σ : G → B →ₗ[ℂ] B}
    (hσ : ∀ g (a b : B), σ g (a * b) = σ g a * σ g b) {V V' : Submodule ℂ B}
    (hV : IsStableUnder σ V) (hV' : IsStableUnder σ V') : IsStableUnder σ (V * V') :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    show σ g (a * b) ∈ V * V'
    rw [hσ]
    exact Submodule.mul_mem_mul (hV g a ha) (hV' g b hb)

end Bridges

end StandardModel
