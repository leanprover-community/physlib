/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Generators
public import Physlib.Particles.StandardModel.Fermions.JetAlgebra.Species
/-!
# The field algebra of the Standard Model is everything

## i. Overview

The thirteen generator families of `JetAlgebra.Generators` — the gauge field, the Higgs and
its conjugate, and the five fermion species in three generations each with a conjugate —
generate the whole jet algebra of the Standard Model. Physically: every element of the
algebra in which a Standard Model Lagrangian lives is a polynomial in the fields and their
derivatives, because there is nothing else to write down.

The set adjoined is `JetAlgebra.generators`, written to match the body of
`AlgebraRealization.fieldAlgebra` verbatim, so that once the `AlgebraRealization` instance on the
jet algebra exists the two are identified by `rfl`.

The proof factors along the two tensor products. `Algebra.TensorProduct.adjoin_tmul_eq_top`
reduces the whole algebra to its pure tensors, and a pure tensor is the product of the
three sector inclusions applied to its factors; so it is enough that each sector inclusion
lands in the adjoined algebra. Each of those is the sector's own generation theorem —
`FermionicAlgebra.adjoin_iteratedJetDeriv_eq_top`, its bosonic counterpart, and
`GaugeJetAlgebra.adjoin_iteratedJetDeriv_eq_top` — pushed through the inclusion.

Two things do not come for free. The fermion families are indexed by covectors on the
*individual species*, while the fermionic generation theorem produces every covector on the
total target space `FermionSpace`; the gap is closed by
`FermionSpace.span_speciesDual_eq_top`, which says the pulled-back covectors span. And the
gauge sector's generation theorem is a statement over `ℝ` about `GaugeJetAlgebra`, whereas
the gauge tensor factor is the complexification `ℂ ⊗[ℝ] GaugeJetAlgebra`; the extra complex
scalar is supplied by the algebra map, since `z ⊗ₜ x = (z ⊗ₜ 1) * (1 ⊗ₜ x)` and the first
factor is the image of `z` under `algebraMap`.

## ii. Key results

- `JetAlgebra.generators` : the derivative symbols of every field of the Standard Model.
- `JetAlgebra.adjoin_generators_eq_top` : they generate the whole jet algebra.

## iii. Table of contents

- A. The generating set
  - A.1. Membership of the generating set
- B. The three sectors lie in the generated algebra
  - B.1. Adjoining through an algebra map
  - B.2. The Higgs sector
  - B.3. The fermionic sector
  - B.4. The gauge sector
- C. The generation theorem

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

namespace JetAlgebra

open TensorProduct Matrix MatrixGroups

/-!

## A. The generating set

-/

/-- The derivative symbols of every field of the Standard Model: the gauge field, the Higgs
  and its conjugate, and the three generations of each of the five fermion species with
  their conjugates. The set is written in exactly the shape of the body of
  `AlgebraRealization.fieldAlgebra`, so that the field algebra of the eventual
  `AlgebraRealization` instance on the jet algebra is this set adjoined. -/
noncomputable def generators : Set JetAlgebra :=
  (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (gaugeField s μ)) ∪
    (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)),
      Set.range (higgsField s) ∪ Set.range (conjHiggsField s)) ∪
    (⋃ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)),
      Set.range (downSingletField i s) ∪ Set.range (conjDownSingletField i s) ∪
      Set.range (upSingletField i s) ∪ Set.range (conjUpSingletField i s) ∪
      Set.range (quarkDoubletField i s) ∪ Set.range (conjQuarkDoubletField i s) ∪
      Set.range (leptonDoubletField i s) ∪ Set.range (conjLeptonDoubletField i s) ∪
      Set.range (leptonSingletField i s) ∪ Set.range (conjLeptonSingletField i s))

/-!

### A.1. Membership of the generating set

-/

/-- The gauge-field symbols are generators. -/
lemma gaugeField_mem_generators (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : gaugeField s μ φ ∈ generators :=
  Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨μ, ⟨φ, rfl⟩⟩⟩))

/-- The Higgs symbols are generators. -/
lemma higgsField_mem_generators (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ HiggsVec) : higgsField s φ ∈ generators :=
  Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl ⟨φ, rfl⟩⟩))

/-- The conjugate Higgs symbols are generators. -/
lemma conjHiggsField_mem_generators (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) : conjHiggsField s φ ∈ generators :=
  Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inr ⟨φ, rfl⟩⟩))

/-- The symbols of the `i`-th generation down-type quark singlet are
  generators. -/
lemma downSingletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) : downSingletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨φ, rfl⟩)))))))))⟩⟩)

/-- The conjugate symbols of the `i`-th generation down-type quark singlet are
  generators. -/
lemma conjDownSingletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) : conjDownSingletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩))))))))⟩⟩)

/-- The symbols of the `i`-th generation up-type quark singlet are
  generators. -/
lemma upSingletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet) : upSingletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩)))))))⟩⟩)

/-- The conjugate symbols of the `i`-th generation up-type quark singlet are
  generators. -/
lemma conjUpSingletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) : conjUpSingletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩))))))⟩⟩)

/-- The symbols of the `i`-th generation quark doublet are
  generators. -/
lemma quarkDoubletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) : quarkDoubletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩)))))⟩⟩)

/-- The conjugate symbols of the `i`-th generation quark doublet are
  generators. -/
lemma conjQuarkDoubletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) : conjQuarkDoubletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩))))⟩⟩)

/-- The symbols of the `i`-th generation lepton doublet are
  generators. -/
lemma leptonDoubletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet) : leptonDoubletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩)))⟩⟩)

/-- The conjugate symbols of the `i`-th generation lepton doublet are
  generators. -/
lemma conjLeptonDoubletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) : conjLeptonDoubletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inl (Or.inr ⟨φ, rfl⟩))⟩⟩)

/-- The symbols of the `i`-th generation charged-lepton singlet are
  generators. -/
lemma leptonSingletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonSinglet) : leptonSingletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inl (Or.inr ⟨φ, rfl⟩)⟩⟩)

/-- The conjugate symbols of the `i`-th generation charged-lepton singlet are
  generators. -/
lemma conjLeptonSingletField_mem_generators (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) : conjLeptonSingletField i s φ ∈ generators :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
    Or.inr ⟨φ, rfl⟩⟩⟩)

/-!

## B. The three sectors lie in the generated algebra

-/

/-!

### B.1. Adjoining through an algebra map

-/

/-- If a set generates an algebra, then every image of that algebra under an algebra map
  lies in any subalgebra of the target containing the image of the generating set. This is
  the step that transports each sector's own generation theorem into the jet algebra. -/
private lemma mem_of_adjoin_eq_top {R A B : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] (f : A →ₐ[R] B) {T : Set A}
    (hT : Algebra.adjoin R T = ⊤) {C : Subalgebra R B} (hfT : f '' T ⊆ (C : Set B))
    (x : A) : f x ∈ C := by
  have hmap : (Algebra.adjoin R T).map f ≤ C := by
    rw [AlgHom.map_adjoin]
    exact Algebra.adjoin_le hfT
  refine hmap ⟨x, ?_, rfl⟩
  rw [hT]
  exact Algebra.mem_top

/-!

### B.2. The Higgs sector

-/

/-- A Higgs symbol is the Higgs sector's own derivative symbol, included. -/
lemma higgsField_eq_includeHiggs (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ HiggsVec) :
    higgsField s φ
      = includeHiggs (BosonicAlgebra.iteratedJetDeriv s (BosonicAlgebra.ofField φ)) := by
  rw [higgsField_apply, BosonicAlgebra.iteratedJetDeriv_ofField]

/-- A conjugate Higgs symbol is the Higgs sector's own conjugate derivative symbol,
  included. -/
lemma conjHiggsField_eq_includeHiggs (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    conjHiggsField s φ
      = includeHiggs (BosonicAlgebra.iteratedJetDeriv s
          (BosonicAlgebra.ofConjField φ)) := by
  rw [conjHiggsField_apply, BosonicAlgebra.iteratedJetDeriv_ofConjField]

/-- Every element of the Higgs sector lies in the algebra generated by the symbols: the
  Higgs jet algebra is generated by the Higgs field, its conjugate and their derivatives,
  and those are exactly the two Higgs families. -/
lemma includeHiggs_mem_adjoin_generators (h : HiggsJetAlgebra) :
    includeHiggs h ∈ Algebra.adjoin ℂ generators := by
  refine mem_of_adjoin_eq_top includeHiggs
    (BosonicAlgebra.adjoin_iteratedJetDeriv_eq_top (V := HiggsVec)) ?_ h
  rintro _ ⟨y, hy, rfl⟩
  rw [Set.mem_iUnion] at hy
  obtain ⟨s, hs⟩ := hy
  rcases hs with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
  · rw [← higgsField_eq_includeHiggs]
    exact Algebra.subset_adjoin (higgsField_mem_generators s φ)
  · rw [← conjHiggsField_eq_includeHiggs]
    exact Algebra.subset_adjoin (conjHiggsField_mem_generators s φ)

/-!

### B.3. The fermionic sector

The fermionic generation theorem produces the symbols of every covector on the total target
space `FermionSpace`, while the ten families supply only the covectors pulled back from a
single species and generation. Those span, by `FermionSpace.span_speciesDual_eq_top`, and
the symbol map is linear, so the families reach every symbol.

-/

/-- A fermionic symbol is the fermionic sector's own derivative symbol, included. -/
lemma fermionSymbol_eq_includeFermion (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ FermionSpace) :
    fermionSymbol s φ
      = includeFermion (FermionicAlgebra.iteratedJetDeriv s
          (FermionicAlgebra.ofField φ)) := by
  rw [fermionSymbol_apply, FermionicAlgebra.iteratedJetDeriv_ofField]

/-- A conjugate fermionic symbol is the fermionic sector's own conjugate derivative symbol,
  included. -/
lemma conjFermionSymbol_eq_includeFermion (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule FermionSpace)) :
    conjFermionSymbol s φ
      = includeFermion (FermionicAlgebra.iteratedJetDeriv s
          (FermionicAlgebra.ofConjField φ)) := by
  rw [conjFermionSymbol_apply, FermionicAlgebra.iteratedJetDeriv_ofConjField]

/-- Every fermionic symbol lies in the generated algebra. The families give the symbols of
  the covectors pulled back from a single species and generation; those span every covector
  on the total fermionic target space, and the symbol map is linear. -/
lemma fermionSymbol_mem_adjoin_generators (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ FermionSpace) :
    fermionSymbol s φ ∈ Algebra.adjoin ℂ generators := by
  have hφ : φ ∈ Submodule.span ℂ FermionSpace.speciesDual := by
    rw [FermionSpace.span_speciesDual_eq_top]
    trivial
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
    rcases hψ with ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩
    · rw [← leptonDoubletField_eq_fermionSymbol]
      exact Algebra.subset_adjoin (leptonDoubletField_mem_generators i s χ)
    · rw [← leptonSingletField_eq_fermionSymbol]
      exact Algebra.subset_adjoin (leptonSingletField_mem_generators i s χ)
    · rw [← quarkDoubletField_eq_fermionSymbol]
      exact Algebra.subset_adjoin (quarkDoubletField_mem_generators i s χ)
    · rw [← upSingletField_eq_fermionSymbol]
      exact Algebra.subset_adjoin (upSingletField_mem_generators i s χ)
    · rw [← downSingletField_eq_fermionSymbol]
      exact Algebra.subset_adjoin (downSingletField_mem_generators i s χ)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c

/-- Every conjugate fermionic symbol lies in the generated algebra, by the conjugate form
  of the spanning argument. -/
lemma conjFermionSymbol_mem_adjoin_generators (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule FermionSpace)) :
    conjFermionSymbol s φ ∈ Algebra.adjoin ℂ generators := by
  have hφ : φ ∈ Submodule.span ℂ FermionSpace.speciesConjDual := by
    rw [FermionSpace.span_speciesConjDual_eq_top]
    trivial
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
    rcases hψ with ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩ | ⟨i, χ, rfl⟩
    · rw [← conjLeptonDoubletField_eq_conjFermionSymbol]
      exact Algebra.subset_adjoin (conjLeptonDoubletField_mem_generators i s χ)
    · rw [← conjLeptonSingletField_eq_conjFermionSymbol]
      exact Algebra.subset_adjoin (conjLeptonSingletField_mem_generators i s χ)
    · rw [← conjQuarkDoubletField_eq_conjFermionSymbol]
      exact Algebra.subset_adjoin (conjQuarkDoubletField_mem_generators i s χ)
    · rw [← conjUpSingletField_eq_conjFermionSymbol]
      exact Algebra.subset_adjoin (conjUpSingletField_mem_generators i s χ)
    · rw [← conjDownSingletField_eq_conjFermionSymbol]
      exact Algebra.subset_adjoin (conjDownSingletField_mem_generators i s χ)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c

/-- Every element of the fermionic sector lies in the algebra generated by the symbols. -/
lemma includeFermion_mem_adjoin_generators (f : FermionJetAlgebra) :
    includeFermion f ∈ Algebra.adjoin ℂ generators := by
  refine mem_of_adjoin_eq_top includeFermion
    (FermionicAlgebra.adjoin_iteratedJetDeriv_eq_top (V := FermionSpace)) ?_ f
  rintro _ ⟨y, hy, rfl⟩
  rw [Set.mem_iUnion] at hy
  obtain ⟨s, hs⟩ := hy
  rcases hs with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
  · rw [← fermionSymbol_eq_includeFermion]
    exact fermionSymbol_mem_adjoin_generators s φ
  · rw [← conjFermionSymbol_eq_includeFermion]
    exact conjFermionSymbol_mem_adjoin_generators s φ


/-!

### B.4. The gauge sector

The gauge tensor factor is the complexification `ℂ ⊗[ℝ] GaugeJetAlgebra`, while the gauge
sector's generation theorem is a statement over `ℝ` about `GaugeJetAlgebra` itself. The
real part of the factor is handled by that theorem transported along the real algebra map
`x ↦ 1 ⊗ₜ x`; the complex scalar is then supplied by `z ⊗ₜ x = (z ⊗ₜ 1) * (1 ⊗ₜ x)`, whose
first factor is the image of `z` under `algebraMap` and so lies in every subalgebra.

-/

/-- The iterated derivative of the complexification acts on a pure tensor through the
  gauge sector's own iterated derivative. -/
lemma iteratedD_complexJetDeriv_tmul (s : Multiset (Fin 1 ⊕ Fin 3)) (z : ℂ)
    (x : GaugeJetAlgebra) :
    Lorentz.iteratedD GaugeJetAlgebra.complexJetDeriv
        GaugeJetAlgebra.complexJetDeriv_comm s (z ⊗ₜ[ℝ] x)
      = z ⊗ₜ[ℝ] GaugeJetAlgebra.iteratedJetDeriv s x := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Lorentz.iteratedD_zero, GaugeJetAlgebra.iteratedJetDeriv_zero, LinearMap.id_apply,
      LinearMap.id_apply]
  | cons μ s ih =>
    rw [Lorentz.iteratedD_cons, GaugeJetAlgebra.iteratedJetDeriv_cons,
      LinearMap.comp_apply, LinearMap.comp_apply, ih,
      GaugeJetAlgebra.complexJetDeriv_tmul]

/-- The real gauge-boson jet algebra inside the jet algebra of the Standard Model: the
  inclusion of the gauge sector precomposed with the inclusion of the real part of the
  complexification. It is a map of `ℝ`-algebras, which is the level at which the gauge
  sector's generation theorem is stated. -/
noncomputable def includeGaugeReal : GaugeJetAlgebra →ₐ[ℝ] JetAlgebra :=
  (AlgHom.restrictScalars ℝ includeGauge).comp
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ) (B := GaugeJetAlgebra))

/-- The real gauge inclusion is the gauge inclusion of the pure tensor with complex part
  one. -/
@[simp]
lemma includeGaugeReal_apply (x : GaugeJetAlgebra) :
    includeGaugeReal x = includeGauge ((1 : ℂ) ⊗ₜ[ℝ] x) := rfl

/-- A gauge-field symbol is the gauge sector's own derivative symbol, included through the
  real part of the complexification. -/
lemma gaugeField_eq_includeGaugeReal (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    gaugeField s μ φ
      = includeGaugeReal (GaugeJetAlgebra.iteratedJetDeriv s
          (GaugeJetAlgebra.ofA μ φ)) := by
  rw [gaugeField_apply, includeGaugeReal_apply, GaugeJetAlgebra.gaugeField_apply,
    iteratedD_complexJetDeriv_tmul]

/-- Every element of the real gauge sector lies in the algebra generated by the symbols:
  the gauge-boson jet algebra is generated over `ℝ` by the derivative symbols of the gauge
  field, and those are the gauge family. -/
lemma includeGaugeReal_mem_adjoin_generators (x : GaugeJetAlgebra) :
    includeGaugeReal x ∈ Algebra.adjoin ℂ generators := by
  have h : includeGaugeReal x ∈ (Algebra.adjoin ℂ generators).restrictScalars ℝ := by
    refine mem_of_adjoin_eq_top includeGaugeReal
      GaugeJetAlgebra.adjoin_iteratedJetDeriv_eq_top ?_ x
    rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨s, μ, φ, rfl⟩ := hy
    rw [← gaugeField_eq_includeGaugeReal]
    exact Algebra.subset_adjoin (gaugeField_mem_generators s μ φ)
  exact h

/-- Every element of the complexified gauge sector lies in the algebra generated by the
  symbols: a pure tensor splits as a complex scalar times the image of its real part. -/
lemma includeGauge_mem_adjoin_generators (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    includeGauge y ∈ Algebra.adjoin ℂ generators := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul z x =>
    have hsplit : (z ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] GaugeJetAlgebra)
        = algebraMap ℂ (ℂ ⊗[ℝ] GaugeJetAlgebra) z * ((1 : ℂ) ⊗ₜ[ℝ] x) := by
      rw [show algebraMap ℂ (ℂ ⊗[ℝ] GaugeJetAlgebra) z
          = z ⊗ₜ[ℝ] (1 : GaugeJetAlgebra) from rfl,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, map_mul, AlgHom.commutes]
    exact mul_mem (Subalgebra.algebraMap_mem _ z)
      (includeGaugeReal_mem_adjoin_generators x)

/-!

## C. The generation theorem

-/

/-- A triple pure tensor is the product of the three factors placed in their own slots:
  the abstract statement, proved at abstract types so that it can be instantiated on the
  jet algebra without rewriting inside it. -/
private lemma tensor_tmul_tmul {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B]
    [Algebra ℂ B] [Ring C] [Algebra ℂ C] (a : A) (b : B) (c : C) :
    ((a ⊗ₜ[ℂ] (1 : B)) ⊗ₜ[ℂ] (1 : C)) * (((1 : A) ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (1 : C))
        * (((1 : A) ⊗ₜ[ℂ] (1 : B)) ⊗ₜ[ℂ] c)
      = (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- A pure tensor of the jet algebra is the product of the three sector inclusions applied
  to its factors. -/
lemma includeFermion_mul_includeHiggs_mul_includeGauge (a : FermionJetAlgebra)
    (b : HiggsJetAlgebra) (c : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    includeFermion a * includeHiggs b * includeGauge c = (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c :=
  tensor_tmul_tmul a b c

/-- Every pure tensor of the jet algebra lies in the algebra generated by the symbols. -/
lemma tmul_mem_adjoin_generators (w : FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra)
    (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    (w ⊗ₜ[ℂ] y : JetAlgebra) ∈ Algebra.adjoin ℂ generators := by
  induction w using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul]; exact zero_mem _
  | add a b ha hb => rw [TensorProduct.add_tmul]; exact add_mem ha hb
  | tmul a b =>
    rw [← includeFermion_mul_includeHiggs_mul_includeGauge]
    exact mul_mem
      (mul_mem (includeFermion_mem_adjoin_generators a)
        (includeHiggs_mem_adjoin_generators b))
      (includeGauge_mem_adjoin_generators y)

/-- The fields of the Standard Model generate its jet algebra. As a `ℂ`-algebra,
  `JetAlgebra` is adjoined by the derivative symbols of the gauge field, the Higgs and its
  conjugate, and the three generations of each of the five fermion species with their
  conjugates.

  Physically: every element of the algebra in which a Standard Model Lagrangian lives is a
  polynomial in the fields and their spacetime derivatives — nothing else is available to
  write down. Formally it is the statement that the field algebra of the eventual
  `AlgebraRealization` instance on the jet algebra is the whole of it. -/
theorem adjoin_generators_eq_top :
    Algebra.adjoin ℂ generators = (⊤ : Subalgebra ℂ JetAlgebra) := by
  refine top_le_iff.mp ?_
  rw [← Algebra.TensorProduct.adjoin_tmul_eq_top ℂ
    (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) (ℂ ⊗[ℝ] GaugeJetAlgebra)]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨w, y, rfl⟩
  exact tmul_mem_adjoin_generators w y


end JetAlgebra

end StandardModel
