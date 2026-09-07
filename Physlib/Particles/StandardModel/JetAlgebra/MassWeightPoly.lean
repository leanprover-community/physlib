/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Generators
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassWeightPoly
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.MassWeightPoly
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.MassWeightPoly
/-!
# The mass-weight polynomial on the jet algebra of the Standard Model

## i. Overview

Each of the three sectors of the jet algebra of the Standard Model carries its own
mass-weight grading: `FermionicAlgebra.massWeightPoly 3` on the fermions, whose symbols have
mass dimension `3/2`, `BosonicAlgebra.massWeightPoly 2` on the Higgs and
`GaugeJetAlgebra.complexMassWeightPoly` on the gauge bosons, whose symbols have mass
dimension one. This file assembles them into a single grading

`massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra`

and computes it on every generating family.

The assembly is two applications of the universal property of the tensor product of
algebras. Each sector grading is first transported into `Polynomial JetAlgebra` along
`Polynomial.mapAlgHom` of that sector's inclusion; the two matter gradings are then lifted
over `FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra`, and that lift over the whole algebra. Both
lifts need a commutation side condition, and both reduce to the statistics already proved
in `Physlib.Particles.StandardModel.JetAlgebra.Generators`: two polynomials commute as soon
as their coefficients do, the Higgs sector commutes with the fermionic sector, and the
gauge sector is central.

Because each sector's generator lemma has the shape `massWeightPoly g = monomial n g` — the
generator *itself* as the coefficient — transporting it along `Polynomial.mapAlgHom` is a
single rewrite by `Polynomial.mapAlgHom_monomial`. So every generating family of the full
algebra is again a monomial eigenvector, of exactly the weight `AlgebraRealization` predicts:
`2 * (1 + |s|)` for the bosons, `3 + 2 * |s|` for the fermions.

## ii. Key results

- `JetAlgebra.massWeightPoly` : the mass-weight grading on the jet algebra of the Standard
  Model.
- `JetAlgebra.massWeightPoly_includeFermion`, `massWeightPoly_includeHiggs`,
  `massWeightPoly_includeGauge` : the grading restricted to each sector.
- `JetAlgebra.massWeightPoly_higgsField`, `massWeightPoly_gaugeField`,
  `massWeightPoly_leptonDoubletField`, … : the fifteen generator families are monomial
  eigenvectors.

## iii. Table of contents

- A. Commuting polynomials over the jet algebra
- B. The mass-weight polynomial on the jet algebra
- C. The grading through the sector inclusions
- D. The mass weight of the Higgs symbols
- E. The mass weight of the gauge-field symbols
- F. The mass weight of the fermion symbols
  - F.1. The symbols on the total fermionic target space
  - F.2. The ten species families

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

## A. Commuting polynomials over the jet algebra

The two lifts that assemble the grading each demand that the images of the two factors
commute. Both images consist of polynomials, and in both cases the commutation is already
known one coefficient at a time — so the work of this section is to promote a commutation
of coefficients to a commutation of polynomials, which is an induction over monomials.

-/

/-- Two monomials with commuting coefficients commute: the variable is central, so the two
  products are the same monomial. -/
lemma commute_monomial {C : Type*} [Semiring C] {a b : C} (h : Commute a b)
    (n m : ℕ) : Commute (Polynomial.monomial n a) (Polynomial.monomial m b) := by
  show Polynomial.monomial n a * Polynomial.monomial m b
    = Polynomial.monomial m b * Polynomial.monomial n a
  rw [Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial, h.eq,
    Nat.add_comm]

/-- Polynomials pushed forward along two algebra maps with commuting images commute: every
  polynomial is a sum of monomials, and monomials with commuting coefficients commute. -/
lemma commute_mapAlgHom {A B C : Type*} [Semiring A] [Algebra ℂ A] [Semiring B]
    [Algebra ℂ B] [Semiring C] [Algebra ℂ C] (f : A →ₐ[ℂ] C) (g : B →ₐ[ℂ] C)
    (h : ∀ (a : A) (b : B), Commute (f a) (g b)) (p : Polynomial A) (q : Polynomial B) :
    Commute (Polynomial.mapAlgHom f p) (Polynomial.mapAlgHom g q) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => rw [map_add]; exact h₁.add_left h₂
  | monomial n a =>
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
    | monomial m b =>
      rw [Polynomial.mapAlgHom_monomial, Polynomial.mapAlgHom_monomial]
      exact commute_monomial (h a b) n m

/-- Every polynomial over the jet algebra commutes with a polynomial whose coefficients lie
  in the gauge sector: the gauge sector is central, so the commutation holds coefficient by
  coefficient. -/
lemma commute_mapAlgHom_includeGauge (p : Polynomial JetAlgebra)
    (q : Polynomial (ℂ ⊗[ℝ] GaugeJetAlgebra)) :
    Commute p (Polynomial.mapAlgHom includeGauge q) := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
  | monomial m b =>
    rw [Polynomial.mapAlgHom_monomial]
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ => exact h₁.add_left h₂
    | monomial n a =>
      have hc : Commute a (includeGauge b) := includeGauge_commute b a
      exact commute_monomial hc n m

/-!

## B. The mass-weight polynomial on the jet algebra

Each sector's grading is transported into `Polynomial JetAlgebra` along
`Polynomial.mapAlgHom` of that sector's inclusion, and the three transported gradings are
assembled by the universal property of the tensor product — first over the matter factor,
then over the whole algebra.

-/

/-- The fermionic mass-weight grading, transported into the full jet algebra. The fermionic
  symbols have mass dimension `3/2`, hence mass weight three. -/
noncomputable def fermionMassWeightPoly :
    FermionJetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  (Polynomial.mapAlgHom includeFermion).comp (FermionicAlgebra.massWeightPoly 3)

/-- The Higgs mass-weight grading, transported into the full jet algebra. The Higgs symbols
  have mass dimension one, hence mass weight two. -/
noncomputable def higgsMassWeightPoly : HiggsJetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  (Polynomial.mapAlgHom includeHiggs).comp (BosonicAlgebra.massWeightPoly 2)

/-- The gauge-boson mass-weight grading, transported into the full jet algebra. The gauge
  symbols have mass dimension one, hence mass weight two. -/
noncomputable def gaugeMassWeightPoly :
    (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₐ[ℂ] Polynomial JetAlgebra :=
  (Polynomial.mapAlgHom includeGauge).comp GaugeJetAlgebra.complexMassWeightPoly

/-- The mass-weight grading on the matter factor of the jet algebra: the fermionic and
  Higgs gradings, lifted over their tensor product. The side condition is that the two
  images commute, which they do because the Higgs sector commutes with the fermionic
  sector. -/
noncomputable def matterMassWeightPoly :
    (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) →ₐ[ℂ] Polynomial JetAlgebra :=
  Algebra.TensorProduct.lift (R := ℂ) (S := ℂ) (A := FermionJetAlgebra)
    (B := HiggsJetAlgebra) (C := Polynomial JetAlgebra)
    fermionMassWeightPoly higgsMassWeightPoly fun _ _ =>
      commute_mapAlgHom _ _ (fun a b =>
        (MemHiggsSector.commute_of_memFermionSector ⟨b, rfl⟩ ⟨a, rfl⟩).symm) _ _

/-- The mass-weight polynomial on the jet algebra of the Standard Model: the `ℂ`-algebra
  map sending a generator of mass weight `n` to `X ^ n` times itself, so that the
  coefficient of `X ^ n` in `massWeightPoly a` is the part of `a` of mass weight `n`. It is
  the three sector gradings lifted over the tensor product, the side condition for the
  outer lift being the centrality of the gauge sector. -/
noncomputable def massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  Algebra.TensorProduct.lift (R := ℂ) (S := ℂ)
    (A := FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) (B := ℂ ⊗[ℝ] GaugeJetAlgebra)
    (C := Polynomial JetAlgebra) matterMassWeightPoly gaugeMassWeightPoly
    fun _ _ => commute_mapAlgHom_includeGauge _ _

/-!

## C. The grading through the sector inclusions

The lift is computed on pure tensors by construction, and each sector inclusion is a pure
tensor with ones in the other factors. So on each sector the full grading is that sector's
own grading, transported. These three lemmas are the whole content of the assembly: every
generator computation below is one of them followed by a sector generator lemma.

-/

/-- On a pure tensor the grading is the product of the matter and gauge gradings. -/
lemma massWeightPoly_tmul (x : FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra)
    (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    massWeightPoly (x ⊗ₜ[ℂ] y) = matterMassWeightPoly x * gaugeMassWeightPoly y := rfl

/-- On a pure tensor the matter grading is the product of the fermionic and Higgs
  gradings. -/
lemma matterMassWeightPoly_tmul (a : FermionJetAlgebra) (h : HiggsJetAlgebra) :
    matterMassWeightPoly (a ⊗ₜ[ℂ] h) = fermionMassWeightPoly a * higgsMassWeightPoly h :=
  rfl

/-- On the fermionic sector the grading is the fermionic sector's own grading, pushed
  forward along the fermionic inclusion. -/
lemma massWeightPoly_includeFermion (a : FermionJetAlgebra) :
    massWeightPoly (includeFermion a)
      = Polynomial.mapAlgHom includeFermion (FermionicAlgebra.massWeightPoly 3 a) := by
  rw [show includeFermion a = (a ⊗ₜ[ℂ] (1 : HiggsJetAlgebra)) ⊗ₜ[ℂ]
      (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) from rfl, massWeightPoly_tmul,
    matterMassWeightPoly_tmul, map_one, map_one, mul_one, mul_one]
  rfl

/-- On the Higgs sector the grading is the Higgs sector's own grading, pushed forward along
  the Higgs inclusion. -/
lemma massWeightPoly_includeHiggs (h : HiggsJetAlgebra) :
    massWeightPoly (includeHiggs h)
      = Polynomial.mapAlgHom includeHiggs (BosonicAlgebra.massWeightPoly 2 h) := by
  rw [show includeHiggs h = ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ]
      (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) from rfl, massWeightPoly_tmul,
    matterMassWeightPoly_tmul, map_one, map_one, mul_one, one_mul]
  rfl

/-- On the gauge sector the grading is the gauge sector's own grading, pushed forward along
  the gauge inclusion. -/
lemma massWeightPoly_includeGauge (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    massWeightPoly (includeGauge y)
      = Polynomial.mapAlgHom includeGauge (GaugeJetAlgebra.complexMassWeightPoly y) := by
  rw [show includeGauge y = ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      ⊗ₜ[ℂ] y from rfl, massWeightPoly_tmul,
    show ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (1 : FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) from rfl, map_one, one_mul]
  rfl

/-!

## D. The mass weight of the Higgs symbols

The Higgs field has mass dimension one, so the symbol `∂_s H_φ` has mass dimension
`1 + |s|` and mass weight twice that. The exponent is written in the form
`2 * (1 + |s|)` that `AlgebraRealization` asks for.

-/

/-- The Higgs symbol `∂_s H_φ` is a monomial eigenvector of mass weight `2 * (1 + |s|)`:
  the Higgs field has mass dimension one and each derivative adds one more. -/
lemma massWeightPoly_higgsField (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ HiggsVec) :
    massWeightPoly (higgsField s φ)
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (higgsField s φ) := by
  rw [show 2 * (1 + Multiset.card s) = 2 + 2 * Multiset.card s from by ring,
    higgsField_apply, massWeightPoly_includeHiggs, BosonicAlgebra.massWeightPoly_ι,
    BosonicAlgebra.jetComponentPoly_inl, Polynomial.mapAlgHom_monomial]

/-- The conjugate Higgs symbol `∂_s H̄_φ` is a monomial eigenvector of the same mass weight
  `2 * (1 + |s|)` as the symbol it conjugates. -/
lemma massWeightPoly_conjHiggsField (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    massWeightPoly (conjHiggsField s φ)
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (conjHiggsField s φ) := by
  rw [show 2 * (1 + Multiset.card s) = 2 + 2 * Multiset.card s from by ring,
    conjHiggsField_apply, massWeightPoly_includeHiggs, BosonicAlgebra.massWeightPoly_ι,
    BosonicAlgebra.jetComponentPoly_inr, Polynomial.mapAlgHom_monomial]

/-!

## E. The mass weight of the gauge-field symbols

The gauge field, like the Higgs, has mass dimension one. Its symbols reach the full jet
algebra through the complexification of the real gauge-boson jet algebra, so the
computation passes through the complexified grading of that sector.

-/

/-- The gauge-field symbol `∂_s A_μ^φ` is a monomial eigenvector of mass weight
  `2 * (1 + |s|)`: the gauge field has mass dimension one and each derivative adds one
  more. -/
lemma massWeightPoly_gaugeField (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    massWeightPoly (gaugeField s μ φ)
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (gaugeField s μ φ) := by
  rw [show 2 * (1 + Multiset.card s) = 2 + 2 * Multiset.card s from by ring,
    gaugeField_apply, GaugeJetAlgebra.gaugeField_apply,
    GaugeJetAlgebra.iteratedD_complexJetDeriv_one_tmul, massWeightPoly_includeGauge,
    GaugeJetAlgebra.complexMassWeightPoly_tmul_iteratedJetDeriv_ofA,
    Polynomial.mapAlgHom_monomial]

/-!

## F. The mass weight of the fermion symbols

Every fermion of the Standard Model has mass dimension `3/2`, so a fermionic symbol
`∂_s ψ_φ` has mass dimension `3/2 + |s|` and mass weight `3 + 2 |s|` — the exponent form
`AlgebraRealization` asks for. The computation is the same for all ten species families,
because each of them reduces, by the lemmas of
`Physlib.Particles.StandardModel.JetAlgebra.Generators`, to a single included generator of
the fermionic sector.

-/

/-!

### F.1. The symbols on the total fermionic target space

-/

/-- A fermionic symbol `∂_s ψ_φ` on the total fermionic target space is a monomial
  eigenvector of mass weight `3 + 2 |s|`: a fermion has mass dimension `3/2` and each
  derivative adds one more. -/
lemma massWeightPoly_fermionSymbol (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ FermionSpace) :
    massWeightPoly (fermionSymbol s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (fermionSymbol s φ) := by
  rw [fermionSymbol_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inl,
    Polynomial.mapAlgHom_monomial]

/-- A conjugate fermionic symbol `∂_s ψ̄_φ` on the total fermionic target space is a
  monomial eigenvector of the same mass weight `3 + 2 |s|` as the symbol it conjugates. -/
lemma massWeightPoly_conjFermionSymbol (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule FermionSpace)) :
    massWeightPoly (conjFermionSymbol s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjFermionSymbol s φ) := by
  rw [conjFermionSymbol_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inr,
    Polynomial.mapAlgHom_monomial]

/-!

### F.2. The ten species families

-/

/-- The symbol `∂_s ψ_φ` of the `i`-th generation lepton doublet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_leptonDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet) :
    massWeightPoly (leptonDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (leptonDoubletField i s φ) := by
  rw [leptonDoubletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inl,
    Polynomial.mapAlgHom_monomial]

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation lepton doublet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjLeptonDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    massWeightPoly (conjLeptonDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjLeptonDoubletField i s φ) := by
  rw [conjLeptonDoubletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inr,
    Polynomial.mapAlgHom_monomial]

/-- The symbol `∂_s ψ_φ` of the `i`-th generation charged-lepton singlet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_leptonSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonSinglet) :
    massWeightPoly (leptonSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (leptonSingletField i s φ) := by
  rw [leptonSingletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inl,
    Polynomial.mapAlgHom_monomial]

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation charged-lepton singlet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjLeptonSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    massWeightPoly (conjLeptonSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjLeptonSingletField i s φ) := by
  rw [conjLeptonSingletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inr,
    Polynomial.mapAlgHom_monomial]

/-- The symbol `∂_s ψ_φ` of the `i`-th generation quark doublet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_quarkDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) :
    massWeightPoly (quarkDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (quarkDoubletField i s φ) := by
  rw [quarkDoubletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inl,
    Polynomial.mapAlgHom_monomial]

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation quark doublet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjQuarkDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    massWeightPoly (conjQuarkDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjQuarkDoubletField i s φ) := by
  rw [conjQuarkDoubletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inr,
    Polynomial.mapAlgHom_monomial]

/-- The symbol `∂_s ψ_φ` of the `i`-th generation up-type quark singlet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_upSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet) :
    massWeightPoly (upSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (upSingletField i s φ) := by
  rw [upSingletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inl,
    Polynomial.mapAlgHom_monomial]

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation up-type quark singlet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjUpSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    massWeightPoly (conjUpSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjUpSingletField i s φ) := by
  rw [conjUpSingletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inr,
    Polynomial.mapAlgHom_monomial]

/-- The symbol `∂_s ψ_φ` of the `i`-th generation down-type quark singlet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_downSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) :
    massWeightPoly (downSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (downSingletField i s φ) := by
  rw [downSingletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inl,
    Polynomial.mapAlgHom_monomial]

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation down-type quark singlet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjDownSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    massWeightPoly (conjDownSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjDownSingletField i s φ) := by
  rw [conjDownSingletField_apply, massWeightPoly_includeFermion,
    FermionicAlgebra.massWeightPoly_ι, FermionicAlgebra.jetComponentPoly_inr,
    Polynomial.mapAlgHom_monomial]

end JetAlgebra

end StandardModel
