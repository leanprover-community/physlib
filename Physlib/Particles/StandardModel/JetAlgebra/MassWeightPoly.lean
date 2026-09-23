/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Generators
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassWeightPoly
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.MassWeightPoly
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.MassWeightPoly
/-!
# The mass-weight polynomial on the jet algebra of the Standard Model

## i. Overview

Each of the three sectors of the jet algebra of the Standard Model carries its own
mass-weight grading: `FermionicAlgebra.massWeightPoly 3` on the fermions, whose symbols have
mass dimension `3/2`, `BosonicAlgebra.massWeightPoly 2` on the Higgs and
`LocalGaugeFieldAlgebra.complexMassWeightPoly` on the gauge bosons, whose symbols have mass
dimension one. This file assembles them into a single grading

`massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra`

and computes it on every generating family.

The assembly is two applications of the universal property of the tensor product of
algebras. Each sector grading is first transported into `Polynomial JetAlgebra` along
`Polynomial.mapAlgHom` of that sector's inclusion; the two matter gradings are then read on
the two matter factors of the carrier through the sector equivalences of
`Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic`, lifted over the matter
factor `GaugeFieldData.MatterAlgebra`, and that lift over the whole algebra. The connection
factor needs no equivalence, being the gauge sector itself. Both lifts need a commutation
side condition, and both reduce to the statistics already proved in
`Physlib.Particles.StandardModel.JetAlgebra.Generators`: two polynomials commute as soon as
their coefficients do, the Higgs sector commutes with the fermionic sector, and the gauge
sector is central.

Because each sector's generator lemma has the shape `massWeightPoly g = monomial n g` — the
generator *itself* as the coefficient — transporting it along `Polynomial.mapAlgHom` is a
single rewrite by `Polynomial.mapAlgHom_monomial`. So every generating family of the full
algebra is again a monomial eigenvector, of exactly the weight `AlgebraRealization` predicts:
`2 * (1 + |s|)` for the bosons, `3 + 2 * |s|` for the fermions.

## ii. Key results

- `JetAlgebra.massWeightPoly` : the mass-weight grading on the jet algebra of the Standard
  Model.
- `JetAlgebra.fermionFactorMassWeightPoly`, `bosonFactorMassWeightPoly` : the two matter
  sector gradings read on the two matter factors of the carrier.
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
    (q : Polynomial (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra))) :
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
    (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) →ₐ[ℂ] Polynomial JetAlgebra :=
  (Polynomial.mapAlgHom includeGauge).comp LocalGaugeFieldAlgebra.complexMassWeightPoly

/-- The fermionic grading read on the fermionic factor of the carrier: the fermionic sector
  grading, precomposed with the sector equivalence. The sector helper above keeps its own
  domain, the fermionic sector algebra; this is the map the carrier's factor needs. -/
noncomputable def fermionFactorMassWeightPoly :
    ExteriorAlgebra ℂ fieldData.FermionGenerators →ₐ[ℂ] Polynomial JetAlgebra :=
  fermionMassWeightPoly.comp fermionAlgebraEquiv.symm.toAlgHom

/-- The Higgs grading read on the bosonic factor of the carrier. -/
noncomputable def bosonFactorMassWeightPoly :
    SymmetricAlgebra ℂ fieldData.BosonGenerators →ₐ[ℂ] Polynomial JetAlgebra :=
  higgsMassWeightPoly.comp higgsAlgebraEquiv.symm.toAlgHom

lemma fermionFactorMassWeightPoly_apply (a : ExteriorAlgebra ℂ fieldData.FermionGenerators) :
    fermionFactorMassWeightPoly a
      = Polynomial.mapAlgHom includeFermion
        (FermionicAlgebra.massWeightPoly 3 (fermionAlgebraEquiv.symm a)) := rfl

lemma bosonFactorMassWeightPoly_apply (b : SymmetricAlgebra ℂ fieldData.BosonGenerators) :
    bosonFactorMassWeightPoly b
      = Polynomial.mapAlgHom includeHiggs
        (BosonicAlgebra.massWeightPoly 2 (higgsAlgebraEquiv.symm b)) := rfl

/-- The mass-weight grading on the matter factor of the jet algebra: the fermionic and
  Higgs gradings, lifted over the tensor product of the two matter factors of the carrier.
  The side condition is that the two images commute, which they do because the Higgs sector
  commutes with the fermionic sector. -/
noncomputable def matterMassWeightPoly :
    fieldData.MatterAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  Algebra.TensorProduct.lift (R := ℂ) (S := ℂ)
    (A := ExteriorAlgebra ℂ fieldData.FermionGenerators)
    (B := SymmetricAlgebra ℂ fieldData.BosonGenerators) (C := Polynomial JetAlgebra)
    fermionFactorMassWeightPoly bosonFactorMassWeightPoly fun a b =>
      commute_mapAlgHom includeFermion includeHiggs
        (fun x y => (MemHiggsSector.commute_of_memFermionSector ⟨y, rfl⟩ ⟨x, rfl⟩).symm)
        (FermionicAlgebra.massWeightPoly 3 (fermionAlgebraEquiv.symm a))
        (BosonicAlgebra.massWeightPoly 2 (higgsAlgebraEquiv.symm b))

/-- The mass-weight polynomial on the jet algebra of the Standard Model: the `ℂ`-algebra
  map sending a generator of mass weight `n` to `X ^ n` times itself, so that the
  coefficient of `X ^ n` in `massWeightPoly a` is the part of `a` of mass weight `n`. It is
  the three sector gradings lifted over the tensor product, the side condition for the
  outer lift being the centrality of the gauge sector. -/
noncomputable def massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  Algebra.TensorProduct.lift (R := ℂ) (S := ℂ)
    (A := fieldData.MatterAlgebra) (B := ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra))
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
lemma massWeightPoly_tmul (x : fieldData.MatterAlgebra)
    (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    massWeightPoly (x ⊗ₜ[ℂ] y) = matterMassWeightPoly x * gaugeMassWeightPoly y := rfl

/-- On a pure tensor the matter grading is the product of the fermionic and bosonic factor
  gradings. -/
lemma matterMassWeightPoly_tmul (a : ExteriorAlgebra ℂ fieldData.FermionGenerators)
    (b : SymmetricAlgebra ℂ fieldData.BosonGenerators) :
    matterMassWeightPoly (a ⊗ₜ[ℂ] b)
      = fermionFactorMassWeightPoly a * bosonFactorMassWeightPoly b := rfl

/-- On the fermionic factor the grading is that factor's own grading. Like every step
  below it is written as an equation chain, which never abstracts a pattern out of a goal
  mentioning the jet algebra. -/
lemma massWeightPoly_includeFermionFactor
    (a : ExteriorAlgebra ℂ fieldData.FermionGenerators) :
    massWeightPoly (fieldData.includeFermion a) = fermionFactorMassWeightPoly a :=
  (congrArg massWeightPoly (GaugeFieldData.includeFermion_apply a)).trans
    ((massWeightPoly_tmul _ _).trans
      ((congrArg₂ (fun p q : Polynomial JetAlgebra => p * q)
            ((matterMassWeightPoly_tmul a 1).trans
              (congrArg (fun q : Polynomial JetAlgebra =>
                  fermionFactorMassWeightPoly a * q)
                (map_one bosonFactorMassWeightPoly)))
            (map_one gaugeMassWeightPoly)).trans
        ((mul_one _).trans (mul_one _))))

/-- On the bosonic factor the grading is that factor's own grading. -/
lemma massWeightPoly_includeBosonFactor
    (b : SymmetricAlgebra ℂ fieldData.BosonGenerators) :
    massWeightPoly (fieldData.includeBoson b) = bosonFactorMassWeightPoly b :=
  (congrArg massWeightPoly (GaugeFieldData.includeBoson_apply b)).trans
    ((massWeightPoly_tmul _ _).trans
      ((congrArg₂ (fun p q : Polynomial JetAlgebra => p * q)
            ((matterMassWeightPoly_tmul 1 b).trans
              (congrArg (fun q : Polynomial JetAlgebra =>
                  q * bosonFactorMassWeightPoly b)
                (map_one fermionFactorMassWeightPoly)))
            (map_one gaugeMassWeightPoly)).trans
        ((mul_one _).trans (one_mul _))))

/-- On the connection factor the grading is the generic gauge-boson grading. -/
lemma massWeightPoly_includeConnection (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    massWeightPoly (fieldData.includeConnection y) = gaugeMassWeightPoly y :=
  (congrArg massWeightPoly (GaugeFieldData.includeConnection_apply y)).trans
    ((massWeightPoly_tmul _ _).trans
      ((congrArg (fun p : Polynomial JetAlgebra => p * gaugeMassWeightPoly y)
          (map_one matterMassWeightPoly)).trans (one_mul _)))

/-- On the fermionic sector the grading is the fermionic sector's own grading, pushed
  forward along the fermionic inclusion. -/
lemma massWeightPoly_includeFermion (a : FermionJetAlgebra) :
    massWeightPoly (includeFermion a)
      = Polynomial.mapAlgHom includeFermion (FermionicAlgebra.massWeightPoly 3 a) :=
  (massWeightPoly_includeFermionFactor (fermionAlgebraEquiv a)).trans
    (congrArg (fun x : FermionJetAlgebra =>
        Polynomial.mapAlgHom includeFermion (FermionicAlgebra.massWeightPoly 3 x))
      (fermionAlgebraEquiv.symm_apply_apply a))

/-- On the Higgs sector the grading is the Higgs sector's own grading, pushed forward along
  the Higgs inclusion. -/
lemma massWeightPoly_includeHiggs (h : HiggsJetAlgebra) :
    massWeightPoly (includeHiggs h)
      = Polynomial.mapAlgHom includeHiggs (BosonicAlgebra.massWeightPoly 2 h) :=
  (massWeightPoly_includeBosonFactor (higgsAlgebraEquiv h)).trans
    (congrArg (fun x : HiggsJetAlgebra =>
        Polynomial.mapAlgHom includeHiggs (BosonicAlgebra.massWeightPoly 2 x))
      (higgsAlgebraEquiv.symm_apply_apply h))

/-- On the gauge sector the grading is the gauge sector's own grading, pushed forward along
  the gauge inclusion. The gauge sector inclusion is the connection inclusion of the datum,
  so there is nothing to transport here. -/
lemma massWeightPoly_includeGauge (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    massWeightPoly (includeGauge y)
      = Polynomial.mapAlgHom includeGauge (LocalGaugeFieldAlgebra.complexMassWeightPoly y) :=
  massWeightPoly_includeConnection y

/-- The mass-weight exponent of a symbol of mass dimension one, in the two forms the
  statements below use: `AlgebraRealization` asks for `2 * (1 + |s|)`, and each sector
  grading produces `2 + 2 * |s|`. -/
private lemma monomial_two_mul_one_add (n : ℕ) (x : JetAlgebra) :
    Polynomial.monomial (2 + 2 * n) x = Polynomial.monomial (2 * (1 + n)) x :=
  congrArg (fun m => (Polynomial.monomial m) x) (by ring)

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
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (higgsField s φ) :=
  (congrArg massWeightPoly (higgsField_apply s φ)).trans
    ((massWeightPoly_includeHiggs _).trans
      ((congrArg (Polynomial.mapAlgHom includeHiggs)
            ((BosonicAlgebra.massWeightPoly_ι 2 _).trans
              (BosonicAlgebra.jetComponentPoly_inl 2 s φ))).trans
        ((Polynomial.mapAlgHom_monomial includeHiggs _ _).trans
          ((monomial_two_mul_one_add _ _).trans
            (congrArg (Polynomial.monomial (2 * (1 + Multiset.card s)))
              (higgsField_apply s φ).symm)))))

/-- The conjugate Higgs symbol `∂_s H̄_φ` is a monomial eigenvector of the same mass weight
  `2 * (1 + |s|)` as the symbol it conjugates. -/
lemma massWeightPoly_conjHiggsField (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    massWeightPoly (conjHiggsField s φ)
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (conjHiggsField s φ) :=
  (congrArg massWeightPoly (conjHiggsField_apply s φ)).trans
    ((massWeightPoly_includeHiggs _).trans
      ((congrArg (Polynomial.mapAlgHom includeHiggs)
            ((BosonicAlgebra.massWeightPoly_ι 2 _).trans
              (BosonicAlgebra.jetComponentPoly_inr 2 s φ))).trans
        ((Polynomial.mapAlgHom_monomial includeHiggs _ _).trans
          ((monomial_two_mul_one_add _ _).trans
            (congrArg (Polynomial.monomial (2 * (1 + Multiset.card s)))
              (conjHiggsField_apply s φ).symm)))))

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
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (gaugeField s μ φ) :=
  have hg : gaugeField s μ φ
      = includeGauge ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.iteratedJetDeriv GaugeAlgebra s
        (LocalGaugeFieldAlgebra.ofA GaugeAlgebra μ φ)) :=
    (gaugeField_apply s μ φ).trans
      (congrArg includeGauge
        (_root_.LocalGaugeFieldAlgebra.iteratedD_complexJetDeriv_one_tmul s
          (_root_.LocalGaugeFieldAlgebra.ofA GaugeAlgebra μ φ)))
  (congrArg massWeightPoly hg).trans
    ((massWeightPoly_includeGauge _).trans
      ((congrArg (Polynomial.mapAlgHom includeGauge)
            (LocalGaugeFieldAlgebra.complexMassWeightPoly_tmul_iteratedJetDeriv_ofA
              1 s μ φ)).trans
        ((Polynomial.mapAlgHom_monomial includeGauge _ _).trans
          ((monomial_two_mul_one_add _ _).trans
            (congrArg (Polynomial.monomial (2 * (1 + Multiset.card s))) hg.symm)))))

/-!

## F. The mass weight of the fermion symbols

Every fermion of the Standard Model has mass dimension `3/2`, so a fermionic symbol
`∂_s ψ_φ` has mass dimension `3/2 + |s|` and mass weight `3 + 2 |s|` — the exponent form
`AlgebraRealization` asks for. The computation is the same for all ten species families,
because each of them reduces, by the lemmas of
`Physlib.Particles.StandardModel.JetAlgebra.Generators`, to a fermionic symbol on the total
target space; so section F.2 is ten instantiations of section F.1 and nothing more.

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
      = Polynomial.monomial (3 + 2 * Multiset.card s) (fermionSymbol s φ) :=
  (congrArg massWeightPoly (fermionSymbol_apply s φ)).trans
    ((massWeightPoly_includeFermion _).trans
      ((congrArg (Polynomial.mapAlgHom includeFermion)
            ((FermionicAlgebra.massWeightPoly_ι 3 _).trans
              (FermionicAlgebra.jetComponentPoly_inl 3 s φ))).trans
        ((Polynomial.mapAlgHom_monomial includeFermion _ _).trans
          (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
            (fermionSymbol_apply s φ).symm))))

/-- A conjugate fermionic symbol `∂_s ψ̄_φ` on the total fermionic target space is a
  monomial eigenvector of the same mass weight `3 + 2 |s|` as the symbol it conjugates. -/
lemma massWeightPoly_conjFermionSymbol (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule FermionSpace)) :
    massWeightPoly (conjFermionSymbol s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjFermionSymbol s φ) :=
  (congrArg massWeightPoly (conjFermionSymbol_apply s φ)).trans
    ((massWeightPoly_includeFermion _).trans
      ((congrArg (Polynomial.mapAlgHom includeFermion)
            ((FermionicAlgebra.massWeightPoly_ι 3 _).trans
              (FermionicAlgebra.jetComponentPoly_inr 3 s φ))).trans
        ((Polynomial.mapAlgHom_monomial includeFermion _ _).trans
          (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
            (conjFermionSymbol_apply s φ).symm))))

/-!

### F.2. The ten species families

-/

/-- The symbol `∂_s ψ_φ` of the `i`-th generation lepton doublet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_leptonDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet) :
    massWeightPoly (leptonDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (leptonDoubletField i s φ) :=
  (congrArg massWeightPoly (leptonDoubletField_eq_fermionSymbol i s φ)).trans
    ((massWeightPoly_fermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (leptonDoubletField_eq_fermionSymbol i s φ).symm))

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation lepton doublet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjLeptonDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    massWeightPoly (conjLeptonDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjLeptonDoubletField i s φ) :=
  (congrArg massWeightPoly (conjLeptonDoubletField_eq_conjFermionSymbol i s φ)).trans
    ((massWeightPoly_conjFermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (conjLeptonDoubletField_eq_conjFermionSymbol i s φ).symm))

/-- The symbol `∂_s ψ_φ` of the `i`-th generation charged-lepton singlet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_leptonSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonSinglet) :
    massWeightPoly (leptonSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (leptonSingletField i s φ) :=
  (congrArg massWeightPoly (leptonSingletField_eq_fermionSymbol i s φ)).trans
    ((massWeightPoly_fermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (leptonSingletField_eq_fermionSymbol i s φ).symm))

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation charged-lepton singlet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjLeptonSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    massWeightPoly (conjLeptonSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjLeptonSingletField i s φ) :=
  (congrArg massWeightPoly (conjLeptonSingletField_eq_conjFermionSymbol i s φ)).trans
    ((massWeightPoly_conjFermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (conjLeptonSingletField_eq_conjFermionSymbol i s φ).symm))

/-- The symbol `∂_s ψ_φ` of the `i`-th generation quark doublet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_quarkDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) :
    massWeightPoly (quarkDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (quarkDoubletField i s φ) :=
  (congrArg massWeightPoly (quarkDoubletField_eq_fermionSymbol i s φ)).trans
    ((massWeightPoly_fermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (quarkDoubletField_eq_fermionSymbol i s φ).symm))

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation quark doublet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjQuarkDoubletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    massWeightPoly (conjQuarkDoubletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjQuarkDoubletField i s φ) :=
  (congrArg massWeightPoly (conjQuarkDoubletField_eq_conjFermionSymbol i s φ)).trans
    ((massWeightPoly_conjFermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (conjQuarkDoubletField_eq_conjFermionSymbol i s φ).symm))

/-- The symbol `∂_s ψ_φ` of the `i`-th generation up-type quark singlet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_upSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet) :
    massWeightPoly (upSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (upSingletField i s φ) :=
  (congrArg massWeightPoly (upSingletField_eq_fermionSymbol i s φ)).trans
    ((massWeightPoly_fermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (upSingletField_eq_fermionSymbol i s φ).symm))

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation up-type quark singlet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjUpSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    massWeightPoly (conjUpSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjUpSingletField i s φ) :=
  (congrArg massWeightPoly (conjUpSingletField_eq_conjFermionSymbol i s φ)).trans
    ((massWeightPoly_conjFermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (conjUpSingletField_eq_conjFermionSymbol i s φ).symm))

/-- The symbol `∂_s ψ_φ` of the `i`-th generation down-type quark singlet is a monomial eigenvector
  of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_downSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) :
    massWeightPoly (downSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (downSingletField i s φ) :=
  (congrArg massWeightPoly (downSingletField_eq_fermionSymbol i s φ)).trans
    ((massWeightPoly_fermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (downSingletField_eq_fermionSymbol i s φ).symm))

/-- The conjugate symbol `∂_s ψ̄_φ` of the `i`-th generation down-type quark singlet is a monomial
  eigenvector of mass weight `3 + 2 |s|`. -/
lemma massWeightPoly_conjDownSingletField (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    massWeightPoly (conjDownSingletField i s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (conjDownSingletField i s φ) :=
  (congrArg massWeightPoly (conjDownSingletField_eq_conjFermionSymbol i s φ)).trans
    ((massWeightPoly_conjFermionSymbol s _).trans
      (congrArg (Polynomial.monomial (3 + 2 * Multiset.card s))
        (conjDownSingletField_eq_conjFermionSymbol i s φ).symm))
end JetAlgebra

end StandardModel
