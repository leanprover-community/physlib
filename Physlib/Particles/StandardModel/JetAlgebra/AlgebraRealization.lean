/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.TransformsIn
public import Physlib.Particles.StandardModel.AlgebraRealization.MassWeight.Filtration
/-!
# The jet algebra of the Standard Model is a Standard Model

## i. Overview

The abstract theory of `AlgebraRealization` asks an algebra for an equivariant algebra map out
of the jet algebra of the Standard Model. The jet algebra therefore carries one for free —
the identity — and `JetAlgebra.algebraRealization` records it. The four compatibility laws are
definitional; the two multiplicativity laws are the ones the jet gauge action and the
Lorentz action were shown to satisfy when they were built.

That is the whole of section A. Once the instance exists, two things follow that make it
worth having. The field algebra it generates is the whole algebra — the fields of the
Standard Model generate the algebra in which its Lagrangian lives, since nothing else is
available to write down — so the mass-weight submodules stop being intersections with the
field algebra and become the honest eigenspaces of `massWeightPoly` on the whole of
`JetAlgebra`, and are worth defining on `JetAlgebra` directly.

And then the classification of invariants of mass dimension at most four applies to *every*
element of the algebra of that dimension, with no side condition left to check. That is
the result this whole chain of files exists for, and section C states it: for an arbitrary
`x : JetAlgebra` of mass weight at most eight,

`x` is fixed by the jet gauge group and by the Lorentz group
  ↔ `x` is a combination of the constant term, the Higgs mass term `H† H`, and the
    dimension-four Standard Model Lagrangian.

Nothing is assumed of `x` beyond its mass weight: not membership of a subalgebra, not
covariance, not a bound of the form `0 < w`. Every hypothesis of the abstract statement has
discharged against the concrete algebra. The `⊔ S` form, which sets aside a submodule of
higher-dimension operators, follows as a generalization for a reader who wants one.

## ii. Key results

- `JetAlgebra.mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian` : the theorem
  the chain exists for. For every element of the jet algebra of mass weight at most eight
  — with no other hypothesis of any kind — invariance under the jet gauge group and the
  Lorentz group holds exactly when the element is a combination of the constant term, the
  Higgs mass term `H† H`, and the dimension-four Standard Model Lagrangian.
- `JetAlgebra.mem_massWeightSubmoduleLE_eight_sup_and_invariant_iff_lagrangian` : the same
  classification modulo a submodule of higher-dimension operators set aside.
- `JetAlgebra.algebraRealization` : the jet algebra of the Standard Model is a Standard Model.
- `JetAlgebra.algebraRealization_fieldAlgebra_eq_top` : its field algebra is everything.
- `JetAlgebra.massWeightSubmodule`, `JetAlgebra.massWeightSubmoduleLE` : the mass-weight
  grading and its filtration, on the jet algebra itself.

## iii. Table of contents

- A. The Standard Model instance
- B. The field algebra is everything
  - B.1. The field algebra
  - B.2. The collapse of the graded pieces
  - B.3. The mass-weight filtration of the jet algebra
- C. The Standard Model Lagrangian

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

namespace JetAlgebra

open TensorProduct Matrix MatrixGroups Lorentz

/-!

## A. The Standard Model instance

The abstract theory `AlgebraRealization` is written in terms of an equivariant algebra map out
of the jet algebra, so the jet algebra is a Standard Model along the identity map. The four
compatibility laws hold by definition, and the two multiplicativity laws are the ones the
jet gauge action and the Lorentz action were shown to satisfy when they were built.

-/

/-- The jet algebra of the Standard Model is a Standard Model: it is one along the identity
  algebra map, since `AlgebraRealization` asks precisely for an equivariant algebra map out of
  the jet algebra.

  This is the point at which the abstract theory of `AlgebraRealization` — its covariant
  reduction, its mass-weight filtration and its classification of invariants — becomes a
  theory of the concrete algebra in which a Standard Model Lagrangian is written. -/
noncomputable def algebraRealization : AlgebraRealization JetAlgebra repJetGaugeGroupI repLorentzGroup
    massWeightPoly where
  toAlgHom := AlgHom.id ℂ JetAlgebra
  map_repJet _ _ := rfl
  map_repLorentz _ _ := rfl
  map_massWeight x := by
    simp [Polynomial.mapAlgHom]
  repJet_mul := isGaugeField.gauge_mul
  repLorentz_mul := repLorentzGroup_apply_mul

/-!

## B. The field algebra is everything

The field algebra of an `AlgebraRealization` is the algebra generated by the thirteen families
of derivative symbols. On the jet algebra it is everything: a Standard Model Lagrangian
lives in an algebra in which there is nothing to write down but the fields and their
derivatives.

The consequence is that the mass-weight filtration simplifies. The graded piece
`AlgebraRealization.massWeightSubmodule n` is by definition the intersection of the field
algebra with the kernel of `massWeightPoly - X ^ n`; with the field algebra the whole
algebra the intersection is idle, and what is left is the honest weight-`n` eigenspace of
`massWeightPoly` on the whole algebra. That collapse is section B.2, stated for an
arbitrary `AlgebraRealization` whose field algebra is everything.

The weight pieces and the filtration are therefore worth having on `JetAlgebra` directly,
with no mention of an `AlgebraRealization` instance, and section B.3 gives them: a reader of
the classification of section C should not have to know that an instance exists. They are
defined by the eigenvalue equation rather than as a kernel because `Polynomial JetAlgebra`
carries no synthesizable `Ring` instance — the search does not close at this concrete
type — so the subtraction `massWeightPoly - X ^ n` can only be written at an abstract type.
The bridges of section B.3 identify the two.

-/

/-!

### B.1. The field algebra

-/

/-- The fields of the Standard Model generate its jet algebra: the field algebra of the
  instance is the whole of `JetAlgebra`. -/
theorem algebraRealization_fieldAlgebra_eq_top : algebraRealization.fieldAlgebra = ⊤ :=
  adjoin_generators_eq_top

end JetAlgebra

/-!

### B.2. The collapse of the graded pieces

-/

namespace AlgebraRealization

open TensorProduct Matrix MatrixGroups Lorentz

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-- When the field algebra is everything the graded piece of mass weight `n` is the
  weight-`n` eigenspace of `massWeightPoly` on the whole algebra: the intersection with the
  field algebra in the definition of `massWeightSubmodule` cuts nothing away. -/
theorem massWeightSubmodule_eq_ker (htop : h.fieldAlgebra = ⊤) (n : ℕ) :
    h.massWeightSubmodule n
      = LinearMap.ker (massWeightPoly.toLinearMap
        - (Polynomial.monomial n : B →ₗ[B] Polynomial B).restrictScalars ℂ) := by
  show h.fieldAlgebra.toSubmodule ⊓ _ = _
  rw [htop, Algebra.top_toSubmodule, top_inf_eq]

/-- When the field algebra is everything the filtration by mass weight at most `w` is the
  join of the eigenspaces of `massWeightPoly` of weight `0` through `w`, taken over the
  whole algebra. -/
theorem massWeightSubmoduleLE_eq_iSup_ker (htop : h.fieldAlgebra = ⊤) (w : ℕ) :
    h.massWeightSubmoduleLE w
      = ⨆ k ∈ Finset.range (w + 1), LinearMap.ker (massWeightPoly.toLinearMap
          - (Polynomial.monomial k : B →ₗ[B] Polynomial B).restrictScalars ℂ) :=
  iSup_congr fun k => iSup_congr fun _ => h.massWeightSubmodule_eq_ker htop k

end AlgebraRealization

namespace JetAlgebra

open TensorProduct Matrix MatrixGroups Lorentz

/-!

### B.3. The mass-weight filtration of the jet algebra

-/

/-- The weight-`n` piece of the jet algebra, defined on the algebra itself: the eigenspace
  on which `massWeightPoly` is the monomial `X ^ n`. Nothing about `AlgebraRealization` enters
  the definition; that it agrees with the instance's graded piece is
  `algebraRealization_massWeightSubmodule`. -/
noncomputable def massWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra where
  carrier := {x | massWeightPoly x = Polynomial.monomial n x}
  zero_mem' := by simp
  add_mem' hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx, hy, map_add]
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, hx, ← Polynomial.smul_monomial]

/-- Membership of the weight-`n` piece is the eigenvalue equation. -/
@[simp]
lemma mem_massWeightSubmodule {n : ℕ} {x : JetAlgebra} :
    x ∈ massWeightSubmodule n ↔ massWeightPoly x = Polynomial.monomial n x := Iff.rfl

/-- The mass-weight filtration of the jet algebra, defined on the algebra itself: the join
  of the weight pieces of weight at most `w`. An element lies in it exactly when it is a
  sum of eigenvectors of `massWeightPoly` of weight at most `w`. -/
noncomputable def massWeightSubmoduleLE (w : ℕ) : Submodule ℂ JetAlgebra :=
  ⨆ k ∈ Finset.range (w + 1), massWeightSubmodule k

/-- The graded piece defined on the jet algebra is the graded piece of the instance: the
  two differ only by the intersection with the field algebra, which is everything. -/
lemma algebraRealization_massWeightSubmodule (n : ℕ) :
    algebraRealization.massWeightSubmodule n = massWeightSubmodule n := by
  rw [algebraRealization.massWeightSubmodule_eq_ker algebraRealization_fieldAlgebra_eq_top]
  ext x
  rw [LinearMap.mem_ker, mem_massWeightSubmodule]
  simp [sub_eq_zero]

/-- The filtration defined on the jet algebra is the filtration of the instance. -/
lemma algebraRealization_massWeightSubmoduleLE (w : ℕ) :
    algebraRealization.massWeightSubmoduleLE w = massWeightSubmoduleLE w := by
  show ⨆ k ∈ Finset.range (w + 1), algebraRealization.massWeightSubmodule k = _
  exact iSup_congr fun k => iSup_congr fun _ => algebraRealization_massWeightSubmodule k

/-!

## C. The Standard Model Lagrangian

This is what the chain was built for, and the first theorem below is the headline. Take
any element `x` of the jet algebra of mass weight at most eight — that is, of mass
dimension at most four; by section B that is a condition on `x` alone, and it is the only
hypothesis there is. Then `x` is invariant under the jet gauge group and under the Lorentz
group if and only if it is a combination of

* the constant term, of mass dimension zero;
* the Higgs mass term `H† H`, of mass dimension two;
* and the dimension-four Standard Model Lagrangian — the gauge kinetic and theta terms of
  the three gauge groups, the Higgs kinetic term, its quartic potential and its two box
  terms, the kinetic terms of the ten fermion species over the nine family pairs, and the
  six Yukawa couplings over the nine family pairs —

and nothing else. No further term of dimension four is invariant, and none of these is
forced to vanish.

The second theorem is the same classification with a submodule `S` set aside — the
operators of mass dimension above four, for a reader who wants to work modulo them. It is
strictly more general and strictly less readable, which is why it comes second. It keeps its
hypothesis `hScov : S ≤ covAlgebra.toSubmodule`, and that is not an oversight of the
simplification of section B. The field algebra is everything, but the covariant subalgebra
is not: a covariant element is fixed by the pure gauge jets, while the gauge potential
picks up the Maurer–Cartan shift and so is not. `covAlgebra` therefore stays a proper
subalgebra of `JetAlgebra`, and a set-aside `S` still has to be written in the covariant
towers for the classification to say anything about it.

-/

/-- The invariant content of the Standard Model up to mass dimension four, on the jet
  algebra of the Standard Model itself, with nothing set aside. An element of mass weight
  at most eight is fixed by the jet gauge group and by the Lorentz group exactly when it is
  a combination of the constant term, the Higgs mass term `H† H`, and the Standard Model
  Lagrangian of mass dimension four: the gauge kinetic and theta terms
  (`IsGaugeSector.lorentzContractionEightSpan`), the Higgs kinetic term, quartic potential
  and box terms (`IsHiggsSector.lorentzContractionEightSpan`), the fermion kinetic terms
  (`IsFermionSector.kineticSpan`) and the Yukawa couplings (`yukawaSpan`) — and nothing
  else.

  There are no other hypotheses. The mass-weight condition is a condition on `x` alone: by
  `mem_massWeightSubmodule` it says that `x` is a sum of eigenvectors of `massWeightPoly`
  of weight at most eight, with no demand that `x` lie in any subalgebra. -/
theorem mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian (x : JetAlgebra) :
    (x ∈ massWeightSubmoduleLE 8
        ∧ (∀ U : JetGaugeGroupI, repJetGaugeGroupI U x = x)
        ∧ ∀ Λ : SL(2,ℂ), repLorentzGroup Λ x = x)
      ↔ x ∈ 1
          ⊔ (algebraRealization.isCovStandardModel.isHiggsSector.dotSpan 0 0
            ⊔ (algebraRealization.isCovStandardModel.isGaugeSector.lorentzContractionEightSpan
                ⊔ algebraRealization.isCovStandardModel.isHiggsSector.lorentzContractionEightSpan
              ⊔ (algebraRealization.isCovStandardModel.isFermionSector.kineticSpan
                ⊔ algebraRealization.isCovStandardModel.yukawaSpan))) := by
  rw [← algebraRealization_massWeightSubmoduleLE]
  exact algebraRealization.mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian x

set_option maxHeartbeats 40000000 in
/-- The same classification as
  `mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian`, with a submodule `S` set
  aside — the operators of mass dimension above four, say. An element of
  `massWeightSubmoduleLE 8 ⊔ S` is fixed by the jet gauge group and the Lorentz group
  exactly when it is the Standard Model Lagrangian, the Higgs mass term and a constant, up
  to a remainder in `S` fixed by both groups.

  The hypothesis `hScov` does not disappear when the field algebra becomes everything: the
  covariant subalgebra `covAlgebra` remains a proper subalgebra, because a covariant
  element is fixed by the pure gauge jets whereas the gauge potential picks up the
  Maurer–Cartan shift. A set-aside `S` therefore still has to be written in the covariant
  towers, which is the case of interest — higher-dimension operators are built from
  covariant derivatives and the field strength. -/
theorem mem_massWeightSubmoduleLE_eight_sup_and_invariant_iff_lagrangian
    (S : Submodule ℂ JetAlgebra)
    (hS : ∀ U : JetGaugeGroupI, ∀ y ∈ S, repJetGaugeGroupI U y ∈ S)
    (hSL : ∀ Λ : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup Λ y ∈ S)
    (hScov : S ≤ algebraRealization.covAlgebra.toSubmodule) (x : JetAlgebra) :
    (x ∈ massWeightSubmoduleLE 8 ⊔ S
        ∧ (∀ U : JetGaugeGroupI, repJetGaugeGroupI U x = x)
        ∧ ∀ Λ : SL(2,ℂ), repLorentzGroup Λ x = x)
      ↔ ∃ y ∈ S, (∀ U : JetGaugeGroupI, repJetGaugeGroupI U y = y)
          ∧ (∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y)
          ∧ x - y ∈ 1
            ⊔ (algebraRealization.isCovStandardModel.isHiggsSector.dotSpan 0 0
              ⊔ (algebraRealization.isCovStandardModel.isGaugeSector.lorentzContractionEightSpan
                  ⊔ algebraRealization.isCovStandardModel.isHiggsSector.lorentzContractionEightSpan
                ⊔ (algebraRealization.isCovStandardModel.isFermionSector.kineticSpan
                  ⊔ algebraRealization.isCovStandardModel.yukawaSpan))) := by
  rw [← algebraRealization_massWeightSubmoduleLE]
  exact algebraRealization.mem_massWeightSubmoduleLE_eight_sup_and_invariant_iff_lagrangian
    S hS hSL hScov x

end JetAlgebra

end StandardModel
