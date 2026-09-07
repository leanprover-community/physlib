/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Electromagnetism.Kinematics.GaugeTransformation
public import Physlib.Electromagnetism.Dynamics.KineticTerm
public import Physlib.Relativity.SL2C.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.TrivSqZeroExt.Basic
/-!
# The jet algebras of quantum electrodynamics

## i. Overview

This file contains *all the definitions* of the jet-algebra formulation of
quantum electrodynamics: the jet algebras of the photon and of the Dirac
electron, their tensor product — the QED jet algebra — the data of a gauge
transformation as seen by jets, the gauge actions on all three algebras, and
the evaluation of the photon jet algebra on an honest electromagnetic
potential.

The *fields* of QED (the jet coordinates, the field strength, the γ matrices
and the covariant derivatives) are defined on top of these algebras in
`Physlib.Particles.QED.Fields`, and the Lagrangian in `Physlib.Particles.QED.Lagrangian`.  All
theorems about them are proved in the definition-free files
`Physlib.Particles.QED.FermionStatistics`, `Physlib.Particles.QED.FieldStrength`,
`Physlib.Particles.QED.GammaMatrices`, `Physlib.Particles.QED.GaugeInvariance` and
`Physlib.Particles.QED.Evaluation`.

The design choices:

* The photon jet algebra is the free commutative algebra on formal symbols
  `∂_s A_μ`, one for every multiset `s` of spacetime directions and every
  Lorentz index `μ`, built directly on the electromagnetic potential of
  `Physlib.Electromagnetism`.  It deliberately does *not* use
  `Physlib.Particles.StandardModel.GaugeBosons.BBoson`: the `B` boson is the
  gauge boson of `U(1)_Y` before electroweak symmetry breaking, the photon is
  the mixed combination `A = cos θ_W B + sin θ_W W³`, and the two are not the
  same field.  Building directly on `ElectromagneticPotential` also avoids
  inheriting the Standard Model charge normalisation `6Y`, which has no
  meaning for `U(1)_em`.

* The electron jet algebra is the free *exterior* algebra on formal symbols
  `∂_s ψ_α`, `∂_s ψ̄_α` with `α : Fin 2 ⊕ Fin 2` a Dirac index in the chiral
  representation; the exterior product implements fermionic statistics.  A
  faithful QED matter sector needs a *Dirac* electron — equivalently two Weyl
  spinors of the same chirality with charges `±1` — which is what makes the
  dimension-three mass term `m ψ̄ ψ` possible; a single Weyl fermion admits no
  such term.

* A gauge transformation is recorded by its jets: the derivative jets
  `∂_s χ` of the real gauge function together with the derivative jets
  `∂_s (exp (I e χ))` of its unitary phase, related by the formal Leibniz
  identity `∂_μ u = I e (∂_μ χ) u`.  The action on the photon coordinates is
  the affine shift `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`, and on the electron
  coordinates the Leibniz expansion of `∂_s (ū ψ)` over
  `Multiset.antidiagonal s`, whose multiplicities are exactly the multinomial
  coefficients of the Leibniz rule.

This construction mirrors `Physlib.Particles.LeptonGaugeSector`, where the
analogous algebra for a single charged Weyl fermion is built from
representation-theoretic data.

## ii. Key results

- `Photon.JetGenerators`, `Photon.JetAlgebra`, `Photon.JetAlgebra.coord` :
  the photon jet coordinates `∂_s A_μ` and their polynomial algebra.
- `Photon.JetAlgebra.gaugeAction` : the affine gauge action on the photon jet
  algebra.
- `Photon.JetAlgebra.evalPotential` : the evaluation of the photon jet
  algebra on an electromagnetic potential.
- `GaugeJet` : the jets of a `U(1)_em` gauge transformation with coupling `e`.
- `Electron.JetGenerators`, `Electron.JetAlgebra` : the electron jet
  coordinates `∂_s ψ_α`, `∂_s ψ̄_α` and their exterior algebra.
- `Electron.JetAlgebra.gaugeAction` : the Leibniz gauge action on the
  electron jet algebra.
- `JetAlgebra` : the QED jet algebra, the tensor product of the complexified
  photon jet algebra with the electron jet algebra.
- `JetAlgebra.gaugeAction` : the gauge action on the QED jet algebra.
- `JetAlgebra.lorentzAction` : the Lorentz action on the QED jet algebra,
  through the covering map `Lorentz.SL2C.toLorentzGroup` on the photon factor
  and the Dirac spinor representation `Electron.JetAlgebra.spinorRep` on the
  electron factor.
- `JetAlgebra.massScale` : the mass-weight scaling on the QED jet algebra.

## iii. Table of contents

- 0. Transport of derivative indices along a Lorentz transformation
- A. The jet algebra of the photon
  - A.1. The jet coordinates
  - A.2. The gauge action on the photon jet algebra
  - A.3. Iterated derivatives indexed by a multiset
  - A.4. Evaluation on a potential
  - A.5. The Lorentz action on the photon jet algebra
  - A.6. The mass-weight scaling on the photon jet algebra
- B. The gauge jet of a `U(1)_em` transformation
  - B.1. Low-order consequences of the Leibniz identity
- C. The jet algebra of the electron
  - C.1. The jet coordinates
  - C.2. The gauge action on the electron jet algebra
  - C.3. The action on the low-order jet coordinates
  - C.4. The Lorentz action on the electron jet algebra
  - C.5. The mass-weight scaling on the electron jet algebra
- D. The jet algebra of QED
  - D.1. Pure tensors and their arithmetic
  - D.2. The inclusions of the two factors
  - D.3. The gauge action on the QED jet algebra
  - D.4. The Lorentz action on the QED jet algebra
  - D.5. The mass-weight scaling on the QED jet algebra

## iv. References

The concrete electromagnetic side is
`Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean` and
`Physlib/Electromagnetism/Dynamics/KineticTerm.lean`.

-/

@[expose] public section

namespace QED

open Electromagnetism SpaceTime minkowskiMatrix TensorProduct
open Matrix MatrixGroups

/-!

## 0. Transport of derivative indices along a Lorentz transformation

A jet coordinate carries a multiset of derivative indices, each of which
transforms with `Λ⁻¹` under a Lorentz transformation (the chain rule for
`x ↦ Λ⁻¹ x`).  To sum over the transformed indices without summing over
functions on a multiset, the transport recurses along the *canonical sorted
list* of the multiset, threading the chosen indices through a continuation.

-/

/-- The canonical sorted list of a multiset of spacetime directions, sorted
  through `Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
noncomputable def indexList (s : Multiset (Fin 1 ⊕ Fin 3)) : List (Fin 1 ⊕ Fin 3) :=
  ((s.map (finSumFinEquiv (m := 1) (n := 3))).sort).map
    (finSumFinEquiv (m := 1) (n := 3)).symm

@[simp]
lemma indexList_zero : indexList 0 = [] := by
  simp [indexList]

@[simp]
lemma indexList_singleton (μ : Fin 1 ⊕ Fin 3) : indexList {μ} = [μ] := by
  simp [indexList]

lemma mem_indexList {t : Multiset (Fin 1 ⊕ Fin 3)} {a : Fin 1 ⊕ Fin 3} :
    a ∈ indexList t ↔ a ∈ t := by
  simp only [indexList, List.mem_map, Multiset.mem_sort, Multiset.mem_map]
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
    simpa using hc
  · intro ha
    exact ⟨finSumFinEquiv a, ⟨a, ha, rfl⟩, by simp⟩

lemma indexList_length (t : Multiset (Fin 1 ⊕ Fin 3)) :
    (indexList t).length = Multiset.card t := by
  simp [indexList, Multiset.length_sort]

/-- The canonical representative of a nonempty multiset of spacetime
  directions: the head of its canonical sorted list. -/
noncomputable def classRep (t : Multiset (Fin 1 ⊕ Fin 3)) : Fin 1 ⊕ Fin 3 :=
  (indexList t).headI

lemma classRep_mem {t : Multiset (Fin 1 ⊕ Fin 3)} (ht : t ≠ 0) : classRep t ∈ t := by
  have hne : indexList t ≠ [] := by
    intro h
    refine ht (Multiset.card_eq_zero.mp ?_)
    rw [← indexList_length t, h, List.length_nil]
  rw [← mem_indexList, classRep]
  cases hl : indexList t with
  | nil => exact absurd hl hne
  | cons a l => simp

attribute [irreducible] classRep

/-- The Lorentz transport of a family indexed by derivative multisets along a
  list of derivative directions: each direction in the list is summed against
  a row of `Λ⁻¹`, and the chosen directions accumulate in the multiset
  argument of the continuation `k`. -/
noncomputable def derivSum {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (Λ : LorentzGroup 3) :
    List (Fin 1 ⊕ Fin 3) → (Multiset (Fin 1 ⊕ Fin 3) → M) → M
  | [], k => k 0
  | σ :: l, k => ∑ τ, (Λ⁻¹).1 τ σ • derivSum Λ l fun t => k (t + {τ})

@[simp]
lemma derivSum_nil {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (Λ : LorentzGroup 3) (k : Multiset (Fin 1 ⊕ Fin 3) → M) :
    derivSum Λ [] k = k 0 := rfl

@[simp]
lemma derivSum_cons {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (Λ : LorentzGroup 3) (σ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3))
    (k : Multiset (Fin 1 ⊕ Fin 3) → M) :
    derivSum Λ (σ :: l) k =
      ∑ τ, (Λ⁻¹).1 τ σ • derivSum Λ l fun t => k (t + {τ}) := rfl

namespace Photon

/-!

## A. The jet algebra of the photon

### A.1. The jet coordinates

A jet coordinate is a formal symbol `∂_s A_μ`, where `s` is a *multiset* of
spacetime directions: for a smooth potential the partial derivatives commute,
so only the number of times each direction occurs matters.  The jet algebra is
the algebra of real polynomials in these symbols.

-/

/-- The jet coordinates of the electromagnetic potential: the symbol `∂_s A_μ`,
  the `s`-th derivative of the `μ`-th covariant component. -/
inductive JetGenerators where
  /-- The jet coordinate `∂_s A_μ`. -/
  | dA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) : JetGenerators
  deriving DecidableEq

/-- The mass weight (twice the mass dimension) of a photon jet coordinate:
  the potential has mass dimension one and each derivative adds one. -/
def JetGenerators.massWeight : JetGenerators → ℕ
  | .dA s _ => 2 + 2 * s.card

/-- The symmetrized-index class of a photon jet coordinate: under a gauge
  transformation `∂_s A_μ` shifts by `∂_s ∂_μ χ`, which depends only on the
  multiset `s + {μ}`.  Coordinates in a common class shift together. -/
def JetGenerators.indexClass : JetGenerators → Multiset (Fin 1 ⊕ Fin 3)
  | .dA s μ => s + {μ}

/-- The canonical jet coordinate of a symmetrized-index class: the coordinate
  whose Lorentz index is the canonical representative of the class. -/
noncomputable def JetGenerators.classProj (j : JetGenerators) : JetGenerators :=
  .dA (j.indexClass.erase (classRep j.indexClass)) (classRep j.indexClass)

/-- The jet algebra of the photon: real polynomials in the jet coordinates. -/
abbrev JetAlgebra : Type := MvPolynomial JetGenerators ℝ

namespace JetAlgebra

/-- The jet coordinate `∂_s A_μ` as an element of the jet algebra. -/
noncomputable def coord (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  MvPolynomial.X (JetGenerators.dA s μ)

/-!

### A.2. The gauge action on the photon jet algebra

A `U(1)_em` gauge transformation sends `A_μ ↦ A_μ + ∂_μ χ`, hence on jet
coordinates `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`.  All that the photon jet algebra
sees of the gauge function `χ` is the family of its symmetrised derivatives at
the base point, which is what `GaugeJet` records; the shift of `∂_s A_μ` is
then the value of that family at `s + {μ}`.

-/

/-- A photon gauge jet: the family `s ↦ ∂_s χ` of symmetrised derivatives of a
  gauge function at the base point.  This is all the photon jet algebra sees of
  a gauge transformation. -/
abbrev GaugeJet : Type := Multiset (Fin 1 ⊕ Fin 3) → ℝ

/-- The gauge action on the photon jet algebra: the algebra map determined by
  `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`. -/
noncomputable def gaugeAction (c : GaugeJet) : JetAlgebra →ₐ[ℝ] JetAlgebra :=
  MvPolynomial.aeval fun j => match j with
    | JetGenerators.dA s μ => coord s μ + MvPolynomial.C (c (s + {μ}))

@[simp]
lemma gaugeAction_coord (c : GaugeJet) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    gaugeAction c (coord s μ) = coord s μ + MvPolynomial.C (c (s + {μ})) := by
  rw [coord, gaugeAction, MvPolynomial.aeval_X]
  rfl

@[simp]
lemma gaugeAction_C (c : GaugeJet) (r : ℝ) :
    gaugeAction c (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [gaugeAction, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-!

### A.3. Iterated derivatives indexed by a multiset

To evaluate a jet coordinate on a potential we must differentiate along a
multiset of directions, so we must choose an order; we choose the canonical
one, sorting `s` through `Fin 1 ⊕ Fin 3 ≃ Fin 4`.  For a `C^∞` potential the
choice is immaterial, by Clairaut's theorem (`SpaceTime.deriv_commute`).

-/

/-- The iterated partial derivative `∂_s f` along a multiset `s` of spacetime
  directions, taken in the canonical order obtained by sorting `s`. -/
noncomputable def derivMultiset (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTime 3 → ℝ) :
    SpaceTime 3 → ℝ :=
  ((s.map (finSumFinEquiv (m := 1) (n := 3))).sort).foldr
    (fun i g => ∂_ ((finSumFinEquiv (m := 1) (n := 3)).symm i) g) f

@[simp]
lemma derivMultiset_zero (f : SpaceTime 3 → ℝ) : derivMultiset 0 f = f := by
  simp [derivMultiset]

@[simp]
lemma derivMultiset_singleton (μ : Fin 1 ⊕ Fin 3) (f : SpaceTime 3 → ℝ) :
    derivMultiset {μ} f = ∂_ μ f := by
  simp [derivMultiset]

/-!

### A.4. Evaluation on a potential

`ElectromagneticPotential` stores the contravariant components `A^μ`, whereas
a gauge potential carries a lower index, so the jet coordinate `∂_s A_μ`
evaluates to the `s`-th derivative of `A_μ = η_{μμ} A^μ`.

-/

/-- The covariant components `A_μ = η_{μμ} A^μ` of an electromagnetic potential. -/
noncomputable def coPotential (A : ElectromagneticPotential 3) (μ : Fin 1 ⊕ Fin 3) :
    SpaceTime 3 → ℝ := fun x => η μ μ * A x μ

/-- The evaluation of the photon jet algebra at an electromagnetic potential `A`:
  the algebra map sending the formal jet coordinate `∂_s A_μ` to the honest
  function `∂_s A_μ` on spacetime. -/
noncomputable def evalPotential (A : ElectromagneticPotential 3) :
    JetAlgebra →ₐ[ℝ] (SpaceTime 3 → ℝ) :=
  MvPolynomial.aeval fun j => match j with
    | JetGenerators.dA s μ => derivMultiset s (coPotential A μ)

@[simp]
lemma evalPotential_coord (A : ElectromagneticPotential 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) :
    evalPotential A (coord s μ) = derivMultiset s (coPotential A μ) := by
  rw [coord, evalPotential, MvPolynomial.aeval_X]

/-!

### A.5. The Lorentz action on the photon jet algebra

Under a Lorentz transformation the potential transforms as a covector field,
`A'(x) = (Λ⁻¹)ᵀ A (Λ⁻¹ x)`, so every lower index of the jet coordinate
`∂_s A_μ` — the index `μ` and each derivative index in `s` — is summed
against a row of `Λ⁻¹`.

-/

/-- The Lorentz action on the photon jet algebra: the algebra map transporting
  every lower index of `∂_s A_μ` with `Λ⁻¹`. -/
noncomputable def lorentzAction (Λ : LorentzGroup 3) : JetAlgebra →ₐ[ℝ] JetAlgebra :=
  MvPolynomial.aeval fun j => match j with
    | JetGenerators.dA s μ =>
        derivSum Λ (indexList s) fun t => ∑ ν, (Λ⁻¹).1 ν μ • coord t ν

@[simp]
lemma lorentzAction_coord (Λ : LorentzGroup 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) :
    lorentzAction Λ (coord s μ) =
      derivSum Λ (indexList s) fun t => ∑ ν, (Λ⁻¹).1 ν μ • coord t ν := by
  rw [coord, lorentzAction, MvPolynomial.aeval_X]

lemma lorentzAction_coord_zero (Λ : LorentzGroup 3) (μ : Fin 1 ⊕ Fin 3) :
    lorentzAction Λ (coord 0 μ) = ∑ ν, (Λ⁻¹).1 ν μ • coord 0 ν := by
  rw [lorentzAction_coord, indexList_zero, derivSum_nil]

lemma lorentzAction_coord_singleton (Λ : LorentzGroup 3) (σ μ : Fin 1 ⊕ Fin 3) :
    lorentzAction Λ (coord {σ} μ) =
      ∑ τ, ∑ ν, ((Λ⁻¹).1 τ σ * (Λ⁻¹).1 ν μ) • coord {τ} ν := by
  rw [lorentzAction_coord, indexList_singleton, derivSum_cons]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [derivSum_nil, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [smul_smul, zero_add]

/-!

### A.6. The mass-weight scaling on the photon jet algebra

-/

/-- The mass-weight scaling on the photon jet algebra: the algebra map
  multiplying each jet coordinate by `c` to the power of its mass weight. -/
noncomputable def massScale (c : ℝ) : JetAlgebra →ₐ[ℝ] JetAlgebra :=
  MvPolynomial.aeval fun j => c ^ j.massWeight • MvPolynomial.X j

@[simp]
lemma massScale_coord (c : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    massScale c (coord s μ) = c ^ (2 + 2 * Multiset.card s) • coord s μ := by
  rw [coord, massScale, MvPolynomial.aeval_X]
  rfl

/-!

### A.7. The formal total derivative on the photon jet algebra

-/

/-- The formal total spacetime derivative on the photon jet algebra in the
  direction `ρ`: the derivation appending the derivative index,
  `∂_s A_μ ↦ ∂_{s + {ρ}} A_μ`. -/
noncomputable def jetDeriv (ρ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℝ] JetAlgebra :=
  (MvPolynomial.mkDerivation ℝ fun j => match j with
    | JetGenerators.dA s μ => coord (s + {ρ}) μ : Derivation ℝ JetAlgebra JetAlgebra)

@[simp]
lemma jetDeriv_coord (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv ρ (coord s μ) = coord (s + {ρ}) μ := by
  rw [coord]
  exact MvPolynomial.mkDerivation_X _ _ _

@[simp]
lemma jetDeriv_one (ρ : Fin 1 ⊕ Fin 3) : jetDeriv ρ (1 : JetAlgebra) = 0 :=
  Derivation.map_one_eq_zero _

/-- The total derivative is a derivation on the photon jet algebra. -/
lemma jetDeriv_mul (ρ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv ρ (x * y) = jetDeriv ρ x * y + x * jetDeriv ρ y := by
  have h : jetDeriv ρ (x * y) = x • jetDeriv ρ y + y • jetDeriv ρ x :=
    Derivation.leibniz _ x y
  rw [h, smul_eq_mul, smul_eq_mul]
  ring

/-- The Leibniz rule for the complexified total derivative. -/
lemma jetDeriv_baseChange_mul (ρ : Fin 1 ⊕ Fin 3) (x y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (jetDeriv ρ) (x * y) =
      LinearMap.baseChange ℂ (jetDeriv ρ) x * y +
        x * LinearMap.baseChange ℂ (jetDeriv ρ) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    abel
  | tmul c p =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [mul_add, map_add, ha, hb]
      abel
    | tmul c' p' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        jetDeriv_mul, TensorProduct.tmul_add]

end JetAlgebra

end Photon

/-!

## B. The gauge jet of a `U(1)_em` transformation

A gauge transformation with gauge function `χ` acts on the photon by
`A_μ ↦ A_μ + ∂_μ χ` and on a field of charge `q` by `ψ ↦ exp (I q e χ) ψ`.
All that the jet algebras see of `χ` are its derivative jets `c s = ∂_s χ`,
and all they see of the phase are the derivative jets
`u s = ∂_s (exp (I e χ))`.  The two families are not independent:
differentiating the exponential gives `∂_μ u = I e (∂_μ χ) u`, whose `s`-th
derivative is a Leibniz sum over the splittings of `s`.
`Multiset.antidiagonal` counts each splitting with its multiplicity, which is
exactly the multinomial weight of the Leibniz rule.

-/

/-- Summing an indicator supported on the splittings `(0, t)` over the
  antidiagonal of `t` picks out `f t`: the splitting `(0, t)` occurs exactly
  once in `Multiset.antidiagonal t`. -/
lemma sum_map_antidiagonal_ite {M : Type*} [AddCommMonoid M]
    (t : Multiset (Fin 1 ⊕ Fin 3)) (f : Multiset (Fin 1 ⊕ Fin 3) → M) :
    ((t.antidiagonal).map fun p => if p.1 = 0 then f p.2 else 0).sum = f t := by
  induction t using Multiset.induction_on generalizing f with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
      Multiset.map_map, Multiset.map_map]
    have h2 : ((s.antidiagonal).map
        ((fun p => if p.1 = 0 then f p.2 else 0) ∘
          Prod.map (Multiset.cons a) id)).sum = 0 :=
      Multiset.sum_eq_zero fun x hx => by
        obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
        simp
    rw [h2, add_zero,
      show ((fun p => if p.1 = 0 then f p.2 else 0) ∘ Prod.map id (Multiset.cons a)) =
        fun p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3) =>
          if p.1 = 0 then f (a ::ₘ p.2) else 0 from rfl]
    exact ih fun u => f (a ::ₘ u)

/-- The Leibniz convolution of a phase family against a module-valued family
  of jets, over the antidiagonal of the derivative multiset: the formal
  expansion `∂_s (u ⬝ f) = ∑_{x + y = s} (∂_x u) (∂_y f)`, with the
  multiplicities of `Multiset.antidiagonal` supplying the multinomial
  weights. -/
noncomputable def phaseAct {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (u : Multiset (Fin 1 ⊕ Fin 3) → ℂ) (f : Multiset (Fin 1 ⊕ Fin 3) → M) :
    Multiset (Fin 1 ⊕ Fin 3) → M :=
  fun s => (s.antidiagonal.map fun p => u p.1 • f p.2).sum

section PhaseAct

variable {M : Type*} [AddCommMonoid M] [Module ℂ M]
variable (u u₁ u₂ v : Multiset (Fin 1 ⊕ Fin 3) → ℂ)
variable (f g : Multiset (Fin 1 ⊕ Fin 3) → M)

@[simp]
lemma phaseAct_zero_arg : phaseAct u f 0 = u 0 • f 0 := by
  simp [phaseAct]

/-- The convolution as a literal antidiagonal sum of products, for
  scalar-valued families. -/
lemma phaseAct_eq_sum (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct u v s = (s.antidiagonal.map fun p => u p.1 * v p.2).sum := rfl

/-- The Leibniz rule of the convolution: differentiating a convolution
  differentiates one factor at a time. -/
lemma phaseAct_add_singleton (a : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct u f (s + {a}) =
      phaseAct u (fun t => f (t + {a})) s +
        phaseAct (fun t => u (t + {a})) f s := by
  rw [phaseAct, show s + {a} = a ::ₘ s from by
      rw [Multiset.add_comm, Multiset.singleton_add],
    Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Multiset.map_map]
  congr 1
  · refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [Multiset.add_comm, Multiset.singleton_add]
  · refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [Multiset.add_comm, Multiset.singleton_add]

lemma phaseAct_add_left (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct (fun t => u₁ t + u₂ t) f s = phaseAct u₁ f s + phaseAct u₂ f s := by
  rw [phaseAct, phaseAct, phaseAct, ← Multiset.sum_map_add]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => add_smul _ _ _)

lemma phaseAct_add_right (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct u (fun t => f t + g t) s = phaseAct u f s + phaseAct u g s := by
  rw [phaseAct, phaseAct, phaseAct, ← Multiset.sum_map_add]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => smul_add _ _ _)

lemma phaseAct_smul_left (c : ℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct (fun t => c * u t) f s = c • phaseAct u f s := by
  rw [phaseAct, phaseAct, Multiset.smul_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply]
  exact mul_smul _ _ _

lemma phaseAct_smul_right (c : ℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct u (fun t => c • f t) s = c • phaseAct u f s := by
  rw [phaseAct, phaseAct, Multiset.smul_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply]
  exact smul_comm _ _ _

/-- Associativity of the convolution: acting by `u` after `v` is acting by
  the convolution `u ⋆ v`. -/
lemma phaseAct_assoc (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct u (phaseAct v f) s = phaseAct (phaseAct u v) f s := by
  induction s using Multiset.induction_on generalizing u v f with
  | empty =>
    simp [smul_smul]
  | cons a s ih =>
    rw [show a ::ₘ s = s + {a} from by
      rw [Multiset.add_comm, Multiset.singleton_add]]
    rw [phaseAct_add_singleton, phaseAct_add_singleton,
      show (fun t => phaseAct v f (t + {a})) = fun t =>
          phaseAct v (fun t' => f (t' + {a})) t +
            phaseAct (fun t' => v (t' + {a})) f t from
        funext fun t => phaseAct_add_singleton v f a t,
      phaseAct_add_right, ih, ih, ih,
      show (fun t => phaseAct u v (t + {a})) = fun t =>
          phaseAct u (fun t' => v (t' + {a})) t +
            phaseAct (fun t' => u (t' + {a})) v t from
        funext fun t => phaseAct_add_singleton u v a t,
      phaseAct_add_left]
    abel

/-- Commutativity of the scalar convolution. -/
lemma phaseAct_comm (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct u v s = phaseAct v u s := by
  induction s using Multiset.induction_on generalizing u v with
  | empty => simp [smul_eq_mul, mul_comm]
  | cons a s ih =>
    rw [show a ::ₘ s = s + {a} from by
      rw [Multiset.add_comm, Multiset.singleton_add]]
    rw [phaseAct_add_singleton, phaseAct_add_singleton,
      ih u fun t => v (t + {a}), ih (fun t => u (t + {a})) v]
    exact add_comm (phaseAct (fun t => v (t + {a})) u s)
      (phaseAct v (fun t => u (t + {a})) s)

/-- A linear map passes through the convolution. -/
lemma map_phaseAct {N : Type*} [AddCommMonoid N] [Module ℂ N] (L : M →ₗ[ℂ] N)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    L (phaseAct u f s) = phaseAct u (fun t => L (f t)) s := by
  rw [phaseAct, phaseAct, map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => map_smul L _ _)

/-- The convolution against the indicator of the empty multiset is the
  identity: the splitting `(0, t)` occurs exactly once in the
  antidiagonal. -/
lemma phaseAct_indicator (s : Multiset (Fin 1 ⊕ Fin 3)) :
    phaseAct (fun t => if t = 0 then 1 else 0) f s = f s := by
  rw [phaseAct, show (s.antidiagonal.map fun p =>
      (if p.1 = 0 then (1 : ℂ) else 0) • f p.2) =
    s.antidiagonal.map fun p => if p.1 = 0 then f p.2 else 0 from
    Multiset.map_congr rfl fun p _ => by
      by_cases h : p.1 = 0 <;> simp [h]]
  exact sum_map_antidiagonal_ite s f

/-- The star of a convolution is the convolution of the stars. -/
lemma star_phaseAct (s : Multiset (Fin 1 ⊕ Fin 3)) :
    star (phaseAct u v s) =
      phaseAct (fun t => star (u t)) (fun t => star (v t)) s := by
  rw [phaseAct_eq_sum, phaseAct_eq_sum, ← starRingEnd_apply, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  simp only [Function.comp_apply, map_mul, starRingEnd_apply]

end PhaseAct

/-- The jets of a `U(1)_em` gauge transformation with coupling `e`: the
  derivative jets `χjet s = ∂_s χ` of the real gauge function and
  `phase s = ∂_s (exp (I e χ))` of its unitary phase at the base point,
  subject to the two identities every honest gauge function satisfies:
  the phase has unit norm at the base point, and its derivatives obey the
  formal Leibniz expansion of `∂_μ (exp (I e χ)) = I e (∂_μ χ) exp (I e χ)`. -/
structure GaugeJet (e : ℝ) where
  /-- The derivative jets `∂_s χ` of the gauge function. -/
  χjet : Multiset (Fin 1 ⊕ Fin 3) → ℝ
  /-- The derivative jets `∂_s (exp (I e χ))` of the unitary phase. -/
  phase : Multiset (Fin 1 ⊕ Fin 3) → ℂ
  /-- The phase is unitary at the base point. -/
  phase_zero_unitary : phase 0 * star (phase 0) = 1
  /-- The formal Leibniz identity `∂_s ∂_μ u = I e ∂_s ((∂_μ χ) u)`. -/
  phase_deriv : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3),
    phase (s + {μ}) = Complex.I * e *
      ((s.antidiagonal.map fun p => (χjet (p.1 + {μ}) : ℂ) * phase p.2).sum)

namespace GaugeJet

variable {e : ℝ} (g : GaugeJet e)

/-!

### B.1. Low-order consequences of the Leibniz identity

The QED Lagrangian only involves jet coordinates of derivative order at most
one, so its gauge invariance only uses the Leibniz identity at order zero,
together with unitarity at the base point.

-/

lemma star_phase_zero_unitary : star (g.phase 0) * g.phase 0 = 1 := by
  rw [mul_comm]
  exact g.phase_zero_unitary

/-- The first derivative of the phase: the `s = 0` case of the Leibniz
  identity, `∂_μ u = I e (∂_μ χ) u` at the base point. -/
lemma phase_singleton (μ : Fin 1 ⊕ Fin 3) :
    g.phase {μ} = Complex.I * e * (g.χjet {μ} * g.phase 0) := by
  simpa using g.phase_deriv 0 μ

/-- The first derivative of the conjugate phase,
  `∂_μ ū = -I e (∂_μ χ) ū` at the base point. -/
lemma star_phase_singleton (μ : Fin 1 ⊕ Fin 3) :
    star (g.phase {μ}) = -(Complex.I * e * (g.χjet {μ} * star (g.phase 0))) := by
  rw [g.phase_singleton μ]
  simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The trivial gauge jet: the jets of the constant gauge function `χ = 0`. -/
noncomputable def trivial (e : ℝ) : GaugeJet e where
  χjet := 0
  phase s := if s = 0 then 1 else 0
  phase_zero_unitary := by simp
  phase_deriv s μ := by
    rw [if_neg (by simp)]
    rw [show ((s.antidiagonal.map fun p =>
        ((0 : Multiset (Fin 1 ⊕ Fin 3) → ℝ) (p.1 + {μ}) : ℂ) *
          (if p.2 = 0 then (1 : ℂ) else 0)).sum) = 0 from
      Multiset.sum_eq_zero fun x hx => by
        obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
        simp]
    ring

/-!

### B.2. The commutative monoid of gauge jets

Gauge jets compose: the gauge functions add and the phases convolve by the
Leibniz rule.  Closure of the two axioms under this product is a consistency
check on the axiomatisation of `GaugeJet`.

-/

lemma ext {g₁ g₂ : GaugeJet e} (h1 : g₁.χjet = g₂.χjet)
    (h2 : g₁.phase = g₂.phase) : g₁ = g₂ := by
  cases g₁
  cases g₂
  simp_all

/-- The composite of two gauge jets: the gauge functions add and the phases
  convolve by the Leibniz rule. -/
noncomputable instance : Mul (GaugeJet e) where
  mul g₁ g₂ :=
    { χjet := g₁.χjet + g₂.χjet
      phase := phaseAct g₁.phase g₂.phase
      phase_zero_unitary := by
        rw [phaseAct_zero_arg, smul_eq_mul, star_mul']
        calc g₁.phase 0 * g₂.phase 0 * (star (g₁.phase 0) * star (g₂.phase 0))
            = g₁.phase 0 * star (g₁.phase 0) *
                (g₂.phase 0 * star (g₂.phase 0)) := by ring
          _ = 1 := by rw [g₁.phase_zero_unitary, g₂.phase_zero_unitary, one_mul]
      phase_deriv := by
        intro s μ
        rw [phaseAct_add_singleton,
          show (fun t => g₂.phase (t + {μ})) = fun t => (Complex.I * e) •
              phaseAct (fun x => (g₂.χjet (x + {μ}) : ℂ)) g₂.phase t from
            funext fun t => by
              rw [g₂.phase_deriv t μ, phaseAct_eq_sum, smul_eq_mul, mul_assoc],
          show (fun t => g₁.phase (t + {μ})) = fun t => Complex.I * ↑e *
              phaseAct (fun x => (g₁.χjet (x + {μ}) : ℂ)) g₁.phase t from
            funext fun t => by
              rw [g₁.phase_deriv t μ, phaseAct_eq_sum, mul_assoc],
          phaseAct_smul_right, phaseAct_smul_left,
          phaseAct_assoc g₁.phase _ g₂.phase,
          show phaseAct g₁.phase (fun x => (g₂.χjet (x + {μ}) : ℂ)) =
              phaseAct (fun x => (g₂.χjet (x + {μ}) : ℂ)) g₁.phase from
            funext fun t => phaseAct_comm _ _ t,
          ← phaseAct_assoc, ← phaseAct_assoc, ← smul_add,
          show phaseAct (fun x => (g₂.χjet (x + {μ}) : ℂ))
                (phaseAct g₁.phase g₂.phase) s +
              phaseAct (fun x => (g₁.χjet (x + {μ}) : ℂ))
                (phaseAct g₁.phase g₂.phase) s =
              phaseAct (fun x => (((g₁.χjet + g₂.χjet) (x + {μ}) : ℝ) : ℂ))
                (phaseAct g₁.phase g₂.phase) s from by
            rw [← phaseAct_add_left]
            refine congrFun (congrArg
              (fun w => phaseAct w (phaseAct g₁.phase g₂.phase))
              (funext fun x => ?_)) s
            rw [Pi.add_apply]
            push_cast
            ring,
          phaseAct_eq_sum, smul_eq_mul, mul_assoc] }

@[simp]
lemma mul_χjet (g₁ g₂ : GaugeJet e) : (g₁ * g₂).χjet = g₁.χjet + g₂.χjet := rfl

@[simp]
lemma mul_phase (g₁ g₂ : GaugeJet e) :
    (g₁ * g₂).phase = phaseAct g₁.phase g₂.phase := rfl

noncomputable instance : One (GaugeJet e) := ⟨trivial e⟩

@[simp]
lemma one_χjet : (1 : GaugeJet e).χjet = 0 := rfl

@[simp]
lemma one_phase :
    (1 : GaugeJet e).phase = fun s => if s = 0 then (1 : ℂ) else 0 := rfl

/-- **The gauge jets form a commutative monoid**: the gauge symmetry data of
  QED composes associatively, with the trivial gauge jet as the unit. -/
noncomputable instance : CommMonoid (GaugeJet e) where
  mul_assoc g₁ g₂ g₃ := by
    refine ext (add_assoc _ _ _) (funext fun s => ?_)
    exact (phaseAct_assoc g₁.phase g₂.phase g₃.phase s).symm
  one_mul g := by
    refine ext (zero_add _) (funext fun s => ?_)
    exact phaseAct_indicator g.phase s
  mul_one g := by
    refine ext (add_zero _) (funext fun s => ?_)
    rw [mul_phase, one_phase, phaseAct_comm]
    exact phaseAct_indicator g.phase s
  mul_comm g₁ g₂ := by
    refine ext (add_comm _ _) (funext fun s => ?_)
    exact phaseAct_comm g₁.phase g₂.phase s

end GaugeJet

namespace Electron

/-!

## C. The jet algebra of the electron

### C.1. The jet coordinates

A jet coordinate is a formal symbol `∂_s ψ_α` or `∂_s ψ̄_α`, where `s` is a
*multiset* of spacetime directions (partial derivatives of a smooth field
commute) and `α : Fin 2 ⊕ Fin 2` is a Dirac spinor index in the chiral
representation: `Sum.inl` indexes the left-handed and `Sum.inr` the
right-handed Weyl component.

-/

/-- The jet coordinates of the Dirac electron: the symbols `∂_s ψ_α` and
  `∂_s ψ̄_α`, the `s`-th derivatives of the Dirac components and their
  conjugates.  The electron has electric charge `-1`; its conjugate has
  charge `+1`. -/
inductive JetGenerators where
  /-- The jet coordinate `∂_s ψ_α` of the electron. -/
  | dψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) : JetGenerators
  /-- The jet coordinate `∂_s ψ̄_α` of the conjugate electron. -/
  | dbarψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) : JetGenerators
  deriving DecidableEq

/-- The mass weight (twice the mass dimension) of an electron jet coordinate:
  a fermion has mass dimension `3/2` and each derivative adds one. -/
def JetGenerators.massWeight : JetGenerators → ℕ
  | .dψ s _ => 3 + 2 * s.card
  | .dbarψ s _ => 3 + 2 * s.card

/-- The jet component space of the electron: the free complex module on the
  jet coordinates. -/
abbrev JetComponentSpace : Type := JetGenerators →₀ ℂ

/-- The jet algebra of the electron: the exterior algebra on the free module
  over the jet coordinates.  The exterior product implements the fermionic
  anticommutativity of the electron field. -/
abbrev JetAlgebra : Type := ExteriorAlgebra ℂ JetComponentSpace

namespace JetAlgebra

/-- The jet coordinate `∂_s ψ_α` or `∂_s ψ̄_α` as an element of the jet
  algebra. -/
noncomputable def ofGenerator (j : JetGenerators) : JetAlgebra :=
  ExteriorAlgebra.ι ℂ (Finsupp.single j 1)

/-!

### C.2. The gauge action on the electron jet algebra

A gauge transformation sends the electron (charge `-1`) to `ū ψ` and its
conjugate to `u ψ̄`, where `u = exp (I e χ)`.  On jet coordinates this is the
Leibniz expansion

`∂_s ψ_α ↦ ∑_{x + y = s} (∂_x ū) (∂_y ψ_α)`,

the sum running over `Multiset.antidiagonal s`, whose multiplicities are the
multinomial coefficients of the Leibniz rule.  The action is linear on the jet
component space and extends functorially to an algebra map of the exterior
algebra.

-/

/-- The gauge action on a single electron jet coordinate: the Leibniz
  expansion of `∂_s (ū ψ_α)` and `∂_s (u ψ̄_α)` over the splittings of `s`. -/
noncomputable def gaugeActionGenerator {e : ℝ} (g : GaugeJet e) :
    JetGenerators → JetComponentSpace
  | .dψ t α => (t.antidiagonal.map fun p =>
      Finsupp.single (JetGenerators.dψ p.2 α) (star (g.phase p.1))).sum
  | .dbarψ t α => (t.antidiagonal.map fun p =>
      Finsupp.single (JetGenerators.dbarψ p.2 α) (g.phase p.1)).sum

/-- The gauge action on the jet component space: the linear extension of the
  Leibniz expansion on the jet coordinates. -/
noncomputable def gaugeActionCS {e : ℝ} (g : GaugeJet e) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  Finsupp.lift JetComponentSpace ℂ JetGenerators (gaugeActionGenerator g)

@[simp]
lemma gaugeActionCS_single {e : ℝ} (g : GaugeJet e) (j : JetGenerators) :
    gaugeActionCS g (Finsupp.single j 1) = gaugeActionGenerator g j := by
  rw [gaugeActionCS, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- The gauge action on the electron jet algebra: the algebra map induced by
  the Leibniz expansion on the jet coordinates. -/
noncomputable def gaugeAction {e : ℝ} (g : GaugeJet e) :
    JetAlgebra →ₐ[ℂ] JetAlgebra :=
  ExteriorAlgebra.map (gaugeActionCS g)

lemma gaugeAction_ofGenerator_dψ {e : ℝ} (g : GaugeJet e)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ofGenerator (.dψ t α)) =
      (t.antidiagonal.map fun p =>
        star (g.phase p.1) • ofGenerator (.dψ p.2 α)).sum := by
  rw [gaugeAction, ofGenerator, ExteriorAlgebra.map_apply_ι, gaugeActionCS_single,
    gaugeActionGenerator, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, ← Finsupp.smul_single_one, map_smul]
  rfl

lemma gaugeAction_ofGenerator_dbarψ {e : ℝ} (g : GaugeJet e)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ofGenerator (.dbarψ t α)) =
      (t.antidiagonal.map fun p =>
        g.phase p.1 • ofGenerator (.dbarψ p.2 α)).sum := by
  rw [gaugeAction, ofGenerator, ExteriorAlgebra.map_apply_ι, gaugeActionCS_single,
    gaugeActionGenerator, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, ← Finsupp.smul_single_one, map_smul]
  rfl

/-!

### C.3. The action on the low-order jet coordinates

The QED Lagrangian involves only the jet coordinates of derivative order at
most one, for which the antidiagonal sums are short: `antidiagonal 0` is the
single splitting `(0, 0)`, and `antidiagonal {μ}` the two splittings
`(0, {μ})` and `({μ}, 0)`.

-/

lemma antidiagonal_singleton (μ : Fin 1 ⊕ Fin 3) :
    ({μ} : Multiset (Fin 1 ⊕ Fin 3)).antidiagonal = {(0, {μ}), ({μ}, 0)} := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl,
    Multiset.antidiagonal_cons, Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.map_singleton, Multiset.singleton_add]
  rfl

@[simp]
lemma gaugeAction_ofGenerator_dψ_zero {e : ℝ} (g : GaugeJet e) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ofGenerator (.dψ 0 α)) =
      star (g.phase 0) • ofGenerator (.dψ 0 α) := by
  rw [gaugeAction_ofGenerator_dψ]
  simp

@[simp]
lemma gaugeAction_ofGenerator_dbarψ_zero {e : ℝ} (g : GaugeJet e) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ofGenerator (.dbarψ 0 α)) =
      g.phase 0 • ofGenerator (.dbarψ 0 α) := by
  rw [gaugeAction_ofGenerator_dbarψ]
  simp

lemma gaugeAction_ofGenerator_dψ_singleton {e : ℝ} (g : GaugeJet e)
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ofGenerator (.dψ {μ} α)) =
      star (g.phase 0) • ofGenerator (.dψ {μ} α) +
        star (g.phase {μ}) • ofGenerator (.dψ 0 α) := by
  rw [gaugeAction_ofGenerator_dψ, antidiagonal_singleton]
  simp

lemma gaugeAction_ofGenerator_dbarψ_singleton {e : ℝ} (g : GaugeJet e)
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ofGenerator (.dbarψ {μ} α)) =
      g.phase 0 • ofGenerator (.dbarψ {μ} α) +
        g.phase {μ} • ofGenerator (.dbarψ 0 α) := by
  rw [gaugeAction_ofGenerator_dbarψ, antidiagonal_singleton]
  simp

/-!

### C.4. The Lorentz action on the electron jet algebra

Under `M : SL(2,ℂ)` the Dirac spinor transforms in the chiral basis by the
block-diagonal matrix `S(M) = ((M, 0), (0, (M†)⁻¹))`, its conjugate by the
entrywise conjugate of `S(M)`, and every derivative index by `Λ(M)⁻¹`, where
`Λ(M)` is the image of `M` under the covering map
`Lorentz.SL2C.toLorentzGroup`.

-/

/-- The Dirac spinor representation of `SL(2,ℂ)` in the chiral basis: the two
  Weyl components transform in the two conjugate-dual fundamental
  representations, `S(M) = ((M, 0), (0, (M†)⁻¹))`, the assignment being fixed
  by the conventions of `Lorentz.SL2C.toLorentzGroup`. -/
noncomputable def spinorRep (M : SL(2,ℂ)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks M.1 0 0 ((M⁻¹).1)ᴴ

/-- The Lorentz action on a single electron jet coordinate: the spinor index
  is rotated by the spinor representation (its conjugate for `∂_s ψ̄`) and the
  derivative indices are transported with `Λ(M)⁻¹`. -/
noncomputable def lorentzActionGenerator (M : SL(2,ℂ)) :
    JetGenerators → JetComponentSpace
  | .dψ t α => derivSum (Lorentz.SL2C.toLorentzGroup M) (indexList t) fun t' =>
      ∑ β, spinorRep M α β • Finsupp.single (JetGenerators.dψ t' β) 1
  | .dbarψ t α => derivSum (Lorentz.SL2C.toLorentzGroup M) (indexList t) fun t' =>
      ∑ β, star (spinorRep M α β) • Finsupp.single (JetGenerators.dbarψ t' β) 1

/-- The Lorentz action on the jet component space. -/
noncomputable def lorentzActionCS (M : SL(2,ℂ)) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  Finsupp.lift JetComponentSpace ℂ JetGenerators (lorentzActionGenerator M)

@[simp]
lemma lorentzActionCS_single (M : SL(2,ℂ)) (j : JetGenerators) :
    lorentzActionCS M (Finsupp.single j 1) = lorentzActionGenerator M j := by
  rw [lorentzActionCS, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- The Lorentz action on the electron jet algebra: the algebra map induced by
  the action on the jet coordinates. -/
noncomputable def lorentzAction (M : SL(2,ℂ)) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  ExteriorAlgebra.map (lorentzActionCS M)

@[simp]
lemma lorentzAction_ofGenerator_dψ_zero (M : SL(2,ℂ)) (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (ofGenerator (.dψ 0 α)) =
      ∑ β, spinorRep M α β • ofGenerator (.dψ 0 β) := by
  rw [lorentzAction, ofGenerator, ExteriorAlgebra.map_apply_ι, lorentzActionCS_single,
    lorentzActionGenerator, indexList_zero, derivSum_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul]
  rfl

@[simp]
lemma lorentzAction_ofGenerator_dbarψ_zero (M : SL(2,ℂ)) (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (ofGenerator (.dbarψ 0 α)) =
      ∑ β, star (spinorRep M α β) • ofGenerator (.dbarψ 0 β) := by
  rw [lorentzAction, ofGenerator, ExteriorAlgebra.map_apply_ι, lorentzActionCS_single,
    lorentzActionGenerator, indexList_zero, derivSum_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul]
  rfl

lemma lorentzAction_ofGenerator_dψ_singleton (M : SL(2,ℂ)) (σ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (ofGenerator (.dψ {σ} α)) =
      ∑ τ, ∑ β, ((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ σ : ℝ) • spinorRep M α β) •
        ofGenerator (.dψ {τ} β) := by
  rw [lorentzAction, ofGenerator, ExteriorAlgebra.map_apply_ι, lorentzActionCS_single,
    lorentzActionGenerator, indexList_singleton, derivSum_cons]
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [derivSum_nil, ← algebraMap_smul ℂ (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ σ),
    map_smul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, smul_smul, ← algebraMap_smul (R := ℝ) ℂ
    (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ σ) (spinorRep M α β), smul_eq_mul, zero_add]
  rfl

lemma lorentzAction_ofGenerator_dbarψ_singleton (M : SL(2,ℂ)) (σ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (ofGenerator (.dbarψ {σ} α)) =
      ∑ τ, ∑ β, ((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ σ : ℝ) •
          star (spinorRep M α β)) • ofGenerator (.dbarψ {τ} β) := by
  rw [lorentzAction, ofGenerator, ExteriorAlgebra.map_apply_ι, lorentzActionCS_single,
    lorentzActionGenerator, indexList_singleton, derivSum_cons]
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [derivSum_nil, ← algebraMap_smul ℂ (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ σ),
    map_smul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, smul_smul, ← algebraMap_smul (R := ℝ) ℂ
    (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ σ) (star (spinorRep M α β)), smul_eq_mul,
    zero_add]
  rfl

/-!

### C.5. The mass-weight scaling on the electron jet algebra

-/

/-- The mass-weight scaling on the jet component space: the diagonal map
  multiplying each jet coordinate by `c` to the power of its mass weight. -/
noncomputable def massScaleCS (c : ℝ) : JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  Finsupp.lift JetComponentSpace ℂ JetGenerators fun j =>
    ((c : ℂ) ^ j.massWeight) • Finsupp.single j 1

/-- The mass-weight scaling on the electron jet algebra. -/
noncomputable def massScale (c : ℝ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  ExteriorAlgebra.map (massScaleCS c)

@[simp]
lemma massScale_ofGenerator (c : ℝ) (j : JetGenerators) :
    massScale c (ofGenerator j) = (c : ℂ) ^ j.massWeight • ofGenerator j := by
  rw [massScale, ofGenerator, ExteriorAlgebra.map_apply_ι, massScaleCS,
    Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul, map_smul]

end JetAlgebra

/-!

### C.6. The formal total derivative on the electron jet algebra

The total derivative extends from the jet coordinates to the whole exterior
algebra as an *even* derivation, `∂_ρ (x y) = (∂_ρ x) y + x (∂_ρ y)` with no
Koszul signs.  It is constructed by lifting `ι x ↦ (ι x, ι (∂_ρ x))` to an
algebra homomorphism into the trivial square-zero extension of the jet
algebra, following
`Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.JetDeriv`.

-/

/-- The jet coordinate with one further derivative in the direction `ρ`. -/
def JetGenerators.shift (ρ : Fin 1 ⊕ Fin 3) : JetGenerators → JetGenerators
  | .dψ s α => .dψ (s + {ρ}) α
  | .dbarψ s α => .dbarψ (s + {ρ}) α

namespace JetAlgebra

/-- The total derivative on the jet component space: the shift of the
  derivative multi-index. -/
noncomputable def jetDerivCS (ρ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  Finsupp.lift JetComponentSpace ℂ JetGenerators fun j =>
    Finsupp.single (JetGenerators.shift ρ j) 1

@[simp]
lemma jetDerivCS_single (ρ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    jetDerivCS ρ (Finsupp.single j 1) =
      Finsupp.single (JetGenerators.shift ρ j) 1 := by
  rw [jetDerivCS, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- The generator map of the total derivative into the trivial square-zero
  extension of the jet algebra: `ι x ↦ (ι x, ι (∂_ρ x))`. -/
noncomputable def jetDerivGen (ρ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace →ₗ[ℂ] TrivSqZeroExt JetAlgebra JetAlgebra where
  toFun x := (ExteriorAlgebra.ι ℂ x, ExteriorAlgebra.ι ℂ (jetDerivCS ρ x))
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma jetDerivGen_fst (ρ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    (jetDerivGen ρ x).fst = ExteriorAlgebra.ι ℂ x := rfl

@[simp]
lemma jetDerivGen_snd (ρ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    (jetDerivGen ρ x).snd = ExteriorAlgebra.ι ℂ (jetDerivCS ρ x) := rfl

/-- The generator map squares to zero: degree-one elements of the exterior
  algebra anticommute. -/
lemma jetDerivGen_mul_self (ρ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDerivGen ρ x * jetDerivGen ρ x = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, jetDerivGen_fst, ExteriorAlgebra.ι_sq_zero,
      TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, jetDerivGen_fst, jetDerivGen_snd, TrivSqZeroExt.snd_zero,
      smul_eq_mul, op_smul_eq_mul]
    exact ExteriorAlgebra.ι_add_mul_swap x (jetDerivCS ρ x)

/-- The lift of the total derivative to the trivial square-zero extension of
  the jet algebra: the algebra homomorphism `x ↦ (x, ∂_ρ x)`. -/
noncomputable def jetDerivHom (ρ : Fin 1 ⊕ Fin 3) :
    JetAlgebra →ₐ[ℂ] TrivSqZeroExt JetAlgebra JetAlgebra :=
  ExteriorAlgebra.lift ℂ ⟨jetDerivGen ρ, jetDerivGen_mul_self ρ⟩

@[simp]
lemma jetDerivHom_ι (ρ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDerivHom ρ (ExteriorAlgebra.ι ℂ x) = jetDerivGen ρ x := by
  rw [jetDerivHom, ExteriorAlgebra.lift_ι_apply]

/-- The first component of the square-zero lift is the identity. -/
@[simp]
lemma jetDerivHom_fst (ρ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    (jetDerivHom ρ x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ JetAlgebra JetAlgebra).comp (jetDerivHom ρ) =
      AlgHom.id ℂ JetAlgebra := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp
  exact DFunLike.congr_fun h x

/-- The formal total spacetime derivative on the electron jet algebra in the
  direction `ρ`: the even derivation extending the shift
  `∂_s ψ_α ↦ ∂_{s + {ρ}} ψ_α` of the jet coordinates. -/
noncomputable def jetDeriv (ρ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra where
  toFun x := (jetDerivHom ρ x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (jetDerivHom ρ) x y)
  map_smul' c x := congrArg TrivSqZeroExt.snd (map_smul (jetDerivHom ρ) c x)

lemma jetDeriv_apply (ρ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv ρ x = (jetDerivHom ρ x).snd := rfl

@[simp]
lemma jetDeriv_ι (ρ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace) :
    jetDeriv ρ (ExteriorAlgebra.ι ℂ x) =
      ExteriorAlgebra.ι ℂ (jetDerivCS ρ x) := by
  rw [jetDeriv_apply, jetDerivHom_ι, jetDerivGen_snd]

/-- The total derivative appends the derivative index to each jet
  coordinate. -/
@[simp]
lemma jetDeriv_ofGenerator (ρ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    jetDeriv ρ (ofGenerator j) = ofGenerator (JetGenerators.shift ρ j) := by
  rw [ofGenerator, jetDeriv_ι, jetDerivCS_single]
  rfl

@[simp]
lemma jetDeriv_one (ρ : Fin 1 ⊕ Fin 3) : jetDeriv ρ (1 : JetAlgebra) = 0 :=
  congrArg TrivSqZeroExt.snd (map_one (jetDerivHom ρ))

/-- The total derivative is an even derivation: the Leibniz rule holds on the
  electron jet algebra with no Koszul signs. -/
lemma jetDeriv_mul (ρ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv ρ (x * y) = jetDeriv ρ x * y + x * jetDeriv ρ y := by
  have h : jetDeriv ρ (x * y) =
      (jetDerivHom ρ x).fst * jetDeriv ρ y + jetDeriv ρ x * (jetDerivHom ρ y).fst :=
    congrArg TrivSqZeroExt.snd (map_mul (jetDerivHom ρ) x y)
  rw [jetDerivHom_fst, jetDerivHom_fst] at h
  exact h.trans (add_comm _ _)

end JetAlgebra

end Electron

/-!

## D. The jet algebra of QED

-/

/-- The jet algebra of quantum electrodynamics: the tensor product of the
  complexified photon jet algebra with the electron jet algebra.

  This is a `def` rather than an `abbrev`, and its algebraic structure is fixed
  by the single `Ring` and `Algebra` instances below, so that every algebraic
  class projects from one root.  On the bare tensor product `One`, `Mul`,
  `Zero`, `Add`, `SMul` and `Module` are instead supplied by standalone
  `TensorProduct.*` instances rather than as projections of the semiring; those
  are definitionally the projections, but not syntactically, so a generic lemma
  whose type argument is not pinned by an explicit argument (such as `one_pow`)
  cannot be unified against a goal.  Rooting the structure here keeps the
  generic algebraic lemmas usable. -/
def JetAlgebra : Type := (ℂ ⊗[ℝ] Photon.JetAlgebra) ⊗[ℂ] Electron.JetAlgebra

noncomputable instance : Ring JetAlgebra :=
  inferInstanceAs (Ring ((ℂ ⊗[ℝ] Photon.JetAlgebra) ⊗[ℂ] Electron.JetAlgebra))

noncomputable instance : Algebra ℂ JetAlgebra :=
  inferInstanceAs (Algebra ℂ ((ℂ ⊗[ℝ] Photon.JetAlgebra) ⊗[ℂ] Electron.JetAlgebra))

namespace JetAlgebra

/-!

### D.1. Pure tensors and their arithmetic

-/

/-- A pure tensor, as an element of the jet algebra.

  Writing `a ⊗ₜ[ℂ] b` builds an element of the *underlying* tensor product,
  which is only definitionally an element of `JetAlgebra`.  A goal mixing such
  a term with the jet algebra's own operations is then not type-correct at
  `instances` transparency, and no rewrite can fire on it.  This constructor
  keeps pure tensors typed at `JetAlgebra`. -/
noncomputable def tmul (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    JetAlgebra := a ⊗ₜ[ℂ] b

@[inherit_doc] scoped infixl:100 " ⊗ⱼ " => JetAlgebra.tmul

/-- `tmul` is the pure tensor of the underlying tensor product; use this to
  move between the jet algebra and lemmas stated for the tensor product. -/
lemma tmul_eq (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    a ⊗ⱼ b = a ⊗ₜ[ℂ] b := rfl

lemma one_eq_tmul : (1 : JetAlgebra) = (1 : ℂ ⊗[ℝ] Photon.JetAlgebra) ⊗ⱼ 1 := rfl

/-- Multiplication of pure tensors. `Algebra.TensorProduct.tmul_mul_tmul` does
  not rewrite here, even though it is definitionally the same statement. -/
@[simp]
lemma tmul_mul_tmul (a₁ a₂ : ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b₁ b₂ : Electron.JetAlgebra) :
    (a₁ ⊗ⱼ b₁) * (a₂ ⊗ⱼ b₂) = (a₁ * a₂) ⊗ⱼ (b₁ * b₂) :=
  Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

@[simp]
lemma zero_tmul (b : Electron.JetAlgebra) :
    (0 : ℂ ⊗[ℝ] Photon.JetAlgebra) ⊗ⱼ b = 0 := TensorProduct.zero_tmul _ b

@[simp]
lemma tmul_zero (a : ℂ ⊗[ℝ] Photon.JetAlgebra) :
    a ⊗ⱼ (0 : Electron.JetAlgebra) = 0 := TensorProduct.tmul_zero _ a

@[simp]
lemma add_tmul (a₁ a₂ : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    (a₁ + a₂) ⊗ⱼ b = a₁ ⊗ⱼ b + a₂ ⊗ⱼ b := TensorProduct.add_tmul a₁ a₂ b

@[simp]
lemma tmul_add (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b₁ b₂ : Electron.JetAlgebra) :
    a ⊗ⱼ (b₁ + b₂) = a ⊗ⱼ b₁ + a ⊗ⱼ b₂ := TensorProduct.tmul_add a b₁ b₂

@[simp]
lemma sub_tmul (a₁ a₂ : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    (a₁ - a₂) ⊗ⱼ b = a₁ ⊗ⱼ b - a₂ ⊗ⱼ b := TensorProduct.sub_tmul a₁ a₂ b

@[simp]
lemma tmul_sub (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b₁ b₂ : Electron.JetAlgebra) :
    a ⊗ⱼ (b₁ - b₂) = a ⊗ⱼ b₁ - a ⊗ⱼ b₂ := TensorProduct.tmul_sub a b₁ b₂

@[simp]
lemma neg_tmul (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    (-a) ⊗ⱼ b = -(a ⊗ⱼ b) := TensorProduct.neg_tmul a b

@[simp]
lemma tmul_neg (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    a ⊗ⱼ (-b) = -(a ⊗ⱼ b) := TensorProduct.tmul_neg a b

lemma tmul_sum {ι : Type*} (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (s : Finset ι)
    (f : ι → Electron.JetAlgebra) : a ⊗ⱼ (∑ i ∈ s, f i) = ∑ i ∈ s, a ⊗ⱼ f i :=
  TensorProduct.tmul_sum a s f

lemma sum_tmul {ι : Type*} (s : Finset ι) (f : ι → ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b : Electron.JetAlgebra) : (∑ i ∈ s, f i) ⊗ⱼ b = ∑ i ∈ s, f i ⊗ⱼ b :=
  TensorProduct.sum_tmul s f b

@[simp]
lemma tmul_smul (r : ℂ) (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    a ⊗ⱼ (r • b) = r • (a ⊗ⱼ b) := TensorProduct.tmul_smul r a b

@[simp]
lemma smul_tmul' (r : ℂ) (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra) :
    (r • a) ⊗ⱼ b = r • (a ⊗ⱼ b) := TensorProduct.smul_tmul' r a b

/-- An `ℝ`-scalar on the photon factor is a `ℂ`-scalar of the jet algebra. -/
lemma real_smul_tmul (r : ℝ) (a : ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b : Electron.JetAlgebra) :
    (r • a) ⊗ⱼ b = (r : ℂ) • (a ⊗ⱼ b) := by
  rw [show r • a = (r : ℂ) • a by rw [← Complex.coe_algebraMap, algebraMap_smul],
    smul_tmul']

/-- A constant of the photon factor is a scalar of the jet algebra. -/
lemma tmul_C_eq_smul_one (r : ℝ) :
    ((1 : ℂ) ⊗ₜ[ℝ] (MvPolynomial.C r : Photon.JetAlgebra)) ⊗ⱼ
        (1 : Electron.JetAlgebra) = (r : ℂ) • (1 : JetAlgebra) := by
  rw [show (MvPolynomial.C r : Photon.JetAlgebra) = r • 1 by
      rw [MvPolynomial.smul_eq_C_mul, mul_one],
    TensorProduct.tmul_smul,
    show r • ((1 : ℂ) ⊗ₜ[ℝ] (1 : Photon.JetAlgebra)) =
        (r : ℂ) • (1 : ℂ ⊗[ℝ] Photon.JetAlgebra) by
      rw [← Complex.coe_algebraMap, algebraMap_smul,
        Algebra.TensorProduct.one_def],
    smul_tmul', ← one_eq_tmul]

/-- Induction on the jet algebra, stated for `JetAlgebra` itself.  Using
  `TensorProduct.induction_on` directly leaves the zero, the sum and the pure
  tensors in the goals carrying the tensor product's structure rather than the
  jet algebra's, which makes those goals unrewritable. -/
@[elab_as_elim]
lemma induction_on {motive : JetAlgebra → Prop} (x : JetAlgebra) (zero : motive 0)
    (tmul : ∀ (a : ℂ ⊗[ℝ] Photon.JetAlgebra) (b : Electron.JetAlgebra),
      motive (a ⊗ⱼ b))
    (add : ∀ x y : JetAlgebra, motive x → motive y → motive (x + y)) : motive x :=
  TensorProduct.induction_on x zero tmul add

/-!

### D.2. The inclusions of the two factors

-/

/-- The photon factor included into the QED jet algebra. -/
noncomputable abbrev inclA : (ℂ ⊗[ℝ] Photon.JetAlgebra) →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.includeLeft

/-- The electron factor included into the QED jet algebra. -/
noncomputable abbrev inclE : Electron.JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.includeRight

lemma inclA_apply (a : ℂ ⊗[ℝ] Photon.JetAlgebra) : inclA a = a ⊗ⱼ 1 := rfl

lemma inclE_apply (b : Electron.JetAlgebra) : inclE b = 1 ⊗ⱼ b := rfl

/-!

### D.3. The gauge action on the QED jet algebra

A gauge jet acts on the photon factor by the affine shift
`∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`, complexified, and on the electron factor by
the Leibniz expansion of `∂_s (ū ψ)` and `∂_s (u ψ̄)`; the action on the full
jet algebra is the tensor product of the two, an algebra map.

-/

/-- The gauge action on the complexified photon jet algebra: the
  complexification of the affine action `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`. -/
noncomputable def gaugeActionPhoton (c : Photon.JetAlgebra.GaugeJet) :
    (ℂ ⊗[ℝ] Photon.JetAlgebra) →ₐ[ℂ] ℂ ⊗[ℝ] Photon.JetAlgebra :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Photon.JetAlgebra.gaugeAction c)

@[simp]
lemma gaugeActionPhoton_tmul (c : Photon.JetAlgebra.GaugeJet) (x : ℂ)
    (p : Photon.JetAlgebra) :
    gaugeActionPhoton c (x ⊗ₜ[ℝ] p) = x ⊗ₜ[ℝ] Photon.JetAlgebra.gaugeAction c p :=
  rfl

/-- The gauge action on the QED jet algebra: the tensor product of the affine
  action on the photon factor with the Leibniz phase rotation on the electron
  factor. -/
noncomputable def gaugeAction {e : ℝ} (g : GaugeJet e) :
    JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map (gaugeActionPhoton g.χjet)
    (Electron.JetAlgebra.gaugeAction g)

lemma gaugeAction_tmul {e : ℝ} (g : GaugeJet e) (a : ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b : Electron.JetAlgebra) :
    gaugeAction g (a ⊗ⱼ b) =
      gaugeActionPhoton g.χjet a ⊗ⱼ Electron.JetAlgebra.gaugeAction g b :=
  rfl

/-!

### D.4. The Lorentz action on the QED jet algebra

An `M : SL(2,ℂ)` acts on the photon factor through its image `Λ(M)` in the
Lorentz group, complexified, and on the electron factor through the spinor
representation; the action on the full jet algebra is the tensor product of
the two.

-/

/-- The Lorentz action on the complexified photon jet algebra. -/
noncomputable def lorentzActionPhoton (Λ : LorentzGroup 3) :
    (ℂ ⊗[ℝ] Photon.JetAlgebra) →ₐ[ℂ] ℂ ⊗[ℝ] Photon.JetAlgebra :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Photon.JetAlgebra.lorentzAction Λ)

@[simp]
lemma lorentzActionPhoton_tmul (Λ : LorentzGroup 3) (x : ℂ) (p : Photon.JetAlgebra) :
    lorentzActionPhoton Λ (x ⊗ₜ[ℝ] p) = x ⊗ₜ[ℝ] Photon.JetAlgebra.lorentzAction Λ p :=
  rfl

/-- The Lorentz action on the QED jet algebra: the tensor product of the
  photon action through the covering map with the electron spinor action. -/
noncomputable def lorentzAction (M : SL(2,ℂ)) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map (lorentzActionPhoton (Lorentz.SL2C.toLorentzGroup M))
    (Electron.JetAlgebra.lorentzAction M)

lemma lorentzAction_tmul (M : SL(2,ℂ)) (a : ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b : Electron.JetAlgebra) :
    lorentzAction M (a ⊗ⱼ b) =
      lorentzActionPhoton (Lorentz.SL2C.toLorentzGroup M) a ⊗ⱼ
        Electron.JetAlgebra.lorentzAction M b :=
  rfl

/-! TODO: Prove the composition law of the Lorentz action.  Being a pullback on coordinates it -/
/-! TODO: is a right action, `lorentzAction M ∘ lorentzAction N = lorentzAction (N * M)`; the -/
/-! TODO: proof needs permutation-invariance and functoriality of `derivSum` over sorted lists. -/
/-! TODO: Define an antilinear star on the QED jet algebra with `star ψ = ψ̄`, `star A = A`, and -/
/-! TODO: prove hermiticity of the Lagrangian up to the total derivative of the kinetic term. -/

/-!

### D.5. The mass-weight scaling on the QED jet algebra

-/

/-- The mass-weight scaling on the complexified photon jet algebra. -/
noncomputable def massScalePhoton (c : ℝ) :
    (ℂ ⊗[ℝ] Photon.JetAlgebra) →ₐ[ℂ] ℂ ⊗[ℝ] Photon.JetAlgebra :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Photon.JetAlgebra.massScale c)

@[simp]
lemma massScalePhoton_tmul (c : ℝ) (x : ℂ) (p : Photon.JetAlgebra) :
    massScalePhoton c (x ⊗ₜ[ℝ] p) = x ⊗ₜ[ℝ] Photon.JetAlgebra.massScale c p :=
  rfl

/-- The mass-weight scaling on the QED jet algebra: the algebra map
  multiplying each jet coordinate by `c` to the power of its mass weight,
  i.e. `c` squared to the power of its mass dimension. -/
noncomputable def massScale (c : ℝ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map (massScalePhoton c) (Electron.JetAlgebra.massScale c)

lemma massScale_tmul (c : ℝ) (a : ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b : Electron.JetAlgebra) :
    massScale c (a ⊗ⱼ b) =
      massScalePhoton c a ⊗ⱼ Electron.JetAlgebra.massScale c b :=
  rfl

/-!

### D.6. The formal total derivative on the QED jet algebra

-/

/-- The formal total spacetime derivative on the QED jet algebra in the
  direction `ρ`: the Leibniz extension of the total derivatives of the photon
  and electron factors. -/
noncomputable def jetDeriv (ρ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  TensorProduct.map (LinearMap.baseChange ℂ (Photon.JetAlgebra.jetDeriv ρ))
      LinearMap.id +
    TensorProduct.map LinearMap.id (Electron.JetAlgebra.jetDeriv ρ)

lemma jetDeriv_tmul (ρ : Fin 1 ⊕ Fin 3) (a : ℂ ⊗[ℝ] Photon.JetAlgebra)
    (b : Electron.JetAlgebra) :
    jetDeriv ρ (a ⊗ⱼ b) =
      (LinearMap.baseChange ℂ (Photon.JetAlgebra.jetDeriv ρ) a) ⊗ⱼ b +
        a ⊗ⱼ Electron.JetAlgebra.jetDeriv ρ b := rfl

@[simp]
lemma jetDeriv_one (ρ : Fin 1 ⊕ Fin 3) : jetDeriv ρ (1 : JetAlgebra) = 0 := by
  have hB : LinearMap.baseChange ℂ (Photon.JetAlgebra.jetDeriv ρ)
      (1 : ℂ ⊗[ℝ] Photon.JetAlgebra) = 0 := by
    rw [show (1 : ℂ ⊗[ℝ] Photon.JetAlgebra) =
        (1 : ℂ) ⊗ₜ[ℝ] (1 : Photon.JetAlgebra) from rfl,
      LinearMap.baseChange_tmul, Photon.JetAlgebra.jetDeriv_one,
      TensorProduct.tmul_zero]
  rw [one_eq_tmul, jetDeriv_tmul, hB, Electron.JetAlgebra.jetDeriv_one, zero_tmul,
    tmul_zero, add_zero]

/-- The total derivative is an even derivation on the QED jet algebra: the
  Leibniz rule holds with no Koszul signs. -/
lemma jetDeriv_mul (ρ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv ρ (x * y) = jetDeriv ρ x * y + x * jetDeriv ρ y := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    abel
  | tmul p l =>
    induction y using JetAlgebra.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
      abel
    | tmul p' l' =>
      simp only [tmul_mul_tmul, jetDeriv_tmul, add_mul, mul_add,
        Photon.JetAlgebra.jetDeriv_baseChange_mul, Electron.JetAlgebra.jetDeriv_mul,
        add_tmul, tmul_add, tmul_mul_tmul]
      abel

end JetAlgebra

end QED
