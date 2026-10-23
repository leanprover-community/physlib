/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Finite
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Operators
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.ProductState

/-!

# Ontological models of a quantum system

Ontological models of a finite target quantum system, ψ-ontic models and preparation
independence.

## i. Overview

An ontological model (in the sense of Harrigan and Spekkens) of a quantum system reproduces
the predictions of quantum mechanics by assigning to the system a "real" or ontic state `l` in a
measurable space `Λ`. Preparing the system in the pure state of a unit vector `ψ` samples `l`
from a probability measure `prep ψ` on `Λ`, and performing a measurement `M` in the ontic state
`l` gives outcome `x` with probability `resp M x l`. Averaging over `l` must give the Born rule:
the expectation in the vector state of `ψ` of the effect of `x`.

The model is ψ-ontic if the ontic state determines the quantum state: the preparation measures
of two unit vectors with different vector states are mutually singular. Otherwise it is
ψ-epistemic, and the quantum state is (at least partly) a state of knowledge about `l`.

Pusey, Barrett and Rudolph (PBR) show that every model satisfying their preparation-independence
assumption is ψ-ontic. Preparation independence says that `n` independently prepared systems
have independent ontic states `l 0, …, l (n - 1)`, each distributed according to the
single-copy preparation measure, and that these jointly determine the ontic state of the `n`
systems: preparing the product vector gives the ontic state `ι n (l 0, …, l (n - 1))` for some
measurable map `ι n`. The ontic space of the `n` systems need not be the Cartesian product of
`n` copies of `Λ`. Requiring it to be, with `ι n` the identity, is what Leifer calls the
Cartesian Product Assumption; it is strictly stronger, and it is recovered by
`OntologicalModel.PreparationIndependent.of_prep_piProdVec`. The PBR theorem itself is
`OntologicalModel.PreparationIndependent.isPsiOntic` in
`PhyslibAlpha/QuantumMechanics/Foundations/PBR/Theorem.lean`.

## ii. Key results

- `OntologicalModel` : an ontological model of the quantum system `𝓗[d]`.
- `OntologicalModel.IsPsiOntic` : the ψ-ontic property.
- `OntologicalModel.PreparationIndependent` : the PBR preparation-independence assumption.
- `OntologicalModel.PreparationIndependent.of_prep_piProdVec` : the Cartesian-product form of
  preparation independence implies preparation independence.

## iii. Table of contents

- A. Ontological models
- B. ψ-ontic models
- C. Preparation independence

## iv. References

- N. Harrigan and R. W. Spekkens, *Einstein, incompleteness, and the epistemic view of quantum
  states*, Found. Phys. 40, 125–157 (2010), arXiv:0706.2661. [ref: Harrigan:2007wfc]
- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]
- M. S. Leifer, *Is the quantum state real? An extended review of ψ-ontology theorems*,
  Quanta 3, 67–155 (2014), arXiv:1409.1570. [ref: Leifer:2014sza]

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics

open MeasureTheory ProbabilisticTheory FiniteHilbertSpace
open UnitalPositiveLinearMap
open scoped ENNReal

/-!

## A. Ontological models

-/

/-- An ontological model (Harrigan–Spekkens) of the quantum system `𝓗[d]`, with ontic state
space `Λ`.

Preparations are indexed by unit vectors rather than by states. This is more general: a model
whose preparations depend only on the vector state `ofVec hψ` is a special case, while here two
unit vectors differing by a global phase, which have the same vector state and hence the same
measurement statistics, may be prepared with different measures. Only pure-state preparations
are modelled, as only these are needed for the PBR theorem. Measurements have finitely many
outcomes, and response functions take values in `ℝ≥0∞` so that they can be integrated with the
Lebesgue integral `∫⁻`. -/
structure OntologicalModel (d : Type*) [Fintype d] [DecidableEq d] (Λ : Type*)
    [MeasurableSpace Λ] where
  /-- The preparation measure: preparing the unit vector `ψ` puts the system in an ontic state
  distributed according to `prep ψ hψ`. -/
  prep (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) : Measure Λ
  /-- Each preparation measure is a probability measure on the ontic states. -/
  isProbabilityMeasure_prep (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) : IsProbabilityMeasure (prep ψ hψ)
  /-- The response function: `resp M x l` is the probability of obtaining the outcome `x` when
  performing the measurement `M` on a system in the ontic state `l`. -/
  resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] :
    Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d])) → X → Λ → ℝ≥0∞
  /-- The response functions are measurable, so they can be averaged over a preparation. -/
  measurable_resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d]))) (x : X) : Measurable (resp M x)
  /-- In every ontic state, the measurement `M` gives some outcome: the response probabilities
  sum to one. -/
  sum_resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d]))) (l : Λ) : ∑ x, resp M x l = 1
  /-- The model reproduces the Born rule: averaging the response function over the preparation
  measure of `ψ` gives the probability of the outcome `x` in the vector state of `ψ`. -/
  lintegral_resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d]))) (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) (x : X) :
    ∫⁻ l, resp M x l ∂prep ψ hψ =
      ENNReal.ofReal ((ofVec hψ)⟨M {x} (measurableSet_singleton x)⟩)

attribute [instance] OntologicalModel.isProbabilityMeasure_prep

namespace OntologicalModel

variable {d : Type*} [Fintype d] [DecidableEq d] {Λ : Type*} [MeasurableSpace Λ]

/-!

## B. ψ-ontic models

-/

/-- An ontological model is ψ-ontic if the preparation measures of any two unit vectors with
different vector states are mutually singular, so that the ontic state determines the quantum
state. Unit vectors differing only by a global phase have the same vector state, and may share
ontic states. -/
def IsPsiOntic (M : OntologicalModel d Λ) : Prop :=
  ∀ (ψ φ : 𝓗[d]) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1),
    ofVec (𝕜 := ℂ) hψ ≠ ofVec (𝕜 := ℂ) hφ → M.prep ψ hψ ⟂ₘ M.prep φ hφ

/-!

## C. Preparation independence

-/

/-- The preparation-independence assumption of Pusey, Barrett and Rudolph for the model `M`,
relative to a family of models `Mn n` of `n` copies of the system (on `𝓗[Fin n → d]`, with ontic
states `Λn n`). It asks that `n` independently prepared systems have independent ontic states
which jointly determine the ontic state of the `n` copies: there are measurable maps
`ι n : (Fin n → Λ) → Λn n` such that preparing the product vector `piProdVec ψ` gives the ontic
state `ι n l`, where the `l i` are independent and distributed according to `M.prep (ψ i)`.

The ontic space `Λn n` need not be the Cartesian product `Fin n → Λ`; taking `Λn n = Fin n → Λ`
and `ι n = id` gives the stronger Cartesian Product Assumption (in Leifer's terminology), see
`PreparationIndependent.of_prep_piProdVec`.

Since preparations are indexed by vectors, two families `ψ`, `ψ'` with the same product vector
(for example `ψ 0 ⊗ ψ 1 = (i • ψ 0) ⊗ (-i • ψ 1)`) must give the same pushed-forward product
measure, and at `n = 0` the preparation `(Mn 0).prep` of the trivial product vector must be a
Dirac measure. The first condition is automatic when `M.prep` depends only on the ray of the
vector, and the second only concerns the trivial system `n = 0`, which the PBR theorem does not
use; so the standard PBR setting is covered by choosing one representative vector per ray. -/
def PreparationIndependent (M : OntologicalModel d Λ) {Λn : ℕ → Type*}
    [∀ n, MeasurableSpace (Λn n)] (Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)) : Prop :=
  ∃ ι : (n : ℕ) → (Fin n → Λ) → Λn n, (∀ n, Measurable (ι n)) ∧
    ∀ (n : ℕ) (ψ : Fin n → 𝓗[d]) (hψ : ∀ i, ‖ψ i‖ = 1),
      (Mn n).prep (piProdVec ψ) (norm_piProdVec_eq_one hψ) =
        (Measure.pi fun i => M.prep (ψ i) (hψ i)).map (ι n)

/-- The Cartesian-product form of preparation independence: if the `n`-copy models have ontic
space `Fin n → Λ` and prepare the product vector `piProdVec ψ` with the product of the
measures `M.prep (ψ i)`, then `M` is preparation independent (with `ι n = id`). -/
lemma PreparationIndependent.of_prep_piProdVec {M : OntologicalModel d Λ}
    {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Fin n → Λ)}
    (h : ∀ n (ψ : Fin n → 𝓗[d]) (hψ : ∀ i, ‖ψ i‖ = 1),
      (Mn n).prep (piProdVec ψ) (norm_piProdVec_eq_one hψ) =
        Measure.pi fun i => M.prep (ψ i) (hψ i)) :
    M.PreparationIndependent Mn :=
  ⟨fun _ => id, fun _ => measurable_id, fun n ψ hψ => by rw [h, Measure.map_id]⟩

end OntologicalModel

end QuantumMechanics
