/-
Copyright (c) 2026 Brent Yee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brent Yee
-/
module

public import PhyslibAlpha.Mathematics.MeasureTheory.Pi
public import PhyslibAlpha.QuantumMechanics.Foundations.OntologicalModel
public import PhyslibAlpha.QuantumMechanics.Foundations.PBR.Measurement

/-!
# The Pusey–Barrett–Rudolph theorem

Every preparation-independent ontological model of a finite target quantum system is ψ-ontic.

## i. Overview

The Pusey–Barrett–Rudolph (PBR) theorem says that the quantum state is a real property of a
system rather than a state of knowledge about it. Precisely, consider an ontological model of a
finite target quantum system `𝓗[d]` which reproduces the Born rule for every measurement, both
for one system and for `n` independently prepared systems, and which is preparation
independent: preparing `n` systems independently in the product vector
`χ 0 ⊗ ⋯ ⊗ χ (n - 1)` (the unit vector `piProdVec χ`) gives independent ontic states
`l 0, …, l (n - 1)`, distributed according to `prep (χ 0), …, prep (χ (n - 1))`, which jointly
determine the ontic state `ι n l` of the `n` systems. The `n`-copy ontic space need not be the
Cartesian product of `n` copies of the single-copy one (taking it to be, with `ι n = id`, is
the Cartesian-product formulation, see `OntologicalModel.PreparationIndependent.of_prep_piProdVec`).
Then the preparation measures of any two unit vectors with different vector states are mutually
singular, i.e. the model is ψ-ontic.

The proof has a quantum part and a classical part. Fix two unit vectors `ψ` and `φ` with
different vector states and write `ψ₀ = ψ`, `ψ₁ = φ` (in Lean, `![ψ, φ]`). The quantum part is
the PBR measurement `PBR.exists_measurement`: there is a measurement on `n` copies, with
outcomes `x : Fin n → Fin 2`, whose outcome `x` has probability zero in the vector state of the
product vector `ψ_{x 0} ⊗ ⋯ ⊗ ψ_{x (n - 1)}`. Pulling the response functions of this
measurement back along `ι n` gives functions `ξ x` on `n`-tuples of single-copy ontic states.
The classical part, proved here, shows that this forces the preparation measures `μ 0 = prep ψ`,
`μ 1 = prep φ` to be mutually singular: a common lower bound `ν` of `μ 0` and `μ 1` satisfies
`ν(Λ) ^ n = ∑ x, ∫ ξ x dν^{⊗n} ≤ ∑ x, ∫ ξ x dμ_{x 0} ⊗ ⋯ ⊗ μ_{x (n - 1)} = 0`.

## ii. Key results

- `PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero` : the classical part of the proof.
- `OntologicalModel.PreparationIndependent.isPsiOntic` : the PBR theorem.

## iii. Table of contents

- A. The classical part of the proof
- B. The PBR theorem

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]
- N. Harrigan and R. W. Spekkens, *Einstein, incompleteness, and the epistemic view of quantum
  states*, Found. Phys. 40, 125–157 (2010), arXiv:0706.2661. [ref: Harrigan:2007wfc]

-/

@[expose] public section

namespace QuantumMechanics

open MeasureTheory ProbabilisticTheory UnitalPositiveLinearMap FiniteHilbertSpace
open scoped ENNReal

namespace PBR

/-!
## A. The classical part of the proof

-/

/-- Let `ξ o` be measurable response functions on `n` copies which sum to one at every point,
and suppose every outcome `o` integrates to zero against some product measure
`μ (x 0) ⊗ ⋯ ⊗ μ (x (n - 1))`. Then a finite measure `ν` with `ν ≤ μ b` for both `b : Fin 2`
is zero. -/
lemma eq_zero_of_le_of_exists_lintegral_eq_zero {Λ O : Type*}
    [MeasurableSpace Λ] [Fintype O] (μ : Fin 2 → Measure Λ) {n : ℕ}
    (ξ : O → (Fin n → Λ) → ℝ≥0∞) (hξ : ∀ o, Measurable (ξ o)) (hsum : ∀ l, ∑ o, ξ o l = 1)
    (hzero : ∀ o, ∃ x : Fin n → Fin 2, ∫⁻ l, ξ o l ∂Measure.pi (fun i => μ (x i)) = 0)
    (ν : Measure Λ) [IsFiniteMeasure ν] (hν : ∀ b, ν ≤ μ b) : ν = 0 := by
  have hle : ∀ o, ∫⁻ l, ξ o l ∂Measure.pi (fun _ : Fin n => ν) = 0 := fun o => by
    obtain ⟨x, hx⟩ := hzero o
    exact nonpos_iff_eq_zero.1 <|
      (lintegral_mono' (Measure.pi_mono fun i => hν (x i)) le_rfl).trans hx.le
  have hpi : Measure.pi (fun _ : Fin n => ν) Set.univ = 0 := by
    calc _ = ∫⁻ l, ∑ o, ξ o l ∂Measure.pi (fun _ : Fin n => ν) := by simp [hsum]
      _ = 0 := by
        rw [lintegral_finsetSum _ fun o _ => hξ o]
        exact Finset.sum_eq_zero fun o _ => hle o
  rw [Measure.pi_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hpi
  exact Measure.measure_univ_eq_zero.1 (pow_eq_zero_iff'.1 hpi).1

/-- The classical part of the PBR theorem: if every outcome `o` of a family of response
functions `ξ o` on `n` copies (measurable, summing to one) integrates to zero against some
product measure `μ (x 0) ⊗ ⋯ ⊗ μ (x (n - 1))`, then the finite measures `μ 0` and `μ 1` are
mutually singular. -/
lemma mutuallySingular_of_forall_exists_lintegral_eq_zero {Λ O : Type*} [MeasurableSpace Λ]
    [Fintype O] (μ : Fin 2 → Measure Λ) [∀ b, IsFiniteMeasure (μ b)] {n : ℕ}
    (ξ : O → (Fin n → Λ) → ℝ≥0∞) (hξ : ∀ o, Measurable (ξ o)) (hsum : ∀ l, ∑ o, ξ o l = 1)
    (hzero : ∀ o, ∃ x : Fin n → Fin 2, ∫⁻ l, ξ o l ∂Measure.pi (fun i => μ (x i)) = 0) :
    μ 0 ⟂ₘ μ 1 := by
  refine Measure.mutuallySingular_iff_disjoint.2 fun ν h0 h1 => le_bot_iff.2 ?_
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le (μ 0) h0
  exact eq_zero_of_le_of_exists_lintegral_eq_zero μ ξ hξ hsum hzero ν
    (Fin.forall_fin_two.2 ⟨h0, h1⟩)

end PBR

/-!
## B. The PBR theorem

-/

namespace OntologicalModel

/-- **Pusey–Barrett–Rudolph theorem.** An ontological model of a finite target quantum system
which reproduces the Born rule for every measurement, for one system and for any number `n` of
systems, and which is preparation independent (independently prepared product vectors give
independent ontic states, which jointly determine the ontic state of the `n` systems) is
ψ-ontic: the preparation measures of any two unit vectors with different vector states are
mutually singular. The `n`-copy ontic spaces `Λn n` are arbitrary. -/
theorem PreparationIndependent.isPsiOntic {d Λ : Type*} [Fintype d] [DecidableEq d]
    [MeasurableSpace Λ] {M : OntologicalModel d Λ} {Λn : ℕ → Type*}
    [∀ n, MeasurableSpace (Λn n)] {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)}
    (h : M.PreparationIndependent Mn) : M.IsPsiOntic := by
  obtain ⟨ι, hι, h⟩ := h
  intro ψ φ hψ hφ hne
  have hv : ∀ b, ‖![ψ, φ] b‖ = 1 := Fin.forall_fin_two.2 ⟨hψ, hφ⟩
  -- the PBR measurement on `n` copies, whose outcome `x` excludes the product vector `Ψ x`
  obtain ⟨n, E, hE⟩ := PBR.exists_measurement ![ψ, φ] hv hne
  -- its response functions, pulled back to `n`-tuples of single-copy ontic states
  refine PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero
    (fun b => M.prep (![ψ, φ] b) (hv b)) (fun x => (Mn n).resp E x ∘ ι n)
    (fun x => ((Mn n).measurable_resp E x).comp (hι n))
    (fun l => (Mn n).sum_resp E (ι n l)) fun x => ⟨x, ?_⟩
  have key := (Mn n).lintegral_resp E (piProdVec fun i => ![ψ, φ] (x i))
    (norm_piProdVec_eq_one fun i => hv (x i)) x
  rw [h n _ fun i => hv (x i), lintegral_map ((Mn n).measurable_resp E x) (hι n), hE x,
    ENNReal.ofReal_zero] at key
  exact key

end OntologicalModel

end QuantumMechanics
