/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Distribution

@[expose] public section

open BigOperators

/- Channels, as in information theory.

A `Channel` is as a function from `List`s over an input alphabet A to a distribution
of lists over an output alphabet B. The most important case of interest here
is the memoryless channel, which preserves lengths and acts on each symbol
identically and independently.
-/

variable (I O : Type*) [Fintype O]

/- Actually defining Channels this way gets messy fast because of the measure theory.

/-- Although we could simply `def Channel := List A → List B`, defining it as
a structure lets us extend this structure by adding additional properties while
staying a `Channel`. -/
structure Channel [MeasurableSpace O] where
  map : List I → MeasureTheory.Measure (List O)
  map_prob : ∀is, IsProbabilityMeasure (map is)

namespace Channel

variable (A B C D : Type*)
variable (Cab : Channel A B) (Cbc : Channel B C) (Ccd : Channel C D)

/-- Identity channel -/
def id : Channel A A :=
  ⟨_root_.id⟩

/-- Composition of two channels -/
def comp : Channel A C :=
  ⟨Cbc.map ∘ Cab.map⟩

/-- Product of two channels, acting on two product types in parallel. -/
def product : Channel (A × C) (B × D) :=
  ⟨Cab.map × Ccd.map⟩
-/

/-- Discrete Memoryless Channel. Each input symbol `I` has a corresponding
 output distribution `Distribution O`, and this process is applied
 independently on each symbol in the list. -/
structure DMChannel where
  symb_dist : I → ProbDistribution O

namespace DMChannel

/-- Apply a discrete memoryless channel to an n-character string. -/
def on_fin (C : DMChannel I O) {n : ℕ} (is : Fin n → I) : ProbDistribution (Fin n → O) :=
  ProbDistribution.mk' (fun os ↦ ∏ k, (C.symb_dist (is k) (os k) : ℝ))
    (fun _ ↦ Finset.prod_nonneg fun k _ ↦ Prob.zero_le_coe)
    (by
      have h := Finset.sum_prod_piFinset (Finset.univ : Finset O)
        (fun (k : Fin n) (j : O) ↦ ((C.symb_dist (is k)) j : ℝ))
      simp only [Fintype.piFinset_univ] at h
      simp only [h]
      exact Finset.prod_eq_one fun k _ ↦ ProbDistribution.normalized (C.symb_dist (is k)))

/-- Apply a discrete memoryless channel to a list. -/
def on_list (C : DMChannel I O) (is : List I) : ProbDistribution (Fin (is.length) → O) :=
  C.on_fin _ _ (fun k => is.get k)

end DMChannel
