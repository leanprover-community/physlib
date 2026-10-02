/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Lattice

/-!
# Classical systems

## i. Overview

A system is classical when every state decomposes in exactly one way into pure states: a state is
then nothing but a probability distribution over the pure states. In the language of convex
geometry the state space is a Choquet simplex. By the Choquet–Meyer theorem this is the same as
asking that any two positive functionals have a least upper bound, which is how it is stated here.

Classicality is characterized operationally by the absence of incompatibility (Kuramochi's theorem)
and by the uniqueness of composites (the Namioka–Phelps theorem). It is weaker than asking that the
observables themselves form a lattice, as they do for the functions on a sample space.

## ii. Key definitions and results

- `IsClassical E` : the system `E` is classical.
- `OrderUnitLattice.isClassical` : a system whose observables form a lattice is classical.

## iii. Table of contents

- A. Classical systems

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Classical systems -/

/-- A system is **classical** when every state decomposes uniquely into pure states: its state
space is a Choquet simplex, i.e. any two positive functionals have a least upper bound. -/
abbrev IsClassical (E : Type*) [OrderUnitSpace E] : Prop := HasLatticeDualCone E

/-- A system whose observables form a lattice is classical. -/
lemma OrderUnitLattice.isClassical (E : Type*) [OrderUnitLattice E] : IsClassical E :=
  VectorLattice.hasLatticeDualCone E

end ProbabilisticTheory
