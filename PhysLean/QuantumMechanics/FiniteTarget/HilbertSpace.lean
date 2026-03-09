/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import PhysLean.Meta.TODO.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

# The Hilbert space of a finite target quantum mechanical system

-/

@[expose] public section

namespace QuantumMechanics

/-- The finite dimensional Hilbert space of dimension `n`. -/
def FiniteHilbertSpace (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

instance {n : ℕ} : AddCommGroup (FiniteHilbertSpace n) := inferInstanceAs
  (AddCommGroup (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : Module ℂ (FiniteHilbertSpace n) := inferInstanceAs
  (Module ℂ (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : NormedAddCommGroup (FiniteHilbertSpace n) := inferInstanceAs
  (NormedAddCommGroup (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : InnerProductSpace ℂ (FiniteHilbertSpace n) := inferInstanceAs
  (InnerProductSpace ℂ (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : CompleteSpace (FiniteHilbertSpace n) := inferInstanceAs
  (CompleteSpace (EuclideanSpace ℂ (Fin n)))

end QuantumMechanics
