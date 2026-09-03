/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Basic.Observables.Basic
public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Self-adjoint observables

An observable is a self-adjoint element of a unital complex C⋆-algebra. The
ambient algebra supplies its additive, real-linear, norm, and order structure.
-/

@[expose] public section

namespace OperatorAlgebra

/-- A physical observable in an operator algebra. -/
abbrev Observable (A : Type*) [OperatorAlgebra A] := _root_.Observable A

namespace Observable

variable {A : Type*} [OperatorAlgebra A]

/-- The complex spectrum of an observable lies on the real axis. -/
lemma spectrum_subset_real (a : Observable A) :
    spectrum ℂ (a : A) ⊆ Set.range Complex.ofReal := by
  intro z hz
  exact ⟨z.re, (a.property.mem_spectrum_eq_re hz).symm⟩

end Observable

end OperatorAlgebra
