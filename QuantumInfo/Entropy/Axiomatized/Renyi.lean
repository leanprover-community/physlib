/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.Axiomatized.Defs

/-! # Quantum Relative Entropy and α-Renyi Entropy

The concrete relative entropy built here is an instance of the axiomatic `RelEntropy` class of
`QuantumInfo.Entropy.Axiomatized.Defs`. It lives in the `Axiomatized` namespace so that it does
not clash with the development in `QuantumInfo.Entropy.Relative`, which defines the same quantity
directly.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace Axiomatized

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The quantum relative entropy S(ρ‖σ) = Tr[ρ (log ρ - log σ)]. -/
@[irreducible]
noncomputable def qRelativeEnt (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  open Classical in (if σ.ker ≤ ρ.M.ker then
    ENNReal.ofNNReal ⟨ρ.exp_val (ρ.M.log - σ.log),
      /- Quantum relative entropy is nonnegative. This can be proved by an application of
      Klein's inequality. -/
      sorry⟩
  else
    ⊤)

@[inherit_doc] scoped notation "𝐃(" ρ "‖" σ ")" => Axiomatized.qRelativeEnt ρ σ

instance : RelEntropy qRelativeEnt where
  DPI := sorry
  of_kron := sorry
  normalized := sorry

instance : RelEntropy.Nontrivial qRelativeEnt where
  nontrivial := sorry

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  rw [qRelativeEnt, if_pos h]
  rfl

end Axiomatized
