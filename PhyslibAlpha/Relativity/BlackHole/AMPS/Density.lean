/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import QuantumInfo.Entropy.SSA
public import QuantumInfo.States.Entanglement

/-!
# The AMPS argument for density matrices

Radiation entropy and density matrices.

## i. Overview

This file states and proves the entropy half of the AMPS argument (arXiv:1207.3123, §2)
for actual finite-dimensional density matrices, using Physlib's `QuantumInfo` library:
`MState` is a density matrix, `Sᵥₙ` is von Neumann entropy defined from its spectrum,
partial traces are `traceLeft` / `traceRight`.  Strong subadditivity and the Araki–Lieb
inequality are theorems of that library, not premises here.

`R` = early radiation, `B` = a late outgoing mode, `C` = its interior partner,
`D` = the rest of the black hole.

**Main results**

* `amps_from_postulates`: for any pure state of `R, B, C, D`, the pair `BC` cannot be pure
  if emitting `B` lowers the entropy of the hole.
* `amps_contradiction`: the same for any (possibly mixed) state of `R, B, C`.
* `entropy_budget`: `(S(R) - S(RB)) + S(B) ≤ 2 S(BC)` for every state.
* `youngHole_*`, `oldHole_*`: explicit states showing each premise can be dropped.

**What is not here**

That an infalling vacuum makes `BC` pure, and that the hole's entropy falls after the
Page time, are physical inputs.  They appear as hypotheses.

## ii. Key results

* `step5_ssa`
* `step4_decoupling`

## iii. Table of contents

- A. Radiation entropy and density matrices
- B. Marginals of a state on `R ⊗ B ⊗ C`
- C. Steps 4, 5, 6 for an arbitrary state of `R ⊗ B ⊗ C`
- D. Step 1: unitarity and an old black hole
- E. The full argument from a pure state of `R, B, C, D`
- F. Explicit states: each premise can be dropped

## iv. References

* [ref: Almheiri2013]

## A. Radiation entropy and density matrices
-/

@[expose] public section

noncomputable section

namespace AMPS.Density

variable {dR dB dC dD : Type*}
variable [Fintype dR] [Fintype dB] [Fintype dC] [Fintype dD]
variable [DecidableEq dR] [DecidableEq dB] [DecidableEq dC] [DecidableEq dD]

/-! ## B. Marginals of a state on `R ⊗ B ⊗ C` -/

/-- The state of the early radiation and the late mode. -/
abbrev rhoRB (ρ : MState (dR × dB × dC)) : MState (dR × dB) := ρ.assoc'.traceRight

/-- The state of the late mode and its interior partner. -/
abbrev rhoBC (ρ : MState (dR × dB × dC)) : MState (dB × dC) := ρ.traceLeft

/-- The state of the early radiation. -/
abbrev rhoR (ρ : MState (dR × dB × dC)) : MState dR := ρ.traceRight

/-- The state of the late mode. -/
abbrev rhoB (ρ : MState (dR × dB × dC)) : MState dB := ρ.traceLeft.traceRight

/-! ## C. Steps 4, 5, 6 for an arbitrary state of `R ⊗ B ⊗ C` -/

/-- **Step 5.** Strong subadditivity with `B` in the middle. -/
lemma step5_ssa (ρ : MState (dR × dB × dC)) :
    Sᵥₙ ρ + Sᵥₙ (rhoB ρ) ≤ Sᵥₙ (rhoRB ρ) + Sᵥₙ (rhoBC ρ) :=
  Sᵥₙ_strong_subadditivity ρ

/-- **Step 4.** If the pair `BC` has zero entropy, it carries no correlation with `R`:
the entropy of `RBC` equals that of `R`. -/
lemma step4_decoupling (ρ : MState (dR × dB × dC)) (hPair : Sᵥₙ (rhoBC ρ) = 0) :
    Sᵥₙ ρ = Sᵥₙ (rhoR ρ) := by
  have h1 := Sᵥₙ_subadditivity ρ
  have h2 := Sᵥₙ_triangle_ineq_one_way ρ
  linarith

/-- The drop in radiation entropy plus the entropy of the late mode is at most twice the
entropy of the pair `BC`.  Holds for every state; no purity is assumed. -/
lemma entropy_budget (ρ : MState (dR × dB × dC)) :
    (Sᵥₙ (rhoR ρ) - Sᵥₙ (rhoRB ρ)) + Sᵥₙ (rhoB ρ) ≤ 2 * Sᵥₙ (rhoBC ρ) := by
  have h1 := step5_ssa ρ
  have h2 := Sᵥₙ_triangle_ineq_one_way ρ
  linarith

/-- **Step 6.** No state of `R ⊗ B ⊗ C` has a zero-entropy pair `BC` and a radiation
entropy that falls when `B` is added. -/
theorem amps_contradiction (ρ : MState (dR × dB × dC))
    (hPair : Sᵥₙ (rhoBC ρ) = 0) (hDrop : Sᵥₙ (rhoRB ρ) < Sᵥₙ (rhoR ρ)) : False := by
  have h1 := entropy_budget ρ
  have h2 := Sᵥₙ_nonneg (rhoB ρ)
  linarith

/-- If the radiation entropy falls when `B` is added, the pair `BC` is not a pure state. -/
lemma not_pure_pair_of_drop (ρ : MState (dR × dB × dC))
    (hDrop : Sᵥₙ (rhoRB ρ) < Sᵥₙ (rhoR ρ)) :
    ¬ ∃ φ : Ket (dB × dC), rhoBC ρ = MState.pure φ := by
  rintro ⟨φ, hφ⟩
  exact amps_contradiction ρ (by rw [hφ]; exact Sᵥₙ_of_pure_zero φ) hDrop

/-! ## D. Step 1: unitarity and an old black hole -/

/-- **Step 1.** Let the radiation `R`, the late mode `B` and the remaining hole `H` be in a
joint pure state.  If the hole has less entropy after emitting `B` than the hole together
with `B` had before, then `RB` has less entropy than `R`. -/
lemma step1_radiation_drop {dH : Type*} [Fintype dH] [DecidableEq dH]
    (ψ : Ket ((dR × dB) × dH))
    (hOld : Sᵥₙ (MState.pure ψ).traceLeft < Sᵥₙ (MState.pure ψ).assoc.traceLeft) :
    Sᵥₙ (MState.pure ψ).traceRight < Sᵥₙ (MState.pure ψ).assoc.traceRight := by
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = MState.pure ψ' :=
    MState.relabel_pure_exists ψ _
  have h1 := Sᵥₙ_of_partial_eq ψ
  have h2 := Sᵥₙ_of_partial_eq ψ'
  rw [hψ'] at hOld ⊢
  linarith

/-! ## E. The full argument from a pure state of `R, B, C, D` -/

/-- The state of `R`, `B`, `C` obtained from a pure state of `R, B, C, D` by tracing out
the rest of the hole `D`. -/
def exterior (ψ : Ket ((dR × dB) × (dC × dD))) : MState (dR × dB × dC) :=
  (MState.pure ψ).assoc'.traceRight.assoc

lemma rhoRB_exterior (ψ : Ket ((dR × dB) × (dC × dD))) :
    rhoRB (exterior ψ) = (MState.pure ψ).traceRight := by
  simp [rhoRB, exterior]

lemma rhoR_exterior (ψ : Ket ((dR × dB) × (dC × dD))) :
    rhoR (exterior ψ) = (MState.pure ψ).assoc.traceRight := by
  simp [rhoR, exterior]

/-- **AMPS.** Take any pure state of the early radiation `R`, a late mode `B`, an
interior mode `C`, and the rest of the hole `D`, as four independent tensor factors.
Then the following cannot both hold:

* no drama: the pair `BC` is in a pure state;
* unitarity for an old hole: the hole after emitting `B` (that is, `CD`) has less
  entropy than the hole before (that is, `BCD`). -/
lemma amps_from_postulates (ψ : Ket ((dR × dB) × (dC × dD)))
    (hNoDrama : ∃ φ : Ket (dB × dC), rhoBC (exterior ψ) = MState.pure φ)
    (hOld : Sᵥₙ (MState.pure ψ).traceLeft < Sᵥₙ (MState.pure ψ).assoc.traceLeft) :
    False := by
  have hDrop := step1_radiation_drop ψ hOld
  rw [← rhoRB_exterior, ← rhoR_exterior] at hDrop
  exact not_pure_pair_of_drop (exterior ψ) hDrop hNoDrama

/-! ## F. Explicit states: each premise can be dropped

`d` is the dimension of one mode; `Ket.MES d` is the maximally entangled state. -/

section Models

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma Sᵥₙ_uniform [Nonempty d] :
    Sᵥₙ (MState.uniform : MState d) = Real.log (Fintype.card d) := by
  rw [MState.uniform, Sᵥₙ_ofClassical, Hₛ_uniform]
  rfl

/-- A young hole: `B` and `C` maximally entangled, `R` in any state `σ`. -/
def youngHole [Nonempty d] (σ : MState d) : MState (d × d × d) :=
  σ ⊗ᴹ MState.pure (Ket.MES d)

/-- An old hole: `R` and `B` maximally entangled, `C` in any state `τ`. -/
def oldHole [Nonempty d] (τ : MState d) : MState (d × d × d) :=
  (MState.pure (Ket.MES d) ⊗ᴹ τ).assoc

/-- **Dropping the old-hole entropy decrease.** In the young hole the pair `BC` is pure (no
  drama holds). -/
lemma youngHole_pair_pure [Nonempty d] (σ : MState d) :
    rhoBC (youngHole σ) = MState.pure (Ket.MES d) := by
  simp [rhoBC, youngHole, MState.traceLeft_prod_eq]

/-- ... and so its radiation entropy does not fall. -/
lemma youngHole_no_drop [Nonempty d] (σ : MState d) :
    Sᵥₙ (rhoR (youngHole σ)) ≤ Sᵥₙ (rhoRB (youngHole σ)) := by
  by_contra h
  exact not_pure_pair_of_drop _ (not_le.mp h) ⟨_, youngHole_pair_pure σ⟩

lemma rhoRB_oldHole [Nonempty d] (τ : MState d) :
    rhoRB (oldHole τ) = MState.pure (Ket.MES d) := by
  simp [rhoRB, oldHole, MState.traceRight_prod_eq]

lemma rhoR_oldHole [Nonempty d] (τ : MState d) :
    rhoR (oldHole τ) = MState.uniform := by
  simp [rhoR, oldHole, MState.traceRight_prod_eq, traceRight_pure_MES]

/-- **Dropping no drama.** In the old hole the radiation entropy falls by `log d`
when `B` is added for this particular marginal. -/
lemma oldHole_drop [Nontrivial d] (τ : MState d) :
    Sᵥₙ (rhoRB (oldHole τ)) < Sᵥₙ (rhoR (oldHole τ)) := by
  rw [rhoRB_oldHole, rhoR_oldHole, Sᵥₙ_of_pure_zero, Sᵥₙ_uniform]
  exact Real.log_pos (by exact_mod_cast Fintype.one_lt_card)

/-- ... and so the pair `BC` is not pure, whatever state `C` is in. -/
lemma oldHole_pair_not_pure [Nontrivial d] (τ : MState d) :
    ¬ ∃ φ : Ket (d × d), rhoBC (oldHole τ) = MState.pure φ :=
  not_pure_pair_of_drop _ (oldHole_drop τ)

/-- **Dropping independence.** In the same old hole, `B` does have a pure partner:
the radiation `R` itself. -/
lemma oldHole_partner_is_radiation [Nonempty d] (τ : MState d) :
    ∃ φ : Ket (d × d), rhoRB (oldHole τ) = MState.pure φ :=
  ⟨_, rhoRB_oldHole τ⟩

/-- The coefficient two in `entropy_budget` is optimal: a maximally entangled `RB`
and a pure spectator `C` attain equality with strictly positive pair entropy. -/
lemma entropy_budget_saturated [Nontrivial d] (χ : Ket d) :
    let ρ := oldHole (MState.pure χ)
    0 < Sᵥₙ (rhoBC ρ) ∧
    (Sᵥₙ (rhoR ρ) - Sᵥₙ (rhoRB ρ)) + Sᵥₙ (rhoB ρ) = 2 * Sᵥₙ (rhoBC ρ) := by
  let ρ := oldHole (MState.pure χ)
  change 0 < Sᵥₙ (rhoBC ρ) ∧ _ = 2 * Sᵥₙ (rhoBC ρ)
  have hRB : Sᵥₙ (rhoRB ρ) = 0 := by rw [rhoRB_oldHole, Sᵥₙ_of_pure_zero]
  have hpos : 0 < Sᵥₙ (rhoR ρ) := by
    have hdrop := oldHole_drop (MState.pure χ)
    change Sᵥₙ (rhoRB ρ) < Sᵥₙ (rhoR ρ) at hdrop
    linarith
  have hB : Sᵥₙ (rhoB ρ) = Sᵥₙ (rhoR ρ) := by
    simpa [ρ, rhoB, rhoR, oldHole, MState.traceRight_prod_eq] using Sᵥₙ_of_partial_eq (Ket.MES d)
  obtain ⟨φ,hφ⟩ : ∃ φ, ρ = MState.pure φ := by
    dsimp only [ρ, oldHole]
    rw [← MState.pure_prod_pure]
    apply MState.relabel_pure_exists
  have hBC : Sᵥₙ (rhoBC ρ) = Sᵥₙ (rhoR ρ) := by
    rw [hφ]
    exact Sᵥₙ_of_partial_eq φ
  constructor <;> linarith

end Models

end AMPS.Density
