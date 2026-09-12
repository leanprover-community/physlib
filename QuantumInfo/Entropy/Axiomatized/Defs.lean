/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Entropy
public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
/-! # Generalized quantum entropy and relative entropy

Here we define a broad notion of entropy axiomatically, `Entropy`, and the Prop
`Entropy f` means that the function `f : MState → ℝ` acts like a generalized kind of quantum
entropy. For instance, min-, max-, α-Renyi, and von Neumann entropies all fall
into this category. We prove various properties about the entropy for anything
supporting this type class. Any entropy automatically gets corresponding notions
of conditional entropy, mutual information, and so on.

Similarly, `RelEntropy f` means that `f : MState → HermitianMat → ENNReal` is a kind of
relative entropy. Every `RelEntropy` leads to a notion of entropy, as well, by
fixing one argument to the fully mixed state.

Of course relative entropies are "usually" used with a pair of (normalized) quantum
states, but it's still very common in literature to specifically let the second
argument be an arbitrary (PSD, Hermitian) matrix, so we do allow this. The behavior
when not a density matrix is left unspecified by the axioms.

In terms of the file structure, we start with `RelEntropy` as the more "general"
function, and then derive much of `Entropy` from it.

## References:

* Khinchin’s Fourth Axiom of Entropy Revisited. [ref: mdpi_khinchin_fourth_axiom]
* α-z Relative Entropies. [ref: warwick_alpha_z_relative_entropies]
* Watrous's notes, Max-relative entropy and conditional min-entropy. [ref: watrous_qit_notes_02]
* Quantum Relative Entropy - An Axiomatic Approach by Marco Tomamichel.
  [ref: tomamichel_relative_entropy_masterclass]
* StackExchange. [ref: stackexchange_qc_12953]
-/

@[expose] public section

noncomputable section
universe u

open scoped NNReal
open scoped ENNReal

--The entropy function is a variable throughout this file, so every simp lemma about it
--necessarily has a variable as its head symbol.
set_option warning.simp.varHead false

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf).

This simpler class allows for _trivial_ relative entropies, such as `-log tr(ρ⁰σ)`.
Use mixing `RelEntropy.Nontrivial` to only allow nontrivial relative entropies. -/
class RelEntropy : Prop where
  /-- The data processing inequality -/
  DPI {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ σ : MState d₁) (Λ : CPTPMap d₁ d₂) : f (Λ ρ) (Λ σ) ≤ f ρ σ
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂), f (ρ₁ ⊗ᴹ ρ₂) (σ₁ ⊗ᴹ σ₂) = f ρ₁ σ₁ + f ρ₂ σ₂
  /-- Normalization of entropy to be `ln N` for a pure state vs. uniform on `N` many states. -/
  normalized {d : Type u} [fin : Fintype d] [DecidableEq d] [Nonempty d] (i : d) :
    f (.ofClassical (.constant i)) MState.uniform.M =
      some ⟨Real.log fin.card, Real.log_nonneg (mod_cast Fintype.card_pos)⟩

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf). -/
class RelEntropy.Nontrivial [RelEntropy f] where
  /-- Nontriviality condition for a relative entropy. -/
  nontrivial (d) [Fintype d] [DecidableEq d] : ∃ (ρ σ : MState d),
    ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ

namespace RelEntropy

variable {d : Type u} [Fintype d] [DecidableEq d]
variable {d₂ : Type u} [Fintype d₂] [DecidableEq d₂]

variable [RelEntropy f]

section possibly_trivial

/-
At some point we might want to offer a different constructor so that `normalized` only checks
it for domains of size 2, which is sufficient (see Tomamichel's proof). In that case, the
fact that it's still zero when `Unique d` has to be proven, and this (now used) chunk of a proof
can be used in part for that:

-- have h_uniq (ρ') := (Subsingleton.allEq ρ ρ').symm
-- have h_kron := of_kron (f := f) ρ ρ ρ ρ
-- let e : d ≃ (d × d) := (Equiv.prodUnique d d).symm
-- rw [← relabel_eq f e] at h_kron
-- rw [h_uniq ((ρ⊗ρ).relabel e)] at h_kron
-- rw [h_uniq σ]

At that point we need the fact that it's not `⊤`, and then it must be zero.

-/

/-- Relabelling a state with `CPTPOp.ofEquiv` leaves relative entropies unchanged. -/
@[simp]
theorem of_equiv_eq (e : d ≃ d₂) (ρ σ : MState d) :
    f (CPTPOp.ofEquiv e ρ) (CPTPOp.ofEquiv e σ) = f ρ σ := by
  have hinv : ∀ τ : MState d, (CPTPOp.ofEquiv e.symm) ((CPTPOp.ofEquiv e) τ) = τ := by
    intro τ
    simp
  refine le_antisymm (DPI ρ σ _) ?_
  calc f ρ σ
      = f ((CPTPOp.ofEquiv e.symm) ((CPTPOp.ofEquiv e) ρ))
          ((CPTPOp.ofEquiv e.symm) ((CPTPOp.ofEquiv e) σ)) := by rw [hinv, hinv]
    _ ≤ f ((CPTPOp.ofEquiv e) ρ) ((CPTPOp.ofEquiv e) σ) := DPI _ _ _

/-- Relabelling a state with `MState.relabel` leaves relative entropies unchanged. -/
@[simp]
theorem relabel_eq (e : d₂ ≃ d) (ρ σ : MState d) :
    f (ρ.relabel e) (σ.relabel e) = f ρ σ := by
  have h : ∀ τ : MState d, τ.relabel e = (CPTPOp.ofEquiv e.symm) τ := by
    intro τ
    rw [CPTPOp.ofEquiv_apply, Equiv.symm_symm]
  rw [h, h]
  exact of_equiv_eq f e.symm ρ σ

--Tomamichel's "4. Positivity" theorem is implicit true in our description because we
--only allow ENNReals. The only part to prove is that "D(ρ‖σ) = 0 if ρ = σ".

/-- The relative entropy is zero between any two states on a 1-D Hilbert space. -/
private lemma wrt_self_eq_zero' [Unique d] (ρ σ : MState d) : f ρ σ = 0 := by
  have h := normalized (f := f) (d := d) default
  rw [Subsingleton.allEq (MState.ofClassical (ProbDistribution.constant default)) ρ,
    Subsingleton.allEq (MState.uniform (d := d)) σ] at h
  rw [h]
  simp
  rfl

/-- The relative entropy `D(ρ‖ρ) = 0`. -/
@[simp]
theorem wrt_self_eq_zero (ρ : MState d) : f ρ ρ.M = 0 := by
  rw [← nonpos_iff_eq_zero, ← wrt_self_eq_zero' f (d := PUnit) default default]
  have h := DPI (f := f) (default : MState PUnit) default (CPTPOp.replacement ρ)
  rwa [CPTPOp.replacement_apply] at h

end possibly_trivial

section nontrivial
variable [Nontrivial f]

/-- A nontrivial relative entropy is **faithful**, it can distinguish when two states are equal. -/
theorem faithful (ρ σ : MState d) : f ρ σ = 0 ↔ ρ = σ := by
  sorry

end nontrivial

section bounds

open Prob in
/-- Quantum relative min-entropy. -/
def min (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  —log ⟨_, ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ, HermitianMat.projLE_le_one _ _⟩⟩

@[aesop (rule_sets := [finiteness]) simp]
theorem min_eq_top_iff (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ) = ⊤ ↔ ρ.M.support ≤ σ.ker := by
  open scoped HermitianMat in
  have h₂ : {0 ≤ₚ σ}.ker = σ.ker := by
    sorry --missing simp lemma
  simp [min, Prob.negLog_eq_top_iff, MState.exp_val_eq_zero_iff, Subtype.ext_iff, HermitianMat.projLE_nonneg, h₂]

open scoped HermitianMat in
protected theorem toReal_min (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ).toReal = -Real.log (ρ.exp_val {0 ≤ₚ σ}) :=
  Prob.negLog_pos_Real

/-- Min-relative entropy is a valid entropy function, albeit trivial (and not faithful). -/
instance : RelEntropy min where
  DPI := sorry
  of_kron := sorry
  normalized := sorry

theorem not_Nontrivial_min : ¬Nontrivial min := by
  rintro ⟨h⟩
  obtain ⟨ρ, σ, h₁, h₂, h₃⟩ := h (ULift (Fin 2))
  replace h₂ : HermitianMat.projLE 0 σ = (1 : HermitianMat (ULift (Fin 2)) ℂ) := by
    sorry--TODO
  simp [min, Subtype.ext_iff, h₂] at h₃

/-- The relative min-entropy is a lower bound on all relative entropies. -/
theorem min_le (ρ σ : MState d) : min ρ σ ≤ f ρ σ := by
  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)

open Classical in
/-- Quantum relative max-entropy. -/
def max (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  if ∃ (x : ℝ), ρ.M ≤ Real.exp x • σ then
    ((sInf { x : NNReal | ρ.M ≤ Real.exp x • σ } : ℝ≥0) : ℝ≥0∞)
  else
    ⊤

@[aesop (rule_sets := [finiteness]) simp]
protected theorem max_not_top (ρ : MState d) (σ : HermitianMat d ℂ) :
    (max ρ σ) ≠ ⊤ ↔ σ.ker ≤ ρ.M.ker := by
  constructor
  · sorry
  · intro
    have hex : ∃ (x : ℝ), ρ.M ≤ Real.exp x • σ := by
      sorry --log ("min nonzero eigenvalue of σ" / "max eigenvalue of ρ") should work
    rw [max, if_pos hex]
    exact ENNReal.coe_ne_top

protected theorem toReal_max (ρ : MState d) (σ : HermitianMat d ℂ) :
    (max ρ σ).toReal = sInf { x : ℝ | ρ.M ≤ Real.exp x • σ } := by
  rw [max]
  split_ifs with h
  · have : { x : ℝ | ρ.M ≤ Real.exp x • σ }.Nonempty := h
    simp
    sorry
  · push Not at h
    simp [h]

/-- The relative max-entropy is a lower bound on all relative entropies. -/
theorem le_max (ρ σ : MState d) : f ρ σ ≤ max ρ σ := by
  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)

end bounds

end RelEntropy

class Entropy (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → ℝ≥0) where
  /-- The entropy of a pure state is zero -/
  of_const {d : Type u} [Fintype d] [DecidableEq d] (ψ : Ket d) : f (.pure ψ) = 0
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ : MState d₁) (σ : MState d₂), f (ρ ⊗ᴹ σ) = f ρ + f σ
  -- /-- Entropy is convex. TODO def? Or do we even need this? -/
  -- convex : True := by trivial
