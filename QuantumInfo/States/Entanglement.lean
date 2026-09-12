/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa
-/
module

public import QuantumInfo.States.Pure.Braket
public import QuantumInfo.States.Ensemble
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.ClassicalInfo.Entropy

/-!
Entanglement measures. (Mixed) convex roof extensions. Definition of product / separable / entangled states
are in `Braket.lean` and/or `MState.lean`

Important definitions:
 * `convex_roof`: Convex roof extension of `g : KetUpToPhase d → ℝ≥0`
 * `mixed_convex_roof`: Mixed convex roof extension of `f : MState d → ℝ≥0`
 * `EoF`: Entanglement of Formation

TODO:
 - Other entanglement measures (not necessarily based on convex roof extensions). In roughly increasing order of
   difficulty to implement: (Logarithmic) Negativity, Entanglement of Purification, Squashed Entanglement, Relative
   Entropy of Entanglement, Entanglement Cost, Distillable Entanglement.
   For a compendium on the zoo of entanglement measures, see
   [1] Christandl, Matthias. “The Structure of Bipartite Quantum States - Insights from Group Theory and Cryptography.”
       https://doi.org/10.48550/arXiv.quant-ph/0604183.
 - Define classes of entanglement measures with good properties, including: monotonicity under LOCC (easier: just LO),
   monotonicity on average under LOCC, convexity (if the latter two are present, it is called an entanglement monotone
   by some), vanishing on separable states, normalized on the maximally entangled state, (sub)additivity, regularisible.
   For other properties, see [1] above and:
   [2] Szalay, Szilárd. “Multipartite Entanglement Measures.” (mainly Sec. IV)
       https://doi.org/10.1103/PhysRevA.92.042329.
   [3] Horodecki, Ryszard, Paweł Horodecki, Michał Horodecki, and Karol Horodecki. “Quantum Entanglement.”
       https://doi.org/10.1103/RevModPhys.81.865.
 - Useful properties of convex roof extensions:
   1. If f is monotonically non-increasing under LOCC, so is its convex roof.
   2. If f ψ is zero if and only if ψ is a product state, then its convex roof is faithful: zero if and only if
      the mixed state is separable
   For other properties, see Sec. IV.F of [2] above.
-/

@[expose] public section

noncomputable section

open ENNReal
open NNReal
open MState
open Ensemble

/-- Convex roof extension of a function `g : KetUpToPhase d → ℝ≥0`, defined as the infimum of all pure-state
ensembles of a given `ρ` of the average of `g` in that ensemble.

This is valued in the extended nonnegative real numbers `ℝ≥0∞` to have good properties of the infimum, which
come from the fact that `ℝ≥0∞` is a complete lattice. For example, it is necessary for `le_iInf` and `iInf_le_of_le`.
However, it is also proven in `convex_roof_ne_top` that the convex roof is never `∞`, so the definition `convex_roof` should
be used in most applications. -/
def convex_roof_ENNReal {d : Type _} [Fintype d] [DecidableEq d] (g : KetUpToPhase d → ℝ≥0) : MState d → ℝ≥0∞ := fun ρ =>
  ⨅ (n : ℕ+) (e : PEnsemble d (Fin n)) (_ : mix (toMEnsemble e) = ρ), ↑(pure_average_NNReal (g ∘ KetUpToPhase.mk) e)

/-- Mixed convex roof extension of a function `f : MState d → ℝ≥0`, defined as the infimum of all mixed-state
ensembles of a given `ρ` of the average of `f` on that ensemble.

This is valued in the extended nonnegative real numbers `ℝ≥0∞` to have good properties of the infimum, which
come from the fact that `ℝ≥0∞` is a complete lattice (see `ENNReal.instCompleteLinearOrder`). However,
it is also proven in `mixed_convex_roof_ne_top` that the mixed convex roof is never `∞`, so the definition `mixed_convex_roof` should
be used in most applications. -/
def mixed_convex_roof_ENNReal {d : Type _} [Fintype d] [DecidableEq d] (f : MState d → ℝ≥0) : MState d → ℝ≥0∞ := fun ρ =>
  ⨅ (n : ℕ+) (e : MEnsemble d (Fin n)) (_ : mix e = ρ), ↑(average_NNReal f e)

variable {d d₁ d₂ : Type _} [Fintype d] [Fintype d₁] [Fintype d₂] [Nonempty d] [Nonempty d₁] [Nonempty d₂]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂]
variable (f : MState d → ℝ≥0)
variable (g : KetUpToPhase d → ℝ≥0)

set_option backward.isDefEq.respectTransparency false in
/-- The convex roof extension `convex_roof_ENNReal` is never ∞. -/
theorem convex_roof_ne_top : ∀ ρ, convex_roof_ENNReal g ρ ≠ ∞ := fun ρ => by
  simp only [convex_roof_ENNReal, ne_eq, iInf_eq_top, coe_ne_top, imp_false, not_forall]
  use ⟨Fintype.card d, Fintype.card_pos⟩
  have ed : d ≃ Fin ↑(⟨Fintype.card d, Fintype.card_pos⟩ : ℕ+) := by
    simp only
    exact Fintype.equivFin d
  use (congrPEnsemble ed) <| spectral_ensemble ρ
  rw [mix_congrPEnsemble_eq_mix ed]
  push Not
  convert spectral_ensemble_mix

omit [Nonempty d] in
/-- The convex roof extension `mixed_convex_roof_ENNReal` is never ∞. -/
theorem mixed_convex_roof_ne_top : ∀ ρ, mixed_convex_roof_ENNReal f ρ ≠ ∞ := fun ρ => by
  simp only [mixed_convex_roof_ENNReal, ne_eq, iInf_eq_top, coe_ne_top, imp_false, not_forall]
  use 1, trivial_mEnsemble ρ 0
  push Not
  exact trivial_mEnsemble_mix ρ 0

/-- Convex roof extension of a function `g : KetUpToPhase d → ℝ≥0`, defined as the infimum of all pure-state
ensembles of a given `ρ` of the average of `g` in that ensemble.

This is valued in the nonnegative real numbers `ℝ≥0` by applying `ENNReal.toNNReal` to `convex_roof_ENNReal`. Hence,
it should be used in proofs alongside `convex_roof_ne_top`. -/
def convex_roof : MState d → ℝ≥0 := fun x ↦ (convex_roof_ENNReal g x).untop (convex_roof_ne_top g x)

/-- Mixed convex roof extension of a function `f : MState d → ℝ≥0`, defined as the infimum of all mixed-state
ensembles of a given `ρ` of the average of `f` on that ensemble.

This is valued in the nonnegative real numbers `ℝ≥0` by applying `ENNReal.toNNReal` to `mixed_convex_roof_ENNReal`. Hence,
it should be used in proofs alongside `mixed_convex_roof_ne_top`. -/
def mixed_convex_roof : MState d → ℝ≥0 := fun x ↦ (mixed_convex_roof_ENNReal f x).untop (mixed_convex_roof_ne_top f x)

/-- Auxiliary function. Convex roof of a function `f : MState d → ℝ≥0` defined over mixed states by
restricting `f` to pure states, via `pureQ : KetUpToPhase d → MState d`. -/
def convex_roof_of_MState_fun : MState d → ℝ≥0 := convex_roof (f ∘ pureQ)

-- TODO: make `le_convex_roof`, `convex_roof_le`, `le_mixed_convex_roof` and `mixed_convex_roof_le` if-and-only-if statements.

set_option backward.isDefEq.respectTransparency false in
omit [Nonempty d] in
theorem le_mixed_convex_roof (ρ : MState d) :
  (∀ n > 0, ∀ e : MEnsemble d (Fin n), mix e = ρ → c ≤ average_NNReal f e) → (c ≤ mixed_convex_roof f ρ) := fun h => by
  unfold mixed_convex_roof
  rw [WithTop.le_untop_iff]
  apply le_iInf; intro ⟨n, hnpos⟩; apply le_iInf; intro e; apply le_iInf; intro hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h n hnpos e hmix

set_option backward.isDefEq.respectTransparency false in
theorem le_convex_roof (ρ : MState d) :
  (∀ n > 0, ∀ e : PEnsemble d (Fin n), mix (toMEnsemble e) = ρ → c ≤ pure_average_NNReal (g ∘ KetUpToPhase.mk) e) → (c ≤ convex_roof g ρ) := fun h => by
  unfold convex_roof
  rw [WithTop.le_untop_iff]
  apply le_iInf; intro ⟨n, hnpos⟩; apply le_iInf; intro e; apply le_iInf; intro hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h n hnpos e hmix

set_option backward.isDefEq.respectTransparency false in
theorem convex_roof_le (ρ : MState d):
(∃ n > 0, ∃ e : PEnsemble d (Fin n), mix (toMEnsemble e) = ρ ∧ pure_average_NNReal (g ∘ KetUpToPhase.mk) e ≤ c) → (convex_roof g ρ ≤ c) := fun h => by
  obtain ⟨n, hnpos, e, hmix, h⟩ := h
  unfold convex_roof
  rw [WithTop.untop_le_iff]
  apply iInf_le_of_le ⟨n, hnpos⟩; apply iInf_le_of_le e; apply iInf_le_of_le hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h

set_option backward.isDefEq.respectTransparency false in
omit [Nonempty d] in
theorem mixed_convex_roof_le (ρ : MState d):
(∃ n > 0, ∃ e : MEnsemble d (Fin n), mix e = ρ ∧ average_NNReal f e ≤ c) → (mixed_convex_roof f ρ ≤ c) := fun h => by
  obtain ⟨n, hnpos, e, hmix, h⟩ := h
  unfold mixed_convex_roof
  rw [WithTop.untop_le_iff]
  apply iInf_le_of_le ⟨n, hnpos⟩; apply iInf_le_of_le e; apply iInf_le_of_le hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h

/-- The mixed convex roof extension of `f` is smaller than or equal to its convex roof extension, since
the former minimizes over a larger set of ensembles. -/
theorem mixed_convex_roof_le_convex_roof : mixed_convex_roof f ≤ convex_roof_of_MState_fun f := by
  intro ρ
  apply le_convex_roof (f ∘ pureQ) ρ
  intro n hnpos e hmix
  apply mixed_convex_roof_le
  use n
  apply And.intro hnpos
  use ↑e
  apply And.intro hmix
  exact le_of_eq <| NNReal.coe_inj.mp <| average_of_pure_ensemble (toReal ∘ f) e

set_option backward.isDefEq.respectTransparency false in
/-- The convex roof extension of `g : KetUpToPhase d → ℝ≥0` applied to a pure state `ψ` is `g (KetUpToPhase.mk ψ)`. -/
theorem convex_roof_of_pure (ψ : Ket d) : convex_roof g (pure ψ) = g (KetUpToPhase.mk ψ) := by
  rw [le_antisymm_iff]
  constructor
  · apply convex_roof_le
    use 1; simp only [gt_iff_lt, zero_lt_one, true_and]; use trivial_pEnsemble ψ 0
    constructor
    · exact trivial_pEnsemble_mix ψ 0
    · simp only [pure_average_NNReal, Fin.isValue, ← NNReal.coe_le_coe]
      conv_lhs =>
        enter [1, 1]
        rw [trivial_pEnsemble_average ψ _ 0]
      rfl
  · apply le_convex_roof
    intro n hnpos e hmix
    apply le_of_eq
    simp only [pure_average_NNReal, ← NNReal.coe_inj]
    have hphase_inv : ∀ a b, Ket.PhaseEquiv.r a b →
        (NNReal.toReal ∘ g ∘ KetUpToPhase.mk) a = (NNReal.toReal ∘ g ∘ KetUpToPhase.mk) b := by
      intro a b hab
      simp only [Function.comp_apply]
      congr 1
      exact congrArg g (Quotient.sound hab)
    simp [mix_pEnsemble_pure_average (NNReal.toReal ∘ g ∘ KetUpToPhase.mk) hphase_inv hmix]
    rfl

set_option backward.isDefEq.respectTransparency false in
omit [Nonempty d] in
/-- The mixed convex roof extension of `f : MState d → ℝ≥0` applied to a pure state `ψ` is `f (pure ψ)`. -/
theorem mixed_convex_roof_of_pure (ψ : Ket d) : mixed_convex_roof f (pure ψ) = f (pure ψ) := by
  rw [le_antisymm_iff]
  constructor
  · apply mixed_convex_roof_le
    use 1; simp only [gt_iff_lt, zero_lt_one, true_and]; use trivial_mEnsemble (pure ψ) 0
    constructor
    · exact trivial_mEnsemble_mix (pure ψ) 0
    · simp only [average_NNReal, Fin.isValue, ← NNReal.coe_le_coe]
      conv_lhs =>
        enter [1, 1]
        rw [trivial_mEnsemble_average _ (pure ψ) 0]
      rfl
  · apply le_mixed_convex_roof
    intro n hnpos e hmix
    replace hpure := mix_mEnsemble_pure_iff_pure.mp hmix
    apply le_of_eq
    simp only [average_NNReal, ← NNReal.coe_inj]
    conv_rhs =>
      enter [1, 1]
      rw [mix_mEnsemble_pure_average (toReal ∘ f) hmix, Function.comp_apply]
    rfl

/-- Entanglement of Formation of bipartite systems. It is the convex roof extension of the
von Neumann entropy of one of the subsystems (here chosen to be the left one, but see `Entropy.Sᵥₙ_of_partial_eq`).

The function `Sᵥₙ ∘ traceRight ∘ pure` is phase-invariant because `pure` maps phase-equivalent kets to the
same mixed state, so it descends to `KetUpToPhase` via `pureQ`. -/
def EoF : MState (d₁ × d₂) → ℝ≥0 :=
  convex_roof (KetUpToPhase.lift
    (fun ψ ↦ ⟨Sᵥₙ (pure ψ).traceRight, Sᵥₙ_nonneg (pure ψ).traceRight⟩)
    (fun ψ φ h ↦ by
      have hpure : (pure ψ : MState (d₁ × d₂)) = pure φ :=
        (MState.PhaseEquiv_iff_pure_eq ψ φ).mp h
      simp only [hpure]
      rfl))

/-
The partial trace of the maximally entangled state is the maximally mixed state.
-/
theorem traceRight_pure_MES (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] :
    (MState.pure (Ket.MES d)).traceRight = MState.uniform := by
  ext i j
  rw [MState.traceRight_M, MState.uniform, coe_ofClassical]
  simp only [HermitianMat.mat_apply, HermitianMat.traceRight_apply, MState.pure_M_apply,
    HermitianMat.diagonal_apply, ProbDistribution.uniform_def, Ket.apply, Ket.MES, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.card_univ, one_div]
  rcases eq_or_ne i j with rfl | h
  · rw [if_pos rfl, if_pos rfl, map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  · rw [if_neg h, if_neg h.symm]
    simp

/-
The von Neumann entropy of a classical state (diagonal in the basis) is equal to the Shannon entropy of the corresponding distribution.
-/
theorem Sᵥₙ_ofClassical {d : Type*} [Fintype d] [DecidableEq d] (dist : ProbDistribution d) :
    Sᵥₙ (MState.ofClassical dist) = Hₛ dist := by
  have h_def : Sᵥₙ (MState.ofClassical dist) = (HermitianMat.cfc (MState.ofClassical dist).M Real.negMulLog).trace :=
    Sᵥₙ_eq_trace_cfc_negMulLog (ι := d) (ofClassical dist)
  convert h_def using 1;
  -- By definition of $MState.ofClassical$, we know that $(MState.ofClassical dist).M$ is a diagonal matrix with entries $dist i$.
  have h_diag : (MState.ofClassical dist).M = HermitianMat.diagonal ℂ (fun x => dist x) :=
    coe_ofClassical dist
  rw [ h_diag, HermitianMat.cfc_diagonal, HermitianMat.trace_diagonal ] ; aesop

set_option backward.isDefEq.respectTransparency false in
/-- The entanglement of formation of the maximally entangled state with on-site dimension 𝕕 is log(𝕕). -/
theorem EoF_of_MES : EoF (pure <| Ket.MES d) = Real.log (Finset.card Finset.univ (α := d)) := by
  simp only [EoF, convex_roof_of_pure, Finset.card_univ]
  simp only [KetUpToPhase.lift_mk]
  -- The von Neumann entropy of the maximally mixed state is log(d).
  have h_von_neumann : Sᵥₙ (MState.uniform : MState d) = Real.log (Fintype.card d) := by
    rw [MState.uniform, Sᵥₙ_ofClassical ProbDistribution.uniform, Hₛ_uniform, Finset.card_univ]
  simp [traceRight_pure_MES]
  exact h_von_neumann
