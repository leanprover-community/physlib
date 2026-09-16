/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.States.Mixed.Fidelity
public import QuantumInfo.States.Mixed.TraceDistance
public import Physlib.Meta.Sorry

/-!
# Quantum Capacity

## i. Overview

This file focuses on defining and proving theorems about the quantum capacity, the maximum
asymptotic rate at which quantum information can be coherently transmitted through a quantum
channel. The precise definition is not consistent in the literature, see
`QuantumInfo/Capacity/Capacity_doc.lean` for a note on what has been used and how that was used
to arrive at the following definition:

 1. A channel A `Emulates` another channel B if there are D and E such that D∘A∘E = B.
 2. A channel A `εApproximates` channel B (of the same dimensions) if for every state ρ, the
    fidelity F(A(ρ), B(ρ)) is at least 1-ε.
 3. A channel A `AchievesRate` R:ℝ if for every ε>0, n copies of A emulates some channel B such
    that log2(dimout(B))/n ≥ R, and that B is εApproximately the identity.
 4. The `quantumCapacity` of the channel A is the supremum of the achievable rates, i.e.
    `sSup { R : ℝ | AchievesRate A R }`.

## ii. Key results

The most basic facts:
 * `emulates_self`: Every channel emulates itself.
 * `emulates_trans`: If A emulates B and B emulates C, then A emulates C. (That is, emulation
   is an ordering.)
 * `εApproximates A B ε` is equivalent to the existence of some δ (depending on ε and dims(A))
   so that |A-B| has diamond norm at most δ, and δ→0 as ε→0.
 * `achievesRate_0`: Every channel out of a nonempty space achievesRate 0. So, in that case,
   the set of achievable rates is Nonempty.
 * If a channel achievesRate R₁, it also achievesRate every R₂ ≤ R₁, i.e. it is an interval
   extending left towards -∞. Achievable rates are `¬BddBelow`.
 * `bddAbove_achievesRate`: A channel C : dimX → dimY cannot achievesRate R with
   `R > log2(min(dimX, dimY))`. Thus, the interval is `BddAbove`.

The nice lemmas we would want:
 * Capacity of a replacement channel is zero.
 * Capacity of an identity channel is `log2(D)`.
 * Capacity is superadditive under tensor products. (That is, at least additive. Showing that
   it isn't _exactly_ additive, unlike classical capacity which is additive, is a much harder
   task.)
 * Capacity of a kth tensor power is exactly k times the capacity of the original channel.
 * Capacity does not decrease under tensor sums.
 * Capacity does not increase under composition.

Then, we should show that our definition is equivalent to some above. Most, except (3), should
be not too hard to prove.

Then the LSD theorem establishes that the single-copy coherent information is a lower bound.
This is stated in `coherentInfo_le_quantumCapacity`. The corollary, that the n-copy coherent
information converges to the capacity, is `quantumCapacity_eq_piProd_coherentInfo`.

TODO: The only notion of "capacity" here currently is "quantum capacity" in the usual sense.
But there are several non-equal capacities relevant to quantum channels, see e.g. [Watrous's
notes](https://cs.uwaterloo.ca/~watrous/TQI/TQI.8.pdf) for a list:
 * Quantum capacity (`quantumCapacity`)
 * Quantum 1-shot capacity
 * Entanglement-assisted classical capacity
 * Qss, the quantum side-channel capacity
 * Holevo capacity, aka Holevo χ. The Holevo–Schumacher–Westmoreland theorem as a major theorem
 * Entanglement-assisted Holevo capacity
 * Entanglement-assisted quantum capacity
 * One- and two-way distillable entanglement

And other important theorems like superdense coding, nonadditivity, superactivation.

## iii. Table of contents

- A. Basic definitions
- B. Emulation between channels
- C. Approximation between channels
- D. Achievable rates
- E. The quantum capacity

## iv. References

* Watrous's notes, Chapter 8 of The Theory of Quantum Information. [ref: watrous_tqi_ch8]
-/

@[expose] public section

namespace CPTPOp

variable {d₁ d₂ d₃ d₄ d₅ d₆ : Type*}
variable [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype d₄] [Fintype d₅] [Fintype d₆]
variable [DecidableEq d₁] [DecidableEq d₂]

/-!

## A. Basic definitions

-/

variable [DecidableEq d₃] [DecidableEq d₄] in
/--
A channel Λ₁ `Emulates` another channel Λ₂ if there are D and E such that D∘Λ₁∘E = Λ₂.
-/
def Emulates (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) : Prop :=
  ∃ (E : CPTPMap d₃ d₁) (D : CPTPMap d₂ d₄), D.compose (Λ₁.compose E) = Λ₂

/--
A channel A `εApproximates` channel B of the same dimensions if for every state ρ, the
fidelity F(A(ρ), B(ρ)) is at least 1-ε.
-/
def εApproximates (A B : CPTPMap d₁ d₂) (ε : ℝ) : Prop :=
  ∀ (ρ : MState d₁), DensityOp.fidelity (A ρ) (B ρ) ≥ 1-ε

/--
A channel A `AchievesRate` R:ℝ if for every ε>0, some n copies of A emulates a channel B such
that log2(dimout(B))/n ≥ R, and that B εApproximates the identity channel.
-/
def AchievesRate (A : CPTPMap d₁ d₂) (R : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ n > 0, ∃ (dimB : ℕ) (B : CPTPMap (Fin dimB) (Fin dimB)),
      (CPTPOp.piProd (fun (_ : Fin n) ↦ A)).Emulates B ∧
      Real.logb 2 dimB ≥ R*n ∧
      B.εApproximates CPTPOp.id ε

/-- The quantum capacity of a channel A: the supremum of all rates R such that
`A.AchievesRate R`, i.e. the maximum asymptotic rate at which quantum information can be
coherently transmitted through the channel. -/
noncomputable def quantumCapacity (A : CPTPMap d₁ d₂) : ℝ :=
  sSup { R : ℝ | AchievesRate A R }

/-!

## B. Emulation between channels

-/

section emulates
variable [DecidableEq d₃] [DecidableEq d₄] [DecidableEq d₅]

/-- Every quantum channel emulates itself. -/
@[refl]
theorem emulates_self (Λ : CPTPMap d₁ d₂) : Λ.Emulates Λ :=
  ⟨CPTPOp.id, CPTPOp.id, by simp⟩

/-- If a quantum channel A emulates B, and B emulates C, then A emulates C. -/
@[trans]
theorem emulates_trans (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) (Λ₃ : CPTPMap d₅ d₆)
    (h₁₂ : Λ₁.Emulates Λ₂) (h₂₃ : Λ₂.Emulates Λ₃) : Λ₁.Emulates Λ₃ := by
  obtain ⟨E₁, D₁, hED₁⟩ := h₁₂
  obtain ⟨E₂, D₂, hED₂⟩ := h₂₃
  exact ⟨E₁.compose E₂, D₂.compose D₁, by classical simp [← hED₁, ← hED₂, compose_assoc]⟩

end emulates

/-!

## C. Approximation between channels

-/

section εApproximates

omit [DecidableEq d₂] in
/-- Every quantum channel perfectly approximates itself, that is, `εApproximates` with `ε = 0`. -/
theorem εApproximates_self (Λ : CPTPMap d₁ d₂) : Λ.εApproximates Λ 0 :=
  fun ρ ↦ ((DensityOp.fidelity_self_eq_one (Λ ρ)).trans (sub_zero 1).symm).ge

omit [DecidableEq d₂] in
/-- If a quantum channel A approximates B with ε₀, it also approximates B with all larger ε₁. -/
theorem εApproximates_monotone {A B : CPTPMap d₁ d₂} {ε₀ : ℝ} (h : A.εApproximates B ε₀)
    {ε₁ : ℝ} (h₂ : ε₀ ≤ ε₁) : A.εApproximates B ε₁ :=
  fun ρ ↦ (tsub_le_tsub_left h₂ 1).trans (h ρ)

end εApproximates

/-!

## D. Achievable rates

-/

section AchievesRate

/-- Every quantum channel on a nonempty space achieves a rate of zero. (The hypothesis is needed:
a channel out of an empty space into a nonempty one emulates nothing at all, since an emulation
would need both a channel into the empty space and one out of the nonempty one.) -/
theorem achievesRate_0 [Nonempty d₁] (Λ : CPTPMap d₁ d₂) : Λ.AchievesRate 0 := by
  have : Nonempty d₂ := MState.nonempty (Λ default)
  intro ε hε
  refine ⟨1, zero_lt_one, 1, default, ⟨default, default, Unique.eq_default _⟩, by norm_num, ?_⟩
  rw [Unique.eq_default (id : CPTPMap (Fin 1) (Fin 1))]
  exact εApproximates_monotone (εApproximates_self default) hε.le

/-- The identity channel on D dimensional space achieves a rate of log2(D). -/
theorem id_achievesRate_log_dim :
    (id (dIn := d₁)).AchievesRate (Real.logb 2 (Fintype.card d₁)) := by
  intro ε hε
  use 1, zero_lt_one, Fintype.card d₁, id
  constructor
  · --they are equivalent up to permutation
    -- TODO: Instead this proof should be `@[simp] piProd (fun x => id) = id` and `emulates_self`
    refine' ⟨ _, _, _ ⟩;
    exact CPTPOp.ofEquiv ( Fintype.equivFinOfCardEq ( by simp +decide ) ).symm;
    exact CPTPOp.ofEquiv ( Fintype.equivFinOfCardEq ( by simp +decide ) );
    apply CPTPOp.ext_map
    simp only [compose_map, piProd_map, id_map, ofEquiv_map]
    rw [show (fun _ : Fin 1 ↦ (LinearMap.id : MatrixMap d₁ d₁ ℂ)) =
      (fun i : Fin 1 ↦ MatrixMap.id ((fun _ : Fin 1 ↦ d₁) i) ℂ) from rfl]
    simp [MatrixMap.id]
  constructor
  · norm_num
  · exact εApproximates_monotone (εApproximates_self id) hε.le

/-- A channel `D ∘ E` that factors through `d₂` can only approximate the identity channel on `d₁` if
`d₂` is nearly as large as `d₁`: each of the `card d₁` basis states `∣i⟩` must come back out of `D`
with probability at least `(1-ε)²`, and these probabilities are the expectation values of a POVM
whose total trace is only `card d₂`. -/
theorem card_mul_le_card_of_εApproximates_id (E : CPTPMap d₁ d₂) (D : CPTPMap d₂ d₁) {ε : ℝ}
    (hε : ε ≤ 1) (h : (D.compose E).εApproximates CPTPOp.id ε) :
    (Fintype.card d₁ : ℝ) * (1 - ε)^2 ≤ Fintype.card d₂ := by
  have key : ∀ i : d₁, (1 - ε)^2 ≤ (D.dual (MState.pure (Ket.basis i)).M).trace := by
    intro i
    have h1 := h (MState.pure (Ket.basis i))
    rw [ge_iff_le, compose_eq, id_MState, DensityOp.fidelity_symm, DensityOp.fidelity_pure] at h1
    have hnn : 0 ≤ MState.exp_val (D (E (MState.pure (Ket.basis i))))
        (MState.pure (Ket.basis i)).M :=
      MState.exp_val_nonneg _ (MState.pure (Ket.basis i)).nonneg
    have h2 := mul_self_le_mul_self (by linarith : (0:ℝ) ≤ 1 - ε) h1
    rw [Real.mul_self_sqrt hnn, ← sq] at h2
    calc (1 - ε)^2
        ≤ MState.exp_val (D (E (MState.pure (Ket.basis i)))) (MState.pure (Ket.basis i)).M := h2
      _ = MState.exp_val (E (MState.pure (Ket.basis i))) (D.dual (MState.pure (Ket.basis i)).M) :=
          exp_val_Dual D _ _
      _ ≤ MState.exp_val (E (MState.pure (Ket.basis i)))
            ((D.dual (MState.pure (Ket.basis i)).M).trace • 1) :=
          MState.exp_val_le_exp_val _
            (HermitianMat.le_trace_smul_one (D.dual_pos (MState.pure (Ket.basis i)).nonneg))
      _ = (D.dual (MState.pure (Ket.basis i)).M).trace := by
          rw [MState.exp_val_smul, MState.exp_val_one, mul_one]
  calc (Fintype.card d₁ : ℝ) * (1 - ε)^2 = ∑ _i : d₁, (1 - ε)^2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ i : d₁, (D.dual (MState.pure (Ket.basis i)).M).trace :=
        Finset.sum_le_sum fun i _ ↦ key i
    _ = (D.dual (∑ i : d₁, (MState.pure (Ket.basis i)).M)).trace := by
        rw [map_sum, HermitianMat.trace_sum]
    _ = Fintype.card d₂ := by rw [MState.sum_pure_basis, map_one, HermitianMat.trace_one]

/-- A channel cannot achieve a rate greater than log2(D), where D is the input dimension.

If `Λ` achieved a rate `R` above `L = log₂(D)`, then for every `ε` there would be a channel `B` on
`2^(Rn)` dimensions, `ε`-approximating the identity, that factors through the `Dⁿ`-dimensional
input of `Λ⊗ⁿ`. By `card_mul_le_card_of_εApproximates_id` that forces `2^(Rn) (1-ε)² ≤ 2^(Ln)`,
that is, `(1-ε)² ≤ 2^((L-R)n) ≤ 2^(L-R) < 1`, which fails once `ε` is small enough. -/
theorem not_achievesRate_gt_log_dim_in (Λ : CPTPMap d₁ d₂) {R : ℝ} (hR : Real.logb 2 (Fintype.card d₁) < R) :
    ¬Λ.AchievesRate R := by
  intro hach
  set L := Real.logb 2 (Fintype.card d₁) with hL
  have hL0 : 0 ≤ L := by
    rcases Nat.eq_zero_or_pos (Fintype.card d₁) with h | h
    · simp [hL, h]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hR0 : 0 < R := lt_of_le_of_lt hL0 hR
  have hpow : (0:ℝ) < 2 ^ (L - R) := Real.rpow_pos_of_pos two_pos _
  set t := Real.sqrt (2 ^ (L - R)) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hpow
  have ht1 : t < 1 := by
    rw [ht, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    refine Real.sqrt_lt_sqrt hpow.le ?_
    calc (2:ℝ) ^ (L - R) < 2 ^ (0:ℝ) :=
          (Real.rpow_lt_rpow_left_iff one_lt_two).mpr (by linarith)
      _ = 1 := Real.rpow_zero 2
  obtain ⟨n, hn, dimB, B, ⟨E', D', hED⟩, hRate, hApprox⟩ := hach ((1 - t)/2) (by linarith)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hRn : 0 < R * n := mul_pos hR0 hnR
  -- Regroup the emulation `B = D' ∘ Λ⊗ⁿ ∘ E'` as a factorization through `Fin n → d₁`.
  have hApprox' : ((D'.compose (CPTPOp.piProd fun _ : Fin n ↦ Λ)).compose E').εApproximates
      CPTPOp.id ((1 - t)/2) := by
    rw [compose_assoc, hED]
    exact hApprox
  have hcount : (dimB : ℝ) * (1 - (1 - t)/2)^2 ≤ ((Fintype.card d₁ : ℝ)) ^ n := by
    have h := card_mul_le_card_of_εApproximates_id E' (D'.compose (piProd fun _ : Fin n ↦ Λ))
      (by linarith) hApprox'
    rwa [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hd0 : 0 < dimB := by
    rcases Nat.eq_zero_or_pos dimB with h | h
    · rw [h] at hRate
      simp only [Nat.cast_zero, Real.logb_zero, ge_iff_le] at hRate
      linarith
    · exact h
  have hdimB : (2:ℝ) ^ (R * n) ≤ dimB :=
    calc (2:ℝ) ^ (R * n) ≤ 2 ^ Real.logb 2 dimB :=
          (Real.rpow_le_rpow_left_iff one_lt_two).mpr hRate
      _ = dimB := Real.rpow_logb two_pos (by norm_num) (by exact_mod_cast hd0)
  have hcard : ((Fintype.card d₁ : ℝ)) ^ n ≤ (2:ℝ) ^ (L * n) := by
    rcases Nat.eq_zero_or_pos (Fintype.card d₁) with h | h
    · rw [h, Nat.cast_zero, zero_pow hn.ne']
      positivity
    · have hc : ((Fintype.card d₁ : ℝ)) = 2 ^ L :=
        (Real.rpow_logb two_pos (by norm_num) (by exact_mod_cast h)).symm
      rw [hc, ← Real.rpow_natCast (2 ^ L) n, ← Real.rpow_mul zero_le_two]
  have hsq : (1 - (1 - t)/2)^2 ≤ t^2 := by
    rw [ht, Real.sq_sqrt hpow.le]
    have h1 : (2:ℝ) ^ (R * n) * (1 - (1 - t)/2)^2 ≤ 2 ^ (L * n) :=
      le_trans (mul_le_mul_of_nonneg_right hdimB (by positivity)) (hcount.trans hcard)
    have h2 : (2:ℝ) ^ (L * n) ≤ 2 ^ (R * n) * 2 ^ (L - R) := by
      rw [← Real.rpow_add two_pos]
      refine (Real.rpow_le_rpow_left_iff one_lt_two).mpr ?_
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_le_mul_of_nonneg_left hn1 (sub_pos.mpr hR).le]
    exact le_of_mul_le_mul_left (h1.trans h2) (Real.rpow_pos_of_pos two_pos _)
  nlinarith [mul_pos (sub_pos.mpr ht1) (show (0:ℝ) < 1 + 3*t by linarith)]

/-- A channel cannot achieve a rate greater than log2(D), where D is the output dimension. -/
@[sorryful]
theorem not_achievesRate_gt_log_dim_out (Λ : CPTPMap d₁ d₂) {R : ℝ}
    (hR : Real.logb 2 (Fintype.card d₂) < R) : ¬Λ.AchievesRate R := by
  intro h;
  -- We show that the identity channel on the output space `d₂` emulates `Λ`. Since capacity is monotonic under emulation, `Q(Λ) ≤ Q(id_{d₂})`.
  have h_emulate : (CPTPOp.id (dIn := d₂)).Emulates Λ := by
    exact ⟨Λ, CPTPOp.id, by simp⟩
  -- If `Λ` achieves rate `R`, then `id_{d₂}` achieves rate `R`. This follows because if `Λ^{\otimes n}` emulates `B`, and `id^{\otimes n}` emulates `Λ^{\otimes n}` (by functoriality of tensor product), then `id^{\otimes n}` emulates `B`.
  have h_id_achieves : (CPTPOp.id (dIn := d₂)).AchievesRate R := by
    intro ε hε_pos
    obtain ⟨n, hn, dimB, B, hB_emulate, hB_rate, hB_approx⟩ := h ε hε_pos
    have h_id_emulate : (CPTPOp.piProd (fun (_ : Fin n) => CPTPOp.id (dIn := d₂))).Emulates B := by
      -- Since `id_{d₂}` emulates `Λ`, we can use the fact that the tensor product of emulations is an emulation.
      have h_tensor_emulate : ∀ (n : ℕ), (CPTPOp.piProd (fun (_ : Fin n) => CPTPOp.id (dIn := d₂))).Emulates (CPTPOp.piProd (fun (_ : Fin n) => Λ)) := by
        intro n
        obtain ⟨E, D, hD⟩ := h_emulate
        use CPTPOp.piProd (fun (_ : Fin n) => E), CPTPOp.piProd (fun (_ : Fin n) => D);
        simp [ ← hD, ← CPTPOp.piProd_comp];
      exact emulates_trans _ _ _ ( h_tensor_emulate n ) hB_emulate;
    exact ⟨ n, hn, dimB, B, h_id_emulate, hB_rate, hB_approx ⟩;
  refine not_le_of_gt hR <| not_lt.mp fun h => ?_
  exact not_lt_of_ge ( le_of_not_gt fun h' => not_achievesRate_gt_log_dim_in _ h' h_id_achieves ) h

/-- The achievable rates are a bounded set. -/
@[sorryful]
theorem bddAbove_achievesRate (Λ : CPTPMap d₁ d₂) : BddAbove {R | Λ.AchievesRate R} := by
  use Real.logb 2 (Fintype.card d₁)
  intro R h
  contrapose h
  exact not_achievesRate_gt_log_dim_in Λ (lt_of_not_ge h)

end AchievesRate

/-!

## E. The quantum capacity

-/

section capacity

/-- Quantum channel capacity is nonnegative. -/
theorem zero_le_quantumCapacity [Nonempty d₁] (Λ : CPTPMap d₁ d₂) : 0 ≤ Λ.quantumCapacity :=
  le_csSup (bddAbove_achievesRate Λ) (achievesRate_0 Λ)

/-- Quantum channel capacity is at most log2(D), where D is the input dimension. -/
@[sorryful]
theorem quantumCapacity_ge_log_dim_in (Λ : CPTPMap d₁ d₂) :
    Λ.quantumCapacity ≤ Real.logb 2 (Fintype.card d₁) :=
  Real.sSup_le (by
    intro R h
    contrapose h
    exact not_achievesRate_gt_log_dim_in Λ (lt_of_not_ge h))
  (by
    by_cases h : Nonempty d₁
    · apply Real.logb_nonneg one_lt_two (Nat.one_le_cast.mpr Fintype.card_pos)
    · simp [not_nonempty_iff.mp h])

/-- The LSD (Lloyd-Shor-Devetak) theorem: the quantum capacity is at least as large the
single-copy coherent information. The "coherent information" is used in literature to refer to
both a function of state and a channel (`coherentInfo`), or a function of just a channel. In
the latter case, the state is implicitly maximized over. Here we use the former definition and
state that the lower bound is true for all states. -/
@[sorryful]
theorem coherentInfo_le_quantumCapacity (Λ : CPTPMap d₁ d₂) (ρ : MState d₁) :
    coherentInfo ρ Λ ≤ Λ.quantumCapacity := by
  sorry

/-- The quantum capacity is the limit of the coherent information of n-copy uses of the channel. -/
@[sorryful]
theorem quantumCapacity_eq_piProd_coherentInfo (Λ : CPTPMap d₁ d₂) : Λ.quantumCapacity =
    sSup { r : ℝ | ∃ n ρ, r = coherentInfo ρ (CPTPOp.piProd (fun (_ : Fin n) ↦ Λ))} := by
  sorry

end capacity
