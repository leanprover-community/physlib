/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.Positivity

/-!
# An outgoing number measurement and the infalling vacuum

Bogoliubov ladder operators.

## i. Overview

In the two-mode reduction of AMPS §2, Eq. (2.2), let `b` be the outgoing packet, `c`
its independent partner, and `a = α b + β c†` an infalling annihilator. The number-basis
coordinates below realize both oscillators on their full occupation ranges. Other degrees
of freedom may remain entangled with the partner and are indexed by `E`.

For canonical coefficients `|α|² - |β|² = 1`, `a` is a normalized annihilator.
The coefficient inequalities below also hold before this normalization.

An outgoing number measurement prepares a branch supported on a single `b`-occupation.
In this branch `b` and `c†` have disjoint outgoing occupations. This proves that the
infalling vacuum condition fails for nonzero mixing. On the quadratic-form domain of the
number observable it gives the quantitative bound `⟨N_a⟩ ≥ |β|²`.

## ii. Key results

* `numberSharp_projectNumber`
* `infalling_at_sharp`

## iii. Table of contents

- A. Bogoliubov ladder operators
- B. A normalized smooth state and its outgoing density matrix

## iv. References

* [ref: Almheiri2013]

## A. Bogoliubov ladder operators
-/

@[expose] public section

noncomputable section

namespace AMPS.Packet

/-- Number-basis coefficients of the outgoing mode, its partner, and a spectator system. -/
abbrev Amplitude (E : Type*) := (ℕ × ℕ × E) → ℂ

variable {E : Type*}

/-- A branch with a definite outgoing number `n`; the other coordinates are unrestricted. -/
def NumberSharp (ψ : Amplitude E) (n : ℕ) : Prop :=
  ∀ k m e, k ≠ n → ψ (k, m, e) = 0

/-- The unnormalized branch selected by the outgoing packet's number projector. -/
def projectNumber (n : ℕ) (ψ : Amplitude E) : Amplitude E :=
  fun p => if p.1 = n then ψ p else 0

lemma numberSharp_projectNumber (n : ℕ) (ψ : Amplitude E) :
    NumberSharp (projectNumber n ψ) n := by
  intro k m e hk
  simp [projectNumber, hk]

/-- The coefficient of `(α b + β c†) ψ` at output occupations `(k,m)`.
The square roots are the standard bosonic ladder coefficients. -/
def infalling (α β : ℂ) (ψ : Amplitude E) : Amplitude E
  | (k, 0, e) => α * (Real.sqrt (k + 1) : ℂ) * ψ (k + 1, 0, e)
  | (k, m + 1, e) => α * (Real.sqrt (k + 1) : ℂ) * ψ (k + 1, m + 1, e) +
      β * (Real.sqrt (m + 1) : ℂ) * ψ (k, m, e)

/-- At outgoing number `n` the lowering term is zero on a number-`n` branch. -/
lemma infalling_at_sharp {ψ : Amplitude E} {n : ℕ} (h : NumberSharp ψ n)
    (α β : ℂ) (m : ℕ) (e : E) :
    infalling α β ψ (n, m + 1, e) = β * (Real.sqrt (m + 1) : ℂ) * ψ (n, m, e) := by
  simp [infalling, h (n + 1) (m + 1) e (Nat.succ_ne_self n)]

/-- A nonzero sharp outgoing number state cannot be an infalling vacuum for nonzero mixing. -/
lemma numberSharp_not_vacuum {ψ : Amplitude E} {n : ℕ} {α β : ℂ}
    (h : NumberSharp ψ n) (hβ : β ≠ 0) (hψ : ψ ≠ 0) : infalling α β ψ ≠ 0 := by
  intro hvac
  apply hψ
  funext ⟨k, m, e⟩
  by_cases hk : k = n
  · subst k
    have hz := congrFun hvac (n, m + 1, e)
    rw [infalling_at_sharp h] at hz
    have hs : (Real.sqrt (m + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.sqrt (m + 1) ≠ 0 by positivity)
    simpa [hβ, hs] using hz
  · exact h k m e hk

private def raisePartner (p : ℕ × ℕ × E) : ℕ × ℕ × E := (p.1, p.2.1 + 1, p.2.2)

private lemma raisePartner_injective : Function.Injective (raisePartner (E := E)) := by
  rintro ⟨k, m, e⟩ ⟨l, j, t⟩ h
  simpa [raisePartner] using h

/-- At the shifted output each input coefficient contributes at least its mass times
`|β|²`. Amplitudes in other outgoing sectors vanish by sharpness. -/
private lemma mass_le_raised_output {ψ : Amplitude E} {n : ℕ} (h : NumberSharp ψ n)
    (α β : ℂ) (p : ℕ × ℕ × E) :
    β.normSq * (ψ p).normSq ≤ (infalling α β ψ (raisePartner p)).normSq := by
  obtain ⟨k, m, e⟩ := p
  by_cases hk : k = n
  · subst k
    rw [raisePartner, infalling_at_sharp h, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]
    have hm : (1 : ℝ) ≤ m + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Complex.normSq_nonneg _) hm)
      (Complex.normSq_nonneg _)
  · rw [h k m e hk, Complex.normSq_zero, mul_zero]
    exact Complex.normSq_nonneg _

/-- On a normalized sharp branch in the domain of `a`, the expected infalling particle
number `‖a ψ‖²` is at least `|β|²`. Summability is explicit so an infinite quadratic
form cannot accidentally acquire Lean's default real-valued `tsum` of zero. -/
lemma numberSharp_occupation_ge {ψ : Amplitude E} {n : ℕ} {α β : ℂ}
    (h : NumberSharp ψ n) (hnorm : HasSum (fun p => (ψ p).normSq) 1)
    (hdom : Summable (fun p => (infalling α β ψ p).normSq)) :
    β.normSq ≤ ∑' p, (infalling α β ψ p).normSq := by
  let f := fun p => (infalling α β ψ p).normSq
  have hsub : Summable (f ∘ raisePartner) := hdom.comp_injective raisePartner_injective
  have hbase := hnorm.mul_left β.normSq
  calc
    β.normSq = ∑' p, β.normSq * (ψ p).normSq := by simpa using hbase.tsum_eq.symm
    _ ≤ ∑' p, (f ∘ raisePartner) p :=
      hbase.summable.tsum_le_tsum (mass_le_raised_output h α β) hsub
    _ ≤ ∑' p, f p :=
      tsum_comp_le_tsum_of_inj hdom (fun _ => Complex.normSq_nonneg _) raisePartner_injective

/-- For a packet given nonnegative infalling energy `ω` per quantum (in units `ℏ = 1`),
the mean excitation energy above vacuum is bounded below by `ω |β|²`. -/
lemma numberSharp_energy_ge {ψ : Amplitude E} {n : ℕ} {α β : ℂ} {ω : ℝ}
    (h : NumberSharp ψ n) (hnorm : HasSum (fun p => (ψ p).normSq) 1)
    (hdom : Summable (fun p => (infalling α β ψ p).normSq)) (hω : 0 ≤ ω) :
    ω * β.normSq ≤ ω * ∑' p, (infalling α β ψ p).normSq :=
  mul_le_mul_of_nonneg_left (numberSharp_occupation_ge h hnorm hdom) hω

/-! ## B. A normalized smooth state and its outgoing density matrix -/

/-- The two-mode squeezed state with amplitudes `√(1-|q|²) qⁿ` on `|n,n⟩`.
Its physical parameter range is `|q|² < 1`. -/
def squeezed (q : ℂ) : Amplitude Unit := fun p =>
  if p.1 = p.2.1 then (Real.sqrt (1 - q.normSq) : ℂ) * q ^ p.1 else 0

/-- Every admissible squeezing ratio comes from canonical Bogoliubov coefficients.
The first identity normalizes the oscillator, and the second cancels the vacuum terms. -/
lemma canonical_coefficients {q : ℂ} (hq : q.normSq < 1) :
    ∃ α β : ℂ, α.normSq - β.normSq = 1 ∧ α * q + β = 0 ∧ (β = 0 ↔ q = 0) := by
  let α : ℂ := ((Real.sqrt (1 - q.normSq) : ℝ) : ℂ)⁻¹
  have hpos : 0 < 1 - q.normSq := sub_pos.mpr hq
  have hα : α ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hαsq : α.normSq = (1 - q.normSq)⁻¹ := by
    simp [α, Complex.normSq_ofReal, Real.mul_self_sqrt hpos.le]
  refine ⟨α, -(α * q), ?_, by simp, by simp [hα]⟩
  rw [Complex.normSq_neg, Complex.normSq_mul, hαsq, ← mul_one_sub, inv_mul_cancel₀ hpos.ne']

/-- Normalization on the full two-oscillator space, from the convergent geometric series. -/
lemma squeezed_normalized {q : ℂ} (hq : q.normSq < 1) :
    HasSum (fun p => (squeezed q p).normSq) 1 := by
  let diag : ℕ → ℕ × ℕ × Unit := fun n => (n, n, ())
  have hinj : Function.Injective diag := fun _ _ h => congrArg Prod.fst h
  apply (hinj.hasSum_iff (f := fun p => (squeezed q p).normSq) ?_).mp
  · have h := (hasSum_geometric_of_lt_one (Complex.normSq_nonneg q) hq).mul_left (1 - q.normSq)
    rw [mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt hq))] at h
    apply h.congr_fun
    intro n
    simp [diag, squeezed, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt
      (sub_nonneg.mpr hq.le)]
  · rintro ⟨k, m, ⟨⟩⟩ h
    have hkm : k ≠ m := by
      rintro rfl
      exact h ⟨k, rfl⟩
    simp [squeezed, hkm]

/-- Cancellation of the two ladder terms in the squeezed superposition. -/
lemma squeezed_is_vacuum (q α β : ℂ) (h : α * q + β = 0) :
    infalling α β (squeezed q) = 0 := by
  funext ⟨k, m, e⟩
  cases m with
  | zero => simp [infalling, squeezed]
  | succ m =>
    by_cases hkm : k = m
    · subst k
      simp only [infalling, squeezed, ite_true, Pi.zero_apply, pow_succ]
      linear_combination ((Real.sqrt (m + 1) : ℂ) * (Real.sqrt (1 - q.normSq) : ℂ) * q ^ m) * h
    · simp [infalling, squeezed, hkm]

/-- The other infalling annihilator uses the same canonical pair of coefficients
and exchanges the outgoing and partner occupations. -/
def partnerInfalling (α β : ℂ) (ψ : Amplitude E) : Amplitude E :=
  fun p => infalling α β (fun j => ψ (j.2.1, j.1, j.2.2)) (p.2.1, p.1, p.2.2)

private lemma lower_offDiagonal {α β : ℂ} {ψ : Amplitude E}
    (hα : α ≠ 0) (h : infalling α β ψ = 0) (e : E) :
    ∀ k m, m < k → ψ (k,m,e) = 0 := by
  intro k m
  induction m generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k =>
      intro _
      have hk := congrFun h (k,0,e)
      have hs : (Real.sqrt (k + 1) : ℂ) ≠ 0 := by
        exact_mod_cast (show Real.sqrt (k + 1) ≠ 0 by positivity)
      simpa [infalling, hα, hs] using hk
  | succ m ih =>
    cases k with
    | zero => simp
    | succ k =>
      intro hlt
      have hk := congrFun h (k,m+1,e)
      have hs : (Real.sqrt (k + 1) : ℂ) ≠ 0 := by
        exact_mod_cast (show Real.sqrt (k + 1) ≠ 0 by positivity)
      simpa [infalling, ih k (Nat.lt_of_succ_lt_succ hlt), hα, hs] using hk

/-- The joint kernel of the two infalling annihilators is precisely the
geometric diagonal, up to its zero-occupation coefficient for each spectator.
This is a coefficient-domain statement for the actual two ladder operators. -/
lemma jointVacuum_coefficients {q α β : ℂ} {ψ : Amplitude E}
    (hα : α ≠ 0) (hq : α * q + β = 0)
    (hleft : infalling α β ψ = 0) (hright : partnerInfalling α β ψ = 0) :
    ∀ k m e, ψ (k,m,e) = if k = m then q ^ k * ψ (0,0,e) else 0 := by
  have hswap : infalling α β (fun p => ψ (p.2.1,p.1,p.2.2)) = 0 := by
    funext ⟨k, m, e⟩
    exact congrFun hright (m,k,e)
  have hdiag (e : E) (k : ℕ) : ψ (k,k,e) = q ^ k * ψ (0,0,e) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have ht := congrFun hleft (k,k+1,e)
      have hb : β = -(α * q) := eq_neg_of_add_eq_zero_right hq
      have hs : (Real.sqrt (k + 1) : ℂ) ≠ 0 := by
        exact_mod_cast (show Real.sqrt (k + 1) ≠ 0 by positivity)
      replace ht : (α * (Real.sqrt (k + 1) : ℂ)) *
          (ψ (k+1,k+1,e) - q * ψ (k,k,e)) = 0 := by
        simp only [infalling, Pi.zero_apply, hb] at ht
        linear_combination ht
      rw [mul_eq_zero, sub_eq_zero] at ht
      rw [ht.resolve_left (mul_ne_zero hα hs), ih, pow_succ]
      ring
  intro k m e
  rcases lt_trichotomy k m with h | rfl | h
  · simpa [h.ne] using lower_offDiagonal hα hswap e m k h
  · simpa using hdiag e k
  · simpa [h.ne.symm] using lower_offDiagonal hα hleft e k m h

/-- The outgoing reduced density matrix of the squeezed state is diagonal with geometric
weights. Its full matrix, including coherences, is computed by tracing out the partner. -/
lemma squeezed_outgoing_marginal {q : ℂ} (hq : q.normSq < 1) (n n' : ℕ) :
    ∑' m : ℕ, squeezed q (n, m, ()) * star (squeezed q (n', m, ())) =
      if n = n' then (((1 - q.normSq) * q.normSq ^ n : ℝ) : ℂ) else 0 := by
  rw [tsum_eq_single n (fun m hm => by simp [squeezed, Ne.symm hm])]
  by_cases hnn : n = n'
  · subst n'
    simp only [squeezed, ite_true]
    rw [show ∀ z : ℂ, z * star z = (z.normSq : ℂ) from Complex.mul_conj]
    simp [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.mpr hq.le)]
  · simp [squeezed, hnn, Ne.symm hnn]

end AMPS.Packet
