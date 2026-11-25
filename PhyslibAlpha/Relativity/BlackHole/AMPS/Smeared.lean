/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A smeared outgoing number operator on the infalling vacuum

Smeared creation and annihilation.

## i. Overview

AMPS, arXiv:1207.3123v4, §2, Eq. (2.2), write an outgoing mode as a
superposition of infalling annihilation and creation operators. With the
inner product linear in its second slot our convention is `b = a(f) + a†(g)`,
where conjugation of the annihilation coefficient in the integral is absorbed
into the choice of `f`. Arbitrary complex smearing vectors are allowed, with
no orthogonality or frequency-diagonality hypothesis.

Only the Fock sectors visited in `b†b Ω` enter. On the vacuum, creation with
`g` gives the one-particle vector `g`. On a one-particle vector `h`,
annihilation with `g` gives the scalar `⟪g,h⟫`, and creation with `f` gives
the normalized symmetric tensor `(f ⊗ h + h ⊗ f)/√2`. The two-particle
component sits in the algebraic tensor product with its induced Hilbert norm;
these finite sums embed isometrically in the completed sector. The theorem
uses no domain assertion about unbounded operators on arbitrary Fock vectors.

For the sector convention see J. Dereziński and C. Gérard, *Asymptotic
completeness in quantum field theory. Massive Pauli–Fierz Hamiltonians*, §2.3.

## ii. Key results

* `map_createOne`
* `createOne_symmetric`

## iii. Table of contents

- A. Smeared creation and annihilation
- B. Transmission through the exterior barrier

## iv. References

* [ref: Almheiri2013]

## A. Smeared creation and annihilation
-/

@[expose] public section

namespace AMPS.Smeared

open scoped TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Bosonic creation on a one-particle vector, with the Fock-sector normalization. -/
def createOne (f h : H) : H ⊗[ℂ] H :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (f ⊗ₜ[ℂ] h + h ⊗ₜ[ℂ] f)

/-- Applying the same one-particle filter to both excitations restricts each of
the two Bogoliubov profiles. This identity holds before choosing a frequency band. -/
lemma map_createOne {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (filter : H →ₗ[ℂ] G) (f g : H) :
    TensorProduct.map filter filter (createOne f g) = createOne (filter f) (filter g) := by
  simp [createOne]

/-- The two-particle output of creation is invariant under interchange of particles. -/
lemma createOne_symmetric (f h : H) :
    TensorProduct.comm ℂ H H (createOne f h) = createOne f h := by
  simp [createOne, add_comm]

/-- Annihilation from the symmetric two-particle sector, extended to the full
algebraic tensor product by first symmetrizing. The two contractions select
the first and second tensor factors. -/
def annihilateTwo (f : H) : (H ⊗[ℂ] H) →ₗ[ℂ] H :=
  let left := (TensorProduct.lid ℂ H).toLinearMap.comp
    (TensorProduct.map (innerSL ℂ f).toLinearMap LinearMap.id)
  ((Real.sqrt 2 : ℂ)⁻¹) • (left + left.comp (TensorProduct.comm ℂ H H).toLinearMap)

/-- The sector creation and annihilation formulas are adjoints on all algebraic
two-particle test vectors. -/
lemma createOne_adjoint (f h : H) (t : H ⊗[ℂ] H) :
    inner ℂ (createOne f h) t = inner ℂ h (annihilateTwo f t) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp [inner_add_right, ha, hb]
  | tmul x y =>
    simp [createOne, annihilateTwo, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, TensorProduct.inner_tmul, add_comm, mul_comm]

/-- Action of `a(f) + a†(g)` from the vacuum sector to the one-particle sector.
The annihilation term kills the vacuum; `z` is the vacuum amplitude. -/
def outgoingOnVacuum (g : H) (z : ℂ) : H := z • g

/-- Projection of `b = a(f) + a†(g)` from the vacuum and two-particle sectors
onto the one-particle sector. The three-particle component of `b` on a
general two-particle input does not contribute to this matrix element. -/
def outgoingToOne (f g : H) (z : ℂ) (t : H ⊗[ℂ] H) : H :=
  outgoingOnVacuum g z + annihilateTwo f t

/-- Action of the conjugate combination `a†(f) + a(g)` from one particle
to the direct sum of vacuum and two-particle sectors. -/
def outgoingAdjointOnOne (f g h : H) : ℂ × (H ⊗[ℂ] H) :=
  (inner ℂ g h, createOne f h)

/-- The proposed `b†` on one particle obeys the adjoint identity with the
zero- and two-particle components of the bosonic ladder operators. -/
lemma outgoing_sector_adjoint (f g h : H) (z : ℂ) (t : H ⊗[ℂ] H) :
    inner ℂ h (outgoingToOne f g z t) =
      z * starRingEnd ℂ (outgoingAdjointOnOne f g h).1 +
      inner ℂ (outgoingAdjointOnOne f g h).2 t := by
  simp only [outgoingToOne, outgoingOnVacuum, outgoingAdjointOnOne, inner_add_right,
    inner_smul_right, inner_conj_symm, createOne_adjoint]

/-- The outgoing number operator `b†b` evaluated on the normalized infalling vacuum. -/
def numberOnVacuum (f g : H) : ℂ × (H ⊗[ℂ] H) :=
  outgoingAdjointOnOne f g (outgoingToOne f g 1 0)

/-- Vacuum coefficient (the mean outgoing occupation) and the excited two-particle sector. -/
lemma numberOnVacuum_components (f g : H) :
    numberOnVacuum f g = ((‖g‖ : ℂ) ^ 2, createOne f g) := by
  simp [numberOnVacuum, outgoingToOne, outgoingOnVacuum, outgoingAdjointOnOne,
    inner_self_eq_norm_sq_to_K]

/-- Interchanging the two smearings exchanges `b` with `b†`. Thus their
commutator on the vacuum has precisely the canonical normalization difference;
the two excited sectors cancel by bosonic symmetry. -/
lemma commutator_on_vacuum (f g : H) :
    numberOnVacuum g f - numberOnVacuum f g = ((‖f‖ : ℂ) ^ 2 - (‖g‖ : ℂ) ^ 2, 0) := by
  rw [numberOnVacuum_components, numberOnVacuum_components]
  have hsym : createOne g f = createOne f g := by simp [createOne, add_comm]
  rw [hsym]
  exact Prod.ext rfl (sub_self _)

/-- Exact squared norm of the excited component. The overlap term remains
present when the two wavepacket coefficients share frequencies. -/
lemma createOne_norm_sq (f g : H) :
    ‖createOne f g‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 + ‖inner ℂ f g‖ ^ 2 := by
  have hcross : RCLike.re (inner ℂ f g * inner ℂ g f) = ‖inner ℂ f g‖ ^ 2 := by
    rw [inner_mul_symm_re_eq_norm, norm_mul, norm_inner_symm g f, sq]
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [createOne, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp, mul_pow, inv_pow, hroot, norm_add_sq (𝕜 := ℂ),
      TensorProduct.inner_tmul, hcross, TensorProduct.norm_tmul, TensorProduct.norm_tmul]
  ring

/-- Squared Fock norm of `(b†b − n)Ω`, adding the squared norms of the
orthogonal zero- and two-particle sectors. Its value at the vacuum expectation
`n = ‖g‖²` is the outgoing number variance in the infalling vacuum. -/
def numberResidualSq (f g : H) (n : ℂ) : ℝ :=
  ‖(numberOnVacuum f g).1 - n‖ ^ 2 + ‖(numberOnVacuum f g).2‖ ^ 2

/-- Residual to every proposed outgoing eigenvalue, including approximate predictions. -/
lemma numberResidualSq_eq (f g : H) (n : ℂ) :
    numberResidualSq f g n =
      ‖(‖g‖ : ℂ) ^ 2 - n‖ ^ 2 + (‖f‖ ^ 2 * ‖g‖ ^ 2 + ‖inner ℂ f g‖ ^ 2) := by
  simp only [numberResidualSq, numberOnVacuum_components, createOne_norm_sq]

/-- For a canonically normalized packet with mean occupation ν = ‖g‖², the
number variance is ν(1 + ν) plus the squared overlap of the smearing vectors. -/
lemma vacuum_number_variance {f g : H} (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1) :
    numberResidualSq f g ((‖g‖ : ℂ) ^ 2) =
      ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2) + ‖inner ℂ f g‖ ^ 2 := by
  have h : ‖f‖ ^ 2 = 1 + ‖g‖ ^ 2 := by linarith
  simp [numberResidualSq_eq, h, mul_comm]

/-- Nonzero positive- and negative-frequency parts preclude an exact outgoing
number eigenstate. Equality would require the two-particle sector to vanish. -/
lemma vacuum_not_outgoing_number_eigen {f g : H} (hf : f ≠ 0) (hg : g ≠ 0) (n : ℂ) :
    numberOnVacuum f g ≠ (n, 0) := by
  intro heigen
  rw [numberOnVacuum_components] at heigen
  have hpair : createOne f g = 0 := congrArg Prod.snd heigen
  have hnorm := createOne_norm_sq f g
  rw [hpair, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
  have hprod := mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hf)) (sq_pos_of_pos (norm_pos_iff.mpr hg))
  linarith [sq_nonneg ‖inner ℂ f g‖]

/-- For a normalized outgoing bosonic mode, the canonical normalization and
nonzero creation part already force the annihilation part to be nonzero. -/
lemma vacuum_not_eigen_of_normalized {f g : H} (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1)
    (hg : g ≠ 0) (n : ℂ) : numberOnVacuum f g ≠ (n, 0) := by
  apply vacuum_not_outgoing_number_eigen _ hg
  intro hf
  rw [hf, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hCCR
  linarith [sq_nonneg ‖g‖]

/-- Square-integrable frequency envelopes, with any measure (including a
frequency axis restricted to positive frequencies), instantiate the same result.
The coefficient hypotheses are on their almost-everywhere equivalence classes. -/
lemma frequency_packet_not_eigen {ι : Type*} [MeasurableSpace ι] {μ : MeasureTheory.Measure ι}
    {f g : MeasureTheory.Lp ℂ 2 μ} (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1)
    (hg : g ≠ 0) (n : ℂ) : numberOnVacuum f g ≠ (n, 0) :=
  vacuum_not_eigen_of_normalized hCCR hg n

/-! ## B. Transmission through the exterior barrier

AMPS Appendix B, Eqs. (B.1)–(B.3), mix the outgoing packet inside the
barrier, `d = a(f) + a†(g)`, with an independent incoming vacuum mode
`c = a(h)`. Write the detected packet as `b = t d + r c`. In the paper's
phase convention `t = conj T` and `r = R conj T / T` when `T ≠ 0`.
The unitary scattering row `|t|²+|r|²=1` also admits the perfectly reflecting
endpoint. The coefficients here are inputs for one scattering channel.
-/

/-- Since annihilation is antilinear in its profile, the annihilation part of
`t d + r c` has conjugated coefficients. Its creation profile is `t • g`. -/
def greybodyAnnihilation (t r : ℂ) (f h : H) : H := star t • f + star r • h

/-- On one infalling particle the adjoint of the scattered packet uses the conjugated
scattering row. Together with its vacuum creation profile this checks the phases
in the two operator actions used to calculate `b†b Ω`. -/
lemma greybody_adjoint_on_one (t r : ℂ) (f g h x : H) :
    outgoingAdjointOnOne (greybodyAnnihilation t r f h) (t • g) x =
      star t • outgoingAdjointOnOne f g x + star r • outgoingAdjointOnOne h 0 x := by
  apply Prod.ext
  · simp [outgoingAdjointOnOne, inner_smul_left]
  · simp [outgoingAdjointOnOne, greybodyAnnihilation, createOne,
      TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul,
      smul_add, smul_smul, mul_comm, add_comm, add_left_comm, add_assoc]

/-- The reflected incoming channel is orthogonal to both near-horizon profiles.
Unitarity preserves the canonical normalization. The final identity retains
the phase of the anomalous overlap, which picks up two powers of `t`. -/
lemma greybody_profiles {t r : ℂ} {f g h : H}
    (hrow : ‖t‖ ^ 2 + ‖r‖ ^ 2 = 1) (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1)
    (hunit : ‖h‖ = 1) (hfh : inner ℂ f h = 0) (hhg : inner ℂ h g = 0) :
    ‖greybodyAnnihilation t r f h‖ ^ 2 - ‖t • g‖ ^ 2 = 1 ∧
    ‖t • g‖ ^ 2 = ‖t‖ ^ 2 * ‖g‖ ^ 2 ∧
    inner ℂ (greybodyAnnihilation t r f h) (t • g) = t ^ 2 * inner ℂ f g := by
  have horth : inner ℂ (star t • f) (star r • h) = 0 := by
    simp [inner_smul_left, inner_smul_right, hfh]
  have hf : ‖greybodyAnnihilation t r f h‖ ^ 2 =
      ‖t‖ ^ 2 * ‖f‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [greybodyAnnihilation, norm_add_sq (𝕜 := ℂ), horth]
    simp [norm_smul, mul_pow, hunit]
  have hg : ‖t • g‖ ^ 2 = ‖t‖ ^ 2 * ‖g‖ ^ 2 := by rw [norm_smul, mul_pow]
  refine ⟨?_, hg, ?_⟩
  · rw [hf, hg]
    nlinarith [congrArg (fun x : ℝ => ‖t‖ ^ 2 * x) hCCR]
  · simp [greybodyAnnihilation, inner_add_left, inner_smul_left, inner_smul_right,
      hhg, pow_two, mul_assoc]

/-- For a transmitted canonical packet in the joint infalling and incoming
vacuum, the mean occupation is τν, where τ = |t|² and ν = ‖g‖². The variance
is τν + τ²(ν² + |⟪f,g⟫|²). This gives the low-transmission behavior for
the supplied scattering channel without a model of the barrier potential. -/
lemma greybody_number_variance {t r : ℂ} {f g h : H}
    (hrow : ‖t‖ ^ 2 + ‖r‖ ^ 2 = 1) (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1)
    (hunit : ‖h‖ = 1) (hfh : inner ℂ f h = 0) (hhg : inner ℂ h g = 0) :
    numberResidualSq (greybodyAnnihilation t r f h) (t • g) ((‖t • g‖ : ℂ) ^ 2) =
      ‖t‖ ^ 2 * ‖g‖ ^ 2 + (‖t‖ ^ 2) ^ 2 * ((‖g‖ ^ 2) ^ 2 + ‖inner ℂ f g‖ ^ 2) := by
  obtain ⟨hcan, hmean, hoverlap⟩ := greybody_profiles hrow hCCR hunit hfh hhg
  rw [vacuum_number_variance hcan, hmean, hoverlap, norm_mul, norm_pow]
  ring

/-- With nonzero transmitted Hawking occupation, the variance is at least that
occupation. In particular the vacuum fails to be an outgoing number eigenstate. -/
lemma greybody_occupation_le_variance {t r : ℂ} {f g h : H}
    (hrow : ‖t‖ ^ 2 + ‖r‖ ^ 2 = 1) (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1)
    (hunit : ‖h‖ = 1) (hfh : inner ℂ f h = 0) (hhg : inner ℂ h g = 0) :
    ‖t‖ ^ 2 * ‖g‖ ^ 2 ≤
      numberResidualSq (greybodyAnnihilation t r f h) (t • g) ((‖t • g‖ : ℂ) ^ 2) := by
  rw [greybody_number_variance hrow hCCR hunit hfh hhg]
  exact le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

open Filter Topology

/-- Along any family of lossless scattering rows with transmission tending to
zero, the outgoing vacuum variance tends to zero for fixed near-horizon profiles.
The reflection phase can vary without a limit. -/
lemma greybody_variance_tendsto_zero {X : Type*} {l : Filter X} {t r : X → ℂ}
    {f g h : H} (ht : Tendsto t l (𝓝 0))
    (hrow : ∀ᶠ x in l, ‖t x‖ ^ 2 + ‖r x‖ ^ 2 = 1)
    (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1) (hunit : ‖h‖ = 1)
    (hfh : inner ℂ f h = 0) (hhg : inner ℂ h g = 0) :
    Tendsto (fun x => numberResidualSq (greybodyAnnihilation (t x) (r x) f h)
      (t x • g) ((‖t x • g‖ : ℂ) ^ 2)) l (𝓝 0) := by
  have hτ : Tendsto (fun x => ‖t x‖ ^ 2) l (𝓝 0) := by simpa using ht.norm.pow 2
  have hlim : Tendsto (fun x => ‖t x‖ ^ 2 * ‖g‖ ^ 2 +
      (‖t x‖ ^ 2) ^ 2 * ((‖g‖ ^ 2) ^ 2 + ‖inner ℂ f g‖ ^ 2)) l (𝓝 0) := by
    simpa [Pi.add_def, Pi.mul_def, Pi.pow_def] using
      (hτ.mul_const (‖g‖ ^ 2)).add ((hτ.pow 2).mul_const ((‖g‖ ^ 2) ^ 2 + ‖inner ℂ f g‖ ^ 2))
  exact hlim.congr' (hrow.mono fun x hx => (greybody_number_variance hx hCCR hunit hfh hhg).symm)

/-- At zero transmission the outgoing number operator annihilates the joint
vacuum; only the incoming annihilation channel survives. -/
lemma zero_transmission_vacuum (r : ℂ) (f g h : H) :
    numberOnVacuum (greybodyAnnihilation 0 r f h) ((0 : ℂ) • g) = (0, 0) := by
  simp [numberOnVacuum_components, createOne]

end

end AMPS.Smeared
