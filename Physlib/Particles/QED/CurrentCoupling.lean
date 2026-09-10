/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Lagrangian
public import Physlib.Particles.QED.FermionStatistics
public import Physlib.Particles.QED.GaugeInvariance
public import Physlib.Particles.QED.FieldStrength
/-!
# The current coupling of quantum electrodynamics

## i. Overview

The interaction of QED is *minimal coupling to the Dirac current*: expanding
the covariant derivative inside the Dirac kinetic term,

`i ψ̄ γ^μ D_μ ψ = i ψ̄ γ^μ ∂_μ ψ - e J^μ A_μ`  with  `J^μ = ψ̄ γ^μ ψ`.

This is the jet-algebra counterpart of the current coupling `J^μ A_μ` of
`Physlib.Electromagnetism.Dynamics.Lagrangian`: the photon couples to matter
only through a conserved current contracted with the potential, with the
electron supplying `J^μ = ψ̄ γ^μ ψ`.

The current is gauge invariant (`gaugeAction_diracCurrent`) — the electron
and its conjugate carry opposite charges, so the phases cancel — which is
what makes it a physically meaningful source for the photon.

This file contains no definitions, only theorems about the fields of
`Physlib.Particles.QED.Fields` and the Lagrangian of `Physlib.Particles.QED.Lagrangian`.

## ii. Key results

- `JetAlgebra.diracKineticTerm_eq_free_add_current` : **minimal coupling** —
  the Dirac kinetic term is the free kinetic term plus `- e J^μ A_μ`.
- `JetAlgebra.gaugeAction_diracCurrent` : the Dirac current is gauge
  invariant.

## iii. Table of contents

- A. The minimal-coupling decomposition of the kinetic term
- B. Gauge invariance of the Dirac current

## iv. References

The current is defined in `Physlib.Particles.QED.Lagrangian`; the concrete
electromagnetic current coupling is
`Physlib.Electromagnetism.Dynamics.Lagrangian`.

-/

@[expose] public section

/-! TODO: Connect the QED matter content to `Physlib.QFT.QED.AnomalyCancellation`: the electron -/
/-! TODO: spectrum is vector-like (charges `±1`), so it satisfies the gravitational and cubic -/
/-! TODO: anomaly cancellation conditions. -/

namespace QED

namespace JetAlgebra

/-!

## A. The minimal-coupling decomposition of the kinetic term

The photon coordinates commute with the fermion coordinates
(`Physlib.Particles.QED.FermionStatistics`), so the interaction inside the kinetic term
reorganises into the potential times the Dirac current.

-/

/-- The photon potential times the Dirac current, written through the fermion
  bilinears. -/
lemma A_mul_diracCurrent (μ : Fin 1 ⊕ Fin 3) :
    A 0 μ * diracCurrent μ =
      ∑ α, ∑ β, kineticGamma μ α β • (A 0 μ * (barψ 0 α * ψ 0 β)) := by
  rw [diracCurrent, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [mul_smul_comm]

/-- **Minimal coupling**: the Dirac kinetic term with coupling `e` is the free
  Dirac kinetic term plus the current coupling `- e J^μ A_μ`.  All of the
  interaction of QED is the photon contracted with the Dirac current, the
  jet-algebra counterpart of the current coupling of
  `Physlib.Electromagnetism.Dynamics`. -/
theorem diracKineticTerm_eq_free_add_current (e : ℝ) :
    diracKineticTerm e = diracKineticTerm 0 +
      (-e : ℂ) • ∑ μ, A 0 μ * diracCurrent μ := by
  have hsplit : ∀ (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2 ⊕ Fin 2),
      barψ 0 α * covDψ e μ β =
        barψ 0 α * covDψ 0 μ β +
          (Complex.I * e) • (A 0 μ * (barψ 0 α * ψ 0 β)) := by
    intro μ α β
    rw [covDψ, covDψ, Complex.ofReal_zero, mul_zero, zero_smul, add_zero, mul_add,
      mul_smul_comm, ← mul_assoc, ← A_mul_barψ_comm, mul_assoc]
  rw [diracKineticTerm, diracKineticTerm,
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by rw [hsplit μ α β, smul_add]]
  simp only [Finset.sum_add_distrib, smul_add]
  congr 1
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => A_mul_diracCurrent μ,
    Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [smul_smul, smul_smul, smul_smul]
  refine congrArg (· • _) ?_
  ring_nf
  rw [Complex.I_sq]
  ring

/-!

## B. Gauge invariance of the Dirac current

-/

/-- **The Dirac current is gauge invariant**: the electron and its conjugate
  carry opposite charges, so the phases cancel by unitarity.  This is what
  makes `J^μ` a physically meaningful source for the photon. -/
@[simp]
theorem gaugeAction_diracCurrent {e : ℝ} (g : GaugeJet e) (μ : Fin 1 ⊕ Fin 3) :
    gaugeAction g (diracCurrent μ) = diracCurrent μ := by
  rw [diracCurrent, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul,
    gaugeAction_mul_phase_cancel g (gaugeAction_barψ_zero g α)
      (gaugeAction_ψ_zero g β)]

/-!

## C. Noether: conservation of the Dirac current on-shell

-/

set_option maxHeartbeats 1000000 in
/-- **Noether's identity for the Dirac current**: the divergence of the
  current is a combination of the Dirac-equation elements,
  `i ∂_μ J^μ = ψ̄ ⬝ (Dirac eq) + (adjoint Dirac eq) ⬝ ψ`.
  On solutions of the Dirac equations the current is conserved,
  `∂_μ J^μ = 0` — for every coupling `e` and mass `m`: the gauge interaction
  and the mass drop out of the divergence identically. -/
theorem current_conservation (e m : ℝ) :
    Complex.I • ∑ μ, jetDeriv μ (diracCurrent μ) =
      ∑ α, barψ 0 α * diracEquation e m α +
        ∑ β, diracAdjEquation e m β * ψ 0 β := by
  have hL : ∀ μ : Fin 1 ⊕ Fin 3, jetDeriv μ (diracCurrent μ) =
      (∑ α, ∑ β, kineticGamma μ α β • (barψ {μ} α * ψ 0 β)) +
        ∑ α, ∑ β, kineticGamma μ α β • (barψ 0 α * ψ {μ} β) := by
    intro μ
    rw [diracCurrent, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_smul, jetDeriv_mul, jetDeriv_barψ, jetDeriv_ψ, zero_add, smul_add]
  have hT1 : ∀ α : Fin 2 ⊕ Fin 2, barψ 0 α * diracEquation e m α =
      Complex.I • (∑ μ, ∑ β, kineticGamma μ α β • (barψ 0 α * ψ {μ} β)) +
        (Complex.I * (Complex.I * ↑e)) • (∑ μ, ∑ β, kineticGamma μ α β •
          (A 0 μ * (barψ 0 α * ψ 0 β))) -
        (m : ℂ) • ∑ β, gammaMatrix (Sum.inl 0) α β • (barψ 0 α * ψ 0 β) := by
    intro α
    rw [diracEquation, mul_sub, mul_smul_comm, mul_smul_comm, Finset.mul_sum,
      Finset.mul_sum]
    congr 1
    · rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => Finset.mul_sum _ _ _,
        show (∑ μ, ∑ β, barψ 0 α * (kineticGamma μ α β • covDψ e μ β)) =
          ∑ μ, ∑ β, (kineticGamma μ α β • (barψ 0 α * ψ {μ} β) +
            (Complex.I * ↑e) • (kineticGamma μ α β •
              (A 0 μ * (barψ 0 α * ψ 0 β)))) from
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => by
          rw [mul_smul_comm, covDψ, mul_add, smul_add, mul_smul_comm,
            ← mul_assoc, ← A_mul_barψ_comm, mul_assoc, smul_comm
              (Complex.I * (e : ℂ)) (kineticGamma μ α β)]]
      rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) =>
        Finset.sum_add_distrib, Finset.sum_add_distrib, smul_add]
      congr 1
      rw [show (∑ μ, ∑ β, (Complex.I * (e : ℂ)) • (kineticGamma μ α β •
          (A 0 μ * (barψ 0 α * ψ 0 β)))) =
        (Complex.I * (e : ℂ)) • ∑ μ, ∑ β, kineticGamma μ α β •
          (A 0 μ * (barψ 0 α * ψ 0 β)) from by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun μ _ => Finset.smul_sum.symm]
      rw [smul_smul]
    · refine congrArg _ (Finset.sum_congr rfl fun β _ => ?_)
      rw [mul_smul_comm]
  have hT3 : ∀ β : Fin 2 ⊕ Fin 2, diracAdjEquation e m β * ψ 0 β =
      Complex.I • (∑ μ, ∑ α, kineticGamma μ α β • (barψ {μ} α * ψ 0 β)) -
        (Complex.I * (Complex.I * ↑e)) • (∑ μ, ∑ α, kineticGamma μ α β •
          (A 0 μ * (barψ 0 α * ψ 0 β))) +
        (m : ℂ) • ∑ α, gammaMatrix (Sum.inl 0) α β • (barψ 0 α * ψ 0 β) := by
    intro β
    rw [diracAdjEquation, add_mul, smul_mul_assoc, smul_mul_assoc, Finset.sum_mul,
      Finset.sum_mul]
    congr 1
    · rw [show (∑ μ, (∑ α, kineticGamma μ α β • covDbarψ e μ α) * ψ 0 β) =
          ∑ μ, ∑ α, (kineticGamma μ α β • (barψ {μ} α * ψ 0 β) -
            (Complex.I * ↑e) • (kineticGamma μ α β •
              (A 0 μ * (barψ 0 α * ψ 0 β)))) from
        Finset.sum_congr rfl fun μ _ => by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [smul_mul_assoc, covDbarψ, sub_mul, smul_sub, smul_mul_assoc,
            mul_assoc, smul_comm (Complex.I * (e : ℂ)) (kineticGamma μ α β)]]
      rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) =>
        Finset.sum_sub_distrib _ _, Finset.sum_sub_distrib _ _, smul_sub]
      congr 1
      rw [show (∑ μ, ∑ α, (Complex.I * (e : ℂ)) • (kineticGamma μ α β •
          (A 0 μ * (barψ 0 α * ψ 0 β)))) =
        (Complex.I * (e : ℂ)) • ∑ μ, ∑ α, kineticGamma μ α β •
          (A 0 μ * (barψ 0 α * ψ 0 β)) from by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun μ _ => Finset.smul_sum.symm]
      rw [smul_smul]
    · refine congrArg _ (Finset.sum_congr rfl fun α _ => ?_)
      rw [smul_mul_assoc]
  rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => hT1 α,
    Finset.sum_congr rfl fun β (_ : β ∈ Finset.univ) => hT3 β]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => hL μ]
  rw [Finset.sum_comm (f := fun α μ => ∑ β, kineticGamma μ α β •
      (barψ 0 α * ψ {μ} β)),
    Finset.sum_comm (f := fun β μ => ∑ α, kineticGamma μ α β •
      (barψ {μ} α * ψ 0 β)),
    Finset.sum_comm (f := fun α μ => ∑ β, kineticGamma μ α β •
      (A 0 μ * (barψ 0 α * ψ 0 β))),
    Finset.sum_comm (f := fun β μ => ∑ α, kineticGamma μ α β •
      (A 0 μ * (barψ 0 α * ψ 0 β)))]
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) =>
    (Finset.sum_comm (f := fun β α => kineticGamma μ α β •
      (A 0 μ * (barψ 0 α * ψ 0 β))))]
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) =>
    (Finset.sum_comm (f := fun β α => kineticGamma μ α β •
      (barψ {μ} α * ψ 0 β)))]
  rw [Finset.sum_comm (f := fun β α => gammaMatrix (Sum.inl 0) α β •
    (barψ 0 α * ψ 0 β))]
  simp only [smul_add, Finset.smul_sum]
  rw [Finset.sum_add_distrib]
  abel

end JetAlgebra

end QED
