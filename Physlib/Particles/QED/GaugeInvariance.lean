/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Lagrangian
public import Mathlib.Tactic.Module
/-!
# Gauge invariance of quantum electrodynamics

## i. Overview

The gauge-theoretic theorems of QED, culminating in the gauge invariance of
the QED Lagrangian, `gaugeAction_lagrangian`.  The chain of results
decomposes exactly as in the physics texts:

* on the photon jet algebra the gauge transformations form a group acting by
  affine shifts (`Photon.JetAlgebra.gaugeAction_comp`), and the field
  strength and the Maxwell term are invariant because the shift of `∂_s A_μ`
  is symmetric in the derivative indices — Clairaut's theorem is built into
  the multiset indexing (`Photon.JetAlgebra.gaugeAction_fieldStrength`);
* the electron coordinates rotate by the phase and its conjugate, and the
  trivial gauge jet acts trivially (`Electron.JetAlgebra.gaugeAction_trivial`);
* the covariant derivative is covariant, `D_μ ψ ↦ ū D_μ ψ`, because the
  photon shift `∂_μ χ` cancels the derivative `∂_μ ū = -i e (∂_μ χ) ū` of
  the phase (`gaugeAction_covDψ`);
* every charge-neutral fermion bilinear is invariant because the phases of
  the electron and its conjugate cancel by unitarity
  (`gaugeAction_mul_phase_cancel`);
* the Lagrangian, being built from invariant pieces, is invariant
  (`gaugeAction_lagrangian`).

This file contains no definitions, only theorems about the jet algebras of
`Physlib.Particles.QED.Basic`, the fields of `Physlib.Particles.QED.Fields` and the Lagrangian of
`Physlib.Particles.QED.Lagrangian`.

## ii. Key results

- `Photon.JetAlgebra.gaugeAction_comp`, `Photon.JetAlgebra.gaugeAction_zero` :
  the photon gauge transformations form a group acting on the photon jet
  algebra.
- `Photon.JetAlgebra.gaugeAction_fieldStrength`,
  `Photon.JetAlgebra.gaugeAction_maxwellTerm` : gauge invariance of the field
  strength and the Maxwell term.
- `Electron.JetAlgebra.gaugeAction_trivial`, `JetAlgebra.gaugeAction_trivial` :
  the trivial gauge jet acts trivially.
- `JetAlgebra.gaugeAction_A`, `JetAlgebra.gaugeAction_ψ_zero`,
  `JetAlgebra.gaugeAction_ψ_singleton` (and the `barψ` versions) : the action
  on the jet coordinates of QED.
- `JetAlgebra.gaugeAction_covDψ`, `JetAlgebra.gaugeAction_covDbarψ` : gauge
  covariance of the covariant derivatives.
- `JetAlgebra.gaugeAction_diracKineticTerm`,
  `JetAlgebra.gaugeAction_electronMassTerm` : gauge invariance of the terms
  of the Lagrangian.
- `JetAlgebra.gaugeAction_lagrangian` : **gauge invariance of the QED
  Lagrangian**.

## iii. Table of contents

- A. The gauge group acting on the photon jet algebra
  - A.1. Gauge invariance of the field strength and the Maxwell term
- B. The trivial gauge jet acts trivially
- C. The action on the jet coordinates of QED
  - C.1. The photon coordinates
  - C.2. The electron coordinates
  - C.3. The field strength and the Maxwell term
- D. Gauge covariance of the covariant derivatives
- E. Gauge invariance of the Lagrangian
  - E.1. Cancellation of the phases in fermion bilinears
  - E.2. Invariance of each term
  - E.3. Invariance of the QED Lagrangian

## iv. References

The jet algebras and gauge actions are defined in `Physlib.Particles.QED.Basic`, the
fields in `Physlib.Particles.QED.Fields` and the Lagrangian in
`Physlib.Particles.QED.Lagrangian`.

-/

@[expose] public section

namespace QED

open TensorProduct

namespace Photon

namespace JetAlgebra

/-!

## A. The gauge group acting on the photon jet algebra

-/

/-- Photon gauge jets compose by addition: the gauge transformations form a
  group acting on the photon jet algebra. -/
theorem gaugeAction_comp (c₁ c₂ : GaugeJet) :
    (gaugeAction c₁).comp (gaugeAction c₂) = gaugeAction (c₁ + c₂) := by
  refine MvPolynomial.algHom_ext fun j => ?_
  obtain ⟨s, μ⟩ := j
  rw [AlgHom.comp_apply]
  show gaugeAction c₁ (gaugeAction c₂ (coord s μ)) = gaugeAction (c₁ + c₂) (coord s μ)
  rw [gaugeAction_coord, gaugeAction_coord, map_add, gaugeAction_coord, gaugeAction_C,
    add_assoc, ← MvPolynomial.C_add]
  rfl

@[simp]
theorem gaugeAction_zero : gaugeAction 0 = AlgHom.id ℝ JetAlgebra := by
  refine MvPolynomial.algHom_ext fun j => ?_
  obtain ⟨s, μ⟩ := j
  show gaugeAction 0 (coord s μ) = coord s μ
  simp

/-!

### A.1. Gauge invariance of the field strength and the Maxwell term

The field strength is gauge invariant, and the reason is exactly that
multiset addition is commutative: the two shifts are `∂_s ∂_μ ∂_ν χ` and
`∂_s ∂_ν ∂_μ χ`, indexed by `s + {μ} + {ν}` and `s + {ν} + {μ}`.  Clairaut's
theorem is built into the indexing.

-/

@[simp]
theorem gaugeAction_fieldStrength (c : GaugeJet) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    gaugeAction c (fieldStrength s μ ν) = fieldStrength s μ ν := by
  have hcomm : s + {μ} + {ν} = s + {ν} + {μ} := by
    rw [add_assoc, add_assoc, add_comm ({μ} : Multiset _)]
  rw [fieldStrength, map_sub, gaugeAction_coord, gaugeAction_coord, hcomm]
  ring

@[simp]
theorem gaugeAction_maxwellTerm (c : GaugeJet) : gaugeAction c maxwellTerm = maxwellTerm := by
  rw [maxwellTerm, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, map_mul, gaugeAction_fieldStrength]

end JetAlgebra

end Photon

/-!

## B. The trivial gauge jet acts trivially

The key combinatorial fact: in the Leibniz sum over the antidiagonal of `t`,
the splitting `(0, t)` occurs exactly once, so an indicator supported at the
zero multiset picks out the identity.

-/

namespace Electron

namespace JetAlgebra

/-- The trivial gauge jet acts trivially on the electron jet algebra: the
  gauge action is unital. -/
theorem gaugeAction_trivial (e : ℝ) :
    gaugeAction (GaugeJet.trivial e) = AlgHom.id ℂ JetAlgebra := by
  refine ExteriorAlgebra.hom_ext (Finsupp.lhom_ext fun j b => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.coe_id, id_eq]
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  congr 1
  show gaugeAction (GaugeJet.trivial e) (ofGenerator j) = ofGenerator j
  cases j with
  | dψ t α =>
    rw [gaugeAction_ofGenerator_dψ,
      show (t.antidiagonal.map fun p =>
          star ((GaugeJet.trivial e).phase p.1) • ofGenerator (.dψ p.2 α)) =
        t.antidiagonal.map fun p =>
          if p.1 = 0 then ofGenerator (.dψ p.2 α) else 0 from
        Multiset.map_congr rfl fun p _ => by
          by_cases h : p.1 = 0 <;> simp [GaugeJet.trivial, h],
      sum_map_antidiagonal_ite t fun u => ofGenerator (.dψ u α)]
  | dbarψ t α =>
    rw [gaugeAction_ofGenerator_dbarψ,
      show (t.antidiagonal.map fun p =>
          (GaugeJet.trivial e).phase p.1 • ofGenerator (.dbarψ p.2 α)) =
        t.antidiagonal.map fun p =>
          if p.1 = 0 then ofGenerator (.dbarψ p.2 α) else 0 from
        Multiset.map_congr rfl fun p _ => by
          by_cases h : p.1 = 0 <;> simp [GaugeJet.trivial, h],
      sum_map_antidiagonal_ite t fun u => ofGenerator (.dbarψ u α)]

end JetAlgebra

end Electron

namespace JetAlgebra

/-- The trivial gauge jet acts trivially on the QED jet algebra: the gauge
  action is unital. -/
theorem gaugeAction_trivial (e : ℝ) :
    gaugeAction (GaugeJet.trivial e) = AlgHom.id ℂ JetAlgebra := by
  have hP : gaugeActionPhoton (GaugeJet.trivial e).χjet =
      AlgHom.id ℂ (ℂ ⊗[ℝ] Photon.JetAlgebra) := by
    rw [show (GaugeJet.trivial e).χjet = 0 from rfl, gaugeActionPhoton,
      Photon.JetAlgebra.gaugeAction_zero, Algebra.TensorProduct.map_id]
  simp only [gaugeAction, hP, Electron.JetAlgebra.gaugeAction_trivial]
  exact Algebra.TensorProduct.map_id

/-- The electron gauge actions compose through the monoid of gauge jets. -/
theorem _root_.QED.Electron.JetAlgebra.gaugeAction_mul {e : ℝ} (g₁ g₂ : GaugeJet e) :
    (Electron.JetAlgebra.gaugeAction g₁).comp (Electron.JetAlgebra.gaugeAction g₂) =
      Electron.JetAlgebra.gaugeAction (g₁ * g₂) := by
  refine ExteriorAlgebra.hom_ext (Finsupp.lhom_ext fun j b => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply]
  rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul]
  congr 1
  show Electron.JetAlgebra.gaugeAction g₁ (Electron.JetAlgebra.gaugeAction g₂
      (Electron.JetAlgebra.ofGenerator j)) =
    Electron.JetAlgebra.gaugeAction (g₁ * g₂) (Electron.JetAlgebra.ofGenerator j)
  cases j with
  | dψ t α =>
    rw [Electron.JetAlgebra.gaugeAction_ofGenerator_dψ,
      show (t.antidiagonal.map fun p => star (g₂.phase p.1) •
          Electron.JetAlgebra.ofGenerator (.dψ p.2 α)).sum =
        phaseAct (fun x => star (g₂.phase x))
          (fun t' => Electron.JetAlgebra.ofGenerator (.dψ t' α)) t from rfl,
      show Electron.JetAlgebra.gaugeAction g₁ (phaseAct (fun x => star (g₂.phase x))
          (fun t' => Electron.JetAlgebra.ofGenerator (.dψ t' α)) t) =
        phaseAct (fun x => star (g₂.phase x))
          (fun t' => Electron.JetAlgebra.gaugeAction g₁
            (Electron.JetAlgebra.ofGenerator (.dψ t' α))) t from
        map_phaseAct _ _ (Electron.JetAlgebra.gaugeAction g₁).toLinearMap t,
      show (fun t' => Electron.JetAlgebra.gaugeAction g₁
          (Electron.JetAlgebra.ofGenerator (.dψ t' α))) =
        fun t' => phaseAct (fun x => star (g₁.phase x))
          (fun t'' => Electron.JetAlgebra.ofGenerator (.dψ t'' α)) t' from
        funext fun t' => Electron.JetAlgebra.gaugeAction_ofGenerator_dψ g₁ t' α,
      phaseAct_assoc, Electron.JetAlgebra.gaugeAction_ofGenerator_dψ,
      show (t.antidiagonal.map fun p => star ((g₁ * g₂).phase p.1) •
          Electron.JetAlgebra.ofGenerator (.dψ p.2 α)).sum =
        phaseAct (fun x => star ((g₁ * g₂).phase x))
          (fun t' => Electron.JetAlgebra.ofGenerator (.dψ t' α)) t from rfl]
    refine congrFun (congrArg (fun w => phaseAct w
      (fun t' => Electron.JetAlgebra.ofGenerator (.dψ t' α))) (funext fun x => ?_)) t
    rw [GaugeJet.mul_phase, star_phaseAct, phaseAct_comm]
  | dbarψ t α =>
    rw [Electron.JetAlgebra.gaugeAction_ofGenerator_dbarψ,
      show (t.antidiagonal.map fun p => g₂.phase p.1 •
          Electron.JetAlgebra.ofGenerator (.dbarψ p.2 α)).sum =
        phaseAct g₂.phase
          (fun t' => Electron.JetAlgebra.ofGenerator (.dbarψ t' α)) t from rfl,
      show Electron.JetAlgebra.gaugeAction g₁ (phaseAct g₂.phase
          (fun t' => Electron.JetAlgebra.ofGenerator (.dbarψ t' α)) t) =
        phaseAct g₂.phase
          (fun t' => Electron.JetAlgebra.gaugeAction g₁
            (Electron.JetAlgebra.ofGenerator (.dbarψ t' α))) t from
        map_phaseAct _ _ (Electron.JetAlgebra.gaugeAction g₁).toLinearMap t,
      show (fun t' => Electron.JetAlgebra.gaugeAction g₁
          (Electron.JetAlgebra.ofGenerator (.dbarψ t' α))) =
        fun t' => phaseAct g₁.phase
          (fun t'' => Electron.JetAlgebra.ofGenerator (.dbarψ t'' α)) t' from
        funext fun t' => Electron.JetAlgebra.gaugeAction_ofGenerator_dbarψ g₁ t' α,
      phaseAct_assoc, Electron.JetAlgebra.gaugeAction_ofGenerator_dbarψ,
      show (t.antidiagonal.map fun p => (g₁ * g₂).phase p.1 •
          Electron.JetAlgebra.ofGenerator (.dbarψ p.2 α)).sum =
        phaseAct ((g₁ * g₂).phase)
          (fun t' => Electron.JetAlgebra.ofGenerator (.dbarψ t' α)) t from rfl]
    refine congrFun (congrArg (fun w => phaseAct w
      (fun t' => Electron.JetAlgebra.ofGenerator (.dbarψ t' α))) (funext fun x => ?_)) t
    rw [GaugeJet.mul_phase, phaseAct_comm]

/-- The complexified photon gauge actions compose by addition of the gauge
  jets. -/
theorem gaugeActionPhoton_comp (c₁ c₂ : Photon.JetAlgebra.GaugeJet) :
    (gaugeActionPhoton c₁).comp (gaugeActionPhoton c₂) =
      gaugeActionPhoton (c₁ + c₂) := by
  rw [gaugeActionPhoton, gaugeActionPhoton, gaugeActionPhoton,
    ← Algebra.TensorProduct.map_comp, AlgHom.comp_id,
    Photon.JetAlgebra.gaugeAction_comp]

/-- **The gauge actions compose through the monoid of gauge jets**: the QED
  gauge action is a monoid action on the jet algebra. -/
theorem gaugeAction_mul {e : ℝ} (g₁ g₂ : GaugeJet e) :
    (gaugeAction g₁).comp (gaugeAction g₂) = gaugeAction (g₁ * g₂) := by
  simp only [gaugeAction, GaugeJet.mul_χjet]
  rw [← gaugeActionPhoton_comp, ← Electron.JetAlgebra.gaugeAction_mul]
  exact (Algebra.TensorProduct.map_comp _ _ _ _).symm

theorem gaugeAction_mul_apply {e : ℝ} (g₁ g₂ : GaugeJet e) (x : JetAlgebra) :
    gaugeAction (g₁ * g₂) x = gaugeAction g₁ (gaugeAction g₂ x) :=
  (DFunLike.congr_fun (gaugeAction_mul g₁ g₂) x).symm

/-!

## C. The action on the jet coordinates of QED

### C.1. The photon coordinates

The photon coordinate shifts by a *constant* of the jet algebra, the jet
`∂_s ∂_μ χ` of the gauge function; in the full algebra the constant is the
scalar multiple `(∂_s ∂_μ χ) • 1`.

-/

/-- The gauge action on the photon jet coordinate: the affine shift
  `∂_s A_μ ↦ ∂_s A_μ + ∂_s ∂_μ χ`. -/
theorem gaugeAction_A {e : ℝ} (g : GaugeJet e) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) :
    gaugeAction g (A s μ) = A s μ + (g.χjet (s + {μ}) : ℂ) • 1 := by
  simp only [A]
  rw [gaugeAction_tmul, map_one, gaugeActionPhoton_tmul,
    Photon.JetAlgebra.gaugeAction_coord, TensorProduct.tmul_add, add_tmul,
    tmul_C_eq_smul_one]

/-!

### C.2. The electron coordinates

The electron (charge `-1`) rotates by the conjugate phase, its conjugate
(charge `+1`) by the phase; on first-order jets the Leibniz rule feeds the
first derivative of the phase into the zeroth-order coordinate.

-/

@[simp]
theorem gaugeAction_ψ_zero {e : ℝ} (g : GaugeJet e) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ψ 0 α) = star (g.phase 0) • ψ 0 α := by
  simp only [ψ]
  rw [gaugeAction_tmul, map_one,
    Electron.JetAlgebra.gaugeAction_ofGenerator_dψ_zero, tmul_smul]

@[simp]
theorem gaugeAction_barψ_zero {e : ℝ} (g : GaugeJet e) (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (barψ 0 α) = g.phase 0 • barψ 0 α := by
  simp only [barψ]
  rw [gaugeAction_tmul, map_one,
    Electron.JetAlgebra.gaugeAction_ofGenerator_dbarψ_zero, tmul_smul]

theorem gaugeAction_ψ_singleton {e : ℝ} (g : GaugeJet e) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (ψ {μ} α) =
      star (g.phase 0) • ψ {μ} α + star (g.phase {μ}) • ψ 0 α := by
  simp only [ψ]
  rw [gaugeAction_tmul, map_one,
    Electron.JetAlgebra.gaugeAction_ofGenerator_dψ_singleton, tmul_add,
    tmul_smul, tmul_smul]

theorem gaugeAction_barψ_singleton {e : ℝ} (g : GaugeJet e) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (barψ {μ} α) =
      g.phase 0 • barψ {μ} α + g.phase {μ} • barψ 0 α := by
  simp only [barψ]
  rw [gaugeAction_tmul, map_one,
    Electron.JetAlgebra.gaugeAction_ofGenerator_dbarψ_singleton, tmul_add,
    tmul_smul, tmul_smul]

/-!

### C.3. The field strength and the Maxwell term

Both invariances are inherited from the photon jet algebra, where the proof
is the commutativity of multiset addition.

-/

@[simp]
theorem gaugeAction_fieldStrength {e : ℝ} (g : GaugeJet e)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    gaugeAction g (fieldStrength s μ ν) = fieldStrength s μ ν := by
  simp only [fieldStrength]
  rw [gaugeAction_tmul, map_one, gaugeActionPhoton_tmul,
    Photon.JetAlgebra.gaugeAction_fieldStrength]

@[simp]
theorem gaugeAction_maxwellTerm {e : ℝ} (g : GaugeJet e) :
    gaugeAction g maxwellTerm = maxwellTerm := by
  simp only [maxwellTerm]
  rw [gaugeAction_tmul, map_one, gaugeActionPhoton_tmul,
    Photon.JetAlgebra.gaugeAction_maxwellTerm]

/-!

## D. Gauge covariance of the covariant derivatives

Under a gauge transformation the photon coordinate shifts by `∂_μ χ` while
the first-order electron coordinate picks up the derivative
`∂_μ ū = -i e (∂_μ χ) ū` of the phase by the Leibniz rule; the two
contributions cancel and the covariant derivative rotates like the field
itself.

-/

/-- **Gauge covariance of the covariant derivative**: `D_μ ψ` rotates by the
  conjugate phase, exactly like `ψ` itself.  The shift of the photon
  coordinate cancels the derivative of the phase. -/
theorem gaugeAction_covDψ {e : ℝ} (g : GaugeJet e) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (covDψ e μ α) = star (g.phase 0) • covDψ e μ α := by
  rw [covDψ, map_add, map_smul, map_mul, gaugeAction_ψ_singleton,
    gaugeAction_ψ_zero, gaugeAction_A, g.star_phase_singleton μ,
    show (0 : Multiset (Fin 1 ⊕ Fin 3)) + {μ} = {μ} from zero_add _]
  simp only [add_mul, smul_mul_assoc, one_mul, mul_smul_comm, smul_add,
    smul_smul, neg_smul]
  module

/-- Gauge covariance of the conjugate covariant derivative: `D_μ ψ̄` rotates
  by the phase, exactly like `ψ̄` itself. -/
theorem gaugeAction_covDbarψ {e : ℝ} (g : GaugeJet e) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    gaugeAction g (covDbarψ e μ α) = g.phase 0 • covDbarψ e μ α := by
  rw [covDbarψ, map_sub, map_smul, map_mul, gaugeAction_barψ_singleton,
    gaugeAction_barψ_zero, gaugeAction_A, g.phase_singleton μ,
    show (0 : Multiset (Fin 1 ⊕ Fin 3)) + {μ} = {μ} from zero_add _]
  simp only [add_mul, smul_mul_assoc, one_mul, mul_smul_comm, smul_add,
    smul_sub, smul_smul]
  module

/-!

## E. Gauge invariance of the Lagrangian

### E.1. Cancellation of the phases in fermion bilinears

-/

/-- A product of a factor rotating by the phase and a factor rotating by the
  conjugate phase is gauge invariant: the phases cancel by unitarity.  This is
  the reason every charge-neutral fermion bilinear of QED is gauge
  invariant. -/
theorem gaugeAction_mul_phase_cancel {e : ℝ} (g : GaugeJet e) {x y : JetAlgebra}
    (hx : gaugeAction g x = g.phase 0 • x)
    (hy : gaugeAction g y = star (g.phase 0) • y) :
    gaugeAction g (x * y) = x * y := by
  rw [map_mul, hx, hy, smul_mul_smul_comm, g.phase_zero_unitary, one_smul]

/-!

### E.2. Invariance of each term

-/

@[simp]
theorem gaugeAction_diracKineticTerm {e : ℝ} (g : GaugeJet e) :
    gaugeAction g (diracKineticTerm e) = diracKineticTerm e := by
  rw [diracKineticTerm, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul,
    gaugeAction_mul_phase_cancel g (gaugeAction_barψ_zero g α)
      (gaugeAction_covDψ g μ β)]

@[simp]
theorem gaugeAction_diracKineticTermBar {e : ℝ} (g : GaugeJet e) :
    gaugeAction g (diracKineticTermBar e) = diracKineticTermBar e := by
  rw [diracKineticTermBar, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul,
    gaugeAction_mul_phase_cancel g (gaugeAction_covDbarψ g μ α)
      (gaugeAction_ψ_zero g β)]

@[simp]
theorem gaugeAction_electronMassTerm {e : ℝ} (g : GaugeJet e) :
    gaugeAction g electronMassTerm = electronMassTerm := by
  rw [electronMassTerm, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul,
    gaugeAction_mul_phase_cancel g (gaugeAction_barψ_zero g α)
      (gaugeAction_ψ_zero g β)]

/-!

### E.3. Invariance of the QED Lagrangian

-/

/-- **Gauge invariance of the QED Lagrangian.**  The Maxwell term is invariant
  by the symmetry of the photon shift in its derivative indices, the kinetic
  term by the covariance of the covariant derivative, and the mass term by the
  unitarity of the phase. -/
theorem gaugeAction_lagrangian {e : ℝ} (g : GaugeJet e) (m : ℝ) :
    gaugeAction g (lagrangian e m) = lagrangian e m := by
  rw [lagrangian, map_sub, map_add, map_smul, map_smul, gaugeAction_maxwellTerm,
    gaugeAction_diracKineticTerm, gaugeAction_electronMassTerm]

end JetAlgebra

end QED
