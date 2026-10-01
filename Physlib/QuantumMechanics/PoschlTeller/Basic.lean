/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
module

public import Physlib.QuantumMechanics.SpaceDQuantumSystem
public import Physlib.Mathematics.ForMathlib.Trigonometry.Tanh
/-!

# 1d Pöschl-Teller

## i. Overview

The Pöschl-Teller potential, `$V(x) \propto -\mathrm{sech}^2{(\kappa x)}$`, gives rise
to a one-dimensional quantum system for which the energy eigenvalues, energy eigenstates and
scattering data can be computed exactly. Notably, the potential is _reflectionless_ when
the parameter controlling its depth is a positive integer.

## ii. Key results

- `potential` is the Pöschl-Teller potential `-(ℏ² κ² N (N + 1)) / (2 m cosh² (κ x))`, of depth
  `depth = ℏ² κ² N (N + 1) / (2 m)`; it is negative, bounded below by `-depth`, even, of temperate
  growth (`potential_hasTemperateGrowth`) and continuous.
- `toSpaceDQuantumSystem` realises the Pöschl-Teller system as a `SpaceDQuantumSystem` of
  dimension `1`; its kinetic, potential and Hamiltonian operators are the generic ones of
  `SpaceDQuantumSystem`, for which this file gives the pointwise formulas in dimension one
  (`toSpaceDQuantumSystem_kineticCLM_apply`, `toSpaceDQuantumSystem_hamiltonianCLM_apply`) and the
  self-adjointness of the potential operator
  (`toSpaceDQuantumSystem_potentialOperator_isSelfAdjoint`).
- `creationCLM_apply`, `annihilationCLM_apply` give the pointwise action of the ladder operators;
  their sum and difference are `(2 / √(2m)) 𝐩` and `(2 i ℏ κ / √(2m)) tanh (κ X)`.

## iii. Table of contents

- A. Potential function
  - A.1. Definition and depth
  - A.2. Sign, bounds and parity
  - A.3. Regularity
- B. As a quantum system
- C. Operators
  - C.1. Kinetic energy, potential energy and Hamiltonian
  - C.2. Creation and annihilation operators
    - C.2.1. On Schwartz functions
    - C.2.2. As unbounded operators

## iv. References

* https://arxiv.org/pdf/2411.14941. [ref: arxiv_2411_14941]
-/
@[expose] public section

TODO "Develop the eigensystem of the Hamiltonian for the Pöschl-Teller quantum system
  using properties of the creation/annihilation operators
  (e.g. following https://arxiv.org/pdf/2411.14941 [ref: arxiv_2411_14941])."

TODO "Prove that the Pöschl-Teller potential is reflectionless."

noncomputable section

namespace QuantumMechanics

open Complex Constants Real SchwartzMap MeasureTheory SpaceDHilbertSpace

/-- A Pöschl-Teller system is specified by the particle mass `m`, the width parameter `κ`,
  and family number `N` (all positive). --/
structure PoschlTeller where
  /-- mass of the particle -/
  m : ℝ
  /-- width parameter of the potential -/
  κ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- width parameter of the potential is positive
  N_pos : 0 < N -- family number is positive

namespace PoschlTeller

variable (Q : PoschlTeller)

/-!
## A. Potential function
-/

/-!
### A.1. Definition and depth
-/

/-- The Pöschl-Teller potential is `-(ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2)`. --/
def potential (x : Space 1) : ℝ :=
  -(ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / (2 * Q.m * Real.cosh (Q.κ * x 0) ^ 2)

/-- The depth `ℏ^2 * κ^2 * N * (N + 1) / (2 * m)` of the potential well, so that
`potential x = -depth / cosh (κ * x) ^ 2`. -/
def depth : ℝ := ℏ ^ 2 * Q.κ ^ 2 * Q.N * (Q.N + 1) / (2 * Q.m)

/-- The depth of the well is positive. -/
lemma depth_pos : 0 < Q.depth := by
  have hm := Q.m_pos
  have hκ := Q.κ_pos
  have hN := Q.N_pos
  have hℏ := ℏ_pos
  unfold depth
  positivity

/-- The potential in terms of the depth, `potential x = -depth / cosh (κ * x) ^ 2`. -/
lemma potential_eq (x : Space 1) : Q.potential x = -Q.depth / Real.cosh (Q.κ * x 0) ^ 2 := by
  have hm := Q.m_pos
  unfold depth potential
  field_simp [(Real.cosh_pos _).ne']

/-- The potential in terms of `tanh`, `potential x = -depth * (1 - tanh (κ * x) ^ 2)`. -/
lemma potential_eq_tanh (x : Space 1) :
    Q.potential x = -Q.depth * (1 - Real.tanh (Q.κ * x 0) ^ 2) := by
  rw [Q.potential_eq, Real.tanh_eq_sinh_div_cosh, div_pow, Real.sinh_sq]
  field_simp [(Real.cosh_pos _).ne']
  ring

/-!
### A.2. Sign, bounds and parity
-/

/-- The potential is negative. -/
lemma potential_neg (x : Space 1) : Q.potential x < 0 := by
  rw [Q.potential_eq, neg_div, neg_lt_zero]
  exact div_pos Q.depth_pos (pow_pos (Real.cosh_pos _) 2)

/-- The potential is bounded below by `-depth`. -/
lemma neg_depth_le_potential (x : Space 1) : -Q.depth ≤ Q.potential x := by
  rw [Q.potential_eq, neg_div, neg_le_neg_iff]
  exact div_le_self Q.depth_pos.le (one_le_pow₀ (Real.one_le_cosh _))

/-- The minimum `-depth` of the potential is attained at the origin. -/
lemma potential_zero : Q.potential 0 = -Q.depth := by
  rw [Q.potential_eq]
  simp

/-- The potential is even. -/
lemma potential_neg_eq (x : Space 1) : Q.potential (-x) = Q.potential x := by
  rw [Q.potential_eq, Q.potential_eq]
  simp [Real.cosh_neg]

/-!
### A.3. Regularity
-/

/-- The function `tanh (κ * x)` on `Space 1` has temperate growth. -/
lemma tanh_hasTemperateGrowth :
    (fun x : Space 1 => Real.tanh (Q.κ * x 0)).HasTemperateGrowth :=
  (tanh_const_mul_hasTemperateGrowth Q.κ).comp (Space.eval_hasTemperateGrowth 0)

/-- The complexified function `ofReal ∘ tanh (κ * x)` has temperate growth. -/
lemma ofReal_comp_tanh_hasTemperateGrowth :
    (ofReal ∘ fun x : Space 1 => Real.tanh (Q.κ * x 0)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp Q.tanh_hasTemperateGrowth

/-- The potential has temperate growth. -/
lemma potential_hasTemperateGrowth : Q.potential.HasTemperateGrowth := by
  rw [show Q.potential = fun x => -Q.depth * (1 - Real.tanh (Q.κ * x 0) ^ 2) from
    funext Q.potential_eq_tanh]
  exact (Function.HasTemperateGrowth.const _).mul
    ((Function.HasTemperateGrowth.const 1).sub (Q.tanh_hasTemperateGrowth.pow 2))

/-- The complexified potential `ofReal ∘ potential` has temperate growth. -/
lemma ofReal_comp_potential_hasTemperateGrowth : (ofReal ∘ Q.potential).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp Q.potential_hasTemperateGrowth

/-- The potential is continuous. -/
lemma potential_continuous : Continuous Q.potential :=
  Q.potential_hasTemperateGrowth.1.continuous

/-!
## B. As a quantum system
-/

/-- The Pöschl-Teller system as a `SpaceDQuantumSystem` of dimension `1`. Its kinetic, potential
  and Hamiltonian operators are those of `SpaceDQuantumSystem`. -/
abbrev toSpaceDQuantumSystem : SpaceDQuantumSystem := ⟨1, Q.m, Q.m_pos, Q.potential⟩

lemma toSpaceDQuantumSystem_d : Q.toSpaceDQuantumSystem.d = 1 := rfl

lemma toSpaceDQuantumSystem_m : Q.toSpaceDQuantumSystem.m = Q.m := rfl

lemma toSpaceDQuantumSystem_potential : Q.toSpaceDQuantumSystem.potential = Q.potential := rfl

/-- The Hilbert space for the Pöschl-Teller system is `SpaceDHilbertSpace 1`. -/
@[nolint unusedArguments]
abbrev HS (_ : PoschlTeller) : Type _ := SpaceDHilbertSpace 1

/-!
## C. Operators
-/

/-!
### C.1. Kinetic energy, potential energy and Hamiltonian
-/

/-- In dimension one the kinetic operator is `(2m)⁻¹ 𝐩 0 ∘ 𝐩 0`. -/
lemma toSpaceDQuantumSystem_kineticCLM_apply (ψ : 𝓢(Space 1, ℂ)) :
    Q.toSpaceDQuantumSystem.kineticCLM ψ = (2 * Q.m)⁻¹ • momentumCLM 0 (momentumCLM 0 ψ) := by
  simp [SpaceDQuantumSystem.kineticCLM, dotProduct, ContinuousLinearMap.mul_def]

/-- The potential operator acts by pointwise multiplication by the potential. -/
lemma toSpaceDQuantumSystem_potentialCLM_apply (ψ : 𝓢(Space 1, ℂ)) (x : Space 1) :
    Q.toSpaceDQuantumSystem.potentialCLM ψ x = Q.potential x • ψ x :=
  SpaceDQuantumSystem.potentialCLM_apply_apply (Q := Q.toSpaceDQuantumSystem)
    Q.potential_hasTemperateGrowth ψ x

/-- The potential operator is self-adjoint. -/
lemma toSpaceDQuantumSystem_potentialOperator_isSelfAdjoint :
    IsSelfAdjoint Q.toSpaceDQuantumSystem.potentialOperator :=
  SpaceDQuantumSystem.potentialOperator_isSelfAdjoint (Q := Q.toSpaceDQuantumSystem)
    Q.potential_continuous.aestronglyMeasurable

/-- Schwartz functions lie in the domain of the potential operator. -/
lemma toSpaceDQuantumSystem_potentialOperator_domain_ge :
    SchwartzSubmodule 1 ≤ Q.toSpaceDQuantumSystem.potentialOperator.domain :=
  SpaceDQuantumSystem.potentialOperator_domain_ge (Q := Q.toSpaceDQuantumSystem)
    Q.potential_hasTemperateGrowth

/-- The pointwise action of the Hamiltonian on a Schwartz function. -/
lemma toSpaceDQuantumSystem_hamiltonianCLM_apply (ψ : 𝓢(Space 1, ℂ)) (x : Space 1) :
    Q.toSpaceDQuantumSystem.hamiltonianCLM ψ x =
      (2 * Q.m)⁻¹ • momentumCLM 0 (momentumCLM 0 ψ) x + Q.potential x • ψ x := by
  rw [SpaceDQuantumSystem.hamiltonianCLM_eq, _root_.add_apply, _root_.add_apply,
    Q.toSpaceDQuantumSystem_kineticCLM_apply, Q.toSpaceDQuantumSystem_potentialCLM_apply]
  rfl

/-!
### C.2. Creation and annihilation operators
-/

/-!
#### C.2.1. On Schwartz functions
-/

/-- Pointwise multiplication of Schwartz maps by `tanh(κx)`. -/
def tanhCLM : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  smulLeftCLM ℂ (ofReal ∘ fun x => tanh (Q.κ * x 0))

/-- Multiplication by `tanh (κ * x)` acts pointwise. -/
lemma tanhCLM_apply (ψ : 𝓢(Space 1, ℂ)) (x : Space 1) :
    Q.tanhCLM ψ x = Real.tanh (Q.κ * x 0) • ψ x := by
  rw [tanhCLM, smulLeftCLM_apply_apply Q.ofReal_comp_tanh_hasTemperateGrowth]
  simp [Function.comp]

/-- The creation operator, `1/√(2m) (P + iℏκ tanh(κX))` -/
def creationCLM : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  (1 / sqrt (2 * Q.m)) • momentumCLM 0 + (I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhCLM

/-- The annihilation operator, `1/√(2m) (P - iℏκ tanh(κX))` -/
def annihilationCLM : 𝓢(Space 1, ℂ) →L[ℂ] 𝓢(Space 1, ℂ) :=
  (1 / sqrt (2 * Q.m)) • momentumCLM 0 + (-I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhCLM

/-- The pointwise action of the creation operator. -/
lemma creationCLM_apply (ψ : 𝓢(Space 1, ℂ)) (x : Space 1) :
    Q.creationCLM ψ x = (1 / √(2 * Q.m)) • momentumCLM 0 ψ x
      + (I * ℏ * Q.κ / √(2 * Q.m)) * (Real.tanh (Q.κ * x 0) • ψ x) := by
  simp only [creationCLM, _root_.add_apply, _root_.smul_apply, Q.tanhCLM_apply]
  ring_nf

/-- The pointwise action of the annihilation operator. -/
lemma annihilationCLM_apply (ψ : 𝓢(Space 1, ℂ)) (x : Space 1) :
    Q.annihilationCLM ψ x = (1 / √(2 * Q.m)) • momentumCLM 0 ψ x
      + (-I * ℏ * Q.κ / √(2 * Q.m)) * (Real.tanh (Q.κ * x 0) • ψ x) := by
  simp only [annihilationCLM, _root_.add_apply, _root_.smul_apply, Q.tanhCLM_apply]
  ring_nf

/-- The sum of the ladder operators is `(2 / √(2m)) 𝐩`. -/
lemma creationCLM_add_annihilationCLM :
    Q.creationCLM + Q.annihilationCLM = (2 / √(2 * Q.m)) • momentumCLM 0 := by
  ext ψ x
  simp only [creationCLM, annihilationCLM, _root_.add_apply, _root_.smul_apply, Q.tanhCLM_apply]
  simp only [Nat.ofNat_nonneg, sqrt_mul, one_div, mul_inv_rev, Fin.isValue, momentumCLM_apply,
    neg_mul, smul_neg, real_smul, ofReal_mul, ofReal_inv, ofReal_tanh, smul_eq_mul, ofReal_div,
    ofReal_ofNat]
  ring_nf

/-- The difference of the ladder operators is `(2 i ℏ κ / √(2m)) tanh (κ X)`. -/
lemma creationCLM_sub_annihilationCLM :
    Q.creationCLM - Q.annihilationCLM = (2 * I * ℏ * Q.κ / √(2 * Q.m)) • Q.tanhCLM := by
  ext ψ x
  simp only [creationCLM, annihilationCLM, _root_.add_apply, _root_.sub_apply,
    _root_.smul_apply, Q.tanhCLM_apply]
  ring_nf

/-!
#### C.2.2. As unbounded operators
-/

/-- The unbounded operator defined by pointwise multiplication by `tanh(κx)`. -/
def tanhOperator : Q.HS →ₗ.[ℂ] Q.HS := 𝓜 _ (ofReal ∘ fun x => Real.tanh (Q.κ * x 0))

/-- The creation unbounded operator, `1/√(2m) (P + iℏκ tanh(κX))` -/
def creationOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  (1 / sqrt (2 * Q.m)) • momentumOperator 0 + (I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhOperator

/-- The annihilation unbounded operator, `1/√(2m) (P - iℏκ tanh(κX))` -/
def annihilationOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  (1 / sqrt (2 * Q.m)) • momentumOperator 0 + (-I * ℏ * Q.κ / sqrt (2 * Q.m)) • Q.tanhOperator

end PoschlTeller
end QuantumMechanics
end
