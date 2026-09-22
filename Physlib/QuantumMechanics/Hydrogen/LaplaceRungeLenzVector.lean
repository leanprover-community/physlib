/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Hydrogen.Basic
public import Physlib.QuantumMechanics.Operators.AngularMomentum
/-!

# Laplace-Runge-Lenz vector

In this file we define
- The (regularized) LRL vector operator for the quantum mechanical hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`.

The main results are
- The commutators `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` in `angularMomentum_commutation_lrl`
- The commutators `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = (-2iℏm·𝐇(ε) + iℏmkε²·𝐫(ε)⁻³))𝐋ᵢⱼ` in `lrl_commutation_lrl`
- The commutators `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏε²(⋯)` in `hamiltonianReg_commutation_lrl`
- The relation `𝐀(ε)² = 2m 𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k² + ε²(⋯)` in `lrlOperatorSqr_eq`

-/

@[expose] public section

namespace QuantumMechanics
namespace HydrogenAtom
noncomputable section
open Complex Constants
open KroneckerDelta
open ContinuousLinearMap SchwartzMap

variable (H : HydrogenAtom)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The (regularized) Laplace-Runge-Lenz vector operator for the `d`-dimensional hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`. -/
def lrlOperator (ε : ℝˣ) (i : Fin H.d) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 : ℝ)⁻¹ • (𝐩 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐩) - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i

/-- `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = 𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩)
    - (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i := by
  rw [lrlOperator, sub_left_inj] -- mk·r⁻¹x terms match exactly
  calc
    _ = (2 : ℝ)⁻¹ • ∑ j, ((𝐩 j ∘L 𝐱 i) ∘L 𝐩 j + 𝐱 i ∘L 𝐩 j ∘L 𝐩 j
        - ((𝐩 j ∘L 𝐱 j) ∘L 𝐩 i + 𝐱 j ∘L 𝐩 j ∘L 𝐩 i)) := by
      simp_rw [dotProduct, mul_def, ← Finset.sum_add_distrib, angularMomentumCLM, comp_sub,
        sub_comp, comp_assoc, momentum_comp_commute, ← sub_sub, add_sub, sub_add_eq_add_sub]
    _ = (2 : ℂ)⁻¹ • ∑ j, ((2 : ℂ) • 𝐱 i ∘L 𝐩 j ∘L 𝐩 j - (I * ℏ) • δ[i,j] • 𝐩 j
        - ((2 : ℂ) • (𝐱 j ∘L 𝐩 j) ∘L 𝐩 i - (I * ℏ) • 𝐩 i)) := by
      simp only [momentum_comp_position_eq, sub_comp, comp_assoc, smul_comp, id_comp, ofReal_ofNat,
        sub_add_eq_add_sub, eq_one_of_same, one_smul, ← Complex.coe_smul, ofReal_inv, two_smul]
    _ = (2 : ℂ)⁻¹ • ∑ j, ((2 : ℂ) • 𝐱 i ∘L 𝐩 j ∘L 𝐩 j - (2 : ℂ) • (𝐱 j ∘L 𝐩 j) ∘L 𝐩 i
        + (I * ℏ) • 𝐩 i - (I * ℏ) • δ[i,j] • 𝐩 j) := by
      simp_rw [sub_sub_sub_comm, sub_sub_eq_add_sub]
    _ = 𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩) - (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i
        + ((2⁻¹ * I * ℏ) • H.d • 𝐩 i - (2⁻¹ * I * ℏ) • 𝐩 i) := by
      simp only [add_sub_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
        ← comp_finsetSum, ← finsetSum_comp, sum_smul, smul_add, smul_sub, smul_smul, mul_assoc]
      norm_num
      rfl
    _ = 𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩) - (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i := by
      simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← sub_smul, mul_sub, mul_one]

/-- `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i =
    𝐋 i ⬝ᵥ 𝐩 + (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i := by
  rw [lrlOperator_eq, sub_left_inj, add_left_inj]
  symm
  trans ∑ j, 𝐱 i ∘L 𝐩 j ∘L 𝐩 j - ∑ j, (𝐱 j ∘L 𝐩 j) ∘L 𝐩 i
  · simp [dotProduct, mul_def, angularMomentumCLM, comp_assoc, momentum_comp_commute]
  simp [← comp_finsetSum, ← finsetSum_comp, dotProduct, mul_def]

/-- `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq'' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i =
    𝐩 ⬝ᵥ 𝐋 i - (2⁻¹ * I * ℏ * (H.d - 1)) • 𝐩 i - (H.m * H.k) • 𝐫₀ ε (-1) ∘L 𝐱 i := by
  trans (2 : ℝ) • H.lrlOperator ε i - H.lrlOperator ε i
  · simp [two_smul]
  nth_rw 2 [lrlOperator_eq']
  simp only [lrlOperator, smul_add, smul_sub, smul_smul]
  ring_nf
  ext
  simp only [one_smul, one_div, sub_apply, add_apply, smul_apply, comp_apply, radiusRegPowCLM_apply,
    positionCLM_apply, real_smul, ofReal_mul, ofReal_ofNat, momentumCLM_apply, neg_mul, smul_eq_mul,
    mul_neg, sub_neg_eq_add]
  ring

/-
## Angular momentum / LRL vector commutators
-/

/-- A supporting piece of `angularMomentum_commutation_lrl`: how `𝐋ᵢⱼ` commutes with the
dot-product term `𝐋ₖ⬝ᵥ𝐩` appearing in `H.lrlOperator`'s expanded form (`lrlOperator_eq'`). -/
lemma angularMomentum_commutation_Ldot_p (i j k : Fin H.d) :
    ⁅𝐋[H.d] i j, 𝐋 k ⬝ᵥ 𝐩⁆ =
      (I * ℏ) • (δ[i,k] • (𝐋 j ⬝ᵥ 𝐩) - δ[j,k] • (𝐋 i ⬝ᵥ 𝐩)) := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz,
    angularMomentum_commutation_angularMomentum, angularMomentum_commutation_momentum,
    comp_smul, smul_comp, comp_sub, sub_comp, add_comp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    KroneckerDelta.sum_smul]
  rw [angularMomentumCLM_antisymm k i, angularMomentumCLM_antisymm k j]
  simp only [neg_comp]
  module

/-- `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` -/
lemma angularMomentum_commutation_lrl (ε : ℝˣ) (i j k : Fin H.d) : ⁅𝐋 i j, H.lrlOperator ε k⁆ =
    (I * ℏ) • (δ[i,k] • H.lrlOperator ε j - δ[j,k] • H.lrlOperator ε i) := by
  simp_rw [H.lrlOperator_eq']
  rw [lie_sub, lie_add, angularMomentum_commutation_Ldot_p H i j k, lie_smul,
    angularMomentum_commutation_momentum, lie_smul, lie_leibniz,
    angularMomentum_commutation_radiusRegPow, angularMomentum_commutation_position]
  simp only [zero_comp, comp_sub, comp_smul, smul_sub]
  module

/-- `⁅𝐋ᵢⱼ, 𝐀(ε)²⁆ = 0` -/
@[simp]
lemma angularMomentum_commutation_lrlSqr (ε : ℝˣ) (i j : Fin H.d) :
    ⁅𝐋 i j, H.lrlOperator ε ⬝ᵥ H.lrlOperator ε⁆ = 0 := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, H.angularMomentum_commutation_lrl,
    comp_smul, comp_sub, smul_comp, sub_comp, ← smul_add, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_smul, sub_add_sub_cancel, sub_self, smul_zero]

/-- `⁅𝐋², 𝐀(ε)²⁆ = 0` -/
@[simp]
lemma angularMomentumSqr_commutation_lrlSqr (ε : ℝˣ) :
    ⁅𝐋²[H.d], H.lrlOperator ε ⬝ᵥ H.lrlOperator ε⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]

/-

## LRL / LRL commutators

To compute the commutator `⁅𝐀ᵢ(ε), 𝐀ⱼ(ε)⁆` we take the following approach:
- Write `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ ≕ f1ᵢ - f2ᵢ + f3ᵢ - f4ᵢ`
- Organize the sixteen terms which result from expanding `⁅f1ᵢ-f2ᵢ+f3ᵢ-f4ᵢ, f1ⱼ-f2ⱼ+f3ⱼ-f4ⱼ⁆`
  into four diagonal terms such as `⁅f1ᵢ, f1ⱼ⁆` and six off-diagonal pairs such as
  `⁅f1ᵢ, f3ⱼ⁆ + ⁅f3ᵢ, f1ⱼ⁆ = ⁅f1ᵢ, f3ⱼ⁆ - ⁅f1ⱼ, f3ᵢ⁆`.
- Compute the diagonal commutators and off-diagonal pairs individually. Many vanish, and those
  that don't are all of the form `iℏ (⋯) 𝐋ᵢⱼ` (as they must to be antisymmetric in `i,j`).
- Collect terms.

-/

private lemma positionDotMomentum_commutation_position {d : ℕ} (i : Fin d) :
    ⁅𝐱[d] ⬝ᵥ 𝐩, 𝐱 i⁆ = (-I * ℏ) • 𝐱 i := by
  trans ∑ j, 𝐱 j ∘L ⁅𝐩 j, 𝐱 i⁆
  · simp [dotProduct, mul_def, sum_lie, leibniz_lie]
  simp_rw [← lie_skew (𝐩 _), position_commutation_momentum, ← neg_smul, ← neg_mul, comp_smul,
    comp_id, ← Finset.smul_sum, sum_smul]

private lemma positionDotMomentum_commutation_momentum {d : ℕ} (i : Fin d) :
    ⁅𝐱[d] ⬝ᵥ 𝐩, 𝐩 i⁆ = (I * ℏ) • 𝐩 i := by
  trans ∑ j, ⁅𝐱 j, 𝐩 i⁆ ∘L 𝐩 j
  · simp [dotProduct, mul_def, sum_lie, leibniz_lie]
  simp_rw [position_commutation_momentum, smul_comp, id_comp, ← Finset.smul_sum, symm _ i, sum_smul]

private lemma positionDotMomentum_commutation_momentumSqr (d : ℕ) :
    ⁅𝐱[d] ⬝ᵥ 𝐩, 𝐩[d] ⬝ᵥ 𝐩⁆ = (2 * I * ℏ) • (𝐩 ⬝ᵥ 𝐩) := by
  trans ∑ i, ⁅𝐱 i, 𝐩 ⬝ᵥ 𝐩⁆ ∘L 𝐩 i
  · rw [dotProduct]
    simp [mul_def, sum_lie, leibniz_lie, ← lie_skew (𝐩 _) (𝐩 ⬝ᵥ 𝐩)]
  simp_rw [position_commutation_momentumSqr, smul_comp, ← Finset.smul_sum, dotProduct, mul_def]

private lemma positionDotMomentum_commutation_radiusRegPow (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    ⁅𝐱[d] ⬝ᵥ 𝐩, 𝐫₀[d] ε s⁆ = (-s * I * ℏ) • (𝐫₀ ε s - ε.1 ^ 2 • 𝐫₀ ε (s-2)) := by
  calc
    _ = ∑ i, 𝐱 i ∘L ⁅𝐩 i, 𝐫₀ ε s⁆ := by simp [dotProduct, mul_def, sum_lie, leibniz_lie]
    _ = (-s * I * ℏ) • (∑ i, 𝐱 i ∘L 𝐱 i) ∘L 𝐫₀ ε (s-2) := by
      simp [← lie_skew (𝐩 _), radiusRegPow_commutation_momentum, Finset.smul_sum,
        position_comp_radiusRegPow_commute, finsetSum_comp, comp_assoc]
    _ = (-s * I * ℏ) • (𝐫₀ ε s - ε.1 ^ 2 • 𝐫₀ ε (s-2)) := by simp [positionSqCLM_eq ε]

private lemma positionCompMomentumSqr_comm {d : ℕ} (i j : Fin d) :
    ⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆ = (-2 * I * ℏ) • (𝐩 ⬝ᵥ 𝐩) ∘L 𝐋 i j := by
  calc
    _ = (𝐱 j ∘L ⁅𝐱 i, 𝐩[d] ⬝ᵥ 𝐩⁆ + 𝐱 i ∘L ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐱 j⁆) ∘L (𝐩 ⬝ᵥ 𝐩) := by
      simp [lie_leibniz, leibniz_lie, comp_assoc]
    _ = (2 * I * ℏ) • 𝐋 j i ∘L (𝐩 ⬝ᵥ 𝐩) := by
      simp_rw [← lie_skew (𝐩 ⬝ᵥ 𝐩) _, position_commutation_momentumSqr, comp_neg, comp_smul,
        ← sub_eq_add_neg, ← smul_sub, smul_comp, angularMomentumCLM]
    _ = (-2 * I * ℏ) • (𝐩 ⬝ᵥ 𝐩) ∘L 𝐋 i j := by
      rw [angularMomentumCLM_antisymm j i, neg_comp, smul_neg, ← neg_smul, ← neg_mul,
        ← neg_mul, momentumSqr_comp_angularMomentum_commute]

private lemma positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add
    {d : ℕ} (i j : Fin d) : ⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆ +
    ⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆ = (-I * ℏ) • (𝐩 ⬝ᵥ 𝐩) ∘L 𝐋 i j := by
  suffices ∀ k l : Fin d, ⁅𝐱 k ∘L (𝐩 ⬝ᵥ 𝐩), (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 l⁆
      = (-I * ℏ) • (𝐱 k ∘L 𝐩 l - δ[k,l] • (𝐱 ⬝ᵥ 𝐩)) ∘L (𝐩 ⬝ᵥ 𝐩) by
    nth_rw 2 [← lie_skew]
    simp_rw [this, ← sub_eq_add_neg, ← smul_sub, ← sub_comp, symm j i, sub_sub_sub_cancel_right,
      momentumSqr_comp_angularMomentum_commute, angularMomentumCLM]
  intro k l
  calc
    _ = (𝐱 ⬝ᵥ 𝐩) ∘L ⁅𝐱 k, 𝐩 l⁆ ∘L (𝐩 ⬝ᵥ 𝐩) + 𝐱 k ∘L ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐱[d] ⬝ᵥ 𝐩⁆ ∘L 𝐩 l
        + ⁅𝐱 k, 𝐱[d] ⬝ᵥ 𝐩⁆ ∘L (𝐩 ⬝ᵥ 𝐩) ∘L 𝐩 l := by
      simp [lie_leibniz, leibniz_lie, add_assoc, comp_assoc]
    _ = (𝐱 ⬝ᵥ 𝐩) ∘L ⁅𝐱 k, 𝐩 l⁆ ∘L (𝐩 ⬝ᵥ 𝐩) + (-I * ℏ) • 𝐱 k ∘L 𝐩 l ∘L (𝐩 ⬝ᵥ 𝐩) := by
      simp only [← lie_skew _ (𝐱 ⬝ᵥ 𝐩), positionDotMomentum_commutation_position,
        positionDotMomentum_commutation_momentumSqr, momentumSqr_comp_momentum_commute,
        ← neg_smul, ← neg_mul, smul_comp, comp_smul, add_assoc, ← add_smul]
      ring_nf
    _ = (-I * ℏ) • (𝐱 k ∘L 𝐩 l - δ[k,l] • (𝐱 ⬝ᵥ 𝐩)) ∘L (𝐩 ⬝ᵥ 𝐩) := by
      simp_rw [position_commutation_momentum, sub_comp, smul_sub, smul_comp, comp_smul,
        id_comp, sub_eq_add_neg, ← neg_smul, neg_mul, neg_neg, comp_assoc, add_comm]

private lemma positionDotMomentumCompMomentum_comm {d : ℕ} (i j : Fin d) :
    ⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆ = 0 := by
  simp [lie_leibniz, leibniz_lie, momentum_comp_commute,
    ← lie_skew (𝐩 _) (𝐱 ⬝ᵥ 𝐩), positionDotMomentum_commutation_momentum, comp_assoc]

private lemma positionCompMomentumSqr_comm_momentum_add {d : ℕ} (i j : Fin d) :
    ⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), 𝐩 j⁆ + ⁅𝐩 i, 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆ = 0 := by
  nth_rw 2 [← lie_skew]
  simp [leibniz_lie, position_commutation_momentum, symm j]

private lemma positionDotMomentumCompMomentum_comm_momentum_add {d : ℕ} (i j : Fin d) :
    ⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, 𝐩 j⁆ + ⁅𝐩 i, (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆ = 0 := by
  nth_rw 2 [← lie_skew]
  simp [leibniz_lie, positionDotMomentum_commutation_momentum, momentum_comp_commute]

private lemma positionCompMomentumSqr_comm_radiusRegInvCompPosition_add
    {d : ℕ} (ε : ℝˣ) (i j : Fin d) : ⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), 𝐫₀ ε (-1) ∘L 𝐱 j⁆
    + ⁅𝐫₀ ε (-1) ∘L 𝐱 i, 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆ = (-2 * I * ℏ) • 𝐫₀ ε (-1) ∘L 𝐋 i j := by
  let A := ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐫₀[d] ε (-1)⁆
  have hA : 𝐱 i ∘L A ∘L 𝐱 j = 𝐱 j ∘L A ∘L 𝐱 i := by
    suffices A = (2 * I * ℏ) • 𝐫₀[d] ε (-3) ∘L (𝐱 ⬝ᵥ 𝐩)
        + ((d - 3) * ℏ ^ 2 : ℝ) • 𝐫₀ ε (-3) + (3 * ε.1 ^ 2 * ℏ ^ 2) • 𝐫₀ ε (-5) by
      simp_rw [this, add_comp, comp_add, smul_comp, comp_smul, ← comp_assoc,
        position_comp_radiusRegPow_commute, comp_assoc,
        comp_eq_comp_add_commute (𝐱 ⬝ᵥ 𝐩), positionDotMomentum_commutation_position,
        comp_add, comp_smul, ← comp_assoc (𝐱 _) (𝐱 _) _, position_comp_commute j i]
    simp_rw [A, ← lie_skew (𝐩 ⬝ᵥ 𝐩) _, radiusRegPow_commutation_momentumSqr, neg_sub, ← sub_sub,
      sub_eq_add_neg, ← neg_smul, ← neg_mul, neg_neg, ofReal_neg, ofReal_one, dotProduct, mul_def]
    ring_nf
    rw [add_rotate]
  calc
    _ = 𝐫₀ ε (-1) ∘L 𝐱 i ∘L ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐱 j⁆ + 𝐱 i ∘L A ∘L 𝐱 j
        - (𝐫₀ ε (-1) ∘L 𝐱 j ∘L ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐱 i⁆ + 𝐱 j ∘L A ∘L 𝐱 i) := by
      nth_rw 2 [← lie_skew]
      simp_rw [← sub_eq_add_neg, lie_leibniz, leibniz_lie, ← sub_sub]
      simp [A, comp_assoc]
    _ = 𝐫₀ ε (-1) ∘L (𝐱 i ∘L ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐱 j⁆ - 𝐱 j ∘L ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐱 i⁆) := by simp [hA]
    _ = (-2 * I * ℏ) • 𝐫₀ ε (-1) ∘L 𝐋 i j := by
      simp_rw [← lie_skew _ (𝐱 _), position_commutation_momentumSqr, comp_neg, comp_smul,
        ← neg_smul, ← neg_mul, ← smul_sub, comp_smul, angularMomentumCLM]

private lemma momentum_comm_radiusRegPow_position_symm {d : ℕ} (ε : ℝˣ) (s : ℝ) (i j : Fin d) :
    ⁅𝐩 i, 𝐫₀ ε s ∘L 𝐱 j⁆ = ⁅𝐩 j, 𝐫₀ ε s ∘L 𝐱 i⁆ := by
  simp [← lie_skew (𝐩 _), leibniz_lie, position_commutation_momentum, symm j i,
    radiusRegPow_commutation_momentum, position_comp_commute j i, comp_assoc]

private lemma positionDotMomentumCompMomentum_comm_radiusRegInvCompPosition_add
    {d : ℕ} (ε : ℝˣ) (i j : Fin d) : ⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, 𝐫₀ ε (-1) ∘L 𝐱 j⁆ +
    ⁅𝐫₀ ε (-1) ∘L 𝐱 i, (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆ = (I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐋 i j := by
  suffices ∀ k, ⁅𝐱[d] ⬝ᵥ 𝐩, 𝐫₀[d] ε (-1) ∘L 𝐱 k⁆ = (-I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐱 k by
    nth_rw 2 [← lie_skew]
    simp_rw [leibniz_lie, this,
      momentum_comm_radiusRegPow_position_symm, ← sub_eq_add_neg, add_sub_add_left_eq_sub,
      smul_comp, ← smul_sub, comp_assoc, ← comp_sub, angularMomentumCLM_antisymm i j, comp_neg,
      smul_neg, neg_mul, neg_smul, angularMomentumCLM]
  intro k
  calc
    _ = -(I * ℏ) • (ε.1 ^ 2) • 𝐫₀ ε (-1-2) ∘L 𝐱 k := by
      simp [lie_leibniz, positionDotMomentum_commutation_position,
        positionDotMomentum_commutation_radiusRegPow, sub_comp, smul_sub, ← add_sub_assoc]
    _ = (-I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐱 k := by
      simp only [← Complex.coe_smul, ofReal_pow, smul_smul]
      ring_nf

private lemma momentum_comm_radiusRegInvCompPosition_add {d : ℕ} (ε : ℝˣ) (i j : Fin d) :
    ⁅𝐩 i, 𝐫₀ ε (-1) ∘L 𝐱 j⁆ + ⁅𝐫₀ ε (-1) ∘L 𝐱 i, 𝐩 j⁆ = 0 := by
  rw [← lie_skew _ (𝐩 _), momentum_comm_radiusRegPow_position_symm, add_neg_cancel]

private lemma radiusRegInvCompPosition_comm {d : ℕ} (ε : ℝˣ) (i j : Fin d) :
    ⁅𝐫₀ ε (-1) ∘L 𝐱 i, 𝐫₀ ε (-1) ∘L 𝐱 j⁆ = 0 := by
  simp [lie_leibniz, leibniz_lie, ← lie_skew (𝐫₀ _ _) (𝐱 _)]

/-- `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = (-2iℏm·𝐇(ε) + iℏmkε²·𝐫(ε)⁻³)𝐋ᵢⱼ` -/
lemma lrl_commutation_lrl (ε : ℝˣ) (i j : Fin H.d) :
    ⁅H.lrlOperator ε i, H.lrlOperator ε j⁆ = ((-2 * I * ℏ * H.m) • H.hamiltonianRegCLM ε
    + (I * ℏ * H.m * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3)) ∘L 𝐋 i j := by
  repeat rw [lrlOperator_eq]
  let c₁ : ℂ := 2⁻¹ * I * ℏ * (H.d - 1)
  let c₂ : ℂ := H.m * H.k
  trans ⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆ + ⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆
      + (c₂ ^ 2) • ⁅𝐫₀ ε (-1) ∘L 𝐱 i, 𝐫₀ ε (-1) ∘L 𝐱 j⁆
      - (⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆ + ⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆)
      + c₁ • (⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), 𝐩 j⁆ + ⁅𝐩 i, 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆)
      - c₂ • (⁅𝐱 i ∘L (𝐩 ⬝ᵥ 𝐩), 𝐫₀ ε (-1) ∘L 𝐱 j⁆ + ⁅𝐫₀ ε (-1) ∘L 𝐱 i, 𝐱 j ∘L (𝐩 ⬝ᵥ 𝐩)⁆)
      - c₁ • (⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, 𝐩 j⁆ + ⁅𝐩 i, (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆)
      + c₂ • (⁅(𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 i, 𝐫₀ ε (-1) ∘L 𝐱 j⁆ + ⁅𝐫₀ ε (-1) ∘L 𝐱 i, (𝐱 ⬝ᵥ 𝐩) ∘L 𝐩 j⁆)
      - (c₁ * c₂) • (⁅𝐩 i, 𝐫₀ ε (-1) ∘L 𝐱 j⁆ + ⁅𝐫₀ ε (-1) ∘L 𝐱 i, 𝐩 j⁆)
  · simp only [lie_add, add_lie, lie_sub, sub_lie, lie_smul, smul_lie,
      momentum_commutation_momentum, smul_zero, add_zero, ← Complex.coe_smul, ofReal_mul]
    subst c₁ c₂
    ext
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, smul_add]
    ring
  rw [positionCompMomentumSqr_comm, positionDotMomentumCompMomentum_comm,
    positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add,
    positionCompMomentumSqr_comm_momentum_add, positionDotMomentumCompMomentum_comm_momentum_add,
    positionCompMomentumSqr_comm_radiusRegInvCompPosition_add,
    positionDotMomentumCompMomentum_comm_radiusRegInvCompPosition_add,
    momentum_comm_radiusRegInvCompPosition_add, radiusRegInvCompPosition_comm]
  subst c₁ c₂
  simp_rw [hamiltonianRegCLM_eq, smul_zero, add_zero, sub_zero, ← sub_smul, ← Complex.coe_smul,
    ofReal_inv, ofReal_mul, ofReal_ofNat, smul_sub, smul_smul, add_comp, sub_comp, smul_comp]
  ring_nf
  simp

/-
## Hamiltonian / LRL vector commutators
-/

private lemma pSqr_comm_pL_Lp {d : ℕ} (i : Fin d) :
    ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐩 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐩⁆ = 0 := by
  show ⁅𝐩 ⬝ᵥ 𝐩, ∑ j, 𝐩 j ∘L 𝐋 i j + ∑ j, 𝐋 i j ∘L 𝐩 j⁆ = 0
  simp [lie_sum, lie_leibniz, ← lie_skew (𝐩 ⬝ᵥ 𝐩) (𝐋 _ _)]

private lemma r_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) : ⁅𝐫₀[d] ε (-1), 𝐫₀ ε (-1) ∘L 𝐱 i⁆ = 0 := by
  simp [lie_leibniz, ← lie_skew (𝐫₀ _ _) (𝐱 _)]

private lemma xL_Lx_eq {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    𝐱 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐱 = (2 : ℝ) • (𝐱 ⬝ᵥ 𝐩) ∘L 𝐱 i + (-I * ℏ * (d - 3)) • 𝐱 i
    + ((-2 : ℝ) • 𝐫₀ ε 2 ∘L 𝐩 i + (2 * ε.1 ^ 2 : ℝ) • 𝐩 i) := by
  -- Change summand
  simp_rw [dotProduct, mul_def, ← Finset.sum_add_distrib, angularMomentumCLM, comp_sub,
    sub_comp, comp_assoc, sub_add_sub_comm, momentum_comp_position_eq, comp_sub, comp_smul,
    comp_id, ← comp_assoc, position_comp_commute i _, ← add_sub_assoc, ← two_smul ℝ,
    sub_sub_eq_add_sub, sub_add_eq_add_sub, comp_assoc, comp_eq_comp_add_commute (𝐱 i) (𝐩 _),
    position_commutation_momentum, symm _ i, comp_add, comp_smul, smul_add, comp_id, add_assoc,
    ← Complex.coe_smul, smul_smul, ← add_smul, ← comp_assoc, eq_one_of_same, one_smul]
  -- Split/do sums
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← finsetSum_comp,
    sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    positionSqCLM_eq ε, sub_comp, smul_comp, id_comp, smul_sub]
  -- Clean up coefficients
  simp_rw [add_sub_assoc, add_right_inj, smul_smul, ← sub_smul, sub_eq_add_neg, neg_add, ← neg_smul,
    ← Complex.coe_smul, smul_smul, ofReal_neg, ofReal_mul, ofReal_pow, ofReal_ofNat, neg_neg]
  ring_nf

private lemma pSqr_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐫₀ ε (-1) ∘L 𝐱 i⁆ = (I * ℏ) • 𝐫₀ ε (-3) ∘L (𝐱 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐱)
    + ((-2 * I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐩 i
      + (3 * ℏ ^ 2 * ε.1 ^ 2) • 𝐫₀ ε (-5) ∘L 𝐱 i) := by
  trans (-2 * I * ℏ) • 𝐫₀ ε (-1) ∘L 𝐩 i + (2 * I * ℏ) • 𝐫₀ ε (-3) ∘L (𝐱 ⬝ᵥ 𝐩) ∘L 𝐱 i
      + (ℏ ^ 2 * (d - 3) : ℝ) • 𝐫₀ ε (-3) ∘L 𝐱 i + (3 * ℏ ^ 2 * ε.1 ^ 2) • 𝐫₀ ε (-5) ∘L 𝐱 i
  · rw [← lie_skew]
    simp_rw [leibniz_lie, position_commutation_momentumSqr, radiusRegPow_commutation_momentumSqr,
      sub_comp, add_comp, smul_comp, comp_smul, comp_assoc, neg_add, neg_sub', neg_add,
      sub_neg_eq_add, ← neg_smul, add_assoc, ofReal_neg, ofReal_one, dotProduct, mul_def]
    ring_nf
  rw [← add_assoc, add_left_inj, add_rotate]
  simp_rw [xL_Lx_eq ε i, comp_add, comp_smul, smul_add, ← Complex.coe_smul, smul_smul, ← comp_assoc,
    radiusRegPowCLM_comp_eq, comp_assoc, add_assoc, ← add_smul, ofReal_mul, ofReal_sub,
    ofReal_neg, ofReal_pow, ofReal_ofNat]
  ring_nf
  simp [I_sq]

private lemma r_comm_pL_Lp {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐫₀[d] ε (-1), 𝐩 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐩⁆ =
    -((I * ℏ) • 𝐫₀ ε (-3) ∘L (𝐱 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐱)) := by
  calc
    _ = ∑ j, (⁅𝐫₀[d] ε (-1), 𝐩 j⁆ ∘L 𝐋 i j + 𝐋 i j ∘L ⁅𝐫₀[d] ε (-1), 𝐩 j⁆) := by
      simp [dotProduct, mul_def, ← Finset.sum_add_distrib, lie_sum, lie_leibniz,
        ← lie_skew _ (𝐋 _ _)]
    _ = -((I * ℏ) • ∑ j, (𝐫₀ ε (-3) ∘L 𝐱 j ∘L 𝐋 i j + (𝐋 i j ∘L 𝐫₀ ε (-3)) ∘L 𝐱 j)) := by
      simp only [radiusRegPow_commutation_momentum, smul_comp, comp_smul, ← smul_add,
        ← Finset.smul_sum, comp_assoc, ofReal_neg, ofReal_one, ← neg_smul]
      ring_nf
    _ = -((I * ℏ) • 𝐫₀ ε (-3) ∘L (𝐱 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐱)) := by
      simp_rw [angularMomentum_comp_radiusRegPow_commute, comp_assoc, ← comp_add, ← comp_finsetSum,
        Finset.sum_add_distrib, dotProduct, mul_def]

/-- `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏk·ε²𝐫(ε)⁻³𝐩ᵢ - 3ℏ²k/2·ε²𝐫(ε)⁻⁵𝐱ᵢ` -/
lemma hamiltonianReg_commutation_lrl (ε : ℝˣ) (i : Fin H.d) :
    ⁅H.hamiltonianRegCLM ε, H.lrlOperator ε i⁆ = (I * ℏ * H.k * ε.1 ^ 2) • 𝐫₀ ε (-3) ∘L 𝐩 i
    - (3 / 2 * ℏ ^ 2 * H.k * ε.1 ^ 2) • 𝐫₀ ε (-5) ∘L 𝐱 i := by
  trans (-2⁻¹ * H.k) • (⁅𝐩[H.d] ⬝ᵥ 𝐩, 𝐫₀ ε (-1) ∘L 𝐱 i⁆
      + ⁅𝐫₀[H.d] ε (-1), 𝐩 ⬝ᵥ 𝐋 i + 𝐋 i ⬝ᵥ 𝐩⁆)
  · have h : H.m * H.k * (H.m⁻¹ * 2⁻¹) = 2⁻¹ * H.k := by grind [H.m_ne_zero]
    simp only [hamiltonianRegCLM_eq, lrlOperator, lie_sub, sub_lie, smul_lie, lie_smul,
      pSqr_comm_pL_Lp]
    simp [r_comm_rx, h, smul_smul, sub_eq_neg_add, add_comm]
  simp_rw [pSqr_comm_rx, r_comm_pL_Lp, add_neg_cancel_comm, smul_add, sub_eq_add_neg, ← neg_smul,
    ← neg_mul, ← Complex.coe_smul, smul_smul, ofReal_mul, ofReal_neg, ofReal_inv, ofReal_div,
    ofReal_pow, ofReal_ofNat]
  ring_nf

/-

## LRL vector squared

To compute `𝐀(ε)²` we take the following approach:
- Write `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the first term and
  `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the second.
- Expand out to nine terms: one is a triple sum, two are double sums and the rest are single sums.
- Compute each term, symmetrizing the sums (see `sum_symmetrize` and `sum_symmetrize'`).
- Collect terms.

-/

private lemma sum_symmetrize {d : ℕ} (f : Fin d → Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ∑ i, ∑ j, f i j = (2 : ℂ)⁻¹ • ∑ i, ∑ j, (f i j + f j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel_of_invertible, one_smul]

private lemma sum_symmetrize' {d : ℕ}
    (f : Fin d → Fin d → Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ∑ i, ∑ j, ∑ k, f i j k = (2 : ℂ)⁻¹ • ∑ i, ∑ k, ∑ j, (f i j k + f k j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel_of_invertible, one_smul]
  congr with
  rw [Finset.sum_comm]

private lemma sum_Lpp (d : ℕ) : ∑ i : Fin d, ∑ j, 𝐋 i j ∘L 𝐩 j ∘L 𝐩 i = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [angularMomentumCLM_antisymm j i, momentum_comp_commute j i]
  simp

private lemma sum_ppL (d : ℕ) : ∑ i : Fin d, ∑ j, 𝐩 i ∘L 𝐩 j ∘L 𝐋 i j = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← comp_assoc, ← comp_assoc, angularMomentumCLM_antisymm j i, momentum_comp_commute j i]
  simp

private lemma sum_LppL (d : ℕ) :
    ∑ i : Fin d, ∑ j, ∑ k, 𝐋 i j ∘L 𝐩 j ∘L 𝐩 k ∘L 𝐋 i k = (𝐩 ⬝ᵥ 𝐩) ∘L 𝐋² := by
  rw [sum_symmetrize']
  conv_lhs =>
    enter [2, 2, i, 2, j, 2, k]
    calc
      _ = (𝐋 i k ∘L 𝐩 k ∘L 𝐩 j - 𝐋 j k ∘L 𝐩 k ∘L 𝐩 i) ∘L 𝐋 i j := by
        simp [angularMomentumCLM_antisymm j i, comp_neg, ← comp_assoc, sub_eq_add_neg]
      _ = (𝐱 i ∘L 𝐩 k ∘L 𝐩 k ∘L 𝐩 j - 𝐱 k ∘L 𝐩 i ∘L 𝐩 k ∘L 𝐩 j
          - (𝐱 j ∘L 𝐩 k ∘L 𝐩 k ∘L 𝐩 i - 𝐱 k ∘L 𝐩 j ∘L 𝐩 k ∘L 𝐩 i)) ∘L 𝐋 i j := by
        simp_rw [angularMomentumCLM, sub_comp, comp_assoc]
      _ = (𝐱 i ∘L 𝐩 j ∘L 𝐩 k ∘L 𝐩 k - 𝐱 j ∘L 𝐩 i ∘L 𝐩 k ∘L 𝐩 k) ∘L 𝐋 i j := by
        simp_rw [momentum_comp_commute k, ← comp_assoc (𝐩 _), momentum_comp_commute k,
          momentum_comp_commute i j, sub_sub_sub_cancel_right]
      _ = 𝐋 i j ∘L (𝐩 k ∘L 𝐩 k) ∘L 𝐋 i j := by
        simp_rw [← comp_assoc, ← sub_comp, angularMomentumCLM]
  trans (2 : ℂ)⁻¹ • ∑ i, ∑ j, 𝐋 i j ∘L (𝐩 ⬝ᵥ 𝐩) ∘L 𝐋 i j
  · simp_rw [← comp_finsetSum, ← finsetSum_comp, ← comp_assoc, dotProduct, mul_def]
  simp_rw [← comp_assoc, ← momentumSqr_comp_angularMomentum_commute, comp_assoc, ← comp_finsetSum,
    ← comp_smul, angularMomentumOperatorSqr]

private lemma sum_Lprx (d : ℕ) (ε : ℝˣ) :
    ∑ i, ∑ j, 𝐋 i j ∘L 𝐩 j ∘L 𝐫₀[d] ε (-1) ∘L 𝐱 i = 𝐫₀ ε (-1) ∘L 𝐋² := by
  simp_rw [← position_comp_radiusRegPow_commute, ← comp_assoc, ← finsetSum_comp _ (𝐫₀ _ _)]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [1, 2, 2, i, 2, j]
    calc
      _ = 𝐋 i j ∘L (𝐩 j ∘L 𝐱 i - 𝐩 i ∘L 𝐱 j) := by
        simp [angularMomentumCLM_antisymm j i, comp_assoc, sub_eq_add_neg]
      _ = 𝐋 i j ∘L 𝐋 i j := by
        simp [momentum_comp_position_eq, symm j i, angularMomentumCLM]
  rw [← angularMomentumSqr_comp_radiusRegPow_commute, angularMomentumOperatorSqr]

private lemma sum_rxpL (d : ℕ) (ε : ℝˣ) :
    ∑ i, ∑ j, 𝐫₀[d] ε (-1) ∘L 𝐱 i ∘L 𝐩 j ∘L 𝐋 i j = 𝐫₀ ε (-1) ∘L 𝐋² := by
  simp_rw [← comp_finsetSum (𝐫₀ _ _)]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [angularMomentumCLM_antisymm j i, comp_neg, comp_neg, ← sub_eq_add_neg, ← comp_assoc,
      ← comp_assoc, ← sub_comp, ← angularMomentumCLM]
  rw [angularMomentumOperatorSqr]

private lemma sum_prx (d : ℕ) (ε : ℝˣ) :
    ∑ i, 𝐩 i ∘L 𝐫₀[d] ε (-1) ∘L 𝐱 i = 𝐫₀ ε (-1) ∘L (𝐱 ⬝ᵥ 𝐩)
    - (I * ℏ * (d - 1)) • 𝐫₀ ε (-1) - (I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) := by
  calc
    _ = ∑ i, (𝐫₀ ε (-1) ∘L 𝐩 i ∘L 𝐱 i + (I * ℏ) • 𝐫₀ ε (-3) ∘L 𝐱 i ∘L 𝐱 i) := by
      simp_rw [← comp_assoc, momentum_comp_radiusRegPow_eq]
      ring_nf
      simp
    _ = ∑ i, (𝐫₀ ε (-1) ∘L 𝐱 i ∘L 𝐩 i - (I * ℏ) • 𝐫₀ ε (-1)
        + (I * ℏ) • 𝐫₀ ε (-3) ∘L 𝐱 i ∘L 𝐱 i) := by simp [momentum_comp_position_eq]
    _ = 𝐫₀ ε (-1) ∘L ∑ i, 𝐱 i ∘L 𝐩 i + (-d * I * ℏ) • 𝐫₀ ε (-1)
        + (I * ℏ) • 𝐫₀ ε (-3) ∘L ∑ i, 𝐱 i ∘L 𝐱 i := by
      simp [Finset.sum_add_distrib, ← comp_finsetSum, ← Finset.smul_sum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc, sub_eq_add_neg]
    _ = 𝐫₀ ε (-1) ∘L (𝐱 ⬝ᵥ 𝐩) - (I * ℏ * (d - 1)) • 𝐫₀ ε (-1)
        - (I * ℏ * ε.1 ^ 2) • 𝐫₀ ε (-3) := by
      simp only [dotProduct, mul_def, positionSqCLM_eq ε, comp_sub, comp_smul, comp_id,
        radiusRegPowCLM_comp_eq, smul_sub, ← Complex.coe_smul, ofReal_pow, smul_smul]
      ring_nf
      simp_rw [← add_sub_assoc, add_assoc, ← add_smul, sub_eq_add_neg, ← neg_smul]
      ring_nf

private lemma sum_rxp (d : ℕ) (ε : ℝˣ) :
    ∑ i, 𝐫₀[d] ε (-1) ∘L 𝐱 i ∘L 𝐩 i = 𝐫₀ ε (-1) ∘L (𝐱 ⬝ᵥ 𝐩) := by rw [← comp_finsetSum]; rfl

private lemma sum_rxrx (d : ℕ) (ε : ℝˣ) : ∑ i, 𝐫₀[d] ε (-1) ∘L 𝐱 i ∘L 𝐫₀ ε (-1) ∘L 𝐱 i =
    ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) - (ε.1 ^ 2) • 𝐫₀ ε (-2) := by
  simp_rw [← comp_finsetSum, ← comp_assoc, position_comp_radiusRegPow_commute, comp_assoc,
    ← comp_finsetSum, ← comp_assoc, radiusRegPowCLM_comp_eq, positionSqCLM_eq ε]
  ring_nf
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The square of the (regularized) LRL vector operator is related to the (regularized) Hamiltonian
  `𝐇(ε)` of the hydrogen atom, square of the angular momentum `𝐋²` and powers of `𝐫(ε)` as
  `𝐀(ε)² = 2m·𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k²(𝟙 - ε²·𝐫(ε)⁻²) - ½(d-1)mkℏ²ε²𝐫(ε)⁻³`. -/
lemma lrlOperatorSqr_eq (ε : ℝˣ) : H.lrlOperator ε ⬝ᵥ H.lrlOperator ε =
    (2 * H.m) • (H.hamiltonianRegCLM ε) ∘L
      (𝐋² + (4⁻¹ * ℏ ^ 2 * (H.d - 1) ^ 2 : ℝ) • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ))
    + (H.m ^ 2 * H.k ^ 2) • (ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ) - ε.1 ^ 2 • 𝐫₀ ε (-2))
    - (2⁻¹ * ℏ^2 * H.m * H.k * (H.d - 1) * ε.1 ^ 2) • 𝐫₀ ε (-3) := by
  simp_rw [dotProduct, mul_def]
  conv_lhs => enter [2, i, 1]; rw [lrlOperator_eq']
  conv_lhs => enter [2, i, 2]; rw [lrlOperator_eq'']
  simp_rw [dotProduct, mul_def, sub_eq_add_neg, ← neg_smul, add_comp, comp_add, smul_comp,
    comp_smul, finsetSum_comp, comp_finsetSum, Finset.sum_add_distrib, ← Finset.smul_sum,
    comp_assoc, sum_LppL, sum_Lpp, sum_Lprx, sum_ppL, sum_prx, sum_rxpL, sum_rxp, sum_rxrx]
  simp only [dotProduct, mul_def, ← neg_mul, smul_zero, add_zero, ← Complex.coe_smul, ofReal_mul,
    ofReal_neg, smul_smul, zero_add, sub_eq_add_neg, ← neg_smul, smul_add, ofReal_pow,
    hamiltonianRegCLM_eq, ofReal_inv, ofReal_ofNat]
  ring_nf
  ext
  simp only [add_apply, _root_.smul_apply, _root_.add_apply,
    _root_.smul_apply, Function.comp_apply, coe_comp, coe_id', smul_eq_mul, ofReal_add,
    ofReal_neg, ofReal_one, ofReal_natCast]
  grind [I_sq, H.m_ne_zero, mul_inv_cancel₀, ofReal_eq_zero]

end
end HydrogenAtom
end QuantumMechanics
