/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.QuantumMechanics.DDimensions.Hydrogen.Basic
public import PhysLean.QuantumMechanics.DDimensions.Operators.Commutation
/-!

# Laplace-Runge-Lenz vector

In this file we define
- The (regularized) LRL vector operator for the quantum mechanical hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`.
- The square of the LRL vector operator, `𝐀(ε)² ≔ 𝐀(ε)ᵢ𝐀(ε)ᵢ`.

The main results are
- The commutators `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` in `angularMomentum_commutation_lrl`
- The commutators `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = -iℏ 2m 𝐇(ε)𝐋ᵢⱼ` in `lrl_commutation_lrl`
- The commutators `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏε²(⋯)` in `hamiltonianReg_commutation_lrl`
- The relation `𝐀(ε)² = 2m 𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k² + ε²(⋯)` in `lrlOperatorSqr_eq`

-/

@[expose] public section

namespace QuantumMechanics
namespace HydrogenAtom
noncomputable section
open Constants
open KroneckerDelta
open ContinuousLinearMap SchwartzMap

variable (H : HydrogenAtom)

/-- The (regularized) Laplace-Runge-Lenz vector operator for the `d`-dimensional hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`. -/
def lrlOperator (ε : ℝˣ) (i : Fin H.d) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 : ℝ)⁻¹ • ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j]) - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i]

/-- The square of the LRL vector operator, `𝐀(ε)² ≔ 𝐀(ε)ᵢ𝐀(ε)ᵢ`. -/
def lrlOperatorSqr (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  ∑ i, (H.lrlOperator ε i) ∘L (H.lrlOperator ε i)

/-- `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq (ε : ℝˣ) (i : Fin H.d) :
    H.lrlOperator ε i = 𝐱[i] ∘L 𝐩² - (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐩[i]
    + (2⁻¹ * Complex.I * ℏ * (H.d - 1)) • 𝐩[i] - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] := by
  unfold lrlOperator angularMomentumOperator
  congr
  conv_lhs =>
    enter [2, 2, j]
    rw [comp_sub, sub_comp]
    repeat rw [← comp_assoc, momentum_comp_position_eq, sub_comp, smul_comp, id_comp]
    repeat rw [comp_assoc]
    rw [momentum_comp_commute i j]

  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← ContinuousLinearMap.comp_finset_sum]
  simp only [← comp_assoc, ← ContinuousLinearMap.finset_sum_comp]
  rw [← momentumOperatorSqr]
  unfold kroneckerDelta
  simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← smul_assoc]
  ext ψ x
  simp only [Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_one, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, nsmul_eq_mul, smul_add,
    ContinuousLinearMap.add_apply, coe_smul', coe_sub', coe_comp', coe_sum', Pi.smul_apply,
    Pi.sub_apply, Function.comp_apply, Finset.sum_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, SchwartzMap.sub_apply, positionOperator_apply, momentumOperator_apply,
    neg_mul, smul_eq_mul, mul_neg, sub_neg_eq_add, SchwartzMap.sum_apply, Finset.sum_neg_distrib,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

/-- `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = ∑ j, 𝐋[i,j] ∘L 𝐩[j]
    + (2⁻¹ * Complex.I * ℏ * (H.d - 1)) • 𝐩[i] - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] := by
  unfold lrlOperator
  congr
  conv_lhs =>
    enter [2, 2, j]
    rw [comp_eq_comp_sub_commute 𝐩[j] 𝐋[i,j], angularMomentum_commutation_momentum]
  repeat rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  unfold kroneckerDelta
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', coe_sum', coe_comp', Pi.smul_apply,
    Finset.sum_apply, Function.comp_apply, coe_sub', Pi.sub_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, SchwartzMap.sum_apply, SchwartzMap.sub_apply]
  simp only [Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_one, mul_zero,
    momentumOperator_apply, neg_mul, smul_eq_mul, mul_neg, ite_mul, zero_mul,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_neg_eq_add, smul_add, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

/-- `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq'' (ε : ℝˣ) (i : Fin H.d) : H.lrlOperator ε i = ∑ j, 𝐩[j] ∘L 𝐋[i,j]
    - (2⁻¹ * Complex.I * ℏ * (H.d - 1)) • 𝐩[i] - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] := by
  unfold lrlOperator
  congr
  conv_lhs =>
    enter [2, 2, j]
    rw [comp_eq_comp_add_commute 𝐋[i,j] 𝐩[j], angularMomentum_commutation_momentum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ext ψ x
  unfold kroneckerDelta
  simp only [ContinuousLinearMap.add_apply, coe_smul', coe_sum', coe_comp',
    Pi.smul_apply, Finset.sum_apply, Function.comp_apply, coe_sub', Pi.sub_apply,
    SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_ofNat, SchwartzMap.sub_apply]
  simp only [momentumOperator_apply, neg_mul, Finset.sum_neg_distrib, Nat.cast_ite, Nat.cast_one,
    CharP.cast_eq_zero, mul_ite, mul_one, mul_zero, smul_eq_mul, mul_neg, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, sub_neg_eq_add]
  ring

/-- The operator `𝐱ᵢ𝐩ᵢ` on Schwartz maps. -/
private def positionDotMomentum {d} := ∑ i : Fin d, 𝐱[i] ∘L 𝐩[i]

/-- The operator `𝐱ᵢ𝐩²` on Schwartz maps. -/
private def positionCompMomentumSqr {d} (i : Fin d) := 𝐱[i] ∘L 𝐩²

/-- The operator `(𝐱ⱼ𝐩ⱼ)𝐱ᵢ` on Schwartz maps. -/
private def positionDotMomentumCompMomentum {d} (i : Fin d) := positionDotMomentum ∘L 𝐩[i]

/-- The operator `½iℏ(d-1)𝐩ᵢ` on Schwartz maps. -/
private def constMomentum {d} (i : Fin d) := (2⁻¹ * Complex.I * ℏ * (d - 1)) • 𝐩[i]

/-- The operator `mk·𝐫(ε)⁻¹𝐱ᵢ` on Schwartz maps. -/
private def constRadiusRegInvCompPosition (ε : ℝˣ) (i : Fin H.d) :=
  (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i]

/-
## Angular momentum / LRL vector commutators
-/

/-- `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` -/
@[sorryful]
lemma angularMomentum_commutation_lrl (ε : ℝˣ) (i j k : Fin H.d) :
    ⁅𝐋[i,j], H.lrlOperator ε k⁆ = (Complex.I * ℏ * δ[i,k]) • H.lrlOperator ε j
    - (Complex.I * ℏ * δ[j,k]) • H.lrlOperator ε i := by
  sorry

/-- `⁅𝐋ᵢⱼ, 𝐀(ε)²⁆ = 0` -/
@[sorryful]
lemma angularMomentum_commutation_lrlSqr (ε : ℝˣ) (i j : Fin H.d) :
    ⁅𝐋[i,j], H.lrlOperatorSqr ε⁆ = 0 := by
  unfold lrlOperatorSqr
  simp only [lie_sum, lie_leibniz, H.angularMomentum_commutation_lrl]
  simp only [comp_sub, comp_smul, sub_comp, smul_comp]
  dsimp only [kroneckerDelta]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- `⁅𝐋², 𝐀(ε)²⁆ = 0` -/
@[sorryful]
lemma angularMomentumSqr_commutation_lrlSqr (ε : ℝˣ) :
    ⁅angularMomentumOperatorSqr (d := H.d), H.lrlOperatorSqr ε⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  simp [sum_lie, leibniz_lie, H.angularMomentum_commutation_lrlSqr]

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

private lemma positionDotMomentum_commutation_position {d} (i : Fin d) :
    ⁅positionDotMomentum (d := d), 𝐱[i]⁆ = (-Complex.I * ℏ) • 𝐱[i] := by
  unfold positionDotMomentum
  simp only [← lie_skew 𝐩[_] _, position_commutation_position, position_commutation_momentum,
    leibniz_lie, kroneckerDelta, sum_lie, comp_neg, comp_smul]
  simp

private lemma positionDotMomentum_commutation_momentum {d} (i : Fin d) :
    ⁅positionDotMomentum (d := d), 𝐩[i]⁆ = (Complex.I * ℏ) • 𝐩[i] := by
  unfold positionDotMomentum
  simp only [momentum_commutation_momentum, position_commutation_momentum, kroneckerDelta,
    sum_lie, leibniz_lie, smul_comp]
  simp

private lemma positionDotMomentum_commutation_momentumSqr {d} :
    ⁅positionDotMomentum (d := d), momentumOperatorSqr (d := d)⁆ = (2 * Complex.I * ℏ) • 𝐩² := by
  unfold momentumOperatorSqr
  simp only [positionDotMomentum_commutation_momentum, lie_sum, lie_leibniz, comp_smul,
    smul_comp]
  rw [Finset.smul_sum]
  congr
  ext i ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', coe_comp', Pi.smul_apply,
    Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
  ring

private lemma positionDotMomentum_commutation_radiusRegPow {d} (ε : ℝˣ) :
    ⁅positionDotMomentum (d := d), radiusRegPowOperator (d := d) ε s⁆ =
    (-s * Complex.I * ℏ) • (𝐫[d,ε,s] - ε.1 ^ 2 • 𝐫[d,ε,s-2]) := by
  unfold positionDotMomentum
  rw [sum_lie]
  conv_lhs =>
    enter [2, i]
    rw [leibniz_lie, position_commutation_radiusRegPow, zero_comp, add_zero]
    rw [← lie_skew, radiusRegPow_commutation_momentum, comp_neg, comp_smul]
    rw [comp_eq_comp_sub_commute 𝐫[d,ε,_] 𝐱[_], position_commutation_radiusRegPow, sub_zero,
      ← comp_assoc]
  rw [Finset.sum_neg_distrib, ← Finset.smul_sum, ← finset_sum_comp]
  rw [positionOperatorSqr_eq]
  rw [sub_comp, smul_comp, radiusRegPowOperator_comp_eq]
  simp only [add_sub_cancel, neg_mul, neg_smul, neg_inj]
  congr

private lemma positionCompMomentumSqr_comm {d} (i j : Fin d) :
    ⁅positionCompMomentumSqr (d := d) i, positionCompMomentumSqr j⁆ =
    (-2 * Complex.I * ℏ) • 𝐩² ∘L 𝐋[i,j] := by
  unfold positionCompMomentumSqr
  rw [leibniz_lie, lie_leibniz, lie_leibniz]
  rw [lie_self, ← lie_skew 𝐩² 𝐱[j]]
  rw [position_commutation_position, momentumSqr_comp_angularMomentum_commute]
  repeat rw [position_commutation_momentumSqr]
  unfold angularMomentumOperator
  ext ψ x
  simp only [comp_zero, neg_comp, smul_comp, zero_add, comp_neg, comp_smulₛₗ, RingHom.id_apply,
    zero_comp, add_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul',
    coe_comp', Pi.smul_apply, Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    SchwartzMap.smul_apply, smul_eq_mul, neg_mul, sub_comp, neg_smul, coe_sub', Pi.sub_apply,
    SchwartzMap.sub_apply]
  ring

private lemma positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add {d} (i j : Fin d) :
    ⁅positionCompMomentumSqr (d := d) i, positionDotMomentumCompMomentum j⁆ +
    ⁅positionDotMomentumCompMomentum i, positionCompMomentumSqr j⁆ =
    (-Complex.I * ℏ) • 𝐩² ∘L 𝐋[i,j] := by
  unfold positionCompMomentumSqr positionDotMomentumCompMomentum
  nth_rw 2 [← lie_skew]
  repeat rw [leibniz_lie, lie_leibniz, lie_leibniz]
  repeat rw [← lie_skew _ positionDotMomentum]
  repeat rw [position_commutation_momentum]
  repeat rw [momentumSqr_commutation_momentum]
  repeat rw [positionDotMomentum_commutation_position]
  repeat rw [positionDotMomentum_commutation_momentumSqr]
  simp only [neg_comp, smul_comp, add_comp, comp_zero, zero_add, comp_smul, id_comp, comp_assoc]
  repeat rw [comp_eq_comp_add_commute 𝐩² 𝐩[_], momentumSqr_commutation_momentum]
  rw [symm j i]
  trans (-Complex.I * ℏ) • 𝐋[i,j] ∘L 𝐩²
  · ext ψ x
    unfold angularMomentumOperator
    simp only [add_zero, comp_neg, comp_smulₛₗ, RingHom.id_apply, neg_mul, neg_smul, neg_neg,
      coe_sub', Pi.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      coe_smul', coe_comp', Pi.smul_apply, Function.comp_apply, SchwartzMap.sub_apply,
      SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply, smul_eq_mul, sub_comp]
    ring
  rw [comp_eq_comp_sub_commute 𝐩² _, angularMomentum_commutation_momentumSqr, sub_zero]

private lemma positionDotMomentumCompMomentum_comm {d} (i j : Fin d) :
    ⁅positionDotMomentumCompMomentum i, positionDotMomentumCompMomentum j⁆ = 0 := by
  unfold positionDotMomentumCompMomentum
  rw [leibniz_lie, lie_leibniz, lie_leibniz, lie_self,
    ← lie_skew _ positionDotMomentum]
  ext ψ x
  simp [momentum_commutation_momentum, positionDotMomentum_commutation_momentum,
    momentum_comp_commute i j]

private lemma positionCompMomentumSqr_comm_constMomentum_add {d} (i j : Fin d) :
    ⁅positionCompMomentumSqr i, constMomentum j⁆ +
    ⁅constMomentum i, positionCompMomentumSqr j⁆ = 0 := by
  unfold positionCompMomentumSqr constMomentum
  nth_rw 2 [← lie_skew]
  repeat rw [lie_smul, leibniz_lie, momentumSqr_commutation_momentum, comp_zero, zero_add,
    position_commutation_momentum, smul_comp, id_comp]
  rw [symm j i, add_neg_eq_zero]

private lemma positionDotMomentumCompMomentum_comm_constMomentum_add {d} (i j : Fin d) :
    ⁅positionDotMomentumCompMomentum (d := d) i, constMomentum j⁆ +
    ⁅constMomentum i, positionDotMomentumCompMomentum j⁆ = 0 := by
  unfold positionDotMomentumCompMomentum constMomentum
  nth_rw 2 [← lie_skew]
  repeat rw [lie_smul, leibniz_lie, momentum_commutation_momentum, comp_zero, zero_add,
    positionDotMomentum_commutation_momentum, smul_comp]
  rw [momentum_comp_commute, add_neg_eq_zero]

private lemma constMomentum_comm_constMomentum {d} (i j : Fin d) :
    ⁅constMomentum i, constMomentum j⁆ = 0 := by
  unfold constMomentum
  simp [momentum_commutation_momentum]

private lemma positionCompMomentumSqr_comm_constRadiusRegInvCompPosition_add
    (ε : ℝˣ) (i j : Fin H.d) :
    ⁅positionCompMomentumSqr i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, positionCompMomentumSqr j⁆ =
    - (2 * H.m * H.k * Complex.I * ℏ) • 𝐫[ε,-1] ∘L 𝐋[i,j] := by
  unfold positionCompMomentumSqr constRadiusRegInvCompPosition
  nth_rw 2 [← lie_skew]
  repeat rw [lie_smul, leibniz_lie, lie_leibniz, lie_leibniz]
  repeat rw [position_commutation_position]
  repeat rw [position_commutation_radiusRegPow]
  repeat rw [← lie_skew 𝐩² _]
  repeat rw [position_commutation_momentumSqr]
  rw [radiusRegPow_commutation_momentumSqr]
  rw [← positionDotMomentum]

  simp only [zero_comp, comp_zero, add_zero, comp_smul, comp_add, comp_neg, smul_sub, smul_add,
    smul_neg, neg_comp, add_comp, smul_comp, comp_assoc, sub_comp, comp_sub]
  repeat rw [comp_eq_comp_add_commute positionDotMomentum 𝐱[_],
    positionDotMomentum_commutation_position]

  have hxr : ∀ i : Fin H.d, ∀ s, ∀ (A : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ)),
      𝐱[i] ∘L 𝐫[ε,s] ∘L A = 𝐫[ε,s] ∘L 𝐱[i] ∘L A := by
    intro i p A
    rw [← comp_assoc, position_comp_radiusRegPow_commute, comp_assoc]
  repeat rw [hxr]
  simp only [comp_add, comp_smul]
  rw [position_comp_commute j i]

  have hxx_xp : 𝐱[j] ∘L 𝐱[i] ∘L positionDotMomentum = 𝐱[i] ∘L 𝐱[j] ∘L positionDotMomentum := by
    rw [← comp_assoc, position_comp_commute, comp_assoc]
  rw [hxx_xp]

  unfold angularMomentumOperator
  ext ψ x
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, neg_mul, neg_smul, smul_add,
    smul_neg, neg_neg, one_mul, sub_neg_eq_add, neg_add_rev, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, coe_smul', coe_comp', Pi.smul_apply, Function.comp_apply,
    SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_natCast, comp_sub, coe_sub',
    Pi.sub_apply, SchwartzMap.sub_apply]
  ring

private lemma positionDotMomentumCompMomentum_comm_constRadiusRegInvCompPosition_add
    (ε : ℝˣ) (i j : Fin H.d) :
    ⁅positionDotMomentumCompMomentum i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, positionDotMomentumCompMomentum j⁆ =
    (H.m * H.k * Complex.I * ℏ * ε.1 ^ 2) • 𝐫[ε,-3] ∘L 𝐋[i,j] := by
  unfold positionDotMomentumCompMomentum constRadiusRegInvCompPosition
  nth_rw 2 [← lie_skew]
  repeat rw [lie_smul, leibniz_lie, lie_leibniz, lie_leibniz]
  repeat rw [← lie_skew 𝐩[_] 𝐱[_], position_commutation_momentum]
  repeat rw [positionDotMomentum_commutation_position]
  repeat rw [← lie_skew 𝐩[_] _, radiusRegPow_commutation_momentum]
  repeat rw [positionDotMomentum_commutation_radiusRegPow]
  simp only [smul_comp, neg_comp, comp_assoc]
  rw [position_comp_commute j i, symm j i]
  unfold angularMomentumOperator
  ext ψ x
  simp only [comp_neg, comp_smulₛₗ, RingHom.id_apply, comp_id, Complex.ofReal_neg,
    Complex.ofReal_one, neg_mul, one_mul, neg_smul, neg_neg, comp_add, sub_comp, smul_comp,
    add_comp, neg_comp, smul_add, smul_neg, neg_add_rev, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, coe_smul', coe_comp', Pi.smul_apply, Function.comp_apply,
    coe_sub', Pi.sub_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, SchwartzMap.sub_apply, Complex.ofReal_pow,
    comp_sub]
  ring_nf

private lemma constMomentum_comm_constRadiusRegInvCompPosition_add (ε : ℝˣ) (i j : Fin H.d) :
    ⁅constMomentum i, constRadiusRegInvCompPosition H ε j⁆ +
    ⁅constRadiusRegInvCompPosition H ε i, constMomentum j⁆ = 0 := by
  unfold constMomentum constRadiusRegInvCompPosition
  nth_rw 2 [← lie_skew]
  repeat rw [smul_lie, lie_smul, lie_leibniz]
  repeat rw [← lie_skew 𝐩[_] _]
  repeat rw [position_commutation_momentum, radiusRegPow_commutation_momentum]
  simp only [neg_comp, smul_comp, comp_assoc]
  rw [position_comp_commute j i, symm j i]
  ext ψ x
  simp only [comp_neg, comp_smulₛₗ, RingHom.id_apply, comp_id, Complex.ofReal_neg,
    Complex.ofReal_one, neg_mul, one_mul, neg_smul, neg_neg, smul_add, smul_neg, neg_add_rev,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul', Pi.smul_apply,
    coe_comp', Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    SchwartzMap.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring

private lemma constRadiusRegInvCompPosition_comm_constRadiusRegInvCompPosition
    (ε : ℝˣ) (i j : Fin H.d) :
    ⁅constRadiusRegInvCompPosition H ε i, constRadiusRegInvCompPosition H ε j⁆ = 0 := by
  unfold constRadiusRegInvCompPosition
  rw [lie_smul, smul_lie, leibniz_lie, lie_leibniz, lie_leibniz]
  rw [← lie_skew 𝐫[ε,-1] _]
  rw [position_commutation_position]
  rw [radiusRegPow_commutation_radiusRegPow]
  repeat rw [position_commutation_radiusRegPow]
  simp only [comp_zero, zero_comp, add_zero, neg_zero, smul_zero]

/-- `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = -iℏ 2m 𝐇(ε)𝐋ᵢⱼ` -/
lemma lrl_commutation_lrl (ε : ℝˣ) (i j : Fin H.d) : ⁅H.lrlOperator ε i, H.lrlOperator ε j⁆
    = (-2 * Complex.I * ℏ * H.m) • (H.hamiltonianReg ε) ∘L 𝐋[i,j] := by
  repeat rw [lrlOperator_eq]

  let f_x_p_sqr := positionCompMomentumSqr (d := H.d)
  let f_xdotp_p := positionDotMomentumCompMomentum (d := H.d)
  let f_const_p := constMomentum (d := H.d)
  let f_c_rinvx := constRadiusRegInvCompPosition H ε
  trans ⁅f_x_p_sqr i, f_x_p_sqr j⁆ + ⁅f_xdotp_p i, f_xdotp_p j⁆
      + ⁅f_const_p i, f_const_p j⁆ + ⁅f_c_rinvx i, f_c_rinvx j⁆
      - (⁅f_x_p_sqr i, f_xdotp_p j⁆ + ⁅f_xdotp_p i, f_x_p_sqr j⁆)
      + (⁅f_x_p_sqr i, f_const_p j⁆ + ⁅f_const_p i, f_x_p_sqr j⁆)
      - (⁅f_x_p_sqr i, f_c_rinvx j⁆ + ⁅f_c_rinvx i, f_x_p_sqr j⁆)
      - (⁅f_xdotp_p i, f_const_p j⁆ + ⁅f_const_p i, f_xdotp_p j⁆)
      + (⁅f_xdotp_p i, f_c_rinvx j⁆ + ⁅f_c_rinvx i, f_xdotp_p j⁆)
      - (⁅f_const_p i, f_c_rinvx j⁆ + ⁅f_c_rinvx i, f_const_p j⁆)
  · unfold f_x_p_sqr f_xdotp_p f_const_p f_c_rinvx
    unfold positionCompMomentumSqr positionDotMomentumCompMomentum constMomentum
      constRadiusRegInvCompPosition positionDotMomentum
    simp only [lie_add, lie_sub, add_lie, sub_lie]
    ext ψ x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, SchwartzMap.sub_apply,
      SchwartzMap.add_apply]
    ring

  rw [positionCompMomentumSqr_comm]
  rw [positionDotMomentumCompMomentum_comm]
  rw [positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add]
  rw [positionCompMomentumSqr_comm_constMomentum_add]
  rw [positionDotMomentumCompMomentum_comm_constMomentum_add]
  rw [constMomentum_comm_constMomentum]
  rw [positionCompMomentumSqr_comm_constRadiusRegInvCompPosition_add H]
  rw [positionDotMomentumCompMomentum_comm_constRadiusRegInvCompPosition_add H]
  rw [constMomentum_comm_constRadiusRegInvCompPosition_add H]
  rw [constRadiusRegInvCompPosition_comm_constRadiusRegInvCompPosition H]

  unfold hamiltonianReg
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', coe_comp', Pi.smul_apply,
    Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul,
    coe_sub', Pi.sub_apply, SchwartzMap.sub_apply, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_pow, ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring_nf
  simp

/-
## Hamiltonian / LRL vector commutators
-/

private lemma pSqr_comm_pL_Lp (i : Fin H.d) :
    ⁅momentumOperatorSqr (d := H.d), ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j])⁆ = 0 := by
  rw [lie_sum]
  conv_lhs =>
    enter [2, j]
    rw [lie_add, lie_leibniz, lie_leibniz]
    rw [momentumSqr_commutation_momentum]
    rw [← lie_skew, angularMomentum_commutation_momentumSqr]
  simp only [neg_zero, comp_zero, zero_comp, add_zero, Finset.sum_const_zero]

private lemma rr_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐫[d,ε,-1] + (2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-3], 𝐫[ε,-1] ∘L 𝐱[i]⁆ = 0 := by
  rw [add_lie, smul_lie, lie_leibniz, lie_leibniz]
  repeat rw [radiusRegPow_commutation_radiusRegPow]
  repeat rw [← lie_skew, position_commutation_radiusRegPow]
  simp only [neg_zero, comp_zero, zero_comp, add_zero, smul_zero]

private lemma pSqr_comm_rx (ε : ℝˣ) (i : Fin H.d) :
    ⁅momentumOperatorSqr (d := H.d), 𝐫[ε,-1] ∘L 𝐱[i]⁆ =
    (-2 * Complex.I * ℏ) • 𝐫[ε,-1] ∘L 𝐩[i]
    + (ℏ ^ 2 * (H.d - 3) : ℝ) • 𝐫[ε,-3] ∘L 𝐱[i]
    + (3 * ℏ ^ 2 * ε.1 ^ 2) • 𝐫[ε,-5] ∘L 𝐱[i]
    + (2 * Complex.I * ℏ) • 𝐫[ε,-3] ∘L (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐱[i] := by
  rw [lie_leibniz]
  rw [← lie_skew, position_commutation_momentumSqr]
  rw [← lie_skew, radiusRegPow_commutation_momentumSqr]
  ext ψ x
  simp only [comp_neg, comp_smulₛₗ, RingHom.id_apply, Complex.ofReal_neg, Complex.ofReal_one,
    mul_neg, mul_one, neg_mul, neg_smul, one_mul, neg_add_rev, neg_neg, add_comp, smul_comp,
    sub_comp, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul', coe_comp',
    Pi.smul_apply, Function.comp_apply, coe_sub', Pi.sub_apply, coe_sum', Finset.sum_apply, map_sum,
    SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply, smul_eq_mul,
    SchwartzMap.sub_apply, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_pow,
    SchwartzMap.sum_apply]
  ring_nf

private lemma rr_comm_pL_Lp {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅𝐫[d,ε,-1] + (2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-3], ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j])⁆ =
    (- Complex.I * ℏ) • (𝐫[ε,-3] +
      (3 * 2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-5]) ∘L ∑ j, (𝐱[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱[j]) := by
  rw [lie_sum]
  conv_lhs =>
    enter [2, j]
    simp only [add_lie, lie_add, smul_lie, lie_leibniz]
    repeat rw [← lie_skew _ 𝐋[_,_], angularMomentum_commutation_radiusRegPow]
    repeat rw [radiusRegPow_commutation_momentum]
    simp only [neg_zero, comp_zero, zero_comp, zero_add, add_zero]
    simp only [smul_comp, comp_smul, smul_add, ← comp_assoc]
    repeat rw [comp_eq_comp_add_commute 𝐋[_,_] 𝐫[ε,_],
      angularMomentum_commutation_radiusRegPow]
    simp only [comp_assoc]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← comp_finset_sum]
  ext ψ x
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, neg_smul,
    Complex.ofReal_ofNat, smul_neg, add_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, coe_smul', coe_comp', coe_sum', Pi.smul_apply,
    Function.comp_apply, Finset.sum_apply, map_sum, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, comp_add, add_comp, smul_comp,
    smul_add]
  ring_nf

private lemma xL_Lx_eq {d : ℕ} (ε : ℝˣ) (i : Fin d) : ∑ j, (𝐱[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱[j]) =
    (2 : ℝ) • (∑ j, 𝐱[j] ∘L 𝐩[j]) ∘L 𝐱[i]
    - (2 : ℝ) • 𝐫[ε,2] ∘L 𝐩[i] + (2 * ε.1 ^ 2) • 𝐩[i] - (Complex.I * ℏ * (d - 3)) • 𝐱[i] := by
  conv_lhs =>
    enter [2, j]
    calc
      _ = 𝐱[j] ∘L (𝐱[i] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[i])
          + (𝐱[i] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[i]) ∘L 𝐱[j] := rfl
      _ = 𝐱[j] ∘L 𝐱[i] ∘L 𝐩[j] + 𝐱[i] ∘L 𝐩[j] ∘L 𝐱[j]
          - 𝐱[j] ∘L 𝐱[j] ∘L 𝐩[i] - 𝐱[j] ∘L 𝐩[i] ∘L 𝐱[j] := by
        rw [comp_sub, sub_comp]
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_sub', coe_comp', Pi.sub_apply,
          Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.sub_apply]
        ring
      _ = 𝐱[j] ∘L 𝐩[j] ∘L 𝐱[i] + 𝐱[i] ∘L 𝐱[j] ∘L 𝐩[j] - (2 : ℝ) • 𝐱[j] ∘L 𝐱[j] ∘L 𝐩[i]
          + (2 * Complex.I * ℏ * δ[i,j]) • 𝐱[j] - (Complex.I * ℏ) • 𝐱[i] := by
        rw [comp_eq_comp_add_commute 𝐱[i] 𝐩[j], position_commutation_momentum]
        rw [comp_eq_comp_sub_commute 𝐩[i] 𝐱[j], position_commutation_momentum]
        rw [comp_eq_comp_add_commute 𝐱[j] 𝐩[j], position_commutation_momentum]
        rw [symm j i, eq_one_of_same]
        ext ψ x
        simp only [comp_add, comp_smulₛₗ, RingHom.id_apply, comp_id, comp_sub, coe_sub', coe_comp',
          coe_smul', Pi.sub_apply, ContinuousLinearMap.add_apply, Function.comp_apply,
          Pi.smul_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_ofNat]
        ring
      _ = 𝐱[j] ∘L 𝐩[j] ∘L 𝐱[i] + 𝐱[j] ∘L 𝐱[i] ∘L 𝐩[j] - (2 : ℝ) • 𝐱[j] ∘L 𝐱[j] ∘L 𝐩[i]
          + (2 * Complex.I * ℏ * δ[i,j]) • 𝐱[j] - (Complex.I * ℏ) • 𝐱[i] := by
        nth_rw 2 [← comp_assoc]
        rw [position_comp_commute i j, comp_assoc]
      _ = (2 : ℝ) • (𝐱[j] ∘L 𝐩[j]) ∘L 𝐱[i] - (2 : ℝ) • (𝐱[j] ∘L 𝐱[j]) ∘L 𝐩[i]
          + (3 * Complex.I * ℏ * δ[i,j]) • 𝐱[j] - (Complex.I * ℏ) • 𝐱[i] := by
        rw [comp_eq_comp_add_commute 𝐱[i] 𝐩[j], position_commutation_momentum]
        ext ψ x
        simp only [comp_add, comp_smulₛₗ, RingHom.id_apply, comp_id, coe_sub', coe_smul',
          Pi.sub_apply, ContinuousLinearMap.add_apply, coe_comp', Function.comp_apply,
          Pi.smul_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_ofNat, sub_left_inj]
        ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← finset_sum_comp]
  rw [positionOperatorSqr_eq d ε, sub_comp, smul_comp]

  unfold kroneckerDelta
  ext ψ x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, SchwartzMap.sub_apply,
    SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply]
  simp only [coe_comp', coe_sum', Function.comp_apply, Finset.sum_apply, SchwartzMap.sum_apply,
    positionOperator_apply, momentumOperator_apply, neg_mul, mul_neg, Finset.sum_neg_distrib,
    smul_neg, Complex.real_smul, Complex.ofReal_ofNat, radiusRegPowOperator_apply, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_self, Real.rpow_one, Complex.ofReal_add,
    Complex.ofReal_pow, one_apply, sub_neg_eq_add, smul_add, Nat.cast_ite, Nat.cast_one,
    CharP.cast_eq_zero, mul_ite, mul_one, mul_zero, smul_eq_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Complex.ofReal_mul]
  ring

/-- `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏkε²(¾𝐫(ε)⁻⁵(𝐱ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐱ⱼ) + 3iℏ/2 𝐫(ε)⁻⁵𝐱ᵢ + 𝐫(ε)⁻³𝐩ᵢ)` -/
lemma hamiltonianReg_commutation_lrl (ε : ℝˣ) (i : Fin H.d) :
    ⁅H.hamiltonianReg ε, H.lrlOperator ε i⁆ = (Complex.I * ℏ * H.k * ε.1 ^ 2) •
    ((3 * 4⁻¹ : ℝ) • 𝐫[ε,-5] ∘L ∑ j, (𝐱[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐱[j])
      + (3 * 2⁻¹ * Complex.I * ℏ) • 𝐫[ε,-5] ∘L 𝐱[i] + 𝐫[ε,-3] ∘L 𝐩[i]) := by
  unfold hamiltonianReg lrlOperator
  rw [sub_lie, lie_sub, lie_sub]
  simp only [lie_smul, smul_lie]

  rw [pSqr_comm_pL_Lp]
  rw [rr_comm_rx]
  rw [pSqr_comm_rx]
  rw [rr_comm_pL_Lp]
  rw [xL_Lx_eq ε]

  simp only [smul_zero, sub_zero, zero_sub, smul_smul, smul_add, smul_sub, comp_smul, smul_comp,
    add_comp, comp_sub, comp_add]
  simp only [← comp_assoc, radiusRegPowOperator_comp_eq]
  rw [comp_assoc]
  field_simp
  rw [← sub_eq_zero]

  ext ψ x
  simp only [neg_smul, smul_neg, neg_add_rev, neg_neg, Complex.I_sq, neg_mul, one_mul, coe_sub',
    Pi.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, coe_smul',
    coe_comp', coe_sum', Pi.smul_apply, Function.comp_apply, Finset.sum_apply, map_sum,
    SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    SchwartzMap.sum_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring_nf
  rw [Complex.I_sq]
  simp

/-

## LRL vector squared

To compute `𝐀(ε)²` we take the following approach:
- Write `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the first term and
  `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the second.
- Expand out to nine terms: one is a triple sum, two are double sums and the rest are single sums.
- Compute each term, symmetrizing the sums (see `sum_symmetrize` and `sum_symmetrize'`).
- Collect terms.

-/

private lemma sum_symmetrize (f : Fin H.d → Fin H.d → 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ)) :
    ∑ i, ∑ j, f i j = (2 : ℂ)⁻¹ • ∑ i, ∑ j, (f i j + f j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  ext ψ x
  rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.add_apply,
    SchwartzMap.add_apply, smul_eq_mul]
  ring

private lemma sum_symmetrize'
    (f : Fin H.d → Fin H.d → Fin H.d → 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ)) :
    ∑ i, ∑ j, ∑ k, f i j k = (2 : ℂ)⁻¹ • ∑ i, ∑ k, ∑ j, (f i j k + f k j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  conv_rhs =>
    enter [2, 1, 2, i]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, 2, 2, i]
    rw [Finset.sum_comm]
  ext ψ x
  rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.add_apply,
    SchwartzMap.add_apply, smul_eq_mul]
  ring

private lemma sum_Lpp_zero : ∑ i : Fin H.d, ∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[i] = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, momentum_comp_commute j i, neg_comp, add_neg_cancel]
  simp

private lemma sum_ppL_zero : ∑ i : Fin H.d, ∑ j, 𝐩[i] ∘L 𝐩[j] ∘L 𝐋[i,j] = 0 := by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← comp_assoc, ← comp_assoc]
    rw [angularMomentumOperator_antisymm j i, momentum_comp_commute j i, comp_neg, add_neg_cancel]
  simp

private lemma sum_LppL : ∑ i : Fin H.d, ∑ j, ∑ k, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[k] ∘L 𝐋[i,k]
    = 𝐩² ∘L 𝐋² := by
  -- Apply a particular symmetrization to the triple sum
  rw [sum_symmetrize']
  conv_lhs =>
    enter [2, 2, i, 2, j, 2, k]
    rw [angularMomentumOperator_antisymm j i]
    repeat rw [comp_neg]
    repeat rw [← comp_assoc]
    rw [← sub_eq_add_neg, ← sub_comp]
    enter [1]
    unfold angularMomentumOperator
    calc
      _ = 𝐱[i] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[j] - 𝐱[k] ∘L 𝐩[i] ∘L 𝐩[k] ∘L 𝐩[j]
          - 𝐱[j] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[i] + 𝐱[k] ∘L 𝐩[j] ∘L 𝐩[k] ∘L 𝐩[i] := by
        simp only [sub_comp, comp_assoc, sub_add]

      _ = 𝐱[i] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[k] ∘L 𝐩[k] ∘L 𝐩[i] := by
        nth_rw 2 [momentum_comp_commute k j]
        nth_rw 2 [momentum_comp_commute k i]
        nth_rw 4 [← comp_assoc]
        rw [momentum_comp_commute i j, comp_assoc]
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_sub', coe_comp', Pi.sub_apply,
          Function.comp_apply, SchwartzMap.add_apply, SchwartzMap.sub_apply]
        ring

  -- Back out of inner sum
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← finset_sum_comp, Finset.sum_sub_distrib, ← comp_finset_sum, ← comp_finset_sum]
    simp only [← comp_assoc, ← finset_sum_comp]
    rw [← momentumOperatorSqr]
    repeat rw [comp_eq_comp_add_commute 𝐱[_] 𝐩², position_commutation_momentumSqr, add_comp,
      smul_comp, comp_assoc]
    rw [momentum_comp_commute j i]
    rw [add_sub_add_right_eq_sub]
    rw [← comp_sub, ← angularMomentumOperator, comp_assoc]

  simp only [← comp_finset_sum]
  rw [← comp_smul, ← angularMomentumOperatorSqr]

private lemma sum_Lprx (ε : ℝˣ) :
    ∑ i : Fin H.d, ∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐫[ε,-1] ∘L 𝐱[i] = 𝐫[ε,-1] ∘L 𝐋² := by
  simp only [comp_eq_comp_sub_commute 𝐫[ε,-1] 𝐱[_], position_commutation_radiusRegPow,
    sub_zero]
  simp only [← comp_assoc, ← finset_sum_comp _ 𝐫[ε,-1]]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [1, 2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, neg_comp, neg_comp, ← sub_eq_add_neg]
    rw [comp_assoc, comp_assoc, ← comp_sub]
    repeat rw [comp_eq_comp_sub_commute 𝐩[_] 𝐱[_], position_commutation_momentum]
    rw [symm j i, sub_sub_sub_cancel_right]
    rw [← angularMomentumOperator]
  rw [← angularMomentumOperatorSqr, ← sub_eq_zero]
  exact angularMomentumSqr_commutation_radiusRegPow ε

private lemma sum_rxpL (ε : ℝˣ) :
    ∑ i : Fin H.d, ∑ j, 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[j] ∘L 𝐋[i,j] = 𝐫[ε,-1] ∘L 𝐋² := by
  simp only [← comp_finset_sum 𝐫[ε,-1]]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, comp_neg, comp_neg, ← sub_eq_add_neg]
    rw [← comp_assoc, ← comp_assoc, ← sub_comp, ← angularMomentumOperator]
  rw [← angularMomentumOperatorSqr]

private lemma sum_prx (d : ℕ) (ε : ℝˣ) : ∑ i : Fin d, 𝐩[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] =
    𝐫[ε,-1] ∘L ∑ i : Fin d, 𝐱[i] ∘L 𝐩[i] - (Complex.I * ℏ * (d - 1)) • 𝐫[ε,-1]
    - (Complex.I * ℏ * ε.1 ^ 2) • 𝐫[ε,-3] := by
  conv_lhs =>
    enter [2, i]
    rw [← comp_assoc, comp_eq_comp_sub_commute 𝐩[_] 𝐫[ε,-1], radiusRegPow_commutation_momentum]
    rw [sub_comp, smul_comp, comp_assoc, comp_assoc]
    rw [comp_eq_comp_sub_commute 𝐩[_] 𝐱[_], position_commutation_momentum]
    rw [eq_one_of_same]
    rw [comp_sub, comp_smul, comp_id]
  repeat rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← comp_finset_sum]
  rw [positionOperatorSqr_eq, comp_sub, radiusRegPowOperator_comp_eq, comp_smul]

  ext ψ x
  simp only [ContinuousLinearMap.sub_apply, SchwartzMap.sub_apply, ContinuousLinearMap.smul_apply,
    SchwartzMap.smul_apply, ContinuousLinearMap.sum_apply, SchwartzMap.sum_apply]
  simp only [coe_comp', coe_sum', Function.comp_apply, Finset.sum_apply, map_sum,
    SchwartzMap.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
    sub_add_cancel, Complex.real_smul, Complex.ofReal_pow, sub_neg_eq_add]
  ring_nf
  congr

private lemma sum_rxp (d : ℕ) (ε : ℝˣ) : ∑ i : Fin d, 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[i] =
    𝐫[ε,-1] ∘L ∑ i : Fin d, 𝐱[i] ∘L 𝐩[i] := by rw [comp_finset_sum]

private lemma sum_rxrx (d : ℕ) (ε : ℝˣ) : ∑ i, 𝐫[d,ε,-1] ∘L 𝐱[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] =
    1 - (ε.1 ^ 2) • 𝐫[ε,-2] := by
  conv_lhs =>
    enter [2, i]
    calc
      _ = 𝐫[d,ε,-1] ∘L 𝐫[d,ε,-1] ∘L 𝐱[i] ∘L 𝐱[i] := by
        nth_rw 2 [← comp_assoc]
        rw [comp_eq_comp_add_commute 𝐱[i] 𝐫[d,ε,-1], position_commutation_radiusRegPow,
          add_zero, comp_assoc]
      _ = 𝐫[d,ε,-2] ∘L 𝐱[i] ∘L 𝐱[i] := by
        rw [← comp_assoc, radiusRegPowOperator_comp_eq]
        congr
        ring
  rw [← comp_finset_sum, positionOperatorSqr_eq, comp_sub, comp_smul,
    radiusRegPowOperator_comp_eq, neg_add_cancel, radiusRegPowOperator_zero]
  congr

/-- The square of the (regularized) LRL vector operator is related to the (regularized) Hamiltonian
  `𝐇(ε)` of the hydrogen atom, square of the angular momentum `𝐋²` and powers of `𝐫(ε)` as
  `𝐀(ε)² = 2m 𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k² - m²k²ε²𝐫(ε)⁻² + mkε²𝐫(ε)⁻³(𝐋² + ¼ℏ²(d-1)(d-3))`. -/
lemma lrlOperatorSqr_eq (ε : ℝˣ) : H.lrlOperatorSqr ε =
    (2 * H.m) • (H.hamiltonianReg ε) ∘L
      (𝐋² + (4⁻¹ * ℏ ^ 2 * (H.d - 1) ^ 2 : ℝ) • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ))
    + (H.m * H.k) ^ 2 • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ)
    - ((H.m * H.k) ^ 2 * ε ^ 2) • 𝐫[ε,-2]
    + (H.m * H.k * ε ^ 2) • 𝐫[ε,-3] ∘L
      (𝐋² + (4⁻¹ * ℏ^2 * (H.d - 1) * (H.d - 3) : ℝ) •
      ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ)) := by
  unfold lrlOperatorSqr

  let a := (2⁻¹ * Complex.I * ℏ * (H.d - 1))

  -- Replace the two copies of `𝐀(ε)` in different ways and expand to nine terms
  conv_lhs =>
    enter [2, i, 1]
    rw [lrlOperator_eq']
  conv_lhs =>
    enter [2, i]
    rw [lrlOperator_eq'']
    calc
      _ = (∑ j, 𝐋[i,j] ∘L 𝐩[j]) ∘L (∑ k, 𝐩[k] ∘L 𝐋[i,k])
          - a • (∑ j, 𝐋[i,j] ∘L 𝐩[j]) ∘L 𝐩[i]
          + a • 𝐩[i] ∘L (∑ k, 𝐩[k] ∘L 𝐋[i,k])
          - (a * a) • 𝐩[i] ∘L 𝐩[i]
          - (H.m * H.k) • (∑ j, 𝐋[i,j] ∘L 𝐩[j]) ∘L 𝐫[ε,-1] ∘L 𝐱[i]
          - (H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] ∘L (∑ k, 𝐩[k] ∘L 𝐋[i,k])
          - (a * H.m * H.k) • 𝐩[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i]
          + (a * H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[i]
          + (H.m * H.k) ^ 2 • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] := by
        simp only [comp_sub, add_comp, sub_comp, comp_smul, smul_comp]
        ext ψ x
        simp only [coe_sub', coe_smul', coe_comp', coe_sum', Pi.sub_apply, Function.comp_apply,
          ContinuousLinearMap.add_apply, Finset.sum_apply, Pi.smul_apply, SchwartzMap.sub_apply,
          SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
        ring
      _ = ∑ j, ∑ k, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[k] ∘L 𝐋[i,k]
          - a • (∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐩[i])
          + a • (∑ k, 𝐩[i] ∘L 𝐩[k] ∘L 𝐋[i,k])
          - (a * a) • 𝐩[i] ∘L 𝐩[i]
          - (H.m * H.k) • (∑ j, 𝐋[i,j] ∘L 𝐩[j] ∘L 𝐫[ε,-1] ∘L 𝐱[i])
          - (H.m * H.k) • (∑ k, 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[k] ∘L 𝐋[i,k])
          - (a * H.m * H.k) • 𝐩[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i]
          + (a * H.m * H.k) • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐩[i]
          + (H.m * H.k) ^ 2 • 𝐫[ε,-1] ∘L 𝐱[i] ∘L 𝐫[ε,-1] ∘L 𝐱[i] := by
        repeat rw [finset_sum_comp, comp_finset_sum]
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_sub', coe_smul', coe_comp', coe_sum',
          Pi.sub_apply, Finset.sum_apply, Function.comp_apply, map_sum, Pi.smul_apply,
          SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.sum_apply, smul_eq_mul,
          SchwartzMap.smul_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]

  -- Split the outer sum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]

  rw [sum_LppL] -- ∑∑∑ LppL = p²L²
  rw [sum_Lpp_zero, smul_zero] -- ∑∑ Lpp = 0
  rw [sum_ppL_zero, smul_zero] -- ∑∑ ppL = 0
  rw [← momentumOperatorSqr] -- ∑ pp = p²
  rw [sum_Lprx] -- ∑∑ Lpr⁻¹x = r⁻¹L²
  rw [sum_rxpL] -- ∑∑ r⁻¹xpL = r⁻¹L²
  rw [sum_prx] -- ∑ pr⁻¹x = r⁻¹ ∑ xp - iℏ(d-1)r⁻¹ - iℏε²r⁻³
  rw [sum_rxp] -- ∑ r⁻¹xp = r⁻¹ ∑ xp
  rw [sum_rxrx] -- ∑ r⁻¹xr⁻¹x = 1 - ε²r⁻²

  unfold a hamiltonianReg
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_sub', coe_comp', coe_smul', SchwartzMap.add_apply,
    Pi.sub_apply, Function.comp_apply, Pi.smul_apply, SchwartzMap.sub_apply, smul_eq_mul,
    SchwartzMap.smul_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring_nf
  rw [Complex.I_sq]
  simp only [neg_mul, one_mul, one_div, sub_neg_eq_add, Complex.ofReal_mul, Complex.ofReal_pow,
    coe_id', id_eq, Complex.ofReal_inv, Complex.ofReal_ofNat, map_add, map_smul_of_tower,
    SchwartzMap.add_apply, SchwartzMap.smul_apply, Complex.real_smul, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_sub, radiusRegPowOperator_apply, one_apply, ne_eq,
    not_false_eq_true, Complex.ofReal_eq_zero, m_ne_zero, mul_inv_cancel_left₀]
  ring

end
end HydrogenAtom
end QuantumMechanics
