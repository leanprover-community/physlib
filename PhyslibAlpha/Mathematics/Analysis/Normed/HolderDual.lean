/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic.Positivity.Finset

/-!
# Hölder duality in finite dimensions

The dual norm of an `ℓp` coordinate norm is the `ℓq` norm of the values on the basis.

## i. Overview

A continuous linear functional on a finite-dimensional normed space is determined by its values on
a basis. When the norm is the `ℓp` norm of the coordinates in that basis, the norm of a functional
is the `ℓq` norm of its values, `q` the Hölder conjugate of `p`; for the sup norm it is the `ℓ1`
norm. So the unit ball of the dual is the closed `ℓq` ball, resp. the `ℓ1` ball, of value vectors.

## ii. Key results

- `HolderDual.coeffEquiv` : a functional is its vector of values on a basis.
- `HolderDual.dualLp_norm_eq` : Hölder duality for `1 < p < ∞`.
- `HolderDual.dualSup_norm_eq` : Hölder duality for `p = ∞`.
- `HolderDual.dualLpEquiv`, `HolderDual.dualSupEquiv` : the unit ball of the dual in coordinates.

## iii. Table of contents

- A. Functionals from their values on a basis
- B. Hölder duality, `1 < p < ∞`
- C. Hölder duality, `p = ∞`

## iv. References

- W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill, 1991.

-/

@[expose] public section

open scoped NNReal

namespace HolderDual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma abs_sign_mul_le (a g : ℝ) (hg : 0 ≤ g) : |(SignType.sign a : ℝ) * g| ≤ g := by
  rw [abs_mul, abs_of_nonneg hg]
  refine mul_le_of_le_one_left hg ?_
  rcases lt_trichotomy a 0 with h | h | h <;> simp [sign_neg, sign_pos, h]

/-- Hölder's inequality for the absolute value of a finite sum. -/
lemma abs_sum_mul_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q) (c v : Fin n → ℝ) :
    |∑ i, c i * v i| ≤ (∑ i, |c i| ^ q) ^ (1 / q) * (∑ i, |v i| ^ p) ^ (1 / p) :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| by
    simpa [abs_mul] using
      Real.inner_le_Lp_mul_Lq Finset.univ (fun i => |c i|) (fun i => |v i|) hpq.symm

lemma rpow_one_div_le_one_iff {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    x ^ (1 / q) ≤ 1 ↔ x ≤ 1 := by
  have := Real.rpow_le_rpow_iff hx zero_le_one (one_div_pos.2 hq)
  rwa [Real.one_rpow] at this

/-! ## A. Functionals from their values on a basis -/

variable {n : ℕ} (b : Module.Basis (Fin n) ℝ V)

lemma repr_sum_smul_self (v : Fin n → ℝ) (i : Fin n) : b.repr (∑ j, v j • b j) i = v i := by
  simp [map_sum, map_smul, b.repr_self, Finsupp.single_apply, Finset.sum_ite_eq']

lemma apply_eq_sum_repr (f : V →L[ℝ] ℝ) (v : V) : f v = ∑ i, f (b i) * b.repr v i := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

/-- The continuous functional with values `a` on the basis. -/
noncomputable def ofCoeffs (a : Fin n → ℝ) : V →L[ℝ] ℝ :=
  have := Module.Finite.of_basis b
  LinearMap.toContinuousLinearMap (b.constr ℝ a)

@[simp] lemma ofCoeffs_apply_basis (a : Fin n → ℝ) (i : Fin n) : ofCoeffs b a (b i) = a i := by
  simp [ofCoeffs]

/-- A functional is its vector of values on the basis. -/
noncomputable def coeffEquiv : (V →L[ℝ] ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun f i := f (b i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := ofCoeffs b
  left_inv f := ContinuousLinearMap.coe_injective <| b.ext fun i => by simp
  right_inv a := funext fun i => by simp

@[simp] lemma coeffEquiv_apply (f : V →L[ℝ] ℝ) (i : Fin n) : coeffEquiv b f i = f (b i) := rfl

@[simp] lemma coeffEquiv_symm_apply_basis (a : Fin n → ℝ) (i : Fin n) :
    (coeffEquiv b).symm a (b i) = a i :=
  ofCoeffs_apply_basis b a i

/-- If the norm of a functional is a function `N` of its values on the basis, the unit ball of
the dual is `{a | N a ≤ 1}` in coordinates. -/
lemma image_coeffEquiv_ball {N : (Fin n → ℝ) → ℝ}
    (hN : ∀ f : V →L[ℝ] ℝ, ‖f‖ = N fun i => f (b i)) :
    coeffEquiv b '' {f | ‖f‖ ≤ 1} = {a | N a ≤ 1} := by
  ext a
  refine ⟨?_, fun ha => ⟨(coeffEquiv b).symm a, ?_, (coeffEquiv b).apply_symm_apply a⟩⟩
  · rintro ⟨f, hf, rfl⟩
    exact (hN f).symm.trans_le hf
  · simpa [Set.mem_ofPred_eq, hN] using ha

/-- If the norm of a functional is a function `N` of its values on the basis, the functionals
of norm at most `1` are the value vectors `a` with `N a ≤ 1`. -/
noncomputable def dualEquivOfNormEq {N : (Fin n → ℝ) → ℝ}
    (hN : ∀ f : V →L[ℝ] ℝ, ‖f‖ = N fun i => f (b i)) :
    {f : V →L[ℝ] ℝ // ‖f‖ ≤ 1} ≃ {a : Fin n → ℝ // N a ≤ 1} where
  toFun f := ⟨fun i => f.1 (b i), by rw [← hN]; exact f.2⟩
  invFun a := ⟨ofCoeffs b a, by simpa [hN] using a.2⟩
  left_inv f := Subtype.ext <| ContinuousLinearMap.coe_injective <| b.ext fun i => by simp
  right_inv a := Subtype.ext <| funext fun i => by simp

/-! ## B. Hölder duality, `1 < p < ∞` -/

variable {p q : ℝ}

include b in
lemma norm_sum_smul_self (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p))
    (v : Fin n → ℝ) : ‖∑ j, v j • b j‖ = (∑ i, |v i| ^ p) ^ (1 / p) := by
  rw [hnorm, Finset.sum_congr rfl fun i _ => by rw [repr_sum_smul_self b v i]]

include b in
lemma norm_sum_sign_smul_le_one (hpq : p.HolderConjugate q)
    (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p)) (s : Fin n → ℝ) {g : Fin n → ℝ≥0}
    (hg : ∑ i, g i ^ p ≤ 1) : ‖∑ i, ((SignType.sign (s i) : ℝ) * g i) • b i‖ ≤ 1 := by
  rw [norm_sum_smul_self b hnorm]
  refine Real.rpow_le_one (by positivity) ((Finset.sum_le_sum fun i _ => Real.rpow_le_rpow
    (abs_nonneg _) (abs_sign_mul_le _ _ (g i).2) hpq.nonneg).trans ?_)
    (one_div_nonneg.2 hpq.nonneg)
  simpa using NNReal.coe_le_coe.mpr hg

include b in
/-- The unit vector on which a functional attains the `ℓq` norm of its values on the basis. -/
lemma exists_norm_le_one_apply_eq (hpq : p.HolderConjugate q)
    (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p)) (f : V →L[ℝ] ℝ) :
    ∃ w : V, ‖w‖ ≤ 1 ∧ f w = (∑ i, |f (b i)| ^ q) ^ (1 / q) := by
  obtain ⟨⟨g, hg_mem, hg_eq⟩, -⟩ :=
    NNReal.isGreatest_Lp Finset.univ (fun i => ⟨|f (b i)|, abs_nonneg _⟩) hpq.symm
  have hg : ∑ i, |f (b i)| * (g i : ℝ) = (∑ i, |f (b i)| ^ q) ^ (1 / q) := by
    have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) hg_eq
    push_cast at h
    exact h
  refine ⟨_, norm_sum_sign_smul_le_one b hpq hnorm (fun i => f (b i)) hg_mem, ?_⟩
  · rw [← hg, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, smul_eq_mul, mul_right_comm, sign_mul_self]

include b in
/-- **Hölder duality**: the norm of a functional is the `ℓq` norm of its values on the basis. -/
lemma dualLp_norm_eq (hpq : p.HolderConjugate q)
    (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p)) (f : V →L[ℝ] ℝ) :
    ‖f‖ = (∑ i, |f (b i)| ^ q) ^ (1 / q) := by
  refine le_antisymm (f.opNorm_le_bound (by positivity) fun v => ?_) ?_
  · rw [Real.norm_eq_abs, apply_eq_sum_repr b f v, hnorm]
    exact abs_sum_mul_le hpq _ _
  · obtain ⟨w, hw, hfw⟩ := exists_norm_le_one_apply_eq b hpq hnorm f
    exact hfw ▸ (Real.le_norm_self _).trans
      ((f.le_opNorm w).trans (mul_le_of_le_one_right (norm_nonneg f) hw))

include b in
/-- The functionals of norm at most `1` are the closed `ℓq` ball of value vectors. -/
noncomputable def dualLpEquiv (hpq : p.HolderConjugate q)
    (hnorm : ∀ v : V, ‖v‖ = (∑ i, |b.repr v i| ^ p) ^ (1 / p)) :
    {f : V →L[ℝ] ℝ // ‖f‖ ≤ 1} ≃ {a : Fin n → ℝ // ∑ i, |a i| ^ q ≤ 1} :=
  (dualEquivOfNormEq b (dualLp_norm_eq b hpq hnorm)).trans <|
    Equiv.subtypeEquivRight fun _ => rpow_one_div_le_one_iff (by positivity) hpq.symm.pos

/-! ## C. Hölder duality, `p = ∞` -/

variable {m : ℕ}

lemma apply_eq_sum_single (f : (Fin m → ℝ) →L[ℝ] ℝ) (v : Fin m → ℝ) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  simpa using apply_eq_sum_repr (Pi.basisFun ℝ (Fin m)) f v

/-- **Hölder duality** for the sup norm: the norm of a functional is the `ℓ1` norm of its values
on the standard basis. -/
lemma dualSup_norm_eq (f : (Fin m → ℝ) →L[ℝ] ℝ) : ‖f‖ = ∑ i, |f (Pi.single i 1)| := by
  refine le_antisymm (f.opNorm_le_bound (by positivity) fun v => ?_) ?_
  · rw [Real.norm_eq_abs, apply_eq_sum_single f v, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)
  · set s : Fin m → ℝ := fun i => SignType.sign (f (Pi.single i 1))
    have hs : ‖s‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      simpa using abs_sign_mul_le (f (Pi.single i 1)) 1 zero_le_one
    have hfs : f s = ∑ i, |f (Pi.single i 1)| := by
      rw [apply_eq_sum_single f s]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm, sign_mul_self]
    exact hfs ▸ (Real.le_norm_self _).trans
      ((f.le_opNorm s).trans (mul_le_of_le_one_right (norm_nonneg f) hs))

lemma norm_eq_sum_abs_basisFun (f : (Fin m → ℝ) →L[ℝ] ℝ) :
    ‖f‖ = ∑ i, |f (Pi.basisFun ℝ (Fin m) i)| := by
  simpa using dualSup_norm_eq f

/-- The functionals of norm at most `1` on the sup-normed space are the closed `ℓ1` ball. -/
noncomputable def dualSupEquiv :
    {f : (Fin m → ℝ) →L[ℝ] ℝ // ‖f‖ ≤ 1} ≃ {a : Fin m → ℝ // ∑ i, |a i| ≤ 1} :=
  dualEquivOfNormEq (Pi.basisFun ℝ (Fin m)) norm_eq_sum_abs_basisFun

end HolderDual
