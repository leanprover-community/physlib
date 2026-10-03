/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Lorentz invariants among two four-vector indices

## i. Overview

A rank-two tensor `T^{μν}` has a single Lorentz invariant up to scale, its contraction with the
metric: nothing else ties two indices, the Levi-Civita symbol needing four. For an equivariant
map `f : ℂT(fun _ : Fin 2 => .up) →ₗ[ℂ] B`, `IsLorentzCovariant 2`, every Lorentz invariant in the
range of `f` is a multiple of `f metric`, the image of the metric `η` (A), and modulo a
Lorentz-stable submodule `S` the invariants of `LinearMap.range f ⊔ S` reduce to the line through
it (C). For a given `f` the image may be zero.

The invariants of the range of `f` are the images of invariant tensors, so it is enough that an
invariant coefficient tensor `c` (`Invariants.Basic`) is a multiple of the Minkowski metric, and
three kinds of transformation pin `c` down (B). The half turn about each axis has a diagonal
Lorentz matrix with entries `±1`, and for `μ ≠ ν` one of the three negates `c_{μν}`, so the
off-diagonal coefficients vanish. The cyclic rotation `x → y → z → x` permutes the spatial
directions, so `c_xx = c_yy = c_zz`. The boost along `z` scales the light-cone component of `c`
along `D₀ - D_z` in both slots by `t⁴`, so that component vanishes, and with the off-diagonal
coefficients gone it is `c_tt + c_zz`. So `c` is `c_tt` times the Minkowski metric.

## ii. Key results

- `Lorentz.RankTwo.metric` : the metric `η` with the colours of `IsLorentzCovariant 2`.
- `Lorentz.RankTwo.exists_smul_map_metric_of_invariant` : an invariant in the range of `f` is a
  multiple of `f metric`.
- `Lorentz.RankTwo.reducesInvariantsTo_span_metric` : the same modulo a stable submodule.

## iii. Table of contents

- A. The metric
- B. The classification of the invariant coefficient tensors
- C. The invariants of an equivariant map

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

namespace RankTwo

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## A. The metric

-/

/-- The metric `η` on two contravariant indices, with its colours relabelled from
  `![.up, .up]` to `fun _ => .up`. -/
noncomputable def metric : ℂT(fun _ : Fin 2 => Color.up) :=
  permT id (show IsReindexing ![Color.up, Color.up] (fun _ : Fin 2 => Color.up) id from
    ⟨Function.bijective_id, fun i => by fin_cases i <;> rfl⟩) η

/-- The metric is Lorentz invariant. -/
lemma metric_invariant (g : SL(2,ℂ)) : g • metric = metric := by
  rw [metric, ← permT_equivariant, actionT_contrMetric]

/-- The coefficient tensor of the metric is the Minkowski metric. -/
lemma coeffEquiv_symm_minkowskiMatrixZ :
    (coeffEquiv 2).symm (fun d => ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ)) = metric := by
  rw [metric, contrMetric_eq_basis]
  simp only [map_sub, permT_basis]
  rw [coeffEquiv_symm_apply, sum_pi_fin_two]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, minkowskiMatrixZ, sub_eq_add_neg]
  rw [← add_assoc, ← add_assoc]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ (congrArg Neg.neg ?_))
    (congrArg Neg.neg ?_)) (congrArg Neg.neg ?_) <;>
    exact congrArg _ (funext fun i => by fin_cases i <;> rfl)

/-- `ofComponents T` sends the metric to the contraction `η_{μν} T^{μν}`. -/
lemma ofComponents_metric (T : (Fin 2 → Fin 1 ⊕ Fin 3) → B) :
    ofComponents T metric
      = ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) • T d := by
  rw [← coeffEquiv_symm_minkowskiMatrixZ, ofComponents_coeffEquiv_symm]

/-!

## B. The classification of the invariant coefficient tensors

The half turns kill the off-diagonal coefficients, the cyclic rotation equates the three
spatial diagonal ones, and the boost along `z` relates the spatial diagonal to the time
diagonal. Together these leave `c_tt` times the metric.

-/

/-- Two distinct directions are told apart by the half turn about some axis: it keeps one and
  negates the other, a finite check. -/
lemma exists_halfTurnSign_mul_ne_one :
    ∀ μ ν : Fin 1 ⊕ Fin 3, μ ≠ ν → ∃ k, halfTurnSign k μ * halfTurnSign k ν ≠ 1 := by
  decide

/-- An invariant coefficient tensor has no off-diagonal coefficients: for `μ ≠ ν` some half
  turn multiplies `c_{μν}` by `-1`. -/
lemma eq_zero_of_ne {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    {d : Fin 2 → Fin 1 ⊕ Fin 3} (hd : d 0 ≠ d 1) : c d = 0 := by
  obtain ⟨k, hk⟩ := exists_halfTurnSign_mul_ne_one _ _ hd
  exact hc.eq_zero_of_prod_halfTurnSign_ne_one (k := k) (by rwa [Fin.prod_univ_two])

/-- The three spatial diagonal coefficients of an invariant coefficient tensor agree: the
  cyclic rotation carries `c_xx` to `c_yy` to `c_zz`. -/
lemma apply_inr_inr_eq {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (j : Fin 3) : c ![Sum.inr j, Sum.inr j] = c ![Sum.inr 2, Sum.inr 2] := by
  have hcyc (j : Fin 3) : c ![Sum.inr (j + 1), Sum.inr (j + 1)] = c ![Sum.inr j, Sum.inr j] := by
    have h := hc.apply_cycIdx ![Sum.inr j, Sum.inr j]
    rwa [show cycIdx ![Sum.inr j, Sum.inr j] = ![Sum.inr (j + 1), Sum.inr (j + 1)] from
      cycDir_comp_two _ _] at h
  fin_cases j
  · exact hcyc 2
  · exact (hcyc 0).trans (hcyc 2)
  · rfl

/-- The time and spatial diagonal coefficients of an invariant coefficient tensor are opposite.
  The boost along `z` scales the light-cone component along `D₀ - D_z` in both slots by `t⁴`, so
  that component, `c_tt - c_tz - c_zt + c_zz`, vanishes, and the mixed terms are `0`. -/
lemma apply_inl_inl_add_apply_inr_inr {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) : c ![Sum.inl 0, Sum.inl 0] + c ![Sum.inr 2, Sum.inr 2] = 0 := by
  have h := hc.lightConeComponent_eq_zero 2 (κ := ![0, 0]) (by decide)
  rw [lightConeComponent, ← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type] at h
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, lightConeCoeff] at h
  rw [eq_zero_of_ne hc (d := ![Sum.inl 0, Sum.inr 2]) (by simp),
    eq_zero_of_ne hc (d := ![Sum.inr 2, Sum.inl 0]) (by simp)] at h
  linear_combination h

/-- An invariant coefficient tensor is `c_tt` times the Minkowski metric. -/
lemma eq_smul_minkowskiMatrixZ {c : (Fin 2 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (d : Fin 2 → Fin 1 ⊕ Fin 3) :
    c d = c ![Sum.inl 0, Sum.inl 0] * ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) := by
  by_cases hd : d 0 = d 1
  · have hd' : d = ![d 0, d 0] := by
      funext s
      fin_cases s
      · rfl
      · exact hd.symm
    rw [hd', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
    rcases d 0 with a | j
    · rw [Subsingleton.elim a 0]
      simp [minkowskiMatrixZ]
    · rw [apply_inr_inr_eq hc j]
      simp [minkowskiMatrixZ]
      linear_combination apply_inl_inl_add_apply_inr_inr hc
  · rw [eq_zero_of_ne hc hd]
    simp [minkowskiMatrixZ, Matrix.diagonal_apply_ne _ hd]

/-!

## C. The invariants of an equivariant map

-/

variable {f : ℂT(fun _ : Fin 2 => Color.up) →ₗ[ℂ] B}

/-- The invariants of the range of `f` reduce to the line through the image `f metric` of the
  metric: a Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is
  a multiple of `f metric` plus an element of `S`. -/
lemma reducesInvariantsTo_span_metric (hf : IsLorentzCovariant 2 B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f)
      (ℂ ∙ f metric) := by
  have h := hf.reducesInvariantsTo_span (fun _ : Unit =>
    fun d : Fin 2 → Fin 1 ⊕ Fin 3 => ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ)) fun c hc => by
      rw [Set.range_const, Submodule.mem_span_singleton]
      exact ⟨c ![Sum.inl 0, Sum.inl 0], funext fun d => (eq_smul_minkowskiMatrixZ hc d).symm⟩
  rwa [Set.range_const, coeffEquiv_symm_minkowskiMatrixZ] at h

/-- Every Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is a
  multiple of the image `f metric` of the metric plus an element of `S`. -/
lemma exists_smul_map_metric_add_of_invariant (hf : IsLorentzCovariant 2 B repLorentz f)
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • f metric + y := by
  obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1
    (reducesInvariantsTo_span_metric hf S hS x hx hinv)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨a, y, hy, rfl⟩

/-- Every Lorentz invariant in the range of `f` is a multiple of the image `f metric` of the
  metric. -/
lemma exists_smul_map_metric_of_invariant (hf : IsLorentzCovariant 2 B repLorentz f) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • f metric := by
  obtain ⟨a, y, hy, rfl⟩ := exists_smul_map_metric_add_of_invariant hf ⊥
    (fun _ _ hy => by rw [(Submodule.mem_bot ℂ).1 hy, map_zero]; exact Submodule.zero_mem _)
    (Submodule.mem_sup_left hx) hinv
  rw [(Submodule.mem_bot ℂ).1 hy, add_zero]
  exact ⟨a, rfl⟩

end RankTwo

end Lorentz
