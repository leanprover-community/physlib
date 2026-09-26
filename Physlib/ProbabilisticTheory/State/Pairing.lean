/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Separation
public import Physlib.ProbabilisticTheory.Effect.Convex

/-!
# The state–effect pairing

## i. Overview

States and effects are paired by evaluation, `(ω, e) ↦ ω e ∈ [0, 1]`. This pairing is affine in
both arguments. It also separates both spaces: a state is determined by its values on all
effects, and an effect is determined by its values under all states. Moreover, the distance
between two effects is the largest difference in probability that they can produce over all
states.

Thus states and effects admit faithful representations as probability-valued functions on one
another.

## ii. Key results

- `UnitalPositiveLinearMap.apply_mem_Icc` : state–effect evaluation takes values in `[0, 1]`.
- `UnitalPositiveLinearMap.apply_mix` : evaluation is affine in the effect argument.
- `UnitalPositiveLinearMap.ext_of_effect_eq` : effects separate states.
- `Effect.dist_eq_sSup_abs_apply` : effect distance is determined by state evaluations.
- `Effect.ext_of_forall_apply_eq` : states separate effects.
- `UnitalPositiveLinearMap.injective_apply_effect` : states embed into functions on effects.
- `Effect.injective_apply_state` : effects embed into functions on states.

## iii. Table of contents

- A. State–effect evaluation
- B. Effects separate states
- C. States separate effects

-/

@[expose] public section

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

open scoped Effect

namespace UnitalPositiveLinearMap

/-!

## A. State–effect evaluation

-/

/-- State–effect evaluation takes values in `[0, 1]`. -/
lemma apply_mem_Icc (ω : 𝓢[ℝ, E]) (e : Effect E) : ω (e : E) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨map_nonneg ω e.2.1, (ω.monotone' e.2.2).trans_eq (map_one ω)⟩

/-- Evaluation is affine in the effect argument. -/
lemma apply_mix (ω : 𝓢[ℝ, E]) (e f : Effect E) (t : unitInterval) :
    ω ((Effect.mix e f t : E)) = (t : ℝ) * ω (e : E) + (1 - (t : ℝ)) * ω (f : E) := by
  rw [Effect.coe_mix, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-!

## B. Effects separate states

-/

/-- Two states that agree on all effects agree on every nonnegative element. -/
lemma ext_of_effect_eq_of_nonneg {ω φ : 𝓢[ℝ, E]}
    (h : ∀ e : Effect E, ω (e : E) = φ (e : E)) {B : E} (hB : 0 ≤ B) : ω B = φ B := by
  obtain ⟨r, hr, hrB⟩ := Effect.exists_pos_smul_mem hB
  exact mul_left_cancel₀ hr.ne' (by simpa using h ⟨r • B, hrB⟩)

/-- A state is determined by its values on effects. -/
lemma ext_of_effect_eq {ω φ : 𝓢[ℝ, E]}
    (h : ∀ e : Effect E, ω (e : E) = φ (e : E)) : ω = φ := by
  ext A
  obtain ⟨Ap, An, hAp, hAn, rfl⟩ := OrderUnitSpace.exists_eq_sub_nonneg A
  rw [map_sub, map_sub, ext_of_effect_eq_of_nonneg h hAp, ext_of_effect_eq_of_nonneg h hAn]

/-- Evaluation on effects is injective on states. -/
lemma injective_apply_effect :
    Function.Injective (fun (ω : 𝓢[ℝ, E]) (e : Effect E) => ω (e : E)) :=
  fun _ _ h => ext_of_effect_eq (congrFun h)

/-!

## C. States separate effects

-/

/-- The distance between two effects is the supremum of the difference in their evaluations over
all states. -/
lemma _root_.Effect.dist_eq_sSup_abs_apply [Nontrivial E] (e f : Effect E) :
    Dist.dist e f = sSup (Set.range fun ω : 𝓢[ℝ, E] => |ω (e : E) - ω (f : E)|) := by
  rw [Effect.dist_eq_orderUnitNorm, ← sSup_abs_apply_eq_orderUnitNorm]
  simp_rw [map_sub]

/-- An effect is determined by its values under all states. -/
lemma _root_.Effect.ext_of_forall_apply_eq {e f : Effect E}
    (h : ∀ ω : 𝓢[ℝ, E], ω (e : E) = ω (f : E)) : e = f :=
  Subtype.ext (UnitalPositiveLinearMap.ext_of_forall_apply_eq h)

/-- Evaluation by states is injective on effects. -/
lemma _root_.Effect.injective_apply_state :
    Function.Injective (fun (e : Effect E) (ω : 𝓢[ℝ, E]) => ω (e : E)) :=
  fun _ _ h => Effect.ext_of_forall_apply_eq (congrFun h)

end UnitalPositiveLinearMap
