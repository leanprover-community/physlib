/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.ForMathlib.Fin
public import PhyslibAlpha.Mathematics.RepresentationTheory.SlotAction
public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
public import Mathlib.Analysis.Complex.RealDeriv
/-!
# The metric pairings of four Weyl indices

The invariants of four left-handed Weyl indices are spanned by two products of Weyl metrics.

## i. Overview

A coefficient function `C : (Fin n → Fin 2) → ℂ` of `n` left-handed Weyl indices carries the action
of `M ∈ SL(2, ℂ)` on each index, `SlotAction.act M C`. With four indices the products of two Weyl
metrics `ε_{ab} = metricRaw`, pairing the slots `ε_{a₀a₁} ε_{a₂a₃}`, `ε_{a₀a₂} ε_{a₁a₃}` and
`ε_{a₀a₃} ε_{a₁a₂}`, are invariant. They obey the Schouten identity
`ε₀₁ ε₂₃ - ε₀₂ ε₁₃ + ε₀₃ ε₁₂ = 0` (A), and the first two span all invariants (C).

The argument is infinitesimal. The unipotent elements `1 + z E` and `1 + z F` of `SL(2, ℂ)`, with
`E = !![0, 1; 0, 0]` and `F = !![0, 0; 1, 0]`, move a fixed coefficient function along a line, so
it is killed by the infinitesimal actions of `E` and `F`, one slot at a time (B). These
unipotent elements generate `SL(2, ℂ)`, every element being a product of four of them, which
`PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction` uses. For four indices those two conditions
are linear equations on the sixteen coefficients. They force every coefficient with more raised
than lowered indices, or fewer, to vanish, and leave the six balanced ones in a two-dimensional
space. The two coefficients at `1100` and `1010` fix all the others
(`eq_sum_pairingBasis_of_infinitesimalAct_eq_zero`). The right-handed Weyl representation has the
same invariants, the group acting on it through a reparametrisation of itself (C.3). The components
of a tensor with four Weyl indices of one chirality are such a coefficient function, so the
invariant tensors are the span of the two products of metrics (D).

## ii. Key results

- `Fermion.metricPairing` : a product of two Weyl metrics on four indices.
- `Fermion.exists_eq_lowerUnipotent_mul_upperUnipotent` : every element of `SL(2, ℂ)` is a product
  of unipotent elements.
- `Fermion.metricPairing_schouten` : the Schouten identity.
- `Fermion.eq_sum_pairingBasis_of_infinitesimalAct_eq_zero` : a coefficient function killed by `E`
  and `F` is a combination of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`.
- `Fermion.infinitesimalAct_eq_zero_of_invariant` : an invariant coefficient function is killed by
  `E` and `F`.
- `Fermion.mem_span_pairingBasis_iff` : the invariants of four left-handed Weyl indices are the span
  of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`.
- `Fermion.linearIndependent_pairingBasis` : the two are linearly independent.
- `Fermion.mem_span_pairingBasis_iff_map_star` : the same for right-handed indices.
- `complexLorentzTensor.invariants_upL_pow_four_eq_span_range_leftMetricPairing`,
  `complexLorentzTensor.invariants_upR_pow_four_eq_span_range_rightMetricPairing` : the invariant
  tensors with four Weyl indices of one chirality.

## iii. Table of contents

- A. Products of Weyl metrics
- B. The unipotent elements
- C. Four Weyl indices
  - C.1. The infinitesimal equations
  - C.2. The invariants
  - C.3. The other Weyl representations
- D. Tensors with four Weyl indices of one chirality

## iv. References

* None.

-/

@[expose] public section

namespace Fermion

open Matrix MatrixGroups SlotAction

/-!

## A. Products of Weyl metrics

-/

/-- The product `ε_{a_i a_j} ε_{a_k a_l}` of two Weyl metrics on four Weyl indices, pairing the
  slots `i, j` and `k, l`. -/
def metricPairing (i j k l : Fin 4) (a : Fin 4 → Fin 2) : ℂ :=
  metricRaw (a i) (a j) * metricRaw (a k) (a l)

/-- Every index vector of four slots is a vector literal. -/
lemma exists_eq_vecCons {α : Type*} (a : Fin 4 → α) : ∃ w x y z, a = ![w, x, y, z] :=
  ⟨a 0, a 1, a 2, a 3, by funext i; fin_cases i <;> rfl⟩

/-- The Schouten identity `ε₀₁ ε₂₃ - ε₀₂ ε₁₃ + ε₀₃ ε₁₂ = 0`. Two-component spinors admit no
  totally antisymmetric tensor of rank three. -/
lemma metricPairing_schouten :
    metricPairing 0 1 2 3 - metricPairing 0 2 1 3 + metricPairing 0 3 1 2 = 0 := by
  funext a
  obtain ⟨w, x, y, z, rfl⟩ := exists_eq_vecCons a
  fin_cases w <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [metricPairing, metricRaw]

/-- The two pairings spanning the invariants of four Weyl indices, `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
def pairingBasis : Fin 2 → (Fin 4 → Fin 2) → ℂ := ![metricPairing 0 2 1 3, metricPairing 0 1 2 3]

/-- Two index vectors, `1100` and `1010`, on which `pairingBasis` is the unit matrix. -/
def pairingPoint : Fin 2 → Fin 4 → Fin 2 := ![![1, 1, 0, 0], ![1, 0, 1, 0]]

/-- The two basis pairings evaluated at the two test points form the unit matrix. -/
lemma pairingBasis_pairingPoint (i j : Fin 2) :
    pairingBasis i (pairingPoint j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [pairingBasis, pairingPoint, metricPairing, metricRaw]

/-- The two pairings are linearly independent. -/
lemma linearIndependent_pairingBasis : LinearIndependent ℂ pairingBasis := by
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  have h := congrFun hg (pairingPoint i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pairingBasis_pairingPoint, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply] at h
  exact h

/-!

## B. The unipotent elements

-/

/-- The unipotent element `!![1, z; 0, 1] = 1 + z E` of `SL(2, ℂ)`. -/
def upperUnipotent (z : ℂ) : SL(2,ℂ) :=
  ⟨1 + z • !![0, 1; 0, 0], by simp [det_fin_two]⟩

/-- The unipotent element `!![1, 0; z, 1] = 1 + z F` of `SL(2, ℂ)`. -/
def lowerUnipotent (z : ℂ) : SL(2,ℂ) :=
  ⟨1 + z • !![0, 0; 1, 0], by simp [det_fin_two]⟩

/-- Every element of `SL(2, ℂ)` is a product of four unipotent elements, alternately lower and
  upper. With `M = !![p, q; r, s]` and `a` chosen so that `r' = a p + r ≠ 0`, the matrix
  `lowerUnipotent a * M` is `upperUnipotent ((p - 1) / r') * lowerUnipotent r' *
  upperUnipotent ((a q + s - 1) / r')`. -/
lemma exists_eq_lowerUnipotent_mul_upperUnipotent (M : SL(2,ℂ)) :
    ∃ a x r y : ℂ,
      M = lowerUnipotent a * upperUnipotent x * lowerUnipotent r * upperUnipotent y := by
  have hdet : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
    rw [← det_fin_two]
    exact M.2
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a * M.1 0 0 + M.1 1 0 ≠ 0 := by
    by_cases h : M.1 1 0 = 0
    · refine ⟨1, fun h' => ?_⟩
      simp only [h, one_mul, add_zero] at h'
      simp [h, h'] at hdet
    · exact ⟨0, by simpa using h⟩
  refine ⟨-a, (M.1 0 0 - 1) / (a * M.1 0 0 + M.1 1 0), a * M.1 0 0 + M.1 1 0,
    (a * M.1 0 1 + M.1 1 1 - 1) / (a * M.1 0 0 + M.1 1 0), ?_⟩
  have ha' : M.1 0 0 * a + M.1 1 0 ≠ 0 := by rwa [mul_comm]
  ext i j
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  simp only [lowerUnipotent, upperUnipotent]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    field_simp
  · ring
  · linear_combination (-1 : ℂ) * hdet
  · ring
  · linear_combination a * hdet

/-- At `t = 0` the line `t ↦ 1 + c t G` is the identity. -/
lemma one_add_smul_zero_apply (G : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (p q : Fin 2) :
    (1 + (c * ((0 : ℝ) : ℂ)) • G) p q = if p = q then 1 else 0 := by
  simp [Matrix.one_apply]

/-- The line `t ↦ 1 + c t G` has derivative `c G`. -/
lemma hasDerivAt_one_add_smul (G : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (p q : Fin 2) :
    HasDerivAt (fun t : ℝ => (1 + (c * (t : ℂ)) • G) p q) ((c • G) p q) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).mul_const (G p q)).const_add
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) p q)
  simpa [mul_assoc] using h

/-!

## C. Four Weyl indices

### C.1. The infinitesimal equations

-/

/-- An invariant coefficient function of `n` Weyl indices is killed by the infinitesimal actions
  of `E` and `F`, the derivatives of the unipotent lines. -/
lemma infinitesimalAct_eq_zero_of_invariant {n : ℕ} {C : (Fin n → Fin 2) → ℂ}
    (hC : ∀ M : SL(2,ℂ), act M.1 C = C) :
    infinitesimalAct !![0, 1; 0, 0] C = 0 ∧ infinitesimalAct !![0, 0; 1, 0] C = 0 := by
  constructor
  · simpa using infinitesimalAct_eq_zero_of_act_eq (one_add_smul_zero_apply _ 1)
      (hasDerivAt_one_add_smul _ 1) fun t => hC (upperUnipotent (1 * t))
  · simpa using infinitesimalAct_eq_zero_of_act_eq (one_add_smul_zero_apply _ 1)
      (hasDerivAt_one_add_smul _ 1) fun t => hC (lowerUnipotent (1 * t))

/-- The infinitesimal action at four Weyl indices, written out slot by slot. -/
lemma infinitesimalAct_four (N : Fin 2 → Fin 2 → ℂ) (C : (Fin 4 → Fin 2) → ℂ) (w x y z : Fin 2) :
    infinitesimalAct N C ![w, x, y, z] = ∑ q, (N w q * C ![q, x, y, z] + N x q * C ![w, q, y, z]
      + N y q * C ![w, x, q, z] + N z q * C ![w, x, y, q]) := by
  have hu : ∀ (s : Fin 4) (q : Fin 2), Function.update ![w, x, y, z] s q
      = ![if s = 0 then q else w, if s = 1 then q else x, if s = 2 then q else y,
        if s = 3 then q else z] := by
    intro s q
    funext i
    fin_cases s <;> fin_cases i <;> rfl
  simp only [infinitesimalAct, Fin.sum_univ_four, hu, ← Finset.sum_add_distrib]
  simp

/-- A coefficient function of four Weyl indices killed by `E` and `F` is a combination of
  `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`, with its values at `1100` and `1010` as coefficients. The equations
  of `E` at `0111`, of `F` at `1000` and their neighbours kill the unbalanced coefficients, and
  those of `E` at the four index vectors with a single raised slot relate the six balanced ones. -/
lemma eq_sum_pairingBasis_of_infinitesimalAct_eq_zero {C : (Fin 4 → Fin 2) → ℂ}
    (hE : infinitesimalAct !![0, 1; 0, 0] C = 0) (hF : infinitesimalAct !![0, 0; 1, 0] C = 0) :
    C = ∑ i, C (pairingPoint i) • pairingBasis i := by
  have e := fun w x y z =>
    (infinitesimalAct_four _ C w x y z).symm.trans (congrFun hE ![w, x, y, z])
  have f := fun w x y z =>
    (infinitesimalAct_four _ C w x y z).symm.trans (congrFun hF ![w, x, y, z])
  have e0111 := e 0 1 1 1; have e0011 := e 0 0 1 1; have e0101 := e 0 1 0 1
  have e0110 := e 0 1 1 0; have e1001 := e 1 0 0 1; have e1010 := e 1 0 1 0
  have e1000 := e 1 0 0 0; have e0100 := e 0 1 0 0; have e0010 := e 0 0 1 0
  have e0001 := e 0 0 0 1; have f1000 := f 1 0 0 0; have f1100 := f 1 1 0 0
  have f1010 := f 1 0 1 0; have f0110 := f 0 1 1 0; have f1001 := f 1 0 0 1
  have f0011 := f 0 0 1 1
  simp [Fin.sum_univ_two] at e0111 e0011 e0101 e0110 e1001 e1010 e1000 e0100 e0010 e0001
  simp [Fin.sum_univ_two] at f1000 f1100 f1010 f0110 f1001 f0011
  funext a
  obtain ⟨w, x, y, z, rfl⟩ := exists_eq_vecCons a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  fin_cases w <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [pairingBasis, pairingPoint, metricPairing, metricRaw]
  · linear_combination f1000
  · linear_combination (f1001 + f0011 - f1010) / 2
  · linear_combination (f1010 + f0110 - f1100) / 2
  · linear_combination (e0010 + e0001 - e1000 - e0100) / 2
  · linear_combination (f1100 + f0110 - f1010) / 2
  · linear_combination (e0100 + e0001 - e1000 - e0010) / 2
  · linear_combination (e1000 + e0100 + e0010 - e0001) / 2
  · linear_combination (e0011 + e0101 - e1001) / 2
  · linear_combination (f1100 + f1010 - f0110) / 2
  · linear_combination e1000
  · linear_combination (e0011 + e1001 - e0101) / 2
  · linear_combination (e0101 + e1001 - e0011) / 2
  · linear_combination (e0110 + e1010 - e0011) / 2
  · linear_combination e0111

/-!

### C.2. The invariants

The pairings are invariant because `M ε Mᵀ = (det M) ε`, applied to each pair of slots.

-/

/-- The Weyl metric against two rows of a matrix gives the determinant times the metric. -/
lemma sum_metricRaw_mul (M : Matrix (Fin 2) (Fin 2) ℂ) (p q : Fin 2) :
    ∑ x, ∑ z, metricRaw x z * (M p x * M q z) = M.det * metricRaw p q := by
  fin_cases p <;> fin_cases q <;> simp [metricRaw, det_fin_two, Fin.sum_univ_two] <;> ring

/-- A sum over index vectors of four slots is a fourfold sum. -/
lemma sum_pi_four {β : Type*} [AddCommMonoid β] (F : (Fin 4 → Fin 2) → β) :
    ∑ d, F d = ∑ w, ∑ x, ∑ y, ∑ z, F ![w, x, y, z] := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ F fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ fun _ => rfl]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_unique]
  rfl

/-- The pairing `ε₀₂ ε₁₃` is invariant. -/
lemma act_metricPairing_zero_two (M : SL(2,ℂ)) :
    act M.1 (metricPairing 0 2 1 3) = metricPairing 0 2 1 3 := by
  funext a
  simp only [act]
  rw [sum_pi_four]
  have h := congrArg₂ (· * ·) (sum_metricRaw_mul M.1 (a 0) (a 2))
    (sum_metricRaw_mul M.1 (a 1) (a 3))
  simp only [M.2, one_mul] at h
  rw [metricPairing, ← h]
  simp [metricPairing, Fin.prod_univ_four, Fin.sum_univ_two, metricRaw]
  ring

/-- The pairing `ε₀₁ ε₂₃` is invariant. -/
lemma act_metricPairing_zero_one (M : SL(2,ℂ)) :
    act M.1 (metricPairing 0 1 2 3) = metricPairing 0 1 2 3 := by
  funext a
  simp only [act]
  rw [sum_pi_four]
  have h := congrArg₂ (· * ·) (sum_metricRaw_mul M.1 (a 0) (a 1))
    (sum_metricRaw_mul M.1 (a 2) (a 3))
  simp only [M.2, one_mul] at h
  rw [metricPairing, ← h]
  simp [metricPairing, Fin.prod_univ_four, Fin.sum_univ_two, metricRaw]
  ring

/-- The invariants of four left-handed Weyl indices are the span of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
lemma mem_span_pairingBasis_iff (C : (Fin 4 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act M.1 C = C) ↔ C ∈ Submodule.span ℂ (Set.range pairingBasis) := by
  constructor
  · intro hC
    obtain ⟨hE, hF⟩ := infinitesimalAct_eq_zero_of_invariant hC
    rw [eq_sum_pairingBasis_of_infinitesimalAct_eq_zero hE hF]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hC M
    refine Submodule.span_induction (p := fun C _ => act M.1 C = C) ?_ ?_ ?_ ?_ hC
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact act_metricPairing_zero_two M
      · exact act_metricPairing_zero_one M
    · funext a
      simp [act]
    · intro C C' _ _ h h'
      funext a
      have ha := congrFun h a
      have ha' := congrFun h' a
      simp only [act, Pi.add_apply, add_mul, Finset.sum_add_distrib] at ha ha' ⊢
      rw [ha, ha']
    · intro k C _ h
      funext a
      have ha := congrFun h a
      simp only [act, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at ha ⊢
      rw [ha]


/-!

### C.3. The other Weyl representations

On right-handed indices `M` acts through its conjugate, which runs over all of `SL(2, ℂ)` as `M`
does (`Fermion.map_star_coe_map_starRingEnd`), so their invariants are the same span.

-/

/-- The invariants of four right-handed Weyl indices are the span of `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
lemma mem_span_pairingBasis_iff_map_star (C : (Fin 4 → Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act (M.1.map star) C = C)
      ↔ C ∈ Submodule.span ℂ (Set.range pairingBasis) := by
  rw [← mem_span_pairingBasis_iff]
  refine ⟨fun h N => ?_, fun h M => h (SpecialLinearGroup.map (starRingEnd ℂ) M)⟩
  have h' := h (SpecialLinearGroup.map (starRingEnd ℂ) N)
  rwa [map_star_coe_map_starRingEnd] at h'

/-!

## D. Tensors with four Weyl indices of one chirality

The components of a tensor with four left-handed Weyl indices are a coefficient function of four
Weyl indices, on which `g` acts by `act g.1`, and those of a tensor with four right-handed ones a
coefficient function on which `g` acts by `act (g.1.map star)`. The classifications of C are
thereby classifications of the invariant tensors, through
`TensorSpecies.invariants_tensorRep_eq_map_componentEquiv`. The dual colours are reached from
these by `TensorSpecies.invariants_tensorRep_update_eq_map_toDualMapAtIndex`.

-/

open TensorSpecies complexLorentzTensor

/-- The component indices of a tensor with four left-handed Weyl indices, as four spinor
  labels. -/
def upLPowFourIdx :
    Tensor.ComponentIdx (S := complexLorentzTensor) (fun _ : Fin 4 => Color.upL) ≃
      (Fin 4 → Fin 2) :=
  Equiv.refl _

/-- The component indices of a tensor with four right-handed Weyl indices, as four spinor
  labels. -/
def upRPowFourIdx :
    Tensor.ComponentIdx (S := complexLorentzTensor) (fun _ : Fin 4 => Color.upR) ≃
      (Fin 4 → Fin 2) :=
  Equiv.refl _

/-- The products of Weyl metrics `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃` as tensors with four left-handed Weyl
  indices. -/
noncomputable def leftMetricPairing (i : Fin 2) : ℂT(fun _ : Fin 4 => Color.upL) :=
  (componentEquiv upLPowFourIdx).symm (pairingBasis i)

/-- The products of Weyl metrics `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃` as tensors with four right-handed Weyl
  indices. -/
noncomputable def rightMetricPairing (i : Fin 2) : ℂT(fun _ : Fin 4 => Color.upR) :=
  (componentEquiv upRPowFourIdx).symm (pairingBasis i)

/-- The invariant tensors with four left-handed Weyl indices are the span of the two products of
  Weyl metrics `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
lemma _root_.complexLorentzTensor.invariants_upL_pow_four_eq_span_range_leftMetricPairing :
    (complexLorentzTensor.tensorRep (fun _ : Fin 4 => Color.upL)).invariants =
      Submodule.span ℂ (Set.range leftMetricPairing) := by
  rw [invariants_tensorRep_eq_map_componentEquiv upLPowFourIdx
    (A := fun g a b => ∏ s, g.1 (a s) (b s))
    (fun g φ ψ => Finset.prod_congr rfl fun i _ =>
      (congrFun (congrFun (Lorentz.toMatrix_rep_upL g) (φ i)) (ψ i)).symm)
    mem_span_pairingBasis_iff, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The invariant tensors with four right-handed Weyl indices are the span of the two products of
  Weyl metrics `ε₀₂ ε₁₃` and `ε₀₁ ε₂₃`. -/
lemma _root_.complexLorentzTensor.invariants_upR_pow_four_eq_span_range_rightMetricPairing :
    (complexLorentzTensor.tensorRep (fun _ : Fin 4 => Color.upR)).invariants =
      Submodule.span ℂ (Set.range rightMetricPairing) := by
  rw [invariants_tensorRep_eq_map_componentEquiv upRPowFourIdx
    (A := fun g a b => ∏ s, (g.1.map star) (a s) (b s))
    (fun g φ ψ => Finset.prod_congr rfl fun i _ =>
      (congrFun (congrFun (Lorentz.toMatrix_rep_upR g) (φ i)) (ψ i)).symm)
    mem_span_pairingBasis_iff_map_star, Submodule.map_span, ← Set.range_comp]
  rfl

end Fermion
