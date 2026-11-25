/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Basic
/-!
# The metric pairings of bispinor indices

The invariant tensors with left-handed Weyl indices followed by as many right-handed ones are the
products of Weyl metric pairings of each chirality.

## i. Overview

By `complexLorentzTensor.invariants_append_eq_map₂_prodT` the invariant tensors with undotted
indices followed by dotted ones are spanned by the products of an invariant tensor of the undotted
indices and one of the dotted indices. With two left-handed and two right-handed indices the
factors are the metrics `ε` and `ε̄`, so the invariant tensors are the line through `ε ⊗ ε̄` (A).
With four of each they are the two products of metrics of each chirality, so the invariant tensors
are the span of the four products `bispinorPairingTensor`, `ε ε ⊗ ε̄ ε̄` (B). The latter is what
the classification of the invariants of four four-vector indices uses, through the Pauli matrices.

On coefficient functions, the Pauli change of indices sends the Minkowski metric to `2 ε ⊗ ε̄`,
the Fierz identity, matching the single invariant of two four-vector indices with that of two
bispinor indices (C).

## ii. Key results

- `complexLorentzTensor.invariants_upL_upL_upR_upR_eq_span_bispinorMetric` : the invariant tensors
  with two left- and then two right-handed Weyl indices.
- `complexLorentzTensor.invariants_upL_pow_four_upR_pow_four_eq_span_range_bispinorPairing` : the
  invariant tensors with four left- and then four right-handed Weyl indices.
- `Lorentz.pauliTransform_minkowskiMatrix` : the Pauli change sends the Minkowski metric to
  `2 ε ⊗ ε̄`.

## iii. Table of contents

- A. Two left- and two right-handed Weyl indices
- B. Four left- and four right-handed Weyl indices
- C. The Fierz identity

## iv. References

* None.

-/

@[expose] public section

namespace complexLorentzTensor

open TensorSpecies Tensor

/-!

## A. Two left- and two right-handed Weyl indices

-/

/-- The tensor `ε ⊗ ε̄` with two left-handed and then two right-handed Weyl indices, the product of
  the metrics of the two chiralities. -/
noncomputable def bispinorMetricTensor : ℂT(Fin.append ![Color.upL, .upL] ![Color.upR, .upR]) :=
  prodT (metricTensor Color.upL) (metricTensor Color.upR)

/-- The invariant tensors with two left-handed and then two right-handed Weyl indices are the line
  through `ε ⊗ ε̄`. -/
lemma invariants_upL_upL_upR_upR_eq_span_bispinorMetric :
    (complexLorentzTensor.tensorRep (Fin.append ![Color.upL, .upL] ![Color.upR, .upR])).invariants =
      ℂ ∙ bispinorMetricTensor := by
  rw [invariants_append_eq_map₂_prodT (fun i => Or.inl (by fin_cases i <;> rfl))
    (fun i => Or.inl (by fin_cases i <;> rfl)), invariants_pair_eq_span_metricTensor,
    invariants_pair_eq_span_metricTensor, Submodule.map₂_span_span, Set.image2_singleton]
  rfl

/-!

## B. Four left- and four right-handed Weyl indices

-/

/-- The four products `ε ε ⊗ ε̄ ε̄` of a pairing of four left-handed Weyl indices and one of four
  right-handed ones, as tensors with the left-handed indices first. -/
noncomputable def bispinorPairingTensor (ij : Fin 2 × Fin 2) :
    ℂT(Fin.append (fun _ : Fin 4 => Color.upL) (fun _ : Fin 4 => Color.upR)) :=
  prodT (Fermion.leftMetricPairing ij.1) (Fermion.rightMetricPairing ij.2)

/-- The invariant tensors with four left-handed and then four right-handed Weyl indices are the
  span of the four products of pairings `ε ε ⊗ ε̄ ε̄`. -/
lemma invariants_upL_pow_four_upR_pow_four_eq_span_range_bispinorPairing :
    (complexLorentzTensor.tensorRep
      (Fin.append (fun _ : Fin 4 => Color.upL) (fun _ : Fin 4 => Color.upR))).invariants =
      Submodule.span ℂ (Set.range bispinorPairingTensor) := by
  rw [invariants_append_eq_map₂_prodT (fun _ => Or.inl rfl) (fun _ => Or.inl rfl),
    invariants_upL_pow_four_eq_span_range_leftMetricPairing,
    invariants_upR_pow_four_eq_span_range_rightMetricPairing, Submodule.map₂_span_span,
    Set.image2_range]
  rfl

end complexLorentzTensor

/-!

## C. The Fierz identity

-/

namespace Lorentz

open Matrix MatrixGroups SlotAction Fermion

/-- The product `ε_{α₀α₁} ε_{α̇₀α̇₁}` of the Weyl metrics of the two chiralities on two bispinor
  indices. -/
def bispinorMetric (α : Fin 2 → Fin 2 × Fin 2) : ℂ :=
  metricRaw (α 0).1 (α 1).1 * metricRaw (α 0).2 (α 1).2

/-- Through the Pauli matrices the Minkowski metric is twice `ε ⊗ ε̄`, the Fierz identity
  `η^{μν} (σ_μ)_{αα̇} (σ_ν)_{ββ̇} = 2 ε_{αβ} ε_{α̇β̇}`. -/
lemma pauliTransform_minkowskiMatrix :
    pauliTransform (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ))
      = (2 : ℂ) • bispinorMetric := by
  funext α
  obtain ⟨⟨a, a'⟩, ⟨b, b'⟩, rfl⟩ : ∃ p q, α = ![p, q] :=
    ⟨α 0, α 1, by funext i; fin_cases i <;> rfl⟩
  rw [pauliTransform, transform_apply, Physlib.Fin.sum_fin_two_arrow]
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_three, minkowskiMatrixZ, PauliMatrix.pauliLower,
      PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix, bispinorMetric,
      metricRaw] <;> norm_num [Complex.ext_iff]

end Lorentz
