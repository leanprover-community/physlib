/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
public import Physlib.Mathematics.Geometry.Metric.Lorentzian.Defs

/-!
# The Minkowski product as a pseudo-inner product

`Lorentz.Vector.minkowskiProduct`, due to Joseph Tooby-Smith, is already a continuous symmetric
nondegenerate bilinear form, so it is a `PseudoInnerProductSpace` structure on `Lorentz.Vector d`.
This file records that and computes the resulting signature, connecting the relativity
development to `Physlib.Mathematics.Geometry.Metric.PseudoRiemannian`.

In the `+---` convention of `minkowskiProduct` the index — the largest dimension of a negative
definite subspace — is the spatial dimension `d`.

## Main definitions

* `Lorentz.Vector.minkowskiPseudoInner`: the pseudo-inner product structure. Deliberately a `def`,
  since `Vector d` already carries the Euclidean `InnerProductSpace ℝ`.

## Main results

* `Lorentz.Vector.index_minkowskiPseudoInner` and `coindex_minkowskiPseudoInner`: the signature is
  `(+, -, …, -)`, so the index is `d` and the coindex is `1`.
* `Lorentz.Vector.isContMDiffPseudoRiemannianBundle_minkowski` and
  `isLorentzian_minkowskiPseudoInner`: Minkowski spacetime is a smooth Lorentzian manifold.

## Tags

Minkowski, Lorentz vector, signature, index
-/

@[expose] public section

open Module PseudoInnerProductSpace
open scoped Manifold ContDiff

namespace Lorentz.Vector

variable {d : ℕ}

/-- The Minkowski product as a pseudo-inner product on `Vector d`.

Deliberately a `def` and not an instance: `Vector d` already carries the Euclidean
`Lorentz.Vector.innerProductSpace`, hence already a `PseudoInnerProductSpace` of index `0` through
`InnerProductSpace.toPseudoInnerProductSpace`. Two instances would compete. Introduce this one
with `letI` where the Minkowski signature is meant. -/
@[reducible] noncomputable def minkowskiPseudoInner (d : ℕ) :
    PseudoInnerProductSpace (Vector d) where
  pseudoInnerSL := minkowskiProduct
  pseudoInner_symm := minkowskiProduct_symm
  pseudoInner_nondegenerate p h := (minkowskiProduct_eq_zero_forall_iff p).mp h

lemma finrank_eq : finrank ℝ (Vector d) = 1 + d := by
  rw [finrank_eq_card_basis (basis (d := d))]
  simp

/-- The time axis, on which the Minkowski form is positive definite. -/
noncomputable def timeAxis (d : ℕ) : Submodule ℝ (Vector d) :=
  Submodule.span ℝ {basis (Sum.inl 0)}

/-- The space of vectors with vanishing time component, on which the Minkowski form is negative
definite. -/
noncomputable def spatial (d : ℕ) : Submodule ℝ (Vector d) :=
  LinearMap.ker (basis.coord (Sum.inl 0))

lemma mem_spatial_iff {v : Vector d} : v ∈ spatial d ↔ v (Sum.inl 0) = 0 := by
  simp [spatial, Basis.coord_apply, basis_repr_apply]

lemma minkowskiProduct_basis_inl_self (d : ℕ) :
    ⟪(basis (d := d) (Sum.inl 0)), (basis (d := d) (Sum.inl 0))⟫ₘ = (1 : ℝ) := by
  rw [minkowskiProduct_toCoord]
  simp [basis_apply]

/-- The Minkowski form is negative definite on `spatial d`. -/
lemma minkowskiProduct_self_neg_of_mem_spatial {v : Vector d} (hv : v ∈ spatial d) (h0 : v ≠ 0) :
    ⟪v, v⟫ₘ < 0 := by
  rw [minkowskiProduct_toCoord, mem_spatial_iff.mp hv]
  have hne : ∃ i, v (Sum.inr i) ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (eq_of_apply_eq fun μ ↦ by
      cases μ with
      | inl j => simpa [Fin.fin_one_eq_zero j] using mem_spatial_iff.mp hv
      | inr i => simpa using h i)
  obtain ⟨i, hi⟩ := hne
  have hpos : 0 < ∑ j, v (Sum.inr j) * v (Sum.inr j) :=
    Finset.sum_pos' (fun j _ ↦ mul_self_nonneg _) ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  linarith

/-- The Minkowski form is positive definite on `timeAxis d`. -/
lemma minkowskiProduct_self_pos_of_mem_timeAxis {w : Vector d} (hw : w ∈ timeAxis d) (h0 : w ≠ 0) :
    0 < ⟪w, w⟫ₘ := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hc : c ≠ 0 := by rintro rfl; exact h0 (by simp)
  have hval : ⟪c • basis (d := d) (Sum.inl 0), c • basis (d := d) (Sum.inl 0)⟫ₘ = c * c := by
    rw [minkowskiProduct_apply, minkowskiProductMap_smul_fst, minkowskiProductMap_smul_snd,
      ← minkowskiProduct_apply, minkowskiProduct_basis_inl_self d]
    ring
  rw [hval]
  exact mul_self_pos.mpr hc

lemma finrank_timeAxis : finrank ℝ (timeAxis d) = 1 :=
  finrank_span_singleton (basis.ne_zero (Sum.inl 0))

lemma finrank_spatial : finrank ℝ (spatial d) = d := by
  have hsurj : LinearMap.range (basis.coord (Sum.inl (0 : Fin 1)) : Vector d →ₗ[ℝ] ℝ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • basis (Sum.inl 0), by simp [Basis.coord_apply]⟩
  have h := LinearMap.finrank_range_add_finrank_ker
    (basis.coord (Sum.inl (0 : Fin 1)) : Vector d →ₗ[ℝ] ℝ)
  rw [hsurj, finrank_top, finrank_self, finrank_eq] at h
  have hbridge : finrank ℝ (spatial d)
      = finrank ℝ (LinearMap.ker (basis.coord (Sum.inl (0 : Fin 1)) : Vector d →ₗ[ℝ] ℝ)) := rfl
  omega

lemma pseudoInner_minkowskiPseudoInner (d : ℕ) (p q : Vector d) :
    letI := minkowskiPseudoInner d
    pseudoInner p q = ⟪p, q⟫ₘ := rfl

/-- **The Minkowski signature.** In the `+---` convention the index — the largest dimension of a
negative definite subspace — is the spatial dimension `d`. -/
theorem index_minkowskiPseudoInner (d : ℕ) :
    letI := minkowskiPseudoInner d
    index (Vector d) = d := by
  letI := minkowskiPseudoInner d
  have hneg : ∀ v : spatial d, v ≠ 0 → pseudoInner (v : Vector d) (v : Vector d) < 0 := by
    intro v hv
    rw [pseudoInner_minkowskiPseudoInner]
    exact minkowskiProduct_self_neg_of_mem_spatial v.2 fun h ↦ hv (Subtype.ext h)
  have hpos : ∀ w : timeAxis d, w ≠ 0 → 0 < pseudoInner (w : Vector d) (w : Vector d) := by
    intro w hw
    rw [pseudoInner_minkowskiPseudoInner]
    exact minkowskiProduct_self_pos_of_mem_timeAxis w.2 fun h ↦ hw (Subtype.ext h)
  have hdim : finrank ℝ (spatial d) + finrank ℝ (timeAxis d) = finrank ℝ (Vector d) := by
    rw [finrank_spatial, finrank_timeAxis, finrank_eq]
    omega
  rw [index_eq_of_negDef_of_posDef hneg hpos hdim, finrank_spatial]

/-- **Minkowski space is Lorentzian.** In the `+---` convention it has exactly one positive
direction, the time axis. -/
theorem coindex_minkowskiPseudoInner (d : ℕ) :
    letI := minkowskiPseudoInner d
    coindex (Vector d) = 1 := by
  letI := minkowskiPseudoInner d
  have hneg : ∀ v : spatial d, v ≠ 0 → pseudoInner (v : Vector d) (v : Vector d) < 0 := by
    intro v hv
    rw [pseudoInner_minkowskiPseudoInner]
    exact minkowskiProduct_self_neg_of_mem_spatial v.2 fun h ↦ hv (Subtype.ext h)
  have hpos : ∀ w : timeAxis d, w ≠ 0 → 0 < pseudoInner (w : Vector d) (w : Vector d) := by
    intro w hw
    rw [pseudoInner_minkowskiPseudoInner]
    exact minkowskiProduct_self_pos_of_mem_timeAxis w.2 fun h ↦ hw (Subtype.ext h)
  have hdim : finrank ℝ (spatial d) + finrank ℝ (timeAxis d) = finrank ℝ (Vector d) := by
    rw [finrank_spatial, finrank_timeAxis, finrank_eq]
    omega
  rw [coindex_eq_of_negDef_of_posDef hneg hpos hdim, finrank_timeAxis]

/-- The Minkowski metric on the tangent spaces of `Vector d`, viewed as a manifold modelled on
itself. Like `minkowskiPseudoInner`, a `def`: `Vector d` already carries the Euclidean form. -/
@[reducible] noncomputable def tangentMinkowskiPseudoInner (d : ℕ) (x : Vector d) :
    PseudoInnerProductSpace (TangentSpace 𝓘(ℝ, Vector d) x) :=
  letI := minkowskiPseudoInner d
  TangentSpace.pseudoInnerProductSpace x

/-- **Minkowski spacetime is a smooth pseudo-Riemannian manifold**: its metric is constant. -/
theorem isContMDiffPseudoRiemannianBundle_minkowski (d : ℕ) (n : ℕ∞ω) :
    letI := tangentMinkowskiPseudoInner d
    IsContMDiffPseudoRiemannianBundle 𝓘(ℝ, Vector d) n (Vector d)
      (TangentSpace 𝓘(ℝ, Vector d) : Vector d → Type _) := by
  letI := minkowskiPseudoInner d
  exact isContMDiffPseudoRiemannianBundle_self n

/-- **Minkowski spacetime is a Lorentzian manifold.** `Vector d` with the constant Minkowski
metric has coindex `1` everywhere, the `+---` signature. -/
theorem isLorentzian_minkowskiPseudoInner (d : ℕ) :
    letI := tangentMinkowskiPseudoInner d
    PseudoRiemannian.IsLorentzian 𝓘(ℝ, Vector d) (Vector d) := by
  letI := tangentMinkowskiPseudoInner d
  exact ⟨fun _ ↦ coindex_minkowskiPseudoInner d⟩

end Lorentz.Vector
