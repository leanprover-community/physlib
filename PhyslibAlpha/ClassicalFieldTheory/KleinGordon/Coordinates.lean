/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Basic
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedSolution
public import PhyslibAlpha.Relativity.Causality.LightCone

/-!

# Coordinates of spacetime

Spacetime is identified with time and space.

## i. Overview

Spacetime is identified with time and space. The causal relation and the second derivatives are
transported along the identification.

## ii. Key results

- `coordinates` : Time and space coordinates in units with speed of light equal to one.
- `sourceEquiv` : Compact smooth sources transported to time-space coordinates.
- `sourceOperator` : The transported compact Klein–Gordon operator on Minkowski test sources.
- `operator_of_coordinates` : The neighbour's Klein–Gordon operator has the Fourier coordinate
  differential expression.

## iii. Table of contents

- A. The spatial Fourier Green construction on Minkowski spacetime
- B. Coordinate form of the Minkowski Klein–Gordon operator

## iv. References

None.

## A. The spatial Fourier Green construction on Minkowski spacetime

- `coordinates` : Time and space coordinates in units with speed of light equal to one.
- `sourceEquiv` : Compact smooth sources transported to time-space coordinates.
- `sourceOperator` : The transported compact Klein–Gordon operator on Minkowski test sources.

Lemmas: `tsupport_sourceEquiv`.

## B. Coordinate form of the Minkowski Klein–Gordon operator

Lemmas: `coordinates_time`, `coordinates_space`, `precedes_iff_coordinates`,
`causalFuture_coordinates`, `causalPast_coordinates`, `coordinates_basis_time`,
`coordinates_basis_space`, `second_spacetime_deriv`, `second_spacetime_deriv_coordinates`,
`second_time_slice` and more.

-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff Laplacian
open CausalRelation Minkowski TimeSpace WaveEquation TopologicalSpace Topology

namespace KleinGordon.Spacetime

section
variable {d : ℕ} (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Time and space coordinates in units with speed of light equal to one. -/
def coordinates (d : ℕ) : SpaceTime d ≃L[ℝ] ℝ × Space d :=
  (SpaceTime.toTimeAndSpace 1).trans
    (Time.toRealCLE.prodCongr (ContinuousLinearEquiv.refl ℝ (Space d)))

/-- Compact smooth sources transported to time-space coordinates. -/
def sourceEquiv : 𝓓((⊤ : Opens (SpaceTime d)), F) ≃ₗ[ℝ]
    𝓓((⊤ : Opens (ℝ × Space d)), F) where
  toFun f := {
    toFun := f ∘ (coordinates d).symm
    contDiff' := f.contDiff.comp (coordinates d).symm.contDiff
    hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (coordinates d).symm.toHomeomorph
    tsupport_subset' := fun _ _ => trivial }
  invFun f := {
    toFun := f ∘ coordinates d
    contDiff' := f.contDiff.comp (coordinates d).contDiff
    hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (coordinates d).toHomeomorph
    tsupport_subset' := fun _ _ => trivial }
  left_inv f := by
    ext p
    change f ((coordinates d).symm ((coordinates d) p)) = f p
    simp
  right_inv f := by
    ext p
    change f ((coordinates d) ((coordinates d).symm p)) = f p
    simp
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl

omit [CompleteSpace F] in
/-- Coordinate transport carries the source support to its coordinate image. -/
lemma tsupport_sourceEquiv (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    tsupport (sourceEquiv F f) = coordinates d '' tsupport f := by
  change tsupport (f ∘ (coordinates d).symm.toHomeomorph) = _
  rw [tsupport_comp_eq_preimage f (coordinates d).symm.toHomeomorph]
  exact ((coordinates d).toHomeomorph.image_eq_preimage_symm _).symm

/-- The transported compact Klein–Gordon operator on Minkowski test sources. -/
def sourceOperator (μ : ℝ) (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    𝓓((⊤ : Opens (SpaceTime d)), F) :=
  (sourceEquiv F).symm (KleinGordon.testOperator F (sourceEquiv F f) μ)
end

section
variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma coordinates_time (p : SpaceTime d) : (coordinates d p).1 = (p.time 1).val := rfl

lemma coordinates_space (p : SpaceTime d) : (coordinates d p).2 = p.space := rfl

/-- Minkowski causal precedence is exactly the coordinate light-cone inequality. -/
lemma precedes_iff_coordinates (p q : SpaceTime d) :
    (causalRelation d).Precedes p q ↔
      ‖(coordinates d q).2 - (coordinates d p).2‖ ≤ (coordinates d q).1 - (coordinates d p).1 := by
  rw [precedes_iff_time_space 1]
  simp only [SpeedOfLight.val_one, one_mul, coordinates_time, coordinates_space]
  exact ⟨And.right, fun h => ⟨by linarith [norm_nonneg (q.space - p.space)], h⟩⟩

lemma causalFuture_coordinates (K : Set (SpaceTime d)) :
    (coordinates d) ⁻¹' causalFuture (coordinates d '' K) = (causalRelation d).causalFuture K := by
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hqp⟩
    exact ⟨r, hr, (precedes_iff_coordinates r p).mpr hqp⟩
  · rintro ⟨q, hq, hqp⟩
    exact ⟨coordinates d q, ⟨q, hq, rfl⟩, (precedes_iff_coordinates q p).mp hqp⟩

lemma causalPast_coordinates (K : Set (SpaceTime d)) :
    (coordinates d) ⁻¹' causalPast (coordinates d '' K) = (causalRelation d).causalPast K := by
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hqp⟩
    exact ⟨r, hr, (precedes_iff_coordinates p r).mpr (by simpa [norm_sub_rev] using hqp)⟩
  · rintro ⟨q, hq, hpq⟩
    refine ⟨coordinates d q, ⟨q, hq, rfl⟩, ?_⟩
    simpa [norm_sub_rev] using (precedes_iff_coordinates p q).mp hpq

lemma coordinates_basis_time :
    coordinates d (Lorentz.Vector.basis (Sum.inl 0)) = (1, (0 : Space d)) := by
  simp [coordinates, SpaceTime.toTimeAndSpace_basis_inl]
  rfl

lemma coordinates_basis_space (i : Fin d) :
    coordinates d (Lorentz.Vector.basis (Sum.inr i)) = (0, Space.basis i) := by
  simp [coordinates, SpaceTime.toTimeAndSpace_basis_inr]

omit [CompleteSpace F] in
lemma second_spacetime_deriv (h : SpaceTime d → F) (hh : ContDiff ℝ ∞ h)
    (μ : Fin 1 ⊕ Fin d) (p : SpaceTime d) :
    SpaceTime.deriv μ (SpaceTime.deriv μ h) p =
      iteratedFDeriv ℝ 2 h p ![Lorentz.Vector.basis μ, Lorentz.Vector.basis μ] := by
  rw [iteratedFDeriv_two_apply]
  change (fderiv ℝ (fun q => fderiv ℝ h q (Lorentz.Vector.basis μ)) p)
    (Lorentz.Vector.basis μ) = _
  rw [fderiv_clm_apply (((hh.fderiv_right (m := 1) (by simp)).differentiable (by simp)) p)
    (differentiableAt_const _)]
  simp

omit [CompleteSpace F] in
lemma second_spacetime_deriv_coordinates (g : ℝ × Space d → F) (hg : ContDiff ℝ ∞ g)
    (μ : Fin 1 ⊕ Fin d) (p : SpaceTime d) :
    SpaceTime.deriv μ (SpaceTime.deriv μ (g ∘ coordinates d)) p =
      iteratedFDeriv ℝ 2 g (coordinates d p)
        ![coordinates d (Lorentz.Vector.basis μ), coordinates d (Lorentz.Vector.basis μ)] := by
  rw [second_spacetime_deriv _ (hg.comp (coordinates d).contDiff)]
  change (iteratedFDeriv ℝ 2 (g ∘ (coordinates d).toContinuousLinearMap) p) _ = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (coordinates d).toContinuousLinearMap hg p (by
    simp)]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [CompleteSpace F] in
lemma second_time_slice (g : ℝ × Space d → F) (hg : ContDiff ℝ ∞ g)
    (t : ℝ) (x : Space d) :
    deriv (deriv (fun s => g (s, x))) t =
      iteratedFDeriv ℝ 2 g (t, x) ![(1, 0), (1, 0)] := by
  have he : (fun s => g (s, x)) =
      (fun w : ℝ × Space d => g (w + (0, x))) ∘ (ContinuousLinearMap.inl ℝ ℝ (Space d)) := by
    funext s; simp
  have hd : ContDiff ℝ ∞ (fun w : ℝ × Space d => g (w + (0, x))) :=
    hg.comp (contDiff_id.add contDiff_const)
  have hi : iteratedDeriv 2 (fun s => g (s, x)) t =
      iteratedFDeriv ℝ 2 g (t, x) ![(1, 0), (1, 0)] := by
    rw [iteratedDeriv_eq_iteratedFDeriv, he,
      ContinuousLinearMap.iteratedFDeriv_comp_right _ hd t (by simp), iteratedFDeriv_comp_add_right]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hi

omit [CompleteSpace F] in
lemma second_space_slice (g : ℝ × Space d → F) (hg : ContDiff ℝ ∞ g)
    (t : ℝ) (x b : Space d) :
    iteratedFDeriv ℝ 2 (fun y => g (t, y)) x ![b, b] =
      iteratedFDeriv ℝ 2 g (t, x) ![(0, b), (0, b)] := by
  have he : (fun y => g (t, y)) =
      (fun w : ℝ × Space d => g (w + (t, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ (Space d)) := by
    funext y; simp
  have hd : ContDiff ℝ ∞ (fun w : ℝ × Space d => g (w + (t, 0))) :=
    hg.comp (contDiff_id.add contDiff_const)
  rw [he, ContinuousLinearMap.iteratedFDeriv_comp_right _ hd x (by simp),
    iteratedFDeriv_comp_add_right]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [CompleteSpace F] in
/-- The Minkowski metric trace is the time second derivative minus the spatial Laplacian. -/
lemma waveTrace_coordinates (g : ℝ × Space d → F) (hg : ContDiff ℝ ∞ g) (p : SpaceTime d) :
    (∑ μ : Fin 1 ⊕ Fin d, (minkowskiMatrix μ μ : ℝ) •
      SpaceTime.deriv μ (SpaceTime.deriv μ (g ∘ coordinates d)) p) =
      deriv (deriv (fun s => g (s, (coordinates d p).2))) (coordinates d p).1 -
        (Δ (fun y => g ((coordinates d p).1, y))) (coordinates d p).2 := by
  simp_rw [second_spacetime_deriv_coordinates g hg]
  rw [Fintype.sum_sum_type]
  simp only [Fin.sum_univ_one, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    coordinates_basis_time, coordinates_basis_space, one_smul, neg_one_smul, Finset.sum_neg_distrib]
  rw [second_time_slice g hg,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ Space.basis]
  simp_rw [second_space_slice g hg]
  simp only [Prod.mk.eta, sub_eq_add_neg]

omit [CompleteSpace F] in
/-- The neighbour's Klein–Gordon operator has the Fourier coordinate differential expression. -/
lemma operator_of_coordinates (m : ℝ) (g : ℝ × Space d → F) (hg : ContDiff ℝ ∞ g)
    (p : SpaceTime d) :
    (operator m
      ⟨g ∘ coordinates d, hg.comp (coordinates d).contDiff⟩ : SpaceTime d → F) p =
      deriv (deriv (fun s => g (s, (coordinates d p).2))) (coordinates d p).1 -
        (Δ (fun y => g ((coordinates d p).1, y))) (coordinates d p).2 +
          m ^ 2 • g (coordinates d p) := by
  change (smoothWaveOperator
      ⟨g ∘ coordinates d, hg.comp (coordinates d).contDiff⟩ : SpaceTime d → F) p +
    m ^ 2 • g (coordinates d p) = _
  rw [smoothWaveOperator_coe]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [waveTrace_coordinates g hg p]

omit [CompleteSpace F] in
/-- The transported compact source operator is the existing Minkowski Klein–Gordon operator. -/
lemma sourceOperator_eq_operator (m : ℝ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) (p : SpaceTime d) :
    sourceOperator F (m ^ 2) f p =
      (operator m ⟨f, f.contDiff⟩ : SpaceTime d → F) p := by
  let g := sourceEquiv F f
  have he : (⟨f, f.contDiff⟩ : smoothFields d F) =
      ⟨g ∘ coordinates d, g.contDiff.comp (coordinates d).contDiff⟩ := by
    apply Subtype.ext
    funext q
    change f q = f ((coordinates d).symm (coordinates d q))
    simp
  rw [he, operator_of_coordinates m g g.contDiff p]
  change KleinGordon.testOperator F g (m ^ 2) (coordinates d p) = _
  exact testOperator_apply F g (m ^ 2) _ _
end

end KleinGordon.Spacetime
