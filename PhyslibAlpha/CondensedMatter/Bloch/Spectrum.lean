/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Bloch.RegularRep
public import PhyslibAlpha.ProbabilisticTheory.Representation.Bands
public import Mathlib.Algebra.Order.Chebyshev

/-!

# The spectrum of a translation-invariant operator is the union of the Bloch bands

For the space `ℓ²(G, ℂ^N)`, the spectrum of the operator of a continuous symbol is exactly the union
of the spectra of its values.

## i. Overview

Let `b` be a continuous function from the Brillouin zone `Ĝ` to the `N × N` matrices, and let
`B = ∫ b dP` be the corresponding translation-invariant operator on `ℓ²(G, ℂ^N)`. We showed that
`spec B ⊆ ⋃_χ spec b(χ)`. The converse holds on `ℓ²(G, ℂ^N)`. If `λ` is an eigenvalue of `b(χ₀)`
with eigenvector `e₀`, the state localized at the origin with internal state `e₀` has the uniform
momentum distribution given by Haar measure, so its component in a small neighbourhood `W` of `χ₀`
is nonzero, and on `W` the symbol maps `e₀` to within `δ` of `λ e₀`. These components are
approximate eigenvectors of `B` with eigenvalue `λ`, so `λ` is in the spectrum. Hence
`spec B = ⋃_χ spec b(χ)`: the spectrum of a translation-invariant operator is the union of the
bands.

## ii. Key results

- `RegularRep.norm_sq_calculus_projection_localized` : the norm of a symbol applied to the
  momentum-`W` component of a localized state.
- `RegularRep.spectrum_blochHom` : `spec ∫ b dP = ⋃_χ spec b(χ)`.

## iii. Table of contents

- A. Norms of spectral components of localized states
- B. The spectrum

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

open ProbabilisticTheory ProbabilisticTheory.QuantumMechanics
open MeasureTheory Set
open scoped ComplexOrder InnerProductSpace

namespace Bloch

namespace RegularRep

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [Countable G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]
variable {N : ℕ}

/-! ## A. Norms of spectral components of localized states -/

/-- The norm of a continuous function of the translations applied to the momentum-`W` component of
a localized state: the `L²` norm of the function over `W`, for the Haar measure. -/
lemma norm_sq_calculus_projection_localized (g : C(PontryaginDual (Multiplicative G), ℂ))
    {W : Set (PontryaginDual (Multiplicative G))} (hW : MeasurableSet W)
    (e : EuclideanSpace ℂ (Fin N)) :
    ‖UnitaryRep.calculus (translation G N) g
        (UnitaryRep.projection (translation G N) W (localized e))‖ ^ 2 =
      ‖e‖ ^ 2 * ∫ χ in W, ‖g χ‖ ^ 2 ∂(dualHaar (G := G)) := by
  set P := UnitaryRep.spectralMeasure (translation G N) with hP
  have : Nonempty (PontryaginDual (Multiplicative G)) := ⟨1⟩
  have hbg := WOTSpectralMeasure.bound_of_continuous g
  have hind_meas : Measurable (W.indicator fun _ : PontryaginDual (Multiplicative G) => (1 : ℂ)) :=
    measurable_const.indicator hW
  have hind_bdd : ∃ C, ∀ χ, ‖(W.indicator fun _ : PontryaginDual (Multiplicative G) => (1 : ℂ)) χ‖
      ≤ C := ⟨1, fun χ => by by_cases hχ : χ ∈ W <;> simp [hχ]⟩
  have hprod_meas : Measurable (⇑g * W.indicator fun _ : PontryaginDual (Multiplicative G) =>
      (1 : ℂ)) := g.continuous.measurable.mul hind_meas
  have hprod_bdd : ∃ C, ∀ χ, ‖(⇑g * W.indicator fun _ : PontryaginDual (Multiplicative G) =>
      (1 : ℂ)) χ‖ ≤ C := by
    obtain ⟨C₁, h₁⟩ := hbg
    obtain ⟨C₂, h₂⟩ := hind_bdd
    obtain ⟨z₀⟩ := (inferInstance : Nonempty (PontryaginDual (Multiplicative G)))
    exact ⟨C₁ * C₂, fun z => by
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) ((norm_nonneg _).trans (h₁ z))⟩
  have hmul := P.boundedIntegral_mul g.continuous.measurable hind_meas hbg hind_bdd
  have hind := P.boundedIntegral_indicator hW
  have hnorm := P.boundedIntegral_norm_sq_eq_integral hprod_meas hprod_bdd (localized e)
  have hcalc : (P.boundedIntegral (⇑g * W.indicator fun _ : PontryaginDual (Multiplicative G) =>
      (1 : ℂ)) hprod_meas hprod_bdd) (localized e) =
      UnitaryRep.calculus (translation G N) g
        (UnitaryRep.projection (translation G N) W (localized e)) := by
    have h1 : P.boundedIntegral (⇑g * W.indicator fun _ : PontryaginDual (Multiplicative G) =>
        (1 : ℂ)) hprod_meas hprod_bdd = P.boundedIntegral ⇑g g.continuous.measurable hbg *
        P.boundedIntegral (W.indicator fun _ => (1 : ℂ)) hind_meas hind_bdd := hmul
    rw [h1, hind]
    rfl
  rw [hcalc] at hnorm
  rw [hnorm]
  have hdiag : P.diagonalMeasure (localized e) =
      ENNReal.ofReal (‖e‖ ^ 2) • dualHaar (G := G) := vectorMeasure_localized e
  rw [hdiag, integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  congr 1
  rw [← integral_indicator hW]
  congr 1
  funext χ
  by_cases hχ : χ ∈ W <;> simp [hχ]

/-- The matrix unit `E_{ij}` acts on a vector as the `j`-th coordinate carried to the `i`-th. -/
lemma toEuclideanCLM_single_apply (i j : Fin N) (e : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (Matrix.single i j (1 : ℂ)) e =
      e j • EuclideanSpace.single i (1 : ℂ) := by
  have hv : e = WithLp.toLp 2 e.ofLp := rfl
  conv_lhs => rw [hv, Matrix.toEuclideanCLM_toLp]
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.single, PiLp.single_apply]
  by_cases h : i = k
  · subst h; simp [Finset.sum_ite_eq]
  · simp [h, Ne.symm h]

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [Countable G] in
omit [TopologicalSpace G] in
/-- The internal matrix unit `E_{ij}` acts on a localized state by moving the `j`-th component
to the `i`-th.   -/
lemma internal_single_localized (i j : Fin N) (e : EuclideanSpace ℂ (Fin N)) :
    internal (G := G) (Matrix.single i j (1 : ℂ)) (localized e) =
      e j • localized (EuclideanSpace.single i (1 : ℂ)) := by
  show pointwise G N _ (localized e) = _
  rw [pointwise_localized, toEuclideanCLM_single_apply, localized_smul]

/-- The translation-invariant operator `∫ f dP` of a symbol `f` on `ℓ²(G, ℂ^N)`. -/
abbrev blochOperator (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    Space G N →L[ℂ] Space G N :=
  UnitaryRep.blochHom (translation G N) internal (fun M g => commute_translation_internal g M) f

/-- The internal matrix units commute with the spectral projections. -/
lemma commute_projection_internal (W : Set (PontryaginDual (Multiplicative G)))
    (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute (UnitaryRep.projection (translation G N) W) (internal (G := G) M) :=
  UnitaryRep.projection_commute (translation G N)
    (fun g => commute_translation_internal g M) W

/-- **Action of a symbol on a spectral component of a localized state**: the operator of a symbol
`f` applied to the momentum-`W` component of the state localized at the origin with internal state
`e` is the sum over the internal indices `i` of functions of the translations applied to the
momentum-`W` component of the state localized in the `i`-th internal state. -/
lemma blochOperator_projection_localized
    (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (W : Set (PontryaginDual (Multiplicative G))) (e : EuclideanSpace ℂ (Fin N)) :
    blochOperator f (UnitaryRep.projection (translation G N) W (localized e)) =
      ∑ i, UnitaryRep.calculus (translation G N) (∑ j, e j • UnitaryRep.entry f i j)
        (UnitaryRep.projection (translation G N) W
          (localized (EuclideanSpace.single i (1 : ℂ)))) := by
  show UnitaryRep.blochOp (translation G N) internal f _ = _
  simp only [UnitaryRep.blochOp, sum_apply, mul_apply_eq_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, internal (G := G) (Matrix.single i j (1 : ℂ))
      (UnitaryRep.projection (translation G N) W (localized e)) =
      e j • UnitaryRep.projection (translation G N) W
        (localized (EuclideanSpace.single i (1 : ℂ))) := by
    intro j
    have hc := (commute_projection_internal (G := G) (N := N) W (Matrix.single i j (1 : ℂ))).eq
    calc internal (G := G) (Matrix.single i j (1 : ℂ))
          (UnitaryRep.projection (translation G N) W (localized e))
        = (internal (G := G) (Matrix.single i j (1 : ℂ)) *
            UnitaryRep.projection (translation G N) W) (localized e) := rfl
      _ = (UnitaryRep.projection (translation G N) W *
            internal (G := G) (Matrix.single i j (1 : ℂ))) (localized e) := by rw [hc]
      _ = UnitaryRep.projection (translation G N) W
            (internal (G := G) (Matrix.single i j (1 : ℂ)) (localized e)) := rfl
      _ = _ := by rw [internal_single_localized, map_smul]
  simp only [h, map_smul, map_sum, sum_apply, smul_apply]

omit [MeasurableSingletonClass G] in
omit [Countable G] in
omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace G] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
/-- The `i`-th component of a symbol applied to a vector is the combination of its entries. -/
lemma entry_combination_apply
    (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (e : EuclideanSpace ℂ (Fin N)) (i : Fin N) (χ : PontryaginDual (Multiplicative G)) :
    (∑ j, e j • UnitaryRep.entry f i j) χ =
      (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ) e) i := by
  have hv : e = WithLp.toLp 2 e.ofLp := rfl
  rw [hv, Matrix.toEuclideanCLM_toLp]
  simp [Matrix.mulVec, dotProduct, UnitaryRep.entry, mul_comm]

omit [MeasurableSingletonClass G] in
omit [Countable G] in
omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace G] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma sum_norm_entry_combination
    (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (e : EuclideanSpace ℂ (Fin N)) (χ : PontryaginDual (Multiplicative G)) :
    ∑ i, ‖(∑ j, e j • UnitaryRep.entry f i j) χ‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ) e‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [entry_combination_apply]

/-- **The symbol acts on spectral components of a localized state with the size of the symbol on
those momenta**: if the symbol moves the internal state `e` by at most `δ` at all crystal momenta
in `W`, then the operator of the symbol moves the momentum-`W` component of the localized state by
at most `√N δ` times its norm, up to the norm of `e`. -/
lemma norm_blochOperator_projection_localized_le
    (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    {W : Set (PontryaginDual (Multiplicative G))} (hW : MeasurableSet W)
    (e : EuclideanSpace ℂ (Fin N)) {δ : ℝ}
    (hδ : ∀ χ ∈ W, ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ) e‖ ≤ δ) :
    ‖blochOperator f (UnitaryRep.projection (translation G N) W (localized e))‖ ^ 2 ≤
      N * δ ^ 2 * (dualHaar (G := G)).real W := by
  rw [blochOperator_projection_localized]
  set y : Fin N → Space G N := fun i => UnitaryRep.calculus (translation G N)
    (∑ j, e j • UnitaryRep.entry f i j)
    (UnitaryRep.projection (translation G N) W (localized (EuclideanSpace.single i (1 : ℂ))))
    with hy
  have hyi : ∀ i, ‖y i‖ ^ 2 = ∫ χ in W, ‖(∑ j, e j • UnitaryRep.entry f i j) χ‖ ^ 2
      ∂(dualHaar (G := G)) := by
    intro i
    rw [hy]
    simp only
    rw [norm_sq_calculus_projection_localized _ hW]
    simp
  calc ‖∑ i, y i‖ ^ 2 ≤ (∑ i, ‖y i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ N * ∑ i, ‖y i‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
          (f := fun i => ‖y i‖)
        simpa using this
    _ = N * ∫ χ in W, ∑ i, ‖(∑ j, e j • UnitaryRep.entry f i j) χ‖ ^ 2 ∂(dualHaar (G := G)) := by
        rw [integral_finsetSum]
        · simp only [hyi]
        · intro i _
          exact (((∑ j, e j • UnitaryRep.entry f i j).continuous.norm.pow 2
            ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
    _ ≤ N * (δ ^ 2 * (dualHaar (G := G)).real W) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
        have hint : IntegrableOn (fun χ => ∑ i, ‖(∑ j, e j • UnitaryRep.entry f i j) χ‖ ^ 2) W
            (dualHaar (G := G)) := by
          refine Integrable.integrableOn ?_
          refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
          exact continuous_finsetSum _ fun i _ =>
            ((∑ j, e j • UnitaryRep.entry f i j).continuous.norm.pow 2)
        calc ∫ χ in W, ∑ i, ‖(∑ j, e j • UnitaryRep.entry f i j) χ‖ ^ 2 ∂(dualHaar (G := G))
            ≤ ∫ χ in W, δ ^ 2 ∂(dualHaar (G := G)) := by
              refine setIntegral_mono_on hint (integrableOn_const (by simp)) hW fun χ hχ => ?_
              rw [sum_norm_entry_combination]
              exact pow_le_pow_left₀ (norm_nonneg _) (hδ χ hχ) 2
          _ = δ ^ 2 * (dualHaar (G := G)).real W := by
              rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = _ := by ring

/-- The squared norm of the momentum-`W` component of a localized state. -/
lemma norm_sq_projection_localized {W : Set (PontryaginDual (Multiplicative G))}
    (hW : MeasurableSet W) (e : EuclideanSpace ℂ (Fin N)) :
    ‖UnitaryRep.projection (translation G N) W (localized e)‖ ^ 2 =
      ‖e‖ ^ 2 * (dualHaar (G := G)).real W := by
  have h := UnitaryRep.vectorMeasure_apply (translation G N) (localized e) hW
  rw [vectorMeasure_localized] at h
  have h' : ‖UnitaryRep.projection (translation G N) W (localized e)‖ ^ 2 =
      ((ENNReal.ofReal (‖e‖ ^ 2) • dualHaar (G := G)) W).toReal := by
    have := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (sq_nonneg _)] at this
    exact this.symm
  rw [h']
  simp [Measure.smul_apply, ENNReal.toReal_mul,
    Measure.real]

/-! ## B. The spectrum -/

open scoped Matrix.Norms.Operator in
/-- **The spectrum of a translation-invariant operator is the union of its Bloch bands.** For
every continuous symbol `b` on the Brillouin zone, the spectrum of the operator `∫ b dP` on
`ℓ²(G, ℂ^N)` is the union over crystal momenta `χ` of the spectra of the matrices `b(χ)`. -/
lemma spectrum_blochOperator
    (b : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    spectrum ℂ (blochOperator b) =
      ⋃ χ : PontryaginDual (Multiplicative G), spectrum ℂ (b χ) := by
  refine Set.Subset.antisymm (UnitaryRep.spectrum_blochHom_subset _ _ _ b) ?_
  intro z hz
  obtain ⟨χ₀, hχ₀⟩ := Set.mem_iUnion.mp hz
  by_contra hzB
  rw [spectrum.mem_iff, not_not] at hzB
  obtain ⟨u, hu⟩ := hzB
  set f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ) :=
    algebraMap ℂ C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ) z - b with hf
  have hfop : blochOperator f = (u : Space G N →L[ℂ] Space G N) := by
    rw [hu, hf]
    show UnitaryRep.blochHom _ _ _ (algebraMap _ _ z - b) = _
    rw [map_sub, AlgHomClass.commutes]
  -- an eigenvector of the symbol at `χ₀`
  rw [spectrum.mem_iff] at hχ₀
  have hdet : (algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) z - b χ₀).det = 0 := by
    by_contra hne
    exact hχ₀ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set e : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 v with he
  have he0 : e ≠ 0 := fun h => hv0 (by simpa [he] using congrArg WithLp.ofLp h)
  have hfχ₀ : Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ₀) e = 0 := by
    have hfm : f χ₀ = algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) z - b χ₀ := rfl
    rw [he, Matrix.toEuclideanCLM_toLp, hfm, hv]
    rfl
  have hcont : Continuous fun χ => ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ) e‖ := by
    have h2 : (fun χ => ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ) e‖) =
        fun χ => ‖WithLp.toLp 2 (Matrix.mulVec (f χ) v)‖ := by
      funext χ; rw [he, Matrix.toEuclideanCLM_toLp]
    rw [h2]
    exact ((PiLp.continuous_toLp 2 _).comp (f.continuous.matrix_mulVec continuous_const)).norm
  set R : Space G N →L[ℂ] Space G N := ((u⁻¹ : (Space G N →L[ℂ] Space G N)ˣ) :
    Space G N →L[ℂ] Space G N) with hR
  have key : ∀ δ : ℝ, 0 < δ → ‖e‖ ^ 2 ≤ ‖R‖ ^ 2 * N * δ ^ 2 := by
    intro δ hδ
    set W : Set (PontryaginDual (Multiplicative G)) :=
      {χ | ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (f χ) e‖ < δ} with hW
    have hWo : IsOpen W := isOpen_lt hcont continuous_const
    have hχW : χ₀ ∈ W := by simp [hW, hfχ₀, hδ]
    have hxne := projection_localized_ne_zero hWo ⟨χ₀, hχW⟩ he0
    have hT := norm_blochOperator_projection_localized_le f hWo.measurableSet e
      (δ := δ) (fun χ hχ => le_of_lt hχ)
    rw [hfop] at hT
    have hx2 := norm_sq_projection_localized hWo.measurableSet e
    set x := UnitaryRep.projection (translation G N) W (localized e) with hx
    set h := (dualHaar (G := G)).real W with hh
    have hRu : R * (u : Space G N →L[ℂ] Space G N) = 1 := by rw [hR]; exact u.inv_mul
    have hRx : ‖x‖ ≤ ‖R‖ * ‖(u : Space G N →L[ℂ] Space G N) x‖ := by
      calc ‖x‖ = ‖(R * (u : Space G N →L[ℂ] Space G N)) x‖ := by rw [hRu]; simp
        _ ≤ ‖R‖ * ‖(u : Space G N →L[ℂ] Space G N) x‖ := by
          rw [mul_apply_eq_comp]; exact R.le_opNorm _
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hh0 : 0 ≤ h := measureReal_nonneg
    have hhpos : 0 < h := by
      by_contra hneg
      have : h = 0 := le_antisymm (not_lt.mp hneg) hh0
      rw [this, mul_zero] at hx2
      nlinarith
    have h1 : ‖x‖ ^ 2 ≤ ‖R‖ ^ 2 * ‖(u : Space G N →L[ℂ] Space G N) x‖ ^ 2 := by
      calc ‖x‖ ^ 2 ≤ (‖R‖ * ‖(u : Space G N →L[ℂ] Space G N) x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hRx 2
        _ = _ := by ring
    have h2 : ‖e‖ ^ 2 * h ≤ ‖R‖ ^ 2 * (N * δ ^ 2 * h) := by
      calc ‖e‖ ^ 2 * h = ‖x‖ ^ 2 := hx2.symm
        _ ≤ ‖R‖ ^ 2 * ‖(u : Space G N →L[ℂ] Space G N) x‖ ^ 2 := h1
        _ ≤ ‖R‖ ^ 2 * (N * δ ^ 2 * h) :=
            mul_le_mul_of_nonneg_left hT (sq_nonneg _)
    have h3 : ‖e‖ ^ 2 * h ≤ (‖R‖ ^ 2 * N * δ ^ 2) * h := by nlinarith [h2]
    exact le_of_mul_le_mul_right h3 hhpos
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he0
  set δ : ℝ := ‖e‖ / (2 * (‖R‖ + 1) * (N + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hk := key δ hδpos
  have hRn : 0 ≤ ‖R‖ := norm_nonneg _
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδ' : δ * (‖R‖ + 1) = ‖e‖ / (2 * (N + 1)) := by rw [hδ]; field_simp
  have hA : ‖R‖ * δ ≤ ‖e‖ / (2 * (N + 1)) := by nlinarith [hδ', hδpos]
  have hB : (‖R‖ * δ) ^ 2 * N ≤ ‖e‖ ^ 2 / 4 := by
    calc (‖R‖ * δ) ^ 2 * N ≤ (‖e‖ / (2 * (N + 1))) ^ 2 * N :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hA 2) hNn
      _ ≤ ‖e‖ ^ 2 / 4 := by
          rw [div_pow]
          have hN1 : (0 : ℝ) < N + 1 := by positivity
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [sq_nonneg ‖e‖, mul_nonneg (sq_nonneg ‖e‖) hNn, mul_nonneg (sq_nonneg ‖e‖)
            (sq_nonneg (N : ℝ))]
  nlinarith [hk, hB, sq_nonneg ‖e‖]

/-- **The band structure**: for a Hermitian symbol, the spectrum of the translation-invariant
operator on `ℓ²(G, ℂ^N)` is exactly the set of band values `ε_k(χ)`, the ordered eigenvalues of the
Bloch matrices.   -/
lemma spectrum_blochOperator_eq_bands
    (b : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (hb : ∀ χ, (b χ).IsHermitian) :
    spectrum ℂ (blochOperator b) =
      {z | ∃ (χ : PontryaginDual (Multiplicative G)) (k : Fin (Fintype.card (Fin N))),
        z = ((bandOf (hb χ) k : ℝ) : ℂ)} := by
  rw [spectrum_blochOperator]
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨χ, hχ⟩
    rw [(hb χ).spectrum_eq_image_range] at hχ
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hχ
    exact ⟨χ, (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i, rfl⟩
  · rintro ⟨χ, k, rfl⟩
    refine ⟨χ, ?_⟩
    rw [(hb χ).spectrum_eq_image_range]
    refine ⟨(hb χ).eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) k), ⟨_, rfl⟩, ?_⟩
    simp [bandOf, Matrix.IsHermitian.eigenvalues]

end RegularRep

end Bloch

end CondensedMatter

end
