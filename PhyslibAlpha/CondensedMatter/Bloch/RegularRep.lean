/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Koopman
public import PhyslibAlpha.ProbabilisticTheory.Representation.Orthogonality
public import PhyslibAlpha.ProbabilisticTheory.Representation.Floquet
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!

# The space of wavefunctions on a lattice with internal states

`ℓ²(G, ℂ^N)` with its translation representation and its internal matrix algebra.

## i. Overview

The Hilbert space `ℓ²(G, ℂ^N)` of square-summable functions on a countable abelian group `G` with
values in `ℂ^N` carries two commuting structures: the translations `(U_g ψ)(x) = ψ(x - g)`, a
unitary representation of `G`, and the pointwise action of the matrices `M_N(ℂ)` on the internal
index. This is the setting of band theory: `G` is the lattice of translations of a crystal, and `N`
the number of internal states per primitive cell. The space is realized as `L²` of the counting
measure so that the Koopman representation of the translation action applies.

## ii. Key results

- `RegularRep.translation` : the translation representation on `ℓ²(G, ℂ^N)`.
- `RegularRep.internal` : the internal ⋆-homomorphism `M_N(ℂ) → B(ℓ²)`.
- `RegularRep.commute` : the translations commute with the internal algebra.

## iii. Table of contents

- A. Counting measure and translations
- B. The internal algebra
- C. The translation commutes with the internal algebra
- D. Localized states and their momentum distribution
- E. The momentum distribution of localized states

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
  [Countable G]

/-! ## A. Counting measure and translations -/

/-- Translation of a discrete group preserves the counting measure. -/
lemma measurePreserving_addRight (g : G) :
    MeasurePreserving (fun x : G => x + g) (Measure.count : Measure G) Measure.count := by
  refine ⟨measurable_of_countable _, ?_⟩
  have h1 : (Measure.count : Measure G).map (fun x : G => x + g) ≤ Measure.count :=
    (add_left_injective g).map_count_le (measurable_of_countable _)
  have h2 : (Measure.count : Measure G).map (fun x : G => x - g) ≤ Measure.count :=
    (sub_left_injective (b := g)).map_count_le (measurable_of_countable _)
  refine le_antisymm h1 ?_
  calc (Measure.count : Measure G)
      = ((Measure.count : Measure G).map (fun x : G => x - g)).map (fun x : G => x + g) := by
        rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
        have : (fun x : G => x + g) ∘ (fun x : G => x - g) = id := by
          funext x; simp
        rw [this, Measure.map_id]
    _ ≤ (Measure.count : Measure G).map (fun x : G => x + g) :=
        Measure.map_mono h2 (measurable_of_countable _)

/-- Translation by `a`, as a permutation of the group. -/
def shift (a : G) : Equiv.Perm G where
  toFun x := x + a
  invFun x := x - a
  left_inv x := by simp
  right_inv x := by simp

/-- The translation action of the group on itself, as permutations. -/
def translations : Multiplicative G →* Equiv.Perm G where
  toFun g := shift (Multiplicative.toAdd g)
  map_one' := by ext x; simp [shift]
  map_mul' g h := by
    ext x
    simp only [shift, Equiv.Perm.mul_apply, Equiv.coe_fn_mk, toAdd_mul]
    abel

lemma measurePreserving_translations (g : Multiplicative G) :
    MeasurePreserving (translations g) (Measure.count : Measure G) Measure.count :=
  measurePreserving_addRight _

variable (G) (N : ℕ)

/-- The Hilbert space `ℓ²(G, ℂ^N)` of square-summable functions on `G` with values in the internal
space `ℂ^N`, as `L²` of the counting measure. -/
abbrev Space := Lp (EuclideanSpace ℂ (Fin N)) 2 (Measure.count : Measure G)

/-- **The translation representation** on `ℓ²(G, ℂ^N)`: `(U_g ψ)(x) = ψ(x - g)`. -/
def translation : Multiplicative G →* unitary (Space G N →L[ℂ] Space G N) :=
  UnitaryRep.koopman (E := EuclideanSpace ℂ
    (Fin N)) Measure.count translations measurePreserving_translations

/-! ## B. The internal algebra -/

variable {G N}

variable (G N) in
/-- Pointwise action of an operator of the internal space on `ℓ²(G, ℂ^N)`. -/
abbrev pointwise (L : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    Space G N →L[ℂ] Space G N :=
  L.compLpL 2 (Measure.count : Measure G)

omit [AddCommGroup G] [MeasurableSingletonClass G] [Countable G] in
lemma pointwise_apply_ae (L : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (f : Space G N) : pointwise G N L f =ᵐ[Measure.count] fun x => L (f x) :=
  ContinuousLinearMap.coeFn_compLpL L f

omit [AddCommGroup G] [MeasurableSingletonClass G] [Countable G] in
lemma pointwise_mul (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    pointwise G N (A * B) = pointwise G N A * pointwise G N B := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [pointwise_apply_ae (G := G) (A * B) f,
    pointwise_apply_ae (G := G) A (pointwise G N B f), pointwise_apply_ae (G := G) B f]
    with x h1 h2 h3
  rw [h1, mul_apply_eq_comp]
  change _ = ((pointwise G N A) ((pointwise G N B) f)) x
  rw [h2, h3]

omit [AddCommGroup G] [MeasurableSingletonClass G] [Countable G] in
lemma pointwise_one : pointwise G N (1 : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) =
    1 := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [pointwise_apply_ae (G := G) (1 : EuclideanSpace ℂ (Fin N) →L[ℂ]
    EuclideanSpace ℂ (Fin N)) f] with x h1
  rw [h1]
  rfl

omit [AddCommGroup G] [MeasurableSingletonClass G] [Countable G] in
lemma pointwise_star (L : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    pointwise G N (star L) = star (pointwise G N L) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [pointwise_apply_ae (G := G) (ContinuousLinearMap.adjoint L) f,
    pointwise_apply_ae (G := G) L g] with x h1 h2
  rw [h1, h2]
  exact ContinuousLinearMap.adjoint_inner_left L (g x) (f x)

/-- **The internal algebra**: a matrix acts on the internal index of a wavefunction, pointwise. -/
def internal : Matrix (Fin N) (Fin N) ℂ →⋆ₐ[ℂ] (Space G N →L[ℂ] Space G N) where
  toFun M := pointwise G N (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M)
  map_one' := by rw [map_one, pointwise_one]
  map_mul' A B := by rw [map_mul, pointwise_mul]
  map_zero' := by
    rw [map_zero]
    ext f : 1
    refine Lp.ext ?_
    show (pointwise G N 0 f : G → EuclideanSpace ℂ (Fin N)) =ᵐ[Measure.count]
      ((0 : Space G N) : G → EuclideanSpace ℂ (Fin N))
    filter_upwards [pointwise_apply_ae (G := G) (0 : EuclideanSpace ℂ (Fin N) →L[ℂ]
        EuclideanSpace ℂ (Fin N)) f, Lp.coeFn_zero (EuclideanSpace ℂ (Fin N)) 2
          (Measure.count : Measure G)] with x h1 h2
    rw [h1, h2]
    rfl
  map_add' A B := by
    rw [map_add]
    exact ContinuousLinearMap.add_compLpL _ _
  commutes' c := by
    have h := AlgHomClass.commutes (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) c
    show pointwise G N (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)
      (algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) c)) = _
    rw [h, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (ContinuousLinearMap.smul_compLpL c 1).trans (congrArg (c • ·) (pointwise_one (G := G)
      (N := N)))
  map_star' M := by
    rw [map_star, pointwise_star]

/-! ## C. The translation commutes with the internal algebra -/

lemma translation_apply (g : Multiplicative G) (f : Space G N) :
    ((translation G N g : unitary (Space G N →L[ℂ] Space G N)) : Space G N →L[ℂ] Space G N) f =
      Lp.compMeasurePreserving (translations g⁻¹) (measurePreserving_translations g⁻¹) f :=
  rfl

/-- The translations commute with the internal algebra: the matrices act on the internal index and
the translations move the site. -/
lemma commute_translation_internal (g : Multiplicative G) (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute ((translation G N g : unitary (Space G N →L[ℂ] Space G N)) :
      Space G N →L[ℂ] Space G N) (internal M) := by
  set L := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M with hL
  show _ * pointwise G N L = pointwise G N L * _
  ext f : 1
  refine Lp.ext ?_
  have hT := measurePreserving_translations (G := G) g⁻¹
  have h1 := Lp.coeFn_compMeasurePreserving (pointwise G N L f) hT
  have h2 := hT.quasiMeasurePreserving.ae_eq_comp (pointwise_apply_ae (G := G) L f)
  have h3 := pointwise_apply_ae (G := G) L
    (Lp.compMeasurePreserving (translations g⁻¹) hT f)
  have h4 := Lp.coeFn_compMeasurePreserving f hT
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  change (Lp.compMeasurePreserving (translations g⁻¹) hT (pointwise G N L f)) x = _
  rw [e1]
  change (pointwise G N L f) (translations g⁻¹ x) = (pointwise G N L (Lp.compMeasurePreserving
    (translations g⁻¹) hT f)) x
  rw [e3, e4]
  exact e2

/-! ## D. Localized states and their momentum distribution -/

/-- The state localized at the origin with internal state `e`. -/
def localized (e : EuclideanSpace ℂ (Fin N)) : Space G N :=
  indicatorConstLp 2 (measurableSet_singleton (0 : G)) (by simp) e

lemma count_preimage_ne_top (g : Multiplicative G) :
    (Measure.count : Measure G) ((translations g⁻¹) ⁻¹' {(0 : G)}) ≠ ⊤ := by
  rw [(measurePreserving_translations g⁻¹).measure_preimage
    (measurableSet_singleton (0 : G)).nullMeasurableSet]
  simp

/-- Translating a localized state moves it to the translated site. -/
lemma translation_localized (g : Multiplicative G) (e : EuclideanSpace ℂ (Fin N)) :
    ((translation G N g : unitary (Space G N →L[ℂ] Space G N)) : Space G N →L[ℂ] Space G N)
        (localized e) =
      indicatorConstLp 2 ((measurableSet_singleton (0 : G)).preimage
        (measurable_of_countable (translations g⁻¹))) (count_preimage_ne_top g) e :=
  rfl

open scoped Classical in
/-- **The matrix coefficients of a localized state are the Kronecker delta.** -/
lemma inner_localized_translation (g : Multiplicative G) (e e' : EuclideanSpace ℂ (Fin N)) :
    ⟪localized (G := G) e, ((translation G N g : unitary (Space G N →L[ℂ] Space G N)) :
      Space G N →L[ℂ] Space G N) (localized e')⟫_ℂ = if g = 1 then ⟪e, e'⟫_ℂ else 0 := by
  rw [translation_localized, localized,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_singleton (0 : G))
      ((measurableSet_singleton (0 : G)).preimage
        (measurable_of_countable (translations g⁻¹))) (by simp) (count_preimage_ne_top g)]
  by_cases hg : g = 1
  · subst hg
    have : ({(0 : G)} ∩ (translations (1 : Multiplicative G)⁻¹) ⁻¹' {(0 : G)}) = {0} := by
      ext x; simp [translations, shift]
    rw [this]
    simp
  · have : ({(0 : G)} ∩ (translations g⁻¹) ⁻¹' {(0 : G)}) = ∅ := by
      ext x
      simp only [translations, shift, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_preimage,
        MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, toAdd_inv, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl h
      apply hg
      have : Multiplicative.toAdd g = 0 := by simpa using h
      exact toAdd_eq_zero.mp this
    rw [this]
    simp [hg]

omit [Countable G] in
lemma pointwise_localized (L : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (e : EuclideanSpace ℂ (Fin N)) : pointwise G N L (localized e) = localized (L e) := by
  refine Lp.ext ?_
  filter_upwards [pointwise_apply_ae (G := G) L (localized e),
    indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := e),
    indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := L e)] with x h1 h2 h3
  rw [h1]
  change L ((indicatorConstLp 2 _ _ e : Space G N) x) = (indicatorConstLp 2 _ _ (L e) : Space G N) x
  rw [h2, h3]
  by_cases hx : x ∈ ({(0 : G)} : Set G) <;> simp [hx]

omit [Countable G] in
lemma localized_add (e e' : EuclideanSpace ℂ (Fin N)) :
    localized (G := G) (e + e') = localized e + localized e' := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := e + e'),
    indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := e),
    indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := e'),
    Lp.coeFn_add (localized (G := G) e) (localized e')] with x h1 h2 h3 h4
  rw [h4]
  change (indicatorConstLp 2 _ _ (e + e') : Space G N) x = _
  simp only [Pi.add_apply]
  change (indicatorConstLp 2 _ _ (e + e') : Space G N) x =
    (indicatorConstLp 2 _ _ e : Space G N) x + (indicatorConstLp 2 _ _ e' : Space G N) x
  rw [h1, h2, h3]
  by_cases hx : x ∈ ({(0 : G)} : Set G) <;> simp [hx]

omit [Countable G] in
lemma localized_smul (c : ℂ) (e : EuclideanSpace ℂ (Fin N)) :
    localized (G := G) (c • e) = c • localized e := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := c • e),
    indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure G))
      (hs := measurableSet_singleton (0 : G)) (hμs := by simp) (c := e),
    Lp.coeFn_smul c (localized (G := G) e)] with x h1 h2 h3
  rw [h3]
  change (indicatorConstLp 2 _ _ (c • e) : Space G N) x = c •
    (indicatorConstLp 2 _ _ e : Space G N) x
  rw [h1, h2]
  by_cases hx : x ∈ ({(0 : G)} : Set G) <;> simp [hx]

/-! ## E. The momentum distribution of localized states -/

section Momentum

variable [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- **A localized state has a uniform momentum distribution**: its spectral measure for the
translations is the Haar measure of the dual group, weighted by the squared norm of the internal
state. -/
lemma vectorMeasure_localized (e : EuclideanSpace ℂ (Fin N)) :
    UnitaryRep.vectorMeasure (translation G N) (localized e) =
      ENNReal.ofReal (‖e‖ ^ 2) • dualHaar (G := G) := by
  symm
  have : IsFiniteMeasure (ENNReal.ofReal (‖e‖ ^ 2) • dualHaar (G := G)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  refine UnitaryRep.eq_vectorMeasure_of_transform_eq (translation G N) (localized e) _ ?_
  intro g
  have horth := integral_character_dualHaar (G := G) (Multiplicative.toAdd g)
  simp only [ofAdd_toAdd] at horth
  rw [integral_smul_measure, horth]
  have := inner_localized_translation (G := G) g e e
  rw [this]
  by_cases hg : g = 1
  · subst hg
    simp [inner_self_eq_norm_sq_to_K]
  · have hg' : Multiplicative.toAdd g ≠ 0 := fun h => hg (toAdd_eq_zero.mp h)
    simp [hg, hg']

/-- The spectral projection of a nonempty open set of crystal momenta does not annihilate a
localized state of nonzero internal state. -/
lemma projection_localized_ne_zero {U : Set (PontryaginDual (Multiplicative G))}
    (hU : IsOpen U) (hne : U.Nonempty) {e : EuclideanSpace ℂ (Fin N)} (he : e ≠ 0) :
    UnitaryRep.projection (translation G N) U (localized e) ≠ 0 := by
  intro h0
  have hν := UnitaryRep.vectorMeasure_apply (translation G N) (localized e) hU.measurableSet
  have h1 : UnitaryRep.spectralMeasure (translation G N) U (localized e) = 0 := h0
  rw [h1, vectorMeasure_localized] at hν
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    ENNReal.ofReal_zero, Measure.smul_apply, smul_eq_mul] at hν
  have hpos : 0 < dualHaar (G := G) U := hU.measure_pos _ hne
  have hnorm : 0 < ENNReal.ofReal (‖e‖ ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
  exact (ENNReal.mul_pos hnorm.ne' hpos.ne').ne' hν

/-- **The regular representation has full support**: every crystal momentum occurs in every
internal state. -/
lemma hasFullSupport :
    UnitaryRep.HasFullSupport (translation G N) (internal (G := G) (N := N)) := by
  intro U hU hne i hzero
  set e : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single i (1 : ℂ) with he
  have hint : internal (G := G) (N := N) (Matrix.single i i (1 : ℂ)) (localized e) =
      localized e := by
    show pointwise G N _ (localized e) = _
    rw [pointwise_localized]
    congr 1
    have hv : EuclideanSpace.single i (1 : ℂ) = WithLp.toLp 2 (Pi.single i (1 : ℂ)) := by
      ext j; simp [PiLp.single_apply, Pi.single_apply]
    show (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (Matrix.single i i (1 : ℂ))) e = e
    rw [he, hv, Matrix.toEuclideanCLM_toLp]
    congr 1
    ext j
    simp [Matrix.col, Matrix.single, Pi.single_apply, eq_comm]
  have := congrArg (fun A : Space G N →L[ℂ] Space G N => A (localized e)) hzero
  simp only [mul_apply_eq_comp, hint, zero_apply] at this
  exact projection_localized_ne_zero hU hne (by simp [he]) this

end Momentum

end RegularRep

end Bloch

end CondensedMatter

end
