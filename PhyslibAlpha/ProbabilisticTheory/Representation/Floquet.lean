/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Commutant
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.ContinuousCalculus
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!

# Bloch–Floquet theory for representations with a finite-dimensional internal space

Operators built from a unitary representation of an abelian group and an internal matrix algebra
are integrals of a matrix-valued symbol over the dual group.

## i. Overview

Let `π` be a unitary representation of a discrete abelian group `G` on a Hilbert space `H`, and let
`ι : M_N(ℂ) → B(H)` be a ⋆-homomorphism commuting with `π`: an `N`-dimensional internal space
attached to every point. Nothing is assumed about what `H` describes. It may carry the
wavefunctions of a quantum particle, the displacement fields of a classical lattice, or an
`L²` space of a classical statistical ensemble. The spectral measure `P` of `π` turns every
continuous matrix-valued function `f` on the dual group `Ĝ` into the operator
`∫ f dP = ∑_{ij} (∫ f_{ij} dP) ι(E_{ij})`, and this is a unital ⋆-homomorphism from `C(Ĝ, M_N)`
to `B(H)`. Operators commuting with `π` and `ι` that arise this way are the translation-invariant
operators with symbol `f`. Consequently the spectrum of the operator of a symbol is contained in the
union of the spectra of the matrices `f(χ)`: the spectrum is the union of the bands. Under full
support of the representation the map is injective.

## ii. Key results

- `UnitaryRep.calculus` : the functional calculus `f ↦ ∫ f dP` of a representation.
- `UnitaryRep.blochHom` : the ⋆-homomorphism `f ↦ ∫ f dP` on matrix-valued continuous functions.
- `UnitaryRep.spectrum_blochHom_subset` : the spectrum of the operator of a symbol is contained in
  the union of the spectra of the values of the symbol.
- `UnitaryRep.blochHom_injective` : the map is injective for a representation of full support.

## iii. Table of contents

- A. The functional calculus of the representation
- B. Matrix-valued functions
- C. The spectrum
- D. Faithful representations

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology WeakDual
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : Multiplicative G →* unitary (H →L[ℂ] H))
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

instance : Nonempty (PontryaginDual (Multiplicative G)) := ⟨1⟩

/-! ## A. The functional calculus of the representation -/

/-- **The functional calculus of a unitary representation**: `f ↦ ∫ f dP` is a unital
⋆-homomorphism from the continuous functions on the Pontryagin dual to the bounded operators. -/
def calculus : C(PontryaginDual (Multiplicative G), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (spectralMeasure π).continuousCalculus

/-- The functional calculus sends the character `χ ↦ χ(g)` to the operator `π(g)`. -/
lemma calculus_character (g : Multiplicative G) :
    calculus π ⟨fun χ => ((χ g : Circle) : ℂ),
      (TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G) g)⟩ =
      ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) :=
  boundedIntegral_character π g

/-- An operator commuting with the representation commutes with its functional calculus. -/
lemma calculus_commute {T : H →L[ℂ] H}
    (hT : ∀ g, Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) T)
    (f : C(PontryaginDual (Multiplicative G), ℂ)) : Commute (calculus π f) T := by
  have hTS : ∀ S : Set (PontryaginDual (Multiplicative G)),
      spectralMeasure π S * ContinuousLinearMapWOT.ofCLM T =
        ContinuousLinearMapWOT.ofCLM T * spectralMeasure π S := by
    intro S
    apply ContinuousLinearMapWOT.toCLM_injective
    rw [ContinuousLinearMapWOT.toCLM_mul, ContinuousLinearMapWOT.toCLM_mul,
      ContinuousLinearMapWOT.toCLM_ofCLM]
    exact (projection_commute π hT S).eq
  exact WOTSpectralMeasure.boundedIntegral_commute (spectralMeasure π) hTS
    f.continuous.measurable (WOTSpectralMeasure.bound_of_continuous f)

/-! ## B. Matrix-valued functions -/

variable {N : ℕ} (ι : Matrix (Fin N) (Fin N) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The `(i, j)` entry of a continuous matrix-valued function. -/
def entry (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) (i j : Fin N) :
    C(PontryaginDual (Multiplicative G), ℂ) :=
  ⟨fun χ => f χ i j, f.continuous.matrix_elem i j⟩

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
@[simp] lemma entry_apply (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (i j : Fin N) (χ : PontryaginDual (Multiplicative G)) : entry f i j χ = f χ i j := rfl

variable (hι : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (g : Multiplicative G),
  Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) (ι M))

include hι

lemma calculus_commute_ι (f : C(PontryaginDual (Multiplicative G), ℂ))
    (M : Matrix (Fin N) (Fin N) ℂ) : calculus π f * ι M = ι M * calculus π f :=
  (calculus_commute π (hι M) f).eq

omit hι

/-- The operator `∑_{ij} (∫ f_{ij} dP) ι(E_{ij})` of a continuous matrix-valued function. -/
def blochOp (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) : H →L[ℂ] H :=
  ∑ i, ∑ j, calculus π (entry f i j) * ι (Matrix.single i j 1)

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma entry_add (f g : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (i j : Fin N) : entry (f + g) i j = entry f i j + entry g i j := rfl

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma entry_smul (c : ℂ) (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (i j : Fin N) : entry (c • f) i j = c • entry f i j := rfl

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma entry_zero (i j : Fin N) :
    entry (0 : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) i j = 0 := rfl

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma entry_mul (f g : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (i j : Fin N) : entry (f * g) i j = ∑ k, entry f i k * entry g k j := by
  ext χ
  simp [entry, Matrix.mul_apply]

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma entry_star (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (i j : Fin N) : entry (star f) i j = star (entry f j i) := by
  ext χ
  simp [entry]

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
lemma entry_one (i j : Fin N) :
    entry (1 : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) i j =
      if i = j then 1 else 0 := by
  ext χ
  by_cases h : i = j <;> simp [entry, h]

include hι

omit hι in
lemma blochOp_add (f g : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    blochOp π ι (f + g) = blochOp π ι f + blochOp π ι g := by
  simp only [blochOp, entry_add, map_add, add_mul, Finset.sum_add_distrib]

omit hι in
lemma blochOp_smul (c : ℂ)
    (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    blochOp π ι (c • f) = c • blochOp π ι f := by
  simp only [blochOp, entry_smul, map_smul, smul_mul_assoc, Finset.smul_sum]

omit hι in
lemma blochOp_one : blochOp π ι (1 : C(PontryaginDual (Multiplicative G),
    Matrix (Fin N) (Fin N) ℂ)) = 1 := by
  have hterm : ∀ i j : Fin N, calculus π (entry (1 : C(PontryaginDual (Multiplicative G),
      Matrix (Fin N) (Fin N) ℂ)) i j) * ι (Matrix.single i j 1) =
      if i = j then ι (Matrix.single i i 1) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [entry_one]
    · simp [entry_one, h]
  simp only [blochOp, hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← map_sum, Matrix.sum_single_one, map_one]

lemma blochOp_mul (f g : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    blochOp π ι (f * g) = blochOp π ι f * blochOp π ι g := by
  have hterm : ∀ i k l j : Fin N,
      (calculus π (entry f i k) * ι (Matrix.single i k 1)) *
        (calculus π (entry g l j) * ι (Matrix.single l j 1)) =
      if k = l then calculus π (entry f i k) * calculus π (entry g k j) *
        ι (Matrix.single i j 1) else 0 := by
    intro i k l j
    have h1 : ι (Matrix.single i k 1) * calculus π (entry g l j) =
        calculus π (entry g l j) * ι (Matrix.single i k 1) :=
      (calculus_commute_ι π ι hι _ _).symm
    calc (calculus π (entry f i k) * ι (Matrix.single i k 1)) *
          (calculus π (entry g l j) * ι (Matrix.single l j 1))
        = calculus π (entry f i k) * (ι (Matrix.single i k 1) * calculus π (entry g l j)) *
            ι (Matrix.single l j 1) := by simp only [mul_assoc]
      _ = calculus π (entry f i k) * calculus π (entry g l j) *
            (ι (Matrix.single i k 1) * ι (Matrix.single l j 1)) := by
          rw [h1]; simp only [mul_assoc]
      _ = _ := by
          rw [← map_mul ι]
          by_cases hkl : k = l
          · subst hkl
            rw [ite_eq_left rfl, Matrix.single_mul_single_same, mul_one]
          · rw [ite_eq_right hkl]
            have hz : Matrix.single i k (1 : ℂ) * Matrix.single l j (1 : ℂ) = 0 := by
              simp [hkl]
            rw [hz, map_zero, mul_zero]
  calc blochOp π ι (f * g)
      = ∑ i, ∑ j, ∑ k, calculus π (entry f i k) * calculus π (entry g k j) *
          ι (Matrix.single i j 1) := by
        simp only [blochOp, entry_mul, map_sum, map_mul, Finset.sum_mul]
    _ = ∑ i, ∑ k, ∑ j, calculus π (entry f i k) * calculus π (entry g k j) *
          ι (Matrix.single i j 1) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, (if k = l then calculus π (entry f i k) *
          calculus π (entry g k j) * ι (Matrix.single i j 1) else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        simp
    _ = ∑ i, ∑ k, ∑ l, ∑ j, (calculus π (entry f i k) * ι (Matrix.single i k 1)) *
          (calculus π (entry g l j) * ι (Matrix.single l j 1)) := by
        simp only [hterm]
    _ = blochOp π ι f * blochOp π ι g := by
        unfold blochOp
        simp only [Finset.sum_mul]
        simp only [Finset.mul_sum]

lemma blochOp_star (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    blochOp π ι (star f) = star (blochOp π ι f) := by
  have hstar : ∀ i k : Fin N, star (calculus π (entry f i k) * ι (Matrix.single i k 1)) =
      calculus π (star (entry f i k)) * ι (Matrix.single k i 1) := by
    intro i k
    rw [star_mul, ← map_star ι, ← map_star (calculus π), Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_single, star_one]
    exact (calculus_commute_ι π ι hι _ _).symm
  calc blochOp π ι (star f)
      = ∑ j, ∑ i, calculus π (star (entry f j i)) * ι (Matrix.single i j 1) := by
        unfold blochOp
        rw [Finset.sum_comm]
        simp only [entry_star, map_star]
    _ = ∑ i, ∑ k, star (calculus π (entry f i k) * ι (Matrix.single i k 1)) := by
        simp only [hstar]
    _ = star (blochOp π ι f) := by
        simp only [blochOp, star_sum]

/-- **Bloch–Floquet**: the map `f ↦ ∑_{ij} (∫ f_{ij} dP) ι(E_{ij})` is a unital ⋆-homomorphism from
the continuous matrix-valued functions on the Brillouin zone to the bounded operators. -/
def blochHom : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ) →⋆ₐ[ℂ]
    (H →L[ℂ] H) where
  toFun := blochOp π ι
  map_one' := blochOp_one π ι
  map_mul' := blochOp_mul π ι hι
  map_zero' := by simp [blochOp, entry_zero]
  map_add' := blochOp_add π ι
  commutes' c := by
    show blochOp π ι (algebraMap ℂ C(PontryaginDual (Multiplicative G),
      Matrix (Fin N) (Fin N) ℂ) c) = algebraMap ℂ (H →L[ℂ] H) c
    rw [Algebra.algebraMap_eq_smul_one, blochOp_smul π ι, blochOp_one π ι,
      Algebra.algebraMap_eq_smul_one]
  map_star' := blochOp_star π ι hι

omit hι

/-! ## C. The spectrum -/

include hι

open scoped Matrix.Norms.Operator in
/-- **The spectrum of the operator of a symbol is contained in the union of the spectra of the
symbol's values**: a translation-invariant operator has no spectrum outside its Bloch bands. -/
lemma spectrum_blochHom_subset
    (b : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ)) :
    spectrum ℂ (blochHom π ι hι b) ⊆
      ⋃ χ : PontryaginDual (Multiplicative G), spectrum ℂ (b χ) := by
  refine (AlgHom.spectrum_apply_subset (blochHom π ι hι) _).trans ?_
  intro z hz
  by_contra hnot
  simp only [Set.mem_iUnion, not_exists, spectrum.mem_iff, not_not] at hnot
  apply hz
  have : IsUnit (algebraMap ℂ C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ) z -
      b) := by
    refine (ContinuousMap.isUnit_iff_forall_isUnit _).mpr fun χ => ?_
    exact hnot χ
  exact this

omit hι

/-! ## D. Faithful representations -/

/-- A representation has **full support** relative to the internal space when the spectral
projection of every nonempty open set of crystal momenta is nonzero on every internal state:
every crystal momentum is present in every orbital. -/
def HasFullSupport : Prop :=
  ∀ U : Set (PontryaginDual (Multiplicative G)), IsOpen U → U.Nonempty →
    ∀ i : Fin N, projection π U * ι (Matrix.single i i 1) ≠ 0

include hι

/-- Compressing the image of a matrix-valued function to the `(i, j)` orbitals isolates the
`(i, j)` entry. -/
lemma compress_blochOp (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (i j : Fin N) :
    ι (Matrix.single i i 1) * blochOp π ι f * ι (Matrix.single j i 1) =
      calculus π (entry f i j) * ι (Matrix.single i i 1) := by
  have hterm : ∀ k l : Fin N, ι (Matrix.single i i 1) *
      (calculus π (entry f k l) * ι (Matrix.single k l 1)) * ι (Matrix.single j i 1) =
      if k = i ∧ l = j then calculus π (entry f i j) * ι (Matrix.single i i 1) else 0 := by
    intro k l
    have h1 : ι (Matrix.single i i 1) * calculus π (entry f k l) =
        calculus π (entry f k l) * ι (Matrix.single i i 1) :=
      (calculus_commute_ι π ι hι _ _).symm
    calc ι (Matrix.single i i 1) * (calculus π (entry f k l) * ι (Matrix.single k l 1)) *
          ι (Matrix.single j i 1)
        = calculus π (entry f k l) * (ι (Matrix.single i i 1 * Matrix.single k l 1 *
            Matrix.single j i 1)) := by
          rw [← mul_assoc, h1, map_mul, map_mul]; simp only [mul_assoc]
      _ = _ := by
          rw [Matrix.single_mul_mul_single]
          by_cases h : k = i ∧ l = j
          · obtain ⟨rfl, rfl⟩ := h
            simp
          · rw [ite_eq_right h]
            have : (Matrix.single k l (1 : ℂ)) i j = 0 := by
              rw [Matrix.single_apply]
              simp only [ite_and]
              by_cases hk : k = i
              · by_cases hl : l = j
                · exact absurd ⟨hk, hl⟩ h
                · simp [hk, hl]
              · simp [hk]
            rw [this]
            simp
  simp only [blochOp, Finset.mul_sum, Finset.sum_mul, hterm]
  simp [ite_and]

/-- An entry of the image vanishes only if the entry function vanishes: this is the content of
full support. -/
lemma entry_eq_zero_of_blochOp_eq_zero (hfull : HasFullSupport π ι)
    (f : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (hf : blochOp π ι f = 0) : f = 0 := by
  by_contra hne
  obtain ⟨χ₀, hχ₀⟩ := DFunLike.ne_iff.mp hne
  obtain ⟨i, j, hij⟩ : ∃ i j, f χ₀ i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hχ₀ (by ext i j; exact hall i j)
  set g := entry f i j with hg
  have hgχ₀ : g χ₀ ≠ 0 := hij
  have hcomp := compress_blochOp π ι hι f i j
  rw [hf, mul_zero, zero_mul] at hcomp
  -- `V` is where `g` stays away from zero
  set ε : ℝ := ‖g χ₀‖ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set V : Set (PontryaginDual (Multiplicative G)) := {χ | ε < ‖g χ‖} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const g.continuous.norm
  have hVne : V.Nonempty := ⟨χ₀, by
    show ε < ‖g χ₀‖
    have := norm_pos_iff.mpr hgχ₀
    rw [hε]; linarith⟩
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  let h : PontryaginDual (Multiplicative G) → ℂ := V.indicator fun χ => (g χ)⁻¹
  have hhmeas : Measurable h := by
    refine Measurable.indicator ?_ hVmeas
    exact g.continuous.measurable.inv
  have hhbdd : ∃ C, ∀ χ, ‖h χ‖ ≤ C := by
    refine ⟨ε⁻¹, fun χ => ?_⟩
    by_cases hχ : χ ∈ V
    · simp only [h, Set.indicator_of_mem hχ, norm_inv]
      exact inv_anti₀ hεpos (le_of_lt hχ)
    · simp only [h, Set.indicator_of_notMem hχ, norm_zero]
      positivity
  have hmul := (spectralMeasure π).boundedIntegral_mul hhmeas g.continuous.measurable hhbdd
    (WOTSpectralMeasure.bound_of_continuous g)
  have hprod : h * ⇑g = V.indicator (fun _ => (1 : ℂ)) := by
    funext χ
    by_cases hχ : χ ∈ V
    · have hne0 : g χ ≠ 0 := by
        have : ε < ‖g χ‖ := hχ
        exact norm_pos_iff.mp (lt_trans hεpos this)
      simp [h, Set.indicator_of_mem hχ, hne0]
    · simp [h, Set.indicator_of_notMem hχ]
  have hind := (spectralMeasure π).boundedIntegral_indicator hVmeas
  have hcongr := (spectralMeasure π).boundedIntegral_congr (hhmeas.mul g.continuous.measurable)
    (measurable_const.indicator hVmeas) (by
      obtain ⟨C₁, h₁⟩ := hhbdd
      obtain ⟨C₂, h₂⟩ := WOTSpectralMeasure.bound_of_continuous g
      obtain ⟨z₀⟩ := (inferInstance : Nonempty (PontryaginDual (Multiplicative G)))
      exact ⟨C₁ * C₂, fun z => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) ((norm_nonneg _).trans (h₁ z))⟩)
    ⟨1, fun x => by by_cases hx : x ∈ V <;> simp [hx]⟩ (fun χ => congrFun hprod χ)
  have hP : projection π V = ContinuousLinearMapWOT.toCLM
      ((spectralMeasure π).boundedIntegral h hhmeas hhbdd) * calculus π g := by
    have e1 : ContinuousLinearMapWOT.toCLM
        ((spectralMeasure π).boundedIntegral (V.indicator fun _ => (1 : ℂ))
          (measurable_const.indicator hVmeas)
          ⟨1, fun x => by by_cases hx : x ∈ V <;> simp [hx]⟩) = projection π V := by
      rw [hind]; rfl
    have e2 := congrArg ContinuousLinearMapWOT.toCLM (hcongr.symm.trans hmul)
    rw [ContinuousLinearMapWOT.toCLM_mul] at e2
    exact e1.symm.trans e2
  have hcomp' : calculus π g * ι (Matrix.single i i 1) = 0 := hcomp.symm
  apply hfull V hVopen hVne i
  rw [hP, mul_assoc, hcomp', mul_zero]

/-- Under full support the map `f ↦ ∫ f dP` is injective. -/
lemma blochHom_injective (hfull : HasFullSupport π ι) :
    Function.Injective (blochHom π ι hι) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  exact entry_eq_zero_of_blochOp_eq_zero π ι hι hfull f hf

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
