/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsLeftRightWeyl
public import Physlib.Relativity.Fermions.Weyl.Metric
/-!
# Lorentz invariants of two left-handed Weyl indices

Two Weyl spinors of the same handedness have exactly one Lorentz-invariant contraction,
the antisymmetric one

`epsilonContraction = ε_{α β} ψ^α χ^β`,

which is the shape of a Dirac or Majorana mass term. There is nothing else: `SL(2,ℂ)`
preserves the determinant on a pair of fundamental indices and no more. That is
`exists_smul_epsilonContraction_of_invariant`, with
`exists_smul_epsilonContraction_of_invariant_subset` the same statement modulo a
Lorentz-stable subspace `S`; `repLorentz_epsilonContraction` checks that the contraction
is invariant.

The components are vectors `T a` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by two left-handed Weyl indices, and `IsBiLeftWeyl`
says the group moves each index by the matrix of `g` (B). `hT.span` is the set of their
combinations.

The proof is the same-handedness twin of `IsLeftRightWeyl` and reuses its Weyl weight
bases (A, C). An invariant has boost weight `0` along every axis, so it is fixed by the
weight-zero projection along each; averaging the three gives `M = 2 - swap` (D), whose
eigenvalue `3` is simple and carried by the antisymmetric line, so `(3 λ - 1) / 2` at
`λ = M / 3` collapses an invariant onto the antisymmetric part of its coefficients, which
is the `ε` contraction (E). Section F divides out `S`.

Sections G to K handle dual Weyl indices, which transform by the contragredient
`(Λ⁻¹)ᵀ`, or for a barred species by `(Λ⁻¹)ᴴ`. Neither is the fundamental law, and two
separate mechanisms bridge the gap. The contragredient is inner, `(Λ⁻¹)ᵀ = ε Λ ε⁻¹`, so
re-indexing both slots by `ε` turns a contragredient family into a fundamental one
without touching the representation (G, J). Entrywise conjugation is instead an
automorphism of `SL(2,ℂ)` (H), so a conjugated family is a fundamental family for the
twisted representation `repLorentz.comp conjHom`; the twist is by a surjection, so
invariance is the same condition for both and the classification carries over (I, K).
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. The weight basis of a pair of left-handed indices

Both indices are graded by the same Weyl weight basis of `IsLeftRightWeyl`, so the
weight basis of the pair is the tensor square of it and the weight is `pairWeight`.

-/

/-- The axis-`i` weight basis of a pair of left-handed indices. -/
def biLeftCoeff (i : Fin 3) (κ α : Fin 2 × Fin 2) : ℂ :=
  weylCoeff i κ.1 α.1 * weylCoeff i κ.2 α.2

/-- The standard basis of a pair of left-handed indices written back in the axis-`i`
  weight basis. -/
noncomputable def biLeftCoeffInv (i : Fin 3) (α κ : Fin 2 × Fin 2) : ℂ :=
  weylCoeffInv i α.1 κ.1 * weylCoeffInv i α.2 κ.2

/-- The pair weight basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_biLeftCoeffInv_mul (i : Fin 3) (α β : Fin 2 × Fin 2) :
    ∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ * biLeftCoeff i κ β
      = if α = β then 1 else 0 := by
  have hfac : (∑ κ₁, weylCoeffInv i α.1 κ₁ * weylCoeff i κ₁ β.1)
      * (∑ κ₂, weylCoeffInv i α.2 κ₂ * weylCoeff i κ₂ β.2)
      = ∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ * biLeftCoeff i κ β := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun κ₁ _ => Finset.sum_congr rfl fun κ₂ _ => by
      simp only [biLeftCoeff, biLeftCoeffInv]
      ring
  rw [← hfac, sum_weylCoeffInv_mul, sum_weylCoeffInv_mul]
  obtain ⟨α₁, α₂⟩ := α
  obtain ⟨β₁, β₂⟩ := β
  by_cases h1 : α₁ = β₁ <;> by_cases h2 : α₂ = β₂ <;> simp [h1, h2, Prod.mk.injEq]

/-- The pair weight basis diagonalises the axis-`i` boost, with the weight
  `pairWeight`. -/
lemma sum_boostAxis_biLeftCoeff (i : Fin 3) (κ a : Fin 2 × Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
        * ((SL2C.boostAxis i t ht).1 a.1 l.1 * (SL2C.boostAxis i t ht).1 a.2 l.2)
      = ((t : ℝ) : ℂ) ^ (pairWeight κ) * biLeftCoeff i κ a := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hfac : (∑ l₁, (SL2C.boostAxis i t ht).1 a.1 l₁ * weylCoeff i κ.1 l₁)
      * (∑ l₂, (SL2C.boostAxis i t ht).1 a.2 l₂ * weylCoeff i κ.2 l₂)
      = ∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
        * ((SL2C.boostAxis i t ht).1 a.1 l.1 * (SL2C.boostAxis i t ht).1 a.2 l.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => by
      simp only [biLeftCoeff]
      ring
  rw [← hfac, sum_boostAxis_weylCoeff i κ.1 a.1 ht, sum_boostAxis_weylCoeff i κ.2 a.2 ht,
    pairWeight, biLeftCoeff, zpow_add₀ htc]
  ring

/-!

## B. Bi-left-handed Weyl tensors and the span of their components

`IsBiLeftWeyl B repLorentz T` says the group moves each index of `T^{α₁ α₂}` by the matrix
of `g`, and `hT.span` is the set of combinations `∑ a, c a • T a` of the four components.

-/

/-- A family `T` of elements of `B`, indexed by two left-handed Weyl indices, transforms
  as a tensor `T^{α₁ α₂}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsBiLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2), (g.1 a.1 l.1 * g.1 a.2 l.2) • T a

namespace IsBiLeftWeyl

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : Fin 2 × Fin 2 → B}
  (hT : IsBiLeftWeyl B repLorentz T)

set_option linter.unusedVariables false in
/-- The span of the components; `hT` is unused, and is present only so it reads `hT.span`. -/
def span (hT : IsBiLeftWeyl B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span exactly when it is a combination `∑ d, c d • T d`. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ c : Fin 2 × Fin 2 → ℂ, x = ∑ d, c d • T d := by
  rw [span, ← Submodule.span_range_eq_iSup, ← Fintype.range_linearCombination,
    LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, eq_comm]

/-!

## C. The weight grading of the span

The four products `weightVec i κ` of two left weight vectors span the same space as the
components and are boost eigenvectors along the axis `i`, of weights `2`, `0`, `0` and
`-2`.

-/

set_option linter.unusedVariables false in
/-- The weight component of `T` along axis `i` at the pair `κ` of Weyl weight indices;
  `hT` is present only so it reads `hT.weightVec`. -/
noncomputable def weightVec (hT : IsBiLeftWeyl B repLorentz T) (i : Fin 3)
    (κ : Fin 2 × Fin 2) : B :=
  ∑ a : Fin 2 × Fin 2, biLeftCoeff i κ a • T a

/-- Each weight component lies in the span of the components. -/
lemma weightVec_mem_span (i : Fin 3) (κ : Fin 2 × Fin 2) :
    hT.weightVec i κ ∈ hT.span :=
  sum_mem fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _))

/-- Each generator is recovered from the weight components along any axis. -/
lemma eq_sum_weightVec (i : Fin 3) (α : Fin 2 × Fin 2) :
    T α = ∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ • hT.weightVec i κ := by
  calc T α = ∑ β : Fin 2 × Fin 2,
        (∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ * biLeftCoeff i κ β) • T β := by
        simp only [sum_biLeftCoeffInv_mul, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [weightVec, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The weight components along any axis span the same space as the components. -/
lemma span_eq_weightVec (hT : IsBiLeftWeyl B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ κ, ℂ ∙ hT.weightVec i κ := by
  rw [span]
  refine le_antisymm (iSup_le fun α => ?_) (iSup_le fun κ => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_weightVec i α]
    exact sum_mem fun κ _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem κ (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.weightVec_mem_span i κ

/-- The weight components are boost eigenvectors: along axis `i` the component at `κ`
  has boost weight `pairWeight κ`. -/
lemma weightVec_mem_boostWeightSubmodule (i : Fin 3) (κ : Fin 2 × Fin 2) :
    hT.weightVec i κ ∈ boostWeightSubmodule repLorentz i (pairWeight κ) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ l : Fin 2 × Fin 2,
      biLeftCoeff i κ l • repLorentz (SL2C.boostAxis i t ht) (T l)
        = ∑ a : Fin 2 × Fin 2, (biLeftCoeff i κ l
            * ((SL2C.boostAxis i t ht).1 a.1 l.1
              * (SL2C.boostAxis i t ht).1 a.2 l.2)) • T a := by
    intro l
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.weightVec i κ)
      = ∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
          • repLorentz (SL2C.boostAxis i t ht) (T l) := by
        simp only [weightVec, map_sum, map_smul]
    _ = ∑ a : Fin 2 × Fin 2, (∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
          * ((SL2C.boostAxis i t ht).1 a.1 l.1
            * (SL2C.boostAxis i t ht).1 a.2 l.2)) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 2 × Fin 2,
          (((t : ℝ) : ℂ) ^ (pairWeight κ) * biLeftCoeff i κ a) • T a :=
        Finset.sum_congr rfl fun a _ => by rw [sum_boostAxis_biLeftCoeff i κ a ht]
    _ = (algebraMap ℝ ℂ) t ^ (pairWeight κ) • hT.weightVec i κ := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, weightVec, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-- The axis-`i` weight-`m` component of the generator `T α`: the weight-`m` partial sum
  of `eq_sum_weightVec`. -/
noncomputable def monoComponent (i : Fin 3) (α : Fin 2 × Fin 2) (m : ℤ) : B :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = m),
    biLeftCoeffInv i α κ • hT.weightVec i κ

/-- The weight components are homogeneous of the stated weight. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (α : Fin 2 × Fin 2) (m : ℤ) :
    hT.monoComponent i α m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun κ hκ => Submodule.smul_mem _ _ ?_
  exact (show pairWeight κ = m from (Finset.mem_filter.1 hκ).2) ▸
    hT.weightVec_mem_boostWeightSubmodule i κ

/-- A component is the sum of its weight components over the three possible weights. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (α : Fin 2 × Fin 2) :
    T α = ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i α m := by
  rw [hT.eq_sum_weightVec i α]
  exact (Finset.sum_fiberwise_of_maps_to (fun κ _ => pairWeight_mem κ) _).symm

/-!

## D. The weight-zero round and its average over the axes

An invariant has boost weight zero along every axis, so along each axis it equals its own
weight-zero part, which written back on the components is the matrix
`weightZeroTransition i`.

-/

/-- The matrix of the axis-`i` weight-zero projection in the `T`-basis: the coefficient
  of `T β` in the re-expansion of `monoComponent i α 0` through the weight basis. -/
noncomputable def weightZeroTransition (i : Fin 3) (β α : Fin 2 × Fin 2) : ℂ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0),
    biLeftCoeffInv i α κ * biLeftCoeff i κ β

/-- The weight-zero component re-expanded in the `T`-basis: `monoComponent i α 0` is the
  `α`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (α : Fin 2 × Fin 2) :
    hT.monoComponent i α 0
      = ∑ β : Fin 2 × Fin 2, weightZeroTransition i β α • T β := by
  rw [monoComponent]
  simp only [weightVec, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_smul, weightZeroTransition]

include hT in
/-- A vector of boost weight zero along axis `i` is written with the weight-zero transition
  applied to its coefficients. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : Fin 2 × Fin 2 → ℂ) (hx : x = ∑ α, c α • T α)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β := by
  have hsum : x = ∑ m ∈ ({-2, 0, 2} : Finset ℤ),
      ∑ α, c α • hT.monoComponent i α m := by
    rw [hx]
    calc ∑ α, c α • T α
        = ∑ α, c α • ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i α m :=
          Finset.sum_congr rfl fun α _ => by rw [← hT.eq_sum_monoComponent_univ i α]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  have hx0 : x = ∑ α, c α • hT.monoComponent i α 0 :=
    eq_component_zero_of_mem_boostWeightSubmodule
      (w := fun m => ∑ α, c α • hT.monoComponent i α m) hw
      (fun m _ => sum_mem fun α _ => Submodule.smul_mem _ _
        (hT.monoComponent_mem_boostWeightSubmodule i α m))
      (by decide) hsum
  calc x = ∑ α, c α • hT.monoComponent i α 0 := hx0
    _ = ∑ α, c α • ∑ β, weightZeroTransition i β α • T β :=
        Finset.sum_congr rfl fun α _ => by rw [hT.monoComponent_zero_eq i α]
    _ = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_smul]
        exact congrArg (· • T β) (Finset.sum_congr rfl fun α _ => mul_comm _ _)

/-- The closed form of the summed weight-zero transition: twice the identity minus the
  swap of the two indices. -/
def transitionEntry (β α : Fin 2 × Fin 2) : ℂ :=
  2 * (if β.1 = α.1 then 1 else 0) * (if β.2 = α.2 then 1 else 0)
    - (if β.1 = α.2 then 1 else 0) * (if β.2 = α.1 then 1 else 0)

/-- The sum over the three axes of the weight-zero transitions has the closed form
  `transitionEntry`. -/
lemma sum_weightZeroTransition_eq (β α : Fin 2 × Fin 2) :
    ∑ i : Fin 3, weightZeroTransition i β α = transitionEntry β α := by
  simp only [weightZeroTransition, sum_weightZeroFilter, Fin.sum_univ_three]
  obtain ⟨β₁, β₂⟩ := β
  obtain ⟨α₁, α₂⟩ := α
  fin_cases β₁ <;> fin_cases β₂ <;> fin_cases α₁ <;> fin_cases α₂ <;>
    simp [transitionEntry, biLeftCoeff, biLeftCoeffInv, weylCoeff, weylCoeffInv] <;>
    norm_num [Complex.ext_iff]

include hT in
/-- A vector of boost weight zero along all three axes is written with a third of the summed
  transition applied to its coefficients. -/
lemma eq_sum_transitionEntry_smul {x : B} (c : Fin 2 × Fin 2 → ℂ)
    (hx : x = ∑ α, c α • T α)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ β, ((3 : ℂ)⁻¹ * ∑ α, transitionEntry β α * c α) • T β := by
  have hround : ∀ i : Fin 3,
      x = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β :=
    fun i => hT.eq_sum_weightZeroTransition_smul i c hx (hw i)
  have h3 : (3 : ℂ) • x = ∑ i : Fin 3, x := by
    rw [Fin.sum_univ_three, show (3 : ℂ) = 1 + 1 + 1 from by norm_num,
      add_smul, add_smul, one_smul]
  calc x = (3 : ℂ)⁻¹ • ((3 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = (3 : ℂ)⁻¹ • ∑ i : Fin 3, x := by rw [h3]
    _ = (3 : ℂ)⁻¹ • ∑ i : Fin 3, ∑ β,
          (∑ α, weightZeroTransition i β α * c α) • T β :=
        congrArg (fun y => (3 : ℂ)⁻¹ • y) (Finset.sum_congr rfl fun i _ => hround i)
    _ = ∑ β, ((3 : ℂ)⁻¹ * ∑ α, transitionEntry β α * c α) • T β := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_smul, smul_smul]
        congr 1
        rw [show (∑ i : Fin 3, ∑ α, weightZeroTransition i β α * c α)
            = ∑ α, transitionEntry β α * c α from by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun α _ => by
            rw [← Finset.sum_mul, sum_weightZeroTransition_eq]]

/-!

## E. The epsilon contraction and the linear certificate

The summed transition is `2 - swap`, so a third of it fixes exactly the antisymmetric
line. The linear certificate `(3 λ - 1) / 2` therefore collapses an invariant onto the
antisymmetrisation of its coefficients, which is a multiple of the `ε` contraction.

-/

/-- The `ε` symbol on a pair of same-handedness spinor indices, in the convention of
  `Fermion.metricRaw`. -/
def epsZ (α : Fin 2 × Fin 2) : ℤ :=
  if α = (0, 1) then 1 else if α = (1, 0) then -1 else 0

/-- The `ε` contraction `ε_{α β} T^{α β}`, the only invariant contraction of two
  same-handedness Weyl indices, and the shape of a fermion mass term. -/
noncomputable def epsilonContraction : B :=
  ∑ α : Fin 2 × Fin 2, ((epsZ α : ℤ) : ℂ) • T α

/-- The `ε` contraction written out: the antisymmetric combination of the two mixed
  components. -/
lemma epsilonContraction_eq :
    epsilonContraction (T := T) = T (0, 1) - T (1, 0) := by
  rw [epsilonContraction]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, epsZ]
  module

include hT in
/-- The `ε` contraction is Lorentz invariant: the antisymmetric combination picks out
  the determinant of the `SL(2,ℂ)` matrix, which is one. -/
lemma repLorentz_epsilonContraction (g : SL(2,ℂ)) :
    repLorentz g (epsilonContraction (T := T)) = epsilonContraction (T := T) := by
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  rw [epsilonContraction_eq, map_sub, hT.repLorentz_T, hT.repLorentz_T]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  match_scalars
  · ring
  · linear_combination hdet
  · linear_combination -hdet
  · ring

/-- The action of the summed transition matrix on a coefficient vector is twice the
  vector minus its swap. -/
lemma sum_transitionEntry_mul (c : Fin 2 × Fin 2 → ℂ) (β : Fin 2 × Fin 2) :
    ∑ α, transitionEntry β α * c α = 2 * c β - c β.swap := by
  obtain ⟨β₁, β₂⟩ := β
  fin_cases β₁ <;> fin_cases β₂ <;>
    simp [transitionEntry, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- The antisymmetrisation of a coefficient vector is a multiple of the `ε`
  contraction. -/
lemma sum_antisymm_smul (c : Fin 2 × Fin 2 → ℂ) :
    ∑ β : Fin 2 × Fin 2, ((2 : ℂ)⁻¹ * (c β - c β.swap)) • T β
      = ((2 : ℂ)⁻¹ * (c (0, 1) - c (1, 0))) • epsilonContraction (T := T) := by
  rw [epsilonContraction_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Prod.swap_prod_mk]
  module

include hT in
/-- The classification of the Lorentz invariants: every element of the span of the
  components fixed by the Lorentz group is a scalar multiple of the `ε` contraction. -/
theorem exists_smul_epsilonContraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • epsilonContraction (T := T) := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h1 : x = ∑ β, ((3 : ℂ)⁻¹ * (2 * c β - c β.swap)) • T β := by
    rw [hT.eq_sum_transitionEntry_smul c hc hw]
    exact Finset.sum_congr rfl fun β _ => by rw [sum_transitionEntry_mul]
  refine ⟨(2 : ℂ)⁻¹ * (c (0, 1) - c (1, 0)), ?_⟩
  rw [← sum_antisymm_smul c]
  calc x = (3 / 2 : ℂ) • x - (1 / 2 : ℂ) • x := by module
    _ = ∑ β : Fin 2 × Fin 2, ((2 : ℂ)⁻¹ * (c β - c β.swap)) • T β := by
        nth_rewrite 1 [h1]
        nth_rewrite 1 [hc]
        simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, ← sub_smul]
        refine Finset.sum_congr rfl fun β _ => ?_
        congr 1
        ring

/-!

## F. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a bi-left-handed tensor, so
the classification applies there and lifts back with an error term in `S`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a bi-left-handed Weyl tensor. -/
lemma isBiLeftWeyl_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsBiLeftWeyl (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the `ε` contraction to the `ε` contraction of the
  images. -/
lemma mkQ_epsilonContraction (S : Submodule ℂ B) :
    S.mkQ (epsilonContraction (T := T))
      = epsilonContraction (T := fun l => S.mkQ (T l)) := by
  rw [epsilonContraction, epsilonContraction, map_sum]
  exact Finset.sum_congr rfl fun α _ => map_smul _ _ _

include hT in
/-- The same modulo a Lorentz-stable subspace `S`: a multiple of the `ε` contraction plus an
  error in `S`. -/
lemma exists_smul_epsilonContraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • epsilonContraction (T := T) + y := by
  have hT' := hT.isBiLeftWeyl_quotRep S hS
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hT'.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x := by
    intro g
    rw [quotRep_mkQ, hinv g]
  obtain ⟨a, hcomb⟩ := hT'.exists_smul_epsilonContraction_of_invariant hmk hinv'
  rw [← mkQ_epsilonContraction] at hcomb
  refine ⟨a, x - a • epsilonContraction (T := T), ?_, by abel⟩
  have hker : x - a • epsilonContraction (T := T) ∈ LinearMap.ker S.mkQ := by
    rw [LinearMap.mem_ker, map_sub, hcomb, map_smul]
    abel
  rwa [Submodule.ker_mkQ] at hker

end IsBiLeftWeyl

/-!

## G. The symplectic form and the contragredient as an inner twist

`ε = !![0, 1; -1, 0]` has determinant one, so it lies in `SL(2,ℂ)`, and `Λᵀ ε Λ = ε` for
every `Λ` there: that is `det Λ = 1` written out. Rearranged it reads
`(Λ⁻¹)ᵀ = ε Λ ε⁻¹`, so the contragredient is the fundamental matrix conjugated by a fixed
group element, a change of basis on the index type rather than of representation.

-/

namespace SL2C

/-- The antisymmetric symplectic form `ε = !![0, 1; -1, 0]`, whose underlying matrix is
  the Weyl metric `Fermion.metricRaw`, as an element of `SL(2,ℂ)`. -/
def epsilon : SL(2,ℂ) :=
  ⟨Fermion.metricRaw, by simp [Fermion.metricRaw, Matrix.det_fin_two_of]⟩

/-- The matrix underlying `epsilon`. -/
lemma epsilon_coe : (epsilon : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := rfl

/-- The matrix underlying `epsilon` is the Weyl metric `Fermion.metricRaw`. -/
lemma epsilon_coe_metricRaw :
    (epsilon : Matrix (Fin 2) (Fin 2) ℂ) = Fermion.metricRaw := rfl

/-- The form `ε` is the invariant symplectic form of `SL(2,ℂ)`: `Λᵀ ε Λ = ε`, which is
  the determinant condition `det Λ = 1` written out entrywise. -/
lemma transpose_mul_epsilon_mul (g : SL(2,ℂ)) :
    g.1ᵀ * epsilon.1 * g.1 = epsilon.1 := by
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsilon_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination | linear_combination hdet | linear_combination -hdet

/-- The matrix of `ε` times the matrix of its group inverse is the identity. -/
lemma epsilon_mul_epsilon_inv : epsilon.1 * (epsilon⁻¹ : SL(2,ℂ)).1 = 1 := by
  rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]
  rfl

/-- The contragredient is inner: conjugation by `ε` carries the fundamental matrix `Λ`
  to the inverse transpose `(Λ⁻¹)ᵀ`. -/
lemma inv_transpose_eq_epsilon_conj (g : SL(2,ℂ)) :
    (g.1⁻¹)ᵀ = epsilon.1 * g.1 * (epsilon⁻¹ : SL(2,ℂ)).1 := by
  symm
  calc epsilon.1 * g.1 * (epsilon⁻¹ : SL(2,ℂ)).1
      = ((g.1⁻¹)ᵀ * Fermion.metricRaw) * (epsilon⁻¹ : SL(2,ℂ)).1 := by
        rw [epsilon_coe_metricRaw, Fermion.metricRaw_comm]
    _ = (g.1⁻¹)ᵀ * (epsilon.1 * (epsilon⁻¹ : SL(2,ℂ)).1) := by
        rw [epsilon_coe_metricRaw, Matrix.mul_assoc]
    _ = (g.1⁻¹)ᵀ := by rw [epsilon_mul_epsilon_inv, Matrix.mul_one]

/-- The form of the symplectic identity used to re-index: `ε Λ⁻¹ = Λᵀ ε`. -/
lemma epsilon_mul_inv_eq_transpose_mul_epsilon (g : SL(2,ℂ)) :
    epsilon.1 * g.1⁻¹ = g.1ᵀ * epsilon.1 := by
  have hg : g.1 * g.1⁻¹ = 1 := by
    rw [SL2C.inverse_coe, ← SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  calc epsilon.1 * g.1⁻¹ = (g.1ᵀ * epsilon.1 * g.1) * g.1⁻¹ := by
        rw [transpose_mul_epsilon_mul]
    _ = g.1ᵀ * epsilon.1 * (g.1 * g.1⁻¹) := by rw [Matrix.mul_assoc]
    _ = g.1ᵀ * epsilon.1 := by rw [hg, Matrix.mul_one]

/-!

## H. The conjugation automorphism of `SL(2,ℂ)`

Entrywise conjugation is a monoid homomorphism `SL(2,ℂ) → SL(2,ℂ)`, multiplicative
because conjugation is a ring homomorphism and landing in `SL(2,ℂ)` because
`det (conj Λ) = 1`; it is its own inverse. Unlike the `ε` twist of G this is a genuine
automorphism, so twisting a representation along it gives a different representation.

-/

/-- Entrywise conjugation of an element of `SL(2,ℂ)` again has determinant one. -/
lemma det_map_star (g : SL(2,ℂ)) : (g.1.map star).det = 1 := by
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  rw [Matrix.det_fin_two]
  simp only [Matrix.map_apply]
  rw [← star_mul', ← star_mul', ← star_sub, hdet, star_one]

/-- Entrywise complex conjugation as a monoid endomorphism of `SL(2,ℂ)`. -/
def conjHom : SL(2,ℂ) →* SL(2,ℂ) where
  toFun g := ⟨g.1.map star, det_map_star g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [Matrix.map_apply, Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
    rfl

/-- The matrix underlying `conjHom g` is the entrywise conjugate of that of `g`. -/
lemma conjHom_coe (g : SL(2,ℂ)) : (conjHom g).1 = g.1.map star := rfl

/-- Conjugation is an involution. -/
lemma conjHom_conjHom (g : SL(2,ℂ)) : conjHom (conjHom g) = g := by
  apply Subtype.ext
  ext i j
  simp [conjHom_coe, Matrix.map_apply]

/-- Being an involution, conjugation is surjective. -/
lemma conjHom_surjective : Function.Surjective conjHom :=
  fun g => ⟨conjHom g, conjHom_conjHom g⟩

/-- Being an involution, conjugation is bijective. -/
lemma conjHom_bijective : Function.Bijective conjHom :=
  Function.bijective_iff_has_inverse.2 ⟨conjHom, conjHom_conjHom, conjHom_conjHom⟩

end SL2C

/-!

## I. Transfer of invariance along a surjective endomorphism

Twisting by a surjective monoid endomorphism `σ` does not change what invariance means:
`rep g x = x` and `rep (σ g) x = x` range over the same group elements. That is what
makes the conjugation twist of H free.

-/

/-- Invariance under a representation and invariance under its twist by a surjective
  monoid endomorphism of the group are the same condition. -/
lemma forall_comp_apply_eq_self_iff {k G V : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (rep : Representation k G V) {σ : G →* G}
    (hσ : Function.Surjective σ) (x : V) :
    (∀ g : G, (rep.comp σ) g x = x) ↔ ∀ g : G, rep g x = x := by
  constructor
  · intro h g
    obtain ⟨g', rfl⟩ := hσ g
    exact h g'
  · intro h g
    exact h (σ g)

/-!

## J. Dual-index families and the `ε` re-index

`IsBiDualLeftWeyl` and `IsBiDualRightWeyl` are the laws the Standard Model's fermion
symbols carry: one factor of `(Λ⁻¹)ᵀ` per index for an undotted pair, one of `(Λ⁻¹)ᴴ` for
a dotted pair. The re-index `epsReindex` sends both slots through `ε`. By G it converts
the contragredient law into the fundamental one and leaves the representation alone; it is
an involution, so the span is unchanged; and it leaves the `ε` contraction exactly as it
was, with no sign or scalar. For a dotted family the same re-index works once the
representation is twisted by `conjHom`, conjugating the group argument undoing the
conjugation of the entries. Neither law is vacuous:
`isBiDualLeftWeyl_dualLeftHandedWeyl` and `isBiDualRightWeyl_dualRightHandedWeyl` check
they are what the tensor squares of the repo's dual Weyl representations carry.

-/

/-- A family `T` indexed by two dual left-handed Weyl indices, moved as `T_{α₁ α₂}`: one factor
  of the contragredient matrix `(Λ⁻¹)ᵀ` per index. -/
structure IsBiDualLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᵀ a.1 l.1 * (g.1⁻¹)ᵀ a.2 l.2) • T a

/-- The same for two dual right-handed indices, `T_{α̇₁ α̇₂}`: one factor of `(Λ⁻¹)ᴴ` per index. -/
structure IsBiDualRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2),
      ((g.1⁻¹)ᴴ a.1 l.1 * (g.1⁻¹)ᴴ a.2 l.2) • T a

open Fermion in
/-- The tensor square of the dual left-handed Weyl representation, on the products of
  basis vectors, is the basic example of a family with the contragredient index law. -/
lemma isBiDualLeftWeyl_dualLeftHandedWeyl :
    IsBiDualLeftWeyl (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)
      (DualLeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep)
      (fun l => DualLeftHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualLeftHandedWeyl.rep_apply_basis, DualLeftHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

open Fermion in
/-- The tensor square of the dual right-handed Weyl representation carries the conjugate
  contragredient law: the basic example. -/
lemma isBiDualRightWeyl_dualRightHandedWeyl :
    IsBiDualRightWeyl (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl)
      (DualRightHandedWeyl.rep.tprod DualRightHandedWeyl.rep)
      (fun l => DualRightHandedWeyl.basis l.1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis l.2) where
  repLorentz_T g l := by
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      DualRightHandedWeyl.rep_apply_basis, DualRightHandedWeyl.rep_apply_basis,
      TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      smul_smul, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_comm]

/-- The `ε` re-index of a family indexed by two Weyl indices: both index slots are
  transported through the symplectic form. -/
noncomputable def epsReindex {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (T : Fin 2 × Fin 2 → B) : Fin 2 × Fin 2 → B :=
  fun l => ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2) • T k

section Reindex

variable {B : Type*} [AddCommGroup B] [Module ℂ B] (T : Fin 2 × Fin 2 → B)

/-- The re-index written out on the diagonal component `(0, 0)`. -/
lemma epsReindex_zero_zero : epsReindex T (0, 0) = T (1, 1) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the mixed component `(0, 1)`. -/
lemma epsReindex_zero_one : epsReindex T (0, 1) = - T (1, 0) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the mixed component `(1, 0)`. -/
lemma epsReindex_one_zero : epsReindex T (1, 0) = - T (0, 1) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The re-index written out on the diagonal component `(1, 1)`. -/
lemma epsReindex_one_one : epsReindex T (1, 1) = T (0, 0) := by
  simp [epsReindex, Fintype.sum_prod_type, Fin.sum_univ_two, SL2C.epsilon_coe]

/-- The `ε` re-index is an involution, because `ε² = -1` on each index slot. -/
lemma epsReindex_epsReindex : epsReindex (epsReindex T) = T := by
  funext l
  obtain ⟨l₁, l₂⟩ := l
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp [epsReindex_zero_zero, epsReindex_zero_one, epsReindex_one_zero,
      epsReindex_one_one]

/-- The `ε` re-index leaves the `ε` contraction unchanged, with no sign or scalar, so a
  conclusion about the re-indexed family is one about the original. -/
lemma epsilonContraction_epsReindex :
    IsBiLeftWeyl.epsilonContraction (T := epsReindex T)
      = IsBiLeftWeyl.epsilonContraction (T := T) := by
  rw [IsBiLeftWeyl.epsilonContraction_eq, IsBiLeftWeyl.epsilonContraction_eq,
    epsReindex_zero_one, epsReindex_one_zero]
  abel

/-- Every re-indexed component lies in the span of the original components. -/
lemma epsReindex_mem_iSup (d : Fin 2 × Fin 2) : epsReindex T d ∈ ⨆ e, ℂ ∙ T e :=
  sum_mem fun k _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem k (Submodule.mem_span_singleton_self _))

/-- The re-index does not change the span of the components. -/
lemma iSup_span_epsReindex : (⨆ d, ℂ ∙ epsReindex T d) = ⨆ d, ℂ ∙ T d := by
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact epsReindex_mem_iSup T d
  · rw [Submodule.span_singleton_le_iff_mem]
    have h : T d = epsReindex (epsReindex T) d := by rw [epsReindex_epsReindex]
    rw [h]
    exact epsReindex_mem_iSup (epsReindex T) d

end Reindex

/-- The single-index form of the symplectic identity: moving a contragredient factor
  across `ε` turns it into a fundamental factor acting on the other slot. -/
lemma sum_epsilon_mul_inv_transpose (g : SL(2,ℂ)) (l a : Fin 2) :
    ∑ k : Fin 2, epsilon.1 l k * (g.1⁻¹)ᵀ a k
      = ∑ b : Fin 2, g.1 b l * epsilon.1 b a := by
  have h : (epsilon.1 * g.1⁻¹) l a = (g.1ᵀ * epsilon.1) l a := by
    rw [SL2C.epsilon_mul_inv_eq_transpose_mul_epsilon]
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using h

/-- The two-index form of the symplectic identity, obtained from the single-index form
  by factorising each sum over the two slots. -/
lemma sum_biEpsilon_mul_inv_transpose (g : SL(2,ℂ)) (l a : Fin 2 × Fin 2) :
    ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * g.1 b.2 l.2)
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
  have hL : (∑ k₁, epsilon.1 l.1 k₁ * (g.1⁻¹)ᵀ a.1 k₁)
      * (∑ k₂, epsilon.1 l.2 k₂ * (g.1⁻¹)ᵀ a.2 k₂)
      = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
        * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
  have hR : (∑ b₁, g.1 b₁ l.1 * epsilon.1 b₁ a.1)
      * (∑ b₂, g.1 b₂ l.2 * epsilon.1 b₂ a.2)
      = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * g.1 b.2 l.2)
        * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => by ring
  rw [← hL, ← hR, sum_epsilon_mul_inv_transpose, sum_epsilon_mul_inv_transpose]

/-- The `ε` re-index turns the contragredient law into the fundamental one for the same
  representation: a change of basis on the index type, not of representation. -/
lemma IsBiDualLeftWeyl.isBiLeftWeyl_epsReindex {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualLeftWeyl B repLorentz T) :
    IsBiLeftWeyl B repLorentz (epsReindex T) where
  repLorentz_T g l := by
    have hstep : ∀ k : Fin 2 × Fin 2,
        (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2) • repLorentz g (T k)
          = ∑ a : Fin 2 × Fin 2, ((epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
              * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2)) • T a := by
      intro k
      rw [hT.repLorentz_T, Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
    calc repLorentz g (epsReindex T l)
        = ∑ k : Fin 2 × Fin 2, (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
            • repLorentz g (T k) := by
          simp only [epsReindex, map_sum, map_smul]
      _ = ∑ a : Fin 2 × Fin 2, (∑ k : Fin 2 × Fin 2,
            (epsilon.1 l.1 k.1 * epsilon.1 l.2 k.2)
              * ((g.1⁻¹)ᵀ a.1 k.1 * (g.1⁻¹)ᵀ a.2 k.2)) • T a := by
          simp only [hstep]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
      _ = ∑ a : Fin 2 × Fin 2, (∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * g.1 b.2 l.2)
            * (epsilon.1 b.1 a.1 * epsilon.1 b.2 a.2)) • T a :=
          Finset.sum_congr rfl fun a _ => by
            rw [sum_biEpsilon_mul_inv_transpose]
      _ = ∑ b : Fin 2 × Fin 2, (g.1 b.1 l.1 * g.1 b.2 l.2) • epsReindex T b := by
          symm
          simp only [epsReindex, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm

/-- Conjugating the group argument undoes the conjugation of the matrix entries: the
  inverse conjugate transpose at `conjHom g` is the plain inverse transpose at `g`. -/
lemma conjHom_inv_conjTranspose (g : SL(2,ℂ)) :
    (((SL2C.conjHom g).1)⁻¹)ᴴ = (g.1⁻¹)ᵀ := by
  have h1 : ((SL2C.conjHom g).1)⁻¹ = (g.1⁻¹).map star := by
    rw [SL2C.inverse_coe, ← map_inv, SL2C.conjHom_coe, SL2C.inverse_coe]
  rw [h1]
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply]

/-- A family with the conjugate contragredient index law is a family with the plain
  contragredient index law for the representation twisted by `conjHom`. -/
lemma IsBiDualRightWeyl.isBiDualLeftWeyl_comp {B : Type*} [AddCommGroup B] [Module ℂ B]
    {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualRightWeyl B repLorentz T) :
    IsBiDualLeftWeyl B (repLorentz.comp SL2C.conjHom) T where
  repLorentz_T g l := by
    have h := hT.repLorentz_T (SL2C.conjHom g) l
    rwa [conjHom_inv_conjTranspose] at h

/-- The `ε` re-index turns a family with the conjugate contragredient index law into a
  family with the fundamental index law for the conjugation-twisted representation. -/
lemma IsBiDualRightWeyl.isBiLeftWeyl_epsReindex {B : Type*} [AddCommGroup B]
    [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}
    (hT : IsBiDualRightWeyl B repLorentz T) :
    IsBiLeftWeyl B (repLorentz.comp SL2C.conjHom) (epsReindex T) :=
  hT.isBiDualLeftWeyl_comp.isBiLeftWeyl_epsReindex

/-!

## K. The classification of the invariants of a dual-index family

Sections G to J assemble into contragredient and conjugate contragredient versions of
`exists_smul_epsilonContraction_of_invariant`, and of its form modulo a stable subspace.
Nothing had to be redone: the argument is generic in the representation, so it applies to
the twisted one as it stands. The re-index leaves the `ε` contraction alone, so the
contraction in the conclusions is that of the original family, `T (0, 1) - T (1, 0)`,
with no sign or scalar attached.

-/

section DualClassification

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {T : Fin 2 × Fin 2 → B}

/-- The `ε` contraction of a family with the contragredient index law is Lorentz
  invariant. -/
lemma IsBiDualLeftWeyl.repLorentz_epsilonContraction
    (hT : IsBiDualLeftWeyl B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (IsBiLeftWeyl.epsilonContraction (T := T))
      = IsBiLeftWeyl.epsilonContraction (T := T) := by
  have h := hT.isBiLeftWeyl_epsReindex.repLorentz_epsilonContraction g
  rwa [epsilonContraction_epsReindex] at h

/-- The `ε` contraction of a family with the conjugate contragredient index law is
  Lorentz invariant. -/
lemma IsBiDualRightWeyl.repLorentz_epsilonContraction
    (hT : IsBiDualRightWeyl B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (IsBiLeftWeyl.epsilonContraction (T := T))
      = IsBiLeftWeyl.epsilonContraction (T := T) := by
  have h := hT.isBiLeftWeyl_epsReindex.repLorentz_epsilonContraction
  rw [epsilonContraction_epsReindex] at h
  exact (forall_comp_apply_eq_self_iff repLorentz SL2C.conjHom_surjective _).1 h g

/-- For the contragredient law, every Lorentz invariant of the span is a multiple of the `ε`
  contraction of that family. -/
theorem IsBiDualLeftWeyl.exists_smul_epsilonContraction_of_invariant
    (hT : IsBiDualLeftWeyl B repLorentz T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • IsBiLeftWeyl.epsilonContraction (T := T) := by
  have hT' := hT.isBiLeftWeyl_epsReindex
  have hx' : x ∈ hT'.span := by
    rw [IsBiLeftWeyl.span, iSup_span_epsReindex]
    exact hx
  obtain ⟨a, ha⟩ := hT'.exists_smul_epsilonContraction_of_invariant hx' hinv
  exact ⟨a, by rwa [epsilonContraction_epsReindex] at ha⟩

/-- The classification of the Lorentz invariants of a family with the contragredient
  index law, modulo a Lorentz-stable submodule `S`. -/
theorem IsBiDualLeftWeyl.exists_smul_epsilonContraction_of_invariant_subset
    (hT : IsBiDualLeftWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ (⨆ d, ℂ ∙ T d) ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • IsBiLeftWeyl.epsilonContraction (T := T) + y := by
  have hT' := hT.isBiLeftWeyl_epsReindex
  have hx' : x ∈ hT'.span ⊔ S := by
    rw [IsBiLeftWeyl.span, iSup_span_epsReindex]
    exact hx
  obtain ⟨a, y, hy, ha⟩ :=
    hT'.exists_smul_epsilonContraction_of_invariant_subset S hS hx' hinv
  exact ⟨a, y, hy, by rwa [epsilonContraction_epsReindex] at ha⟩

/-- The same for the conjugate contragredient law. -/
theorem IsBiDualRightWeyl.exists_smul_epsilonContraction_of_invariant
    (hT : IsBiDualRightWeyl B repLorentz T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • IsBiLeftWeyl.epsilonContraction (T := T) :=
  hT.isBiDualLeftWeyl_comp.exists_smul_epsilonContraction_of_invariant hx
    ((forall_comp_apply_eq_self_iff repLorentz SL2C.conjHom_surjective x).2 hinv)

/-- The classification of the Lorentz invariants of a family with the conjugate
  contragredient index law, modulo a Lorentz-stable submodule `S`. -/
theorem IsBiDualRightWeyl.exists_smul_epsilonContraction_of_invariant_subset
    (hT : IsBiDualRightWeyl B repLorentz T) {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ (⨆ d, ℂ ∙ T d) ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • IsBiLeftWeyl.epsilonContraction (T := T) + y :=
  hT.isBiDualLeftWeyl_comp.exists_smul_epsilonContraction_of_invariant_subset S
    (fun g y hy => hS (SL2C.conjHom g) y hy) hx
    ((forall_comp_apply_eq_self_iff repLorentz SL2C.conjHom_surjective x).2 hinv)

end DualClassification

end Lorentz
