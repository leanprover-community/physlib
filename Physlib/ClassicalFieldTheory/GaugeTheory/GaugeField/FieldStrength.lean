/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeField.TransformsInAdjoint
/-!

# The field strength

The field strength is defined as
```
  F_{μν} = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆
```
with `⁅·,·⁆` the gauge-algebra bracket, which already carries the physicists' factor
of `i` (on the matrix factors `⁅a, b⁆ = i(ab − ba)`). In terms of the plain matrix
commutator this is `F_{μν} = ∂_μ A_ν − ∂_ν A_μ + i [A_μ, A_ν]`, the sign forced by
the convention `ω_μ(g) = i (∂_μ g) g⁻¹` for the Maurer–Cartan form (equivalently, by
its structural equation `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`): only with this
coefficient do the inhomogeneous terms cancel. With the derivative symbols as
primitives the field strength is itself a family of derivative symbols
`s ↦ [∂_s F_μν]`: the derivative terms shift the multiset index, the commutator term
is the Leibniz convolution `commutatorFam`. It transforms in the adjoint at every
derivative order simultaneously (`repGauge_fieldStrength`,
`transformsInAdjoint_fieldStrength`).

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct
variable {B : Type} [Ring B] [Algebra ℂ B]
variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable [GaugeJet G 𝔤 G₀ 𝔤J]

namespace IsGaugeField

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ G B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}

/-- The field strength `F_μν = ∂_μ A_ν − ∂_ν A_μ + ⁅A_μ, A_ν⁆` of a family of
  gauge-field symbols, as a family of derivative symbols: the `s`-th derivative has
  the derivative terms through the shifted symbols `A (μ ::ₘ s) ν`, the commutator
  term through the Leibniz convolution `commutatorFam`. This is the physicists'
  `F_μν^a = ∂_μ A_ν^a − ∂_ν A_μ^a + f^a_{bc} A_μ^b A_ν^c`: the gauge-algebra bracket
  already carries the physicists' factor of `i`, so no explicit factor appears — the
  same normalization as in the structural equation of the Maurer–Cartan form, which
  is exactly what makes the field strength transform without inhomogeneous terms
  (`repGauge_fieldStrength`). -/
noncomputable def fieldStrength
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  A (μ ::ₘ s) ν - A (ν ::ₘ s) μ + commutatorFam A μ ν s

@[simp]
lemma fieldStrength_apply
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ 𝔤) :
    fieldStrength A μ ν s φ = A (μ ::ₘ s) ν φ - A (ν ::ₘ s) μ φ + commutatorFam A μ ν s φ :=
  rfl

/-- The underived field strength: derivative symbols on singletons, plus the plain
  commutator. -/
lemma fieldStrength_zero
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength A μ ν 0 = A {μ} ν - A {ν} μ + commutator A μ ν := by
  rw [fieldStrength, commutatorFam_zero]
  rfl

/-- The antisymmetrized pair of derivative symbols is the field strength minus its
  commutator term. -/
lemma pair_eq_fieldStrength_sub_commutatorFam
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (ν μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    A (ν ::ₘ s) μ - A (μ ::ₘ s) ν = fieldStrength A ν μ s - commutatorFam A ν μ s := by
  rw [fieldStrength, add_sub_cancel_right]

/-!

## The antisymmetry of the field strength

The field strength is antisymmetric in its two covector indices as soon as the
symbols of the gauge field commute with one another in `B`: the two derivative terms
swap outright, and the commutator term swaps by the antisymmetry of the gauge-algebra
bracket, once the two factors of each product may be exchanged.

-/

/-- The bracket of two component families with commuting values is antisymmetric: in
  the basis expansion the structure constants are antisymmetric in the two gauge
  indices, and the two field factors of each term may be exchanged. -/
lemma bracketFam_swap_of_commute {f g : Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
    (hfg : ∀ φ ψ, Commute (f φ) (g ψ)) :
    bracketFam g f = - bracketFam f g := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.neg_apply, bracketFam_apply_eq_sum, bracketFam_apply_eq_sum]
  set bv := Module.Free.chooseBasis ℝ 𝔤 with hbv
  have hstep : ∀ j k, φ ⁅bv j, bv k⁆ • (g (bv.coord j) * f (bv.coord k)) =
      -(φ ⁅bv k, bv j⁆ • (f (bv.coord k) * g (bv.coord j))) := by
    intro j k
    rw [(hfg (bv.coord k) (bv.coord j)).eq, ← lie_skew (bv k) (bv j), map_neg,
      neg_smul, neg_neg]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hstep j k]
  simp only [Finset.sum_neg_distrib]
  exact congrArg Neg.neg Finset.sum_comm

/-- The derived commutator term is antisymmetric in its two directions when the symbols
  of the gauge field commute: swapping the two parts of the antidiagonal matches the
  Leibniz convolution with the swapped one termwise. -/
lemma commutatorFam_swap
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (hA : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
      (ψ ψ' : Module.Dual ℝ 𝔤), Commute (A s μ ψ) (A s' μ' ψ'))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    commutatorFam A ν μ s = - commutatorFam A μ ν s := by
  rw [commutatorFam, commutatorFam,
    Multiset.sum_antidiagonal_swap s (fun a b => bracketFam (A a ν) (A b μ)),
    ← Multiset.sum_map_neg'']
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ =>
    bracketFam_swap_of_commute fun φ ψ => hA _ _ _ _ _ _)

/-- The field strength is antisymmetric in its two covector indices when the symbols of
  the gauge field commute: the two derivative terms swap outright, the commutator term
  by `commutatorFam_swap`. -/
lemma fieldStrength_swap
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (hA : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
      (ψ ψ' : Module.Dual ℝ 𝔤), Commute (A s μ ψ) (A s' μ' ψ'))
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    fieldStrength A ν μ s = - fieldStrength A μ ν s := by
  rw [fieldStrength, fieldStrength, commutatorFam_swap A hA μ ν s]
  abel

/-- **The field strength transforms in the adjoint, at every derivative order**: under
  a gauge jet `U` every derivative symbol of `F_μν` transforms by the pure Leibniz
  convolution of the dual adjoint action over the multiset antidiagonal — the exact
  analogue of `gauge_apply_deriv` with *no* Maurer–Cartan shift, since the field
  strength transforms homogeneously. The `κ`-into-the-adjoint splittings of the
  derivative terms (`repGauge_cons_apply`) cancel the `ad` cross-term convolutions of
  the commutator (`repGauge_commutatorFam`) through the coassociativity and swap of
  the antidiagonal, and the derived Maurer–Cartan shifts cancel the bracket-shift
  convolution through the all-orders structural equation. -/
theorem repGauge_fieldStrength (hA : IsGaugeField repLorentz repGauge A)
    (U : G) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repGauge U (fieldStrength A μ ν s φ) =
      (s.antidiagonal.map fun p =>
        fieldStrength A μ ν p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum := by
  have hL : repGauge U (fieldStrength A μ ν s φ) =
      repGauge U (A (μ ::ₘ s) ν φ) - repGauge U (A (ν ::ₘ s) μ φ)
      + repGauge U (commutatorFam A μ ν s φ) := by
    rw [fieldStrength_apply, map_add, map_sub]
  have hR : (s.antidiagonal.map fun p =>
      fieldStrength A μ ν p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        A (μ ::ₘ p.2) ν (adjointDualCoeff U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
        A (ν ::ₘ p.2) μ (adjointDualCoeff U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
        commutatorFam A μ ν p.2 (adjointDualCoeff U⁻¹ p.1 φ)).sum := by
    rw [← Multiset.sum_map_sub, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [fieldStrength_apply]
  have hcancel₁ : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        A p.2 ν (adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 q.1 (GaugeJet.mc 𝔤 (G := G) U⁻¹ μ)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        A r.2 ν (adjointDualCoeff U⁻¹ r.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 p.1 (GaugeJet.mc 𝔤 (G := G) U⁻¹ μ)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      A c ν (adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
          (GaugeJet.iteratedDeriv G 𝔤 a (GaugeJet.mc 𝔤 (G := G) U⁻¹ μ))))))
  have hcancel₂ : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        A p.2 μ (adjointDualCoeff U⁻¹ q.2
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 q.1 (GaugeJet.mc 𝔤 (G := G) U⁻¹ ν)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        A q.2 μ (adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 p.2 (GaugeJet.mc 𝔤 (G := G) U⁻¹ ν)))))).sum).sum := by
    refine (Multiset.sum_antidiagonal_assoc s (fun a b c =>
      A c μ (adjointDualCoeff U⁻¹ b
        (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
          (GaugeJet.iteratedDeriv G 𝔤 a (GaugeJet.mc 𝔤 (G := G) U⁻¹ ν))))))).trans ?_
    exact Multiset.sum_antidiagonal_swap s (fun a b =>
      (b.antidiagonal.map fun q =>
        A q.2 μ (adjointDualCoeff U⁻¹ q.1
          (φ ∘ₗ LieAlgebra.ad ℝ 𝔤 (GaugeJet.evalLie G (𝔤 := 𝔤)
            (GaugeJet.iteratedDeriv G 𝔤 a (GaugeJet.mc 𝔤 (G := G) U⁻¹ ν)))))).sum)
  set Θ : 𝔤 →+ B := ((algebraMap ℂ B).toAddMonoidHom.comp
    ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp φ.toAddMonoidHom)) with hΘdef
  have hΘ : ∀ z : 𝔤, algebraMap ℂ B ((φ z : ℝ) : ℂ) = Θ z := fun z => rfl
  have hconst : Θ (GaugeJet.evalLie G (𝔤 := 𝔤) (GaugeJet.iteratedDeriv G 𝔤 (μ ::ₘ s)
      (GaugeJet.mc 𝔤 (G := G) U⁻¹ ν))) =
    Θ (GaugeJet.evalLie G (𝔤 := 𝔤) (GaugeJet.iteratedDeriv G 𝔤 (ν ::ₘ s)
      (GaugeJet.mc 𝔤 (G := G) U⁻¹ μ)))
    - (s.antidiagonal.map fun p =>
        Θ ⁅GaugeJet.evalLie G (𝔤 := 𝔤) (GaugeJet.iteratedDeriv G 𝔤 p.1
            (GaugeJet.mc 𝔤 (G := G) U⁻¹ μ)),
          GaugeJet.evalLie G (𝔤 := 𝔤) (GaugeJet.iteratedDeriv G 𝔤 p.2
            (GaugeJet.mc 𝔤 (G := G) U⁻¹ ν))⁆).sum := by
    rw [eval_iteratedDeriv_maurerCartan_structure U⁻¹ s μ ν, map_sub, map_multiset_sum,
      Multiset.map_map]
    congr 1
  rw [hL, repGauge_cons_apply hA U μ s ν φ, repGauge_cons_apply hA U ν s μ φ,
    hA.repGauge_commutatorFam U s μ ν φ, hR]
  simp only [hΘ]
  rw [hconst, hcancel₁, hcancel₂]
  abel

/-- **The field strength is an adjoint gauge tensor**: the packaging of
  `repGauge_fieldStrength` as `TransformsInAdjoint` — the base case of the
  covariant-derivative recursion `TransformsInAdjoint.covDerivAdjoint`. -/
theorem transformsInAdjoint_fieldStrength (hA : IsGaugeField repLorentz repGauge A)
    (μ ν : Fin 1 ⊕ Fin 3) : TransformsInAdjoint repGauge (fieldStrength A μ ν) :=
  fun U φ s => hA.repGauge_fieldStrength U s μ ν φ

/-- The underived transformation law: at `s = 0` the Leibniz convolution collapses to
  the homogeneous law — the field strength transforms by the base-point dual adjoint
  action of `U⁻¹` on the adjoint index. -/
lemma repGauge_fieldStrength_zero (hA : IsGaugeField repLorentz repGauge A)
    (U : G) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repGauge U (fieldStrength A μ ν 0 φ) =
      fieldStrength A μ ν 0 (adjointDualCoeff U⁻¹ 0 φ) := by
  rw [hA.repGauge_fieldStrength U 0 μ ν φ, Multiset.antidiagonal_zero,
    Multiset.map_singleton, Multiset.sum_singleton]

end IsGaugeField

