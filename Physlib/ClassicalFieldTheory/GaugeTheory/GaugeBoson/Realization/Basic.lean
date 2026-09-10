/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeJetAlgebra.GaugeField
/-!
# Realizations of the gauge-boson jet algebra

## i. Overview

An algebra `B` carries the gauge bosons of a gauge theory when the gauge-boson jet algebra,
the universal algebra on the symbols `∂_s A_μ^φ`, maps into it compatibly with the actions
of the jet gauge group and of the Lorentz group. That is the structure
`GaugeAlgebraRealization`: an algebra map `ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤 →ₐ[ℂ] B` equivariant for
the two groups, together with the demands that both groups act on the whole of `B` by
algebra endomorphisms. It is the gauge-boson part of the Standard Model's
`AlgebraRealization`, for any local-gauge-data package `jets`, and every result about a
gauge field in an algebra of local expressions is stated for a realization `h`.

The gauge-field symbols of a realization are the jet algebra's own symbols pushed along
the map, `GaugeAlgebraRealization.A`, and their transformation laws are the jet algebra's
own laws pushed along it. The base case is the jet algebra realized in itself,
`GaugeAlgebraRealization.id`: its Lorentz law is that of a Lorentz derivative, and its gauge
law is the substitution action of the jet gauge group constructed in
`GaugeJetAlgebra.GaugeAction`.

## ii. The physics

Let `A_μ^a` be a gauge field for the gauge group `G₀`, with `μ` a spacetime (covector)
index and `a` an adjoint index. Under a gauge transformation `g` the field transforms as

  `A_μ ↦ Ad_g A_μ + maurerCartan(g)_μ`,

where `maurerCartan(g)_μ = i (∂_μ g) g⁻¹` is the Maurer–Cartan form. The symbols `[∂_s A_μ^a]`
are coordinate functions on the space of field configurations, so the induced (left)
action is the pullback along `g⁻¹`: one substitutes `g⁻¹` into the field law and
differentiates `s` times with the Leibniz rule:

  `g • [∂_s A_μ^a] = ∑_{x+y=s} C(x,y) (∂_x (Ad_{g⁻¹})^a_b)| [∂_y A_μ^b]`
  `                  + (∂_s maurerCartan(g⁻¹)_μ^a)|`,

where `C(x,y)` is the multinomial coefficient of the splitting and `|` denotes
evaluation at the base point. All the data on the right is carried by the *jet* of the
gauge transformation, which is why the gauge representation is a representation of the
jet group `G` and not merely of its value group `G₀`.

In the formalization, `h.A s μ φ` is the symbol `∂_s A_μ^a` contracted with a dual adjoint
vector `φ`; `∂_x (Ad_{g⁻¹})^a_b|` acting on the dual index is `jets.adjointDualCoeff g⁻¹ x φ`;
the sum `∑_{x+y=s} C(x,y)` is the sum over `s.antidiagonal`, in which a splitting `(x, y)`
occurs with multiplicity exactly `C(x,y)`; and `(∂_s maurerCartan(g⁻¹)_μ)|` is
`jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan g⁻¹ μ))`, paired with `φ` and
embedded in `B` as a scalar. This is the law `GaugeAlgebraRealization.gauge_apply_deriv`;
the Lorentz law `GaugeAlgebraRealization.lorentz_apply` says that the symbol carries one
covector index and that each derivative slot transforms as a covector.

## iii. Key results

- `GaugeAlgebraRealization` : an algebra carrying the gauge bosons, as an equivariant
  algebra map out of the jet algebra.
- `GaugeAlgebraRealization.id` : the jet algebra realized in itself.
- `GaugeAlgebraRealization.A` : the gauge-field symbols of a realization, images of the jet
  algebra's symbols, with the laws `lorentz_apply`, `gauge_apply_deriv` and `gauge_mul`.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G 𝔤 G₀ 𝔤J}

open TensorProduct Matrix MatrixGroups Lorentz

/-- An algebra `B` carrying the gauge bosons of the package `jets`: an algebra map out of
  the complexified gauge-boson jet algebra, equivariant for the jet gauge group and the
  Lorentz group, with both groups acting on the whole of `B` by algebra endomorphisms.
  The gauge-field symbols of `B` are the images of the jet algebra's symbols,
  `GaugeAlgebraRealization.A`, and they satisfy the jet algebra's laws by transport. -/
structure GaugeAlgebraRealization (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) (B : Type) [Ring B]
    [Algebra ℂ B] (repJet : Representation ℂ G B) (repLorentz : Representation ℂ SL(2,ℂ) B)
    where
  /-- The algebra map out of the gauge-boson jet algebra: it places the gauge-boson
    symbols, and every polynomial expression in them, inside `B`. -/
  toAlgHom : ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤 →ₐ[ℂ] B
  /-- The gauge-field symbols `∂_s A_μ^φ` of `B`. They are determined by the map, as the
    images of the jet algebra's symbols (`A_eq`), and are recorded as data so that the
    theory can treat them as opaque symbols and a concrete realization can present the
    symbols it already has. -/
  A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B
  /-- The symbols are the images of the jet algebra's symbols. -/
  A_eq : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤),
    A s μ φ = toAlgHom (GaugeJetAlgebra.gaugeField 𝔤 s μ φ)
  /-- The map is equivariant for the jet gauge group. -/
  map_repJet : ∀ (U : G) (x : ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤),
    toAlgHom (GaugeJetAlgebra.complexRepJet jets U x) = repJet U (toAlgHom x)
  /-- The map is equivariant for the Lorentz group. -/
  map_repLorentz : ∀ (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤),
    toAlgHom (GaugeJetAlgebra.complexRepLorentzGroup 𝔤 Λ x) = repLorentz Λ (toAlgHom x)
  /-- The jet gauge group acts on the whole of `B` by algebra endomorphisms. -/
  repJet_mul : ∀ (U : G) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂
  /-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂

namespace GaugeAlgebraRealization

open GaugeJetAlgebra

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ G B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

variable (jets) in
/-- The gauge-boson jet algebra realized in itself, by the identity. -/
noncomputable def id : GaugeAlgebraRealization jets (ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤)
    (complexRepJet jets) (complexRepLorentzGroup 𝔤) where
  toAlgHom := AlgHom.id ℂ _
  A := gaugeField 𝔤
  A_eq _ _ _ := rfl
  map_repJet _ _ := rfl
  map_repLorentz _ _ := rfl
  repJet_mul := complexRepJet_apply_mul
  repLorentz_mul := complexRepLorentzGroup_apply_mul

variable (h : GaugeAlgebraRealization jets B repJet repLorentz)

lemma A_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    h.A s μ φ = h.toAlgHom (gaugeField 𝔤 s μ φ) :=
  h.A_eq s μ φ

@[simp]
lemma id_A : (GaugeAlgebraRealization.id jets).A = gaugeField 𝔤 := rfl

/-- The gauge-field symbols of a realization commute, being images of a commutative
  algebra. -/
lemma commute_A (p q : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ ψ : Module.Dual ℝ 𝔤) : Commute (h.A p μ φ) (h.A q ν ψ) := by
  rw [A_apply, A_apply]
  exact (Commute.all _ _).map h.toAlgHom

/-- The Lorentz law: the gauge-field symbol carries one covector index, and each derivative
  slot transforms as a covector. -/
lemma lorentz_apply (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repLorentz Λ (h.A (List.ofFn l) μ φ) =
      ∑ (p : Fin n → (Fin 1 ⊕ Fin 3)),
        (∏ (i : Fin n), (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • h.A (List.ofFn p) a φ := by
  have key := congrArg h.toAlgHom (repLorentz_gaugeField (𝔤 := 𝔤) Λ l μ φ)
  rw [h.map_repLorentz] at key
  simp only [A_apply]
  refine key.trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul h.toAlgHom _ _)

/-- The gauge law: a jet `U` acts on the derivative symbol `∂_s A_μ^φ` by the Leibniz
  convolution of the dual adjoint Taylor coefficients of `U⁻¹` against lower symbols (the
  multiset antidiagonal carrying the multinomial coefficients), plus the base-point value of
  the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
lemma gauge_apply_deriv (U : G) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repJet U (h.A s μ φ) =
      (s.antidiagonal.map fun p => h.A p.2 μ (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + algebraMap ℂ B (φ (jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U⁻¹ μ)))) := by
  have key := congrArg h.toAlgHom (repJet_gaugeField jets U s μ φ)
  rw [h.map_repJet] at key
  simp only [A_apply]
  refine key.trans ?_
  rw [map_add, map_multiset_sum, Multiset.map_map, AlgHom.commutes]
  rfl

include h in
/-- The gauge action preserves products: gauge transformations act on the algebra of local
  expressions as algebra homomorphisms. -/
lemma gauge_mul (U : G) (b₁ b₂ : B) : repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂ :=
  h.repJet_mul U b₁ b₂

end GaugeAlgebraRealization
