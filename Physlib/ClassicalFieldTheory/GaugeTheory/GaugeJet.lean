/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Physlib.Relativity.DerivAlgebra
/-!
# Jets of a gauge group

## i. Overview

A gauge transformation is a spacetime-dependent element of the gauge group `G₀`; what a
local Lagrangian sees of it is its *jet* at the base point. The jet gauge transformations
form a group `G`, and their infinitesimal counterparts a Lie algebra `𝔤J` over `ℝ`, with the
value at the base point given by `eval : G →* G₀` and `evalLie : 𝔤J →ₗ⁅ℝ⁆ 𝔤`.

This file records, as the class `GaugeJet G 𝔤 G₀ 𝔤J`, exactly the structure of this
situation that the transformation laws of gauge fields and matter fields use:

* the inclusion of constants and evaluation at the base point, on the group and on the
  Lie algebra;
* the formal spacetime derivatives `deriv μ` on `𝔤J`, commuting, satisfying the Leibniz
  rule for the bracket, and killing constants;
* the adjoint action of `G` on `𝔤J`, by Lie algebra automorphisms;
* the Maurer–Cartan form `mc U μ = i (∂_μ U) U⁻¹`, with its flatness equation
  `mc_structure` and the Leibniz rule `deriv_adjoint` for the adjoint action.

For the Standard Model, `G₀ = SU(3) × SU(2) × U(1)` and `G` is the same group with
coefficients in the ring of formal power series in the spacetime coordinates
(`StandardModel.JetGaugeGroupI`); nothing here depends on that choice.

## ii. Key results

- `GaugeJet` : the class.
- `GaugeJet.iteratedDeriv` : the iterated derivative `∂_s` on `𝔤J` along a multiset of
  directions, with `iteratedDeriv_cons`, `iteratedDeriv_add` and the iterated Leibniz rule
  `iteratedDeriv_bracket`.
- `GaugeJetLeibniz` : the Taylor–Leibniz rule for the adjoint action, the input to the
  gauge action on the algebra of gauge-boson symbols.
- `GaugeJetTruncation` : the filtration of `G` by the order to which a jet is trivial, with
  the vanishing of the derivatives of the adjoint action on its members.

-/

@[expose] public section

/-- **Jets of a gauge group.** A gauge group `G₀` with Lie algebra `𝔤`, its group of jets `G`
  with Lie algebra of jets `𝔤J`, evaluation at the base point, formal derivatives, the adjoint
  action and the Maurer–Cartan form, subject to the identities used by the transformation
  laws of gauge and matter fields. -/
class GaugeJet (G : Type) [Group G] (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (G₀ : outParam Type) [Group G₀] (𝔤J : outParam Type) [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J] where
  /-- Evaluation of a gauge jet at the base point. -/
  eval : G →* G₀
  /-- A constant gauge transformation as a jet. -/
  ofConstant : G₀ →* G
  eval_ofConstant : ∀ g, eval (ofConstant g) = g
  /-- Evaluation of a Lie algebra jet at the base point. -/
  evalLie : 𝔤J →ₗ⁅ℝ⁆ 𝔤
  /-- A constant Lie algebra element as a jet. -/
  ofConstantLie : 𝔤 →ₗ[ℝ] 𝔤J
  ofConstantLie_lie : ∀ a b, ofConstantLie ⁅a, b⁆ = ⁅ofConstantLie a, ofConstantLie b⁆
  /-- The formal derivative in the direction `μ`. -/
  deriv : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  deriv_comm : ∀ (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J), deriv μ (deriv ν a) = deriv ν (deriv μ a)
  deriv_bracket : ∀ (μ : Fin 1 ⊕ Fin 3) (x y : 𝔤J),
    deriv μ ⁅x, y⁆ = ⁅deriv μ x, y⁆ + ⁅x, deriv μ y⁆
  deriv_ofConstantLie : ∀ (μ : Fin 1 ⊕ Fin 3) (a : 𝔤), deriv μ (ofConstantLie a) = 0
  /-- The adjoint action of the jet group on the jet Lie algebra. -/
  adjoint : Representation ℝ G 𝔤J
  adjoint_lie : ∀ (U : G) (x y : 𝔤J), adjoint U ⁅x, y⁆ = ⁅adjoint U x, adjoint U y⁆
  /-- The Maurer–Cartan form `i (∂_μ U) U⁻¹` of a gauge jet. -/
  mc : G → (Fin 1 ⊕ Fin 3) → 𝔤J
  mc_one : ∀ μ, mc 1 μ = 0
  /-- The Maurer–Cartan form is a cocycle for the adjoint action. -/
  mc_cocycle : ∀ (U V : G) (μ : Fin 1 ⊕ Fin 3), mc (U * V) μ = mc U μ + adjoint U (mc V μ)
  /-- The Maurer–Cartan form is flat. -/
  mc_structure : ∀ (U : G) (μ ν : Fin 1 ⊕ Fin 3),
    deriv μ (mc U ν) - deriv ν (mc U μ) + ⁅mc U μ, mc U ν⁆ = 0
  /-- The Leibniz rule for the adjoint action. -/
  deriv_adjoint : ∀ (U : G) (μ : Fin 1 ⊕ Fin 3) (x : 𝔤J),
    deriv μ (adjoint U x) = adjoint U (deriv μ x) - ⁅mc U μ, adjoint U x⁆
  /-- The adjoint representation of the value group on its Lie algebra. -/
  adjointValue : Representation ℝ G₀ 𝔤
  /-- At the base point, the adjoint action of a jet on a constant is the adjoint action of
    its value. -/
  evalLie_adjoint_ofConstantLie : ∀ (U : G) (a : 𝔤),
    evalLie (adjoint U (ofConstantLie a)) = adjointValue (eval U) a

namespace GaugeJet

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  [GaugeJet G 𝔤 G₀ 𝔤J]

/-- A constant jet evaluates to its constant. -/
lemma evalLie_ofConstantLie (a : 𝔤) : evalLie G (𝔤 := 𝔤) (ofConstantLie G a) = a := by
  have h := evalLie_adjoint_ofConstantLie (G := G) (𝔤 := 𝔤) 1 a
  simp only [map_one, Module.End.one_apply] at h
  exact h

/-- A jet with trivial value acts trivially on constants at the base point. -/
lemma evalLie_adjoint_ofConstantLie_of_eval_eq_one {U : G} (hU : eval 𝔤 U = 1) (a : 𝔤) :
    evalLie G (adjoint 𝔤 U (ofConstantLie G a)) = a := by
  rw [evalLie_adjoint_ofConstantLie, hU, map_one, Module.End.one_apply]

/-!

## A. The iterated derivative

-/

/-- Post-composition with `deriv` is right-commutative, since formal derivatives
  commute (`deriv_comm`). This is what allows iterated derivatives to be indexed by a
  `Multiset` of directions. -/
instance instRightCommutativeCompDeriv : RightCommutative
    (fun (D : 𝔤J →ₗ[ℝ] 𝔤J) (μ : Fin 1 ⊕ Fin 3) => D.comp (deriv (G := G) (𝔤 := 𝔤) μ)) where
  right_comm D μ ν := by
    refine LinearMap.ext fun a => ?_
    exact congrArg D (deriv_comm (G := G) (𝔤 := 𝔤) μ ν a)

variable (G 𝔤) in
/-- The iterated formal derivative on the jet Lie algebra, in the (unordered, since
  derivatives commute) directions given by the multiset `μs`. -/
noncomputable def iteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) : 𝔤J →ₗ[ℝ] 𝔤J :=
  μs.foldl (fun D μ => D.comp (deriv (G := G) (𝔤 := 𝔤) μ)) LinearMap.id

@[simp]
lemma iteratedDeriv_zero : iteratedDeriv G 𝔤 (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [iteratedDeriv]

lemma iteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedDeriv G 𝔤 (μ ::ₘ μs) = (deriv (G := G) (𝔤 := 𝔤) μ).comp (iteratedDeriv G 𝔤 μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (D : 𝔤J →ₗ[ℝ] 𝔤J),
      s.foldl (fun D μ => D.comp (deriv (G := G) (𝔤 := 𝔤) μ)) D
        = D.comp (iteratedDeriv G 𝔤 s) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro D; simp [iteratedDeriv]
    | cons κ t ih =>
        intro D
        rw [iteratedDeriv, Multiset.foldl_cons, Multiset.foldl_cons, ih, ih]
        simp [LinearMap.comp_assoc]
  rw [iteratedDeriv, Multiset.foldl_cons, h]
  simp

/-- The iterated derivative is additive in the multiset of directions: deriving
  along `s + t` is deriving along `t` and then along `s`. -/
lemma iteratedDeriv_add (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedDeriv G 𝔤 (s + t) = (iteratedDeriv G 𝔤 s).comp (iteratedDeriv G 𝔤 t) := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ s ih =>
      rw [Multiset.cons_add, iteratedDeriv_cons, iteratedDeriv_cons, ih,
        LinearMap.comp_assoc]

@[simp]
lemma iteratedDeriv_singleton (μ : Fin 1 ⊕ Fin 3) :
    iteratedDeriv G 𝔤 ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = deriv (G := G) (𝔤 := 𝔤) μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, iteratedDeriv_cons,
    iteratedDeriv_zero, LinearMap.comp_id]

/-- The iterated Leibniz rule for the bracket: the iterated derivative of a bracket
  is the antidiagonal convolution of iterated derivatives of the two arguments. -/
lemma iteratedDeriv_bracket (s : Multiset (Fin 1 ⊕ Fin 3)) (a b : 𝔤J) :
    iteratedDeriv G 𝔤 s ⁅a, b⁆ =
      (s.antidiagonal.map fun p => ⁅iteratedDeriv G 𝔤 p.1 a, iteratedDeriv G 𝔤 p.2 b⁆).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons κ s ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, ih, map_multiset_sum,
        Multiset.map_map,
        Multiset.map_congr rfl (fun p hp => by
          rw [Function.comp_apply, deriv_bracket,
            show deriv (G := G) (𝔤 := 𝔤) κ (iteratedDeriv G 𝔤 p.1 a)
                = iteratedDeriv G 𝔤 (κ ::ₘ p.1) a from by
              rw [iteratedDeriv_cons]; rfl,
            show deriv (G := G) (𝔤 := 𝔤) κ (iteratedDeriv G 𝔤 p.2 b)
                = iteratedDeriv G 𝔤 (κ ::ₘ p.2) b from by
              rw [iteratedDeriv_cons]; rfl]),
        Multiset.sum_map_add]
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      abel

/-- The iterated derivative of a constant jet vanishes for a nonempty multiset of
  directions. -/
lemma iteratedDeriv_ofConstantLie_of_ne_zero {p : Multiset (Fin 1 ⊕ Fin 3)} (hp : p ≠ 0)
    (a : 𝔤) : iteratedDeriv G 𝔤 p (ofConstantLie G a) = 0 := by
  induction p using Multiset.induction_on with
  | empty => exact absurd rfl hp
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [iteratedDeriv_zero, LinearMap.id_apply, deriv_ofConstantLie]
    · rw [ih ht, map_zero]

end GaugeJet

/-!

## B. The Taylor–Leibniz rule for the adjoint action

-/

/-- **The Taylor–Leibniz rule for the adjoint action**: the base-point Taylor coefficients
  of `Ad_U Y` are the antidiagonal convolution of the Taylor coefficients of `Ad_U` — the
  `evalLie ∘ ∂_p ∘ Ad_U ∘ ofConstantLie` of the covariance machinery — with those of `Y`.
  This is what makes the gauge action on the algebra of gauge-boson symbols a
  representation; for a matrix group it is the Leibniz rule for products of matrices of
  power series. -/
class GaugeJetLeibniz (G : Type) [Group G] (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (G₀ : outParam Type) [Group G₀] (𝔤J : outParam Type) [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    [GaugeJet G 𝔤 G₀ 𝔤J] where
  evalLie_iteratedDeriv_adjoint : ∀ (U : G) (x : Multiset (Fin 1 ⊕ Fin 3)) (Y : 𝔤J),
    GaugeJet.evalLie G (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J)
        (GaugeJet.iteratedDeriv G 𝔤 x (GaugeJet.adjoint 𝔤 (G := G) (G₀ := G₀) (𝔤J := 𝔤J) U Y))
      = (x.antidiagonal.map fun p => GaugeJet.evalLie G (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J)
          (GaugeJet.iteratedDeriv G 𝔤 p.1 (GaugeJet.adjoint 𝔤 (G := G) (G₀ := G₀) (𝔤J := 𝔤J) U
            (GaugeJet.ofConstantLie G (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J)
              (GaugeJet.evalLie G (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J)
                (GaugeJet.iteratedDeriv G 𝔤 p.2 Y)))))).sum

/-!

## C. Truncation

-/

/-- **The truncation filtration of the jet gauge group**: `truncationKer n` is the subgroup
  of jets trivial to order `n`. What is used of it is that on a jet trivial to order `n` all
    derivatives of the adjoint action
  of order between `1` and `n` vanish at the base point. -/
class GaugeJetTruncation (G : Type) [Group G] (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (G₀ : outParam Type) [Group G₀] (𝔤J : outParam Type) [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    [GaugeJet G 𝔤 G₀ 𝔤J] where
  /-- The subgroup of jets trivial to order `n`. -/
  truncationKer : ℕ → Subgroup G
  evalLie_iteratedDeriv_adjoint_ofConstantLie_eq_zero : ∀ {U : G} {n : ℕ},
    U ∈ truncationKer n → ∀ {x : Multiset (Fin 1 ⊕ Fin 3)}, x ≠ 0 → x.card ≤ n →
    ∀ b : 𝔤, GaugeJet.evalLie (G := G) (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J)
      (GaugeJet.iteratedDeriv G 𝔤 x
        (GaugeJet.adjoint (G := G) (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J) U
          (GaugeJet.ofConstantLie (G := G) (𝔤 := 𝔤) (G₀ := G₀) (𝔤J := 𝔤J) b))) = 0
