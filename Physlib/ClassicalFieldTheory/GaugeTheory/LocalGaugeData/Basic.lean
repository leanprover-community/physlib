/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Physlib.Mathematics.MultisetAntidiagonal
public import Physlib.Relativity.DerivAlgebra
/-!
# Local gauge data

## i. Overview

A gauge transformation is a spacetime-dependent element of the gauge group `G₀`; what a
local Lagrangian sees of it is its *jet* at the base point. The jet gauge transformations
form a group `G`, and their infinitesimal counterparts a Lie algebra `𝔤J` over `ℝ`, with the
value at the base point given by `eval : G →* G₀` and `evalLie : 𝔤J →ₗ⁅ℝ⁆ 𝔤`.

This file records, as the structure `LocalGaugeData G 𝔤 G₀ 𝔤J`, exactly the structure of
this situation that the transformation laws of gauge fields and matter fields use:

* the inclusion of constants and evaluation at the base point, on the group and on the
  Lie algebra;
* the formal spacetime derivatives `deriv μ` on `𝔤J`, commuting, satisfying the Leibniz
  rule for the bracket, and killing constants;
* the adjoint action of `G` on `𝔤J`, by Lie algebra automorphisms, evaluating at the base
  point to the adjoint action of `G₀` on `𝔤`;
* the Maurer–Cartan form `maurerCartan U μ = i (∂_μ U) U⁻¹`, with its cocycle law, its
  flatness equation `maurerCartan_structure` and the Leibniz rule `deriv_adjoint` for the
  adjoint action.

Everything else — the Taylor coefficients of the adjoint action, the truncation filtration
of `G`, the symmetrized Maurer–Cartan form — is *derived* from these laws in the sibling
files of this folder. Two further properties, which are true of any honest jet group but are
not consequences of the transformation laws, are collected in the mixin `Faithful`: an
element of `𝔤J` is determined by its base-point Taylor data, and a jet with vanishing
Maurer–Cartan form is constant.

A term `jets : LocalGaugeData G 𝔤 G₀ 𝔤J` is supplied, not inferred: every construction
below, and every construction downstream, takes the package it works over as an ordinary
argument. The four carriers do not determine it — a truncated jet group beside the full
one is the same four carriers with different data — so there is nothing canonical for
instance search to choose.

For the Standard Model, `G₀ = SU(3) × SU(2) × U(1)` and `G` is the same group with
coefficients in the ring of formal power series in the spacetime coordinates
(`StandardModel.JetGaugeGroupI`), packaged as `StandardModel.localGaugeData`; nothing here
depends on that choice.

## ii. Key results

- `LocalGaugeData` : the structure.
- `LocalGaugeData.maurerCartan_one`, `LocalGaugeData.maurerCartan_inv` : the values of the
  Maurer–Cartan form on the identity and on inverses, from the cocycle law.
- `LocalGaugeData.maurerCartan_eq_of_deriv_adjoint` : the Maurer–Cartan form is determined
  by the Leibniz rule `deriv_adjoint` up to the centre of `𝔤J`, and so is genuine data
  only because that centre can be nonzero.
- `LocalGaugeData.iteratedDeriv` : the iterated derivative `∂_s` on `𝔤J` along a multiset
  of directions, with `iteratedDeriv_cons`, `iteratedDeriv_add` and the iterated Leibniz
  rule `iteratedDeriv_bracket`.
- `LocalGaugeData.evalLie_iteratedDeriv_coord` : the Euler identity for the coordinates.
- `LocalGaugeData.Faithful` : the jets are determined by their base-point Taylor data.

## iii. Table of contents

- A. The structure
- B. First consequences of the laws
- C. The iterated derivative
- D. Faithful packages

-/

@[expose] public section

/-!

## A. The structure

-/

/-- Local gauge data. A gauge group `G₀` with Lie algebra `𝔤`, its group of jets `G` with
  Lie algebra of jets `𝔤J`, evaluation at the base point, formal derivatives, the adjoint
  action and the Maurer–Cartan form, subject to the identities used by the transformation
  laws of gauge and matter fields.

  This is data attached to the four carriers, not a property of them, and it is passed
  explicitly: the generic theory takes `jets : LocalGaugeData G 𝔤 G₀ 𝔤J` as an argument rather
  than searching for it. -/
structure LocalGaugeData (G : Type) [Group G] (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (G₀ : Type) [Group G₀] (𝔤J : Type) [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J] where
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
  evalLie_ofConstantLie : ∀ a, evalLie (ofConstantLie a) = a
  /-- The formal derivative in the direction `μ`. -/
  deriv : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  deriv_comm : ∀ (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J), deriv μ (deriv ν a) = deriv ν (deriv μ a)
  deriv_bracket : ∀ (μ : Fin 1 ⊕ Fin 3) (x y : 𝔤J),
    deriv μ ⁅x, y⁆ = ⁅deriv μ x, y⁆ + ⁅x, deriv μ y⁆
  deriv_ofConstantLie : ∀ (μ : Fin 1 ⊕ Fin 3) (a : 𝔤), deriv μ (ofConstantLie a) = 0
  /-- Multiplication of a jet by the spacetime coordinate `x_μ`. -/
  coord : (Fin 1 ⊕ Fin 3) → 𝔤J →ₗ[ℝ] 𝔤J
  /-- The Leibniz rule for a coordinate: `∂_μ (x_ν a) = x_ν ∂_μ a + δ_{μν} a`. -/
  deriv_coord : ∀ (μ ν : Fin 1 ⊕ Fin 3) (a : 𝔤J),
    deriv μ (coord ν a) = coord ν (deriv μ a) + if μ = ν then a else 0
  /-- A coordinate vanishes at the base point. -/
  evalLie_coord : ∀ (μ : Fin 1 ⊕ Fin 3) (a : 𝔤J), evalLie (coord μ a) = 0
  /-- The coordinates are central for the bracket. -/
  coord_lie : ∀ (μ : Fin 1 ⊕ Fin 3) (a b : 𝔤J), ⁅coord μ a, b⁆ = coord μ ⁅a, b⁆
  /-- The adjoint action of the jet group on the jet Lie algebra. -/
  adjoint : Representation ℝ G 𝔤J
  adjoint_lie : ∀ (U : G) (x y : 𝔤J), adjoint U ⁅x, y⁆ = ⁅adjoint U x, adjoint U y⁆
  /-- The adjoint representation of the value group on its Lie algebra. -/
  adjointValue : Representation ℝ G₀ 𝔤
  /-- At the base point the adjoint action of a jet is the adjoint action of its value. -/
  evalLie_adjoint : ∀ (U : G) (x : 𝔤J), evalLie (adjoint U x) = adjointValue (eval U) (evalLie x)
  /-- The Maurer–Cartan form `i (∂_μ U) U⁻¹` of a gauge jet. -/
  maurerCartan : G → (Fin 1 ⊕ Fin 3) → 𝔤J
  /-- A constant gauge transformation has vanishing Maurer–Cartan form: it has no
    spacetime dependence to differentiate. -/
  maurerCartan_ofConstant : ∀ (g : G₀) (μ : Fin 1 ⊕ Fin 3), maurerCartan (ofConstant g) μ = 0
  /-- The Maurer–Cartan form is a cocycle for the adjoint action. -/
  maurerCartan_cocycle : ∀ (U V : G) (μ : Fin 1 ⊕ Fin 3),
    maurerCartan (U * V) μ = maurerCartan U μ + adjoint U (maurerCartan V μ)
  /-- The Maurer–Cartan form is flat. -/
  maurerCartan_structure : ∀ (U : G) (μ ν : Fin 1 ⊕ Fin 3),
    deriv μ (maurerCartan U ν) - deriv ν (maurerCartan U μ)
      + ⁅maurerCartan U μ, maurerCartan U ν⁆ = 0
  /-- The Leibniz rule for the adjoint action. -/
  deriv_adjoint : ∀ (U : G) (μ : Fin 1 ⊕ Fin 3) (x : 𝔤J),
    deriv μ (adjoint U x) = adjoint U (deriv μ x) - ⁅maurerCartan U μ, adjoint U x⁆

namespace LocalGaugeData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  (jets : LocalGaugeData G 𝔤 G₀ 𝔤J)

/-!

## B. First consequences of the laws

-/

/-- The Maurer–Cartan form of the identity vanishes: the cocycle law at `1 * 1 = 1`. -/
@[simp]
lemma maurerCartan_one (μ : Fin 1 ⊕ Fin 3) : jets.maurerCartan 1 μ = 0 := by
  have h := jets.maurerCartan_cocycle 1 1 μ
  rw [one_mul, map_one, Module.End.one_apply] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The Maurer–Cartan form of an inverse: `ω_μ(U⁻¹) = − Ad_{U⁻¹} ω_μ(U)`, the cocycle
  law applied to `U⁻¹ U = 1`. -/
lemma maurerCartan_inv (U : G) (μ : Fin 1 ⊕ Fin 3) :
    jets.maurerCartan U⁻¹ μ = - jets.adjoint U⁻¹ (jets.maurerCartan U μ) := by
  have h := jets.maurerCartan_cocycle U⁻¹ U μ
  rw [inv_mul_cancel, jets.maurerCartan_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- At the base point, the adjoint action of a jet on a constant is the adjoint action of
  its value. -/
lemma evalLie_adjoint_ofConstantLie (U : G) (a : 𝔤) :
    jets.evalLie (jets.adjoint U (jets.ofConstantLie a)) = jets.adjointValue (jets.eval U) a := by
  rw [jets.evalLie_adjoint, jets.evalLie_ofConstantLie]

/-- A jet with trivial value acts trivially on constants at the base point. -/
lemma evalLie_adjoint_ofConstantLie_of_eval_eq_one {U : G} (hU : jets.eval U = 1) (a : 𝔤) :
    jets.evalLie (jets.adjoint U (jets.ofConstantLie a)) = a := by
  rw [evalLie_adjoint_ofConstantLie, hU, map_one, Module.End.one_apply]

/-- The Maurer–Cartan form is determined by the Leibniz rule, up to the centre. Since
  `adjoint U` is invertible, `deriv_adjoint` says exactly that the inner derivation
  `⁅maurerCartan U μ, ·⁆` is `adjoint U ∘ deriv μ ∘ adjoint U⁻¹ − deriv μ`; so any other
  form obeying the same rule differs from it by something acting trivially in the adjoint
  representation of `𝔤J`. It follows that the Maurer–Cartan form is redundant data exactly
  when that representation is faithful — which it is not for the Standard Model, whose jet
  gauge algebra has a central `u(1)` factor. That is why `maurerCartan` is a field of the
  structure rather than a construction from the rest of it. -/
lemma maurerCartan_eq_of_deriv_adjoint
    (hfaithful : ∀ x y : 𝔤J, (∀ z : 𝔤J, ⁅x, z⁆ = ⁅y, z⁆) → x = y)
    (ω : G → (Fin 1 ⊕ Fin 3) → 𝔤J)
    (hω : ∀ (U : G) (μ : Fin 1 ⊕ Fin 3) (x : 𝔤J),
      jets.deriv μ (jets.adjoint U x)
        = jets.adjoint U (jets.deriv μ x) - ⁅ω U μ, jets.adjoint U x⁆) :
    ω = jets.maurerCartan := by
  funext U μ
  refine hfaithful _ _ fun z => ?_
  have hz : jets.adjoint U (jets.adjoint U⁻¹ z) = z := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h1 := hω U μ (jets.adjoint U⁻¹ z)
  have h2 := jets.deriv_adjoint U μ (jets.adjoint U⁻¹ z)
  rw [hz] at h1 h2
  exact sub_right_injective (h1.symm.trans h2)

/-!

## C. The iterated derivative

-/

/-- Post-composition with `deriv` is right-commutative, since formal derivatives
  commute (`deriv_comm`). This is what allows iterated derivatives to be indexed by a
  `Multiset` of directions. -/
instance instRightCommutativeCompDeriv : RightCommutative
    (fun (D : 𝔤J →ₗ[ℝ] 𝔤J) (μ : Fin 1 ⊕ Fin 3) => D.comp (jets.deriv μ)) where
  right_comm D μ ν := by
    refine LinearMap.ext fun a => ?_
    exact congrArg D (jets.deriv_comm μ ν a)

/-- The iterated formal derivative on the jet Lie algebra, in the (unordered, since
  derivatives commute) directions given by the multiset `μs`. -/
noncomputable def iteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) : 𝔤J →ₗ[ℝ] 𝔤J :=
  μs.foldl (fun D μ => D.comp (jets.deriv μ)) LinearMap.id

@[simp]
lemma iteratedDeriv_zero : jets.iteratedDeriv (0 : Multiset (Fin 1 ⊕ Fin 3)) = LinearMap.id := by
  simp [iteratedDeriv]

lemma iteratedDeriv_cons (μ : Fin 1 ⊕ Fin 3) (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.iteratedDeriv (μ ::ₘ μs) = (jets.deriv μ).comp (jets.iteratedDeriv μs) := by
  have h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (D : 𝔤J →ₗ[ℝ] 𝔤J),
      s.foldl (fun D μ => D.comp (jets.deriv μ)) D = D.comp (jets.iteratedDeriv s) := by
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
    jets.iteratedDeriv (s + t) = (jets.iteratedDeriv s).comp (jets.iteratedDeriv t) := by
  induction s using Multiset.induction_on with
  | empty => simp [iteratedDeriv_zero]
  | cons μ s ih =>
      rw [Multiset.cons_add, iteratedDeriv_cons, iteratedDeriv_cons, ih,
        LinearMap.comp_assoc]

@[simp]
lemma iteratedDeriv_singleton (μ : Fin 1 ⊕ Fin 3) :
    jets.iteratedDeriv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = jets.deriv μ := by
  rw [show ({μ} : Multiset (Fin 1 ⊕ Fin 3)) = μ ::ₘ 0 from rfl, iteratedDeriv_cons,
    iteratedDeriv_zero, LinearMap.comp_id]

/-- Since derivatives commute, the direction added by `cons` may be taken first as well
  as last. -/
lemma iteratedDeriv_cons_eq_comp_deriv (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    jets.iteratedDeriv (μ ::ₘ s) = (jets.iteratedDeriv s).comp (jets.deriv μ) := by
  rw [show (μ ::ₘ s : Multiset (Fin 1 ⊕ Fin 3)) = s + {μ} from by
      rw [add_comm, Multiset.singleton_add],
    iteratedDeriv_add, iteratedDeriv_singleton]

/-- The iterated Leibniz rule for the bracket: the iterated derivative of a bracket
  is the antidiagonal convolution of iterated derivatives of the two arguments. -/
lemma iteratedDeriv_bracket (s : Multiset (Fin 1 ⊕ Fin 3)) (a b : 𝔤J) :
    jets.iteratedDeriv s ⁅a, b⁆ =
      (s.antidiagonal.map fun p =>
        ⁅jets.iteratedDeriv p.1 a, jets.iteratedDeriv p.2 b⁆).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons κ s ih =>
      rw [iteratedDeriv_cons, LinearMap.comp_apply, ih, map_multiset_sum,
        Multiset.map_map,
        Multiset.map_congr rfl (fun p hp => by
          rw [Function.comp_apply, jets.deriv_bracket,
            show jets.deriv κ (jets.iteratedDeriv p.1 a)
                = jets.iteratedDeriv (κ ::ₘ p.1) a from by
              rw [iteratedDeriv_cons]; rfl,
            show jets.deriv κ (jets.iteratedDeriv p.2 b)
                = jets.iteratedDeriv (κ ::ₘ p.2) b from by
              rw [iteratedDeriv_cons]; rfl]),
        Multiset.sum_map_add]
      simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
        Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      abel

/-- The base-point Taylor data of a bracket is determined by that of its arguments.
  If the base-point values of the iterated derivatives of `a` and `b` along sub-multisets
  of `w` agree with those of `a'` and `b'`, then so do those of the brackets: the iterated
  Leibniz rule expands the bracket over the antidiagonal of `w`, whose parts are all
  sub-multisets of `w`. -/
lemma evalLie_iteratedDeriv_bracket_congr (w : Multiset (Fin 1 ⊕ Fin 3)) (a b a' b' : 𝔤J)
    (ha : ∀ p ≤ w, jets.evalLie (jets.iteratedDeriv p a)
      = jets.evalLie (jets.iteratedDeriv p a'))
    (hb : ∀ p ≤ w, jets.evalLie (jets.iteratedDeriv p b)
      = jets.evalLie (jets.iteratedDeriv p b')) :
    jets.evalLie (jets.iteratedDeriv w ⁅a, b⁆)
      = jets.evalLie (jets.iteratedDeriv w ⁅a', b'⁆) := by
  rw [iteratedDeriv_bracket, iteratedDeriv_bracket, map_multiset_sum, map_multiset_sum,
    Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [LieHom.map_lie, LieHom.map_lie, ha p.1 (Multiset.fst_le_of_mem_antidiagonal hp),
    hb p.2 (Multiset.snd_le_of_mem_antidiagonal hp)]

/-- The iterated derivative of a constant jet vanishes for a nonempty multiset of
  directions. -/
lemma iteratedDeriv_ofConstantLie_of_ne_zero {p : Multiset (Fin 1 ⊕ Fin 3)} (hp : p ≠ 0)
    (a : 𝔤) : jets.iteratedDeriv p (jets.ofConstantLie a) = 0 := by
  induction p using Multiset.induction_on with
  | empty => exact absurd rfl hp
  | cons μ t ih =>
    rw [iteratedDeriv_cons, LinearMap.comp_apply]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [iteratedDeriv_zero, LinearMap.id_apply, deriv_ofConstantLie]
    · rw [ih ht, map_zero]

TODO "Add product of LocalGaugeData."

/-- The Euler identity: at the base point, `x_μ` acts on the `s`-th derivative by
  removing one `μ` and counting how many there were. With `∂_s` the derivatives in `s`,
  `(∂_s (x_μ a))|₀ = s(μ) · (∂_{s − μ} a)|₀`. -/
lemma evalLie_iteratedDeriv_coord (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J) :
    jets.evalLie (jets.iteratedDeriv s (jets.coord μ a)) =
      s.count μ • jets.evalLie (jets.iteratedDeriv (s.erase μ) a) := by
  induction s using Multiset.induction_on generalizing a with
  | empty => simp [jets.evalLie_coord]
  | cons ν s ih =>
      rw [iteratedDeriv_cons_eq_comp_deriv, LinearMap.comp_apply, jets.deriv_coord, map_add,
        map_add, ih]
      by_cases hνμ : ν = μ
      · subst hνμ
        rw [if_pos rfl, Multiset.count_cons_self, Multiset.erase_cons_head, add_smul, one_smul,
          ← LinearMap.comp_apply (jets.iteratedDeriv (s.erase ν)),
          ← iteratedDeriv_cons_eq_comp_deriv]
        by_cases hμ : ν ∈ s
        · rw [Multiset.cons_erase hμ]
        · rw [Multiset.count_eq_zero.mpr hμ, zero_smul, zero_smul]
      · rw [if_neg hνμ, map_zero, map_zero, add_zero, Multiset.count_cons_of_ne (Ne.symm hνμ),
          Multiset.erase_cons_tail s hνμ, ← LinearMap.comp_apply (jets.iteratedDeriv (s.erase μ)),
          ← iteratedDeriv_cons_eq_comp_deriv]

/-!

## D. Faithful packages

The transformation laws never ask that the jets be *honest* jets: nothing in the structure
prevents `𝔤J` from carrying elements invisible to every base-point derivative. The two laws
below say that it does not, and together they make a pure jet (`eval U = 1`) recoverable
from its Maurer–Cartan form; see `LocalGaugeData.maurerCartan_injOn_truncationKer_zero`.
They hold for the full jet group of any matrix group and for its truncations, but are
recorded separately from the structure because the covariance theory does not need them.

-/

/-- A package is faithful when an element of `𝔤J` is determined by the base-point values
  of its iterated derivatives (Taylor determinacy) and a jet with vanishing Maurer–Cartan
  form is the constant jet of its value. -/
class Faithful (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) : Prop where
  ext_of_evalLie_iteratedDeriv : ∀ {x y : 𝔤J},
    (∀ s : Multiset (Fin 1 ⊕ Fin 3),
      jets.evalLie (jets.iteratedDeriv s x) = jets.evalLie (jets.iteratedDeriv s y)) → x = y
  eq_ofConstant_of_maurerCartan_eq_zero : ∀ {U : G},
    jets.maurerCartan U = 0 → U = jets.ofConstant (jets.eval U)

/-- Taylor determinacy of a faithful package, in the form of an extensionality lemma. -/
lemma ext_of_evalLie_iteratedDeriv [jets.Faithful] {x y : 𝔤J}
    (h : ∀ s : Multiset (Fin 1 ⊕ Fin 3),
      jets.evalLie (jets.iteratedDeriv s x) = jets.evalLie (jets.iteratedDeriv s y)) :
    x = y :=
  Faithful.ext_of_evalLie_iteratedDeriv h

/-- In a faithful package, the Maurer–Cartan form vanishes exactly on the constant jets. -/
lemma maurerCartan_eq_zero_iff [jets.Faithful] (U : G) :
    jets.maurerCartan U = 0 ↔ U = jets.ofConstant (jets.eval U) := by
  refine ⟨Faithful.eq_ofConstant_of_maurerCartan_eq_zero, fun h => ?_⟩
  funext μ
  rw [h, jets.maurerCartan_ofConstant]
  rfl

end LocalGaugeData
