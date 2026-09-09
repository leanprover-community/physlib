/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!

# W⋆-algebras: predual and the weak-⋆ topology

A W⋆-algebra is a C⋆-algebra that is additionally, isometrically, the Banach-space dual of some
other Banach space — Sakai's characterization of a von Neumann algebra, purely in Banach-space
terms. There is no need for any Hilbert-space representation, or even for `A` to be an algebra of
operators at all.

Mathlib already has this notion, `WStarAlgebra` (`Mathlib.Analysis.VonNeumannAlgebra.Basic`), but
only asserts the *mere existence* of a predual (a `Prop`), by design — Mathlib's own docstring
flags picking one as a possible source of definitional-unification trouble down the line. That is
exactly the trouble this file needs to avoid: the weak-⋆ topology genuinely depends on *which*
predual is chosen (Sakai's theorem says any two are isometrically isomorphic, but not canonically
so), so a mere existence statement isn't enough to even state `weakStarTopology`, let alone work
with it. `WStarAlgebraStructure` is therefore data — a `class` packaging one chosen predual and
identification — built directly on `Basic/CStarAlgebra/`'s bare-hypothesis convention
(`[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`) rather than on a reinvented wrapper
class. It is a different name for a related but genuinely different (data vs. `Prop`) notion than
Mathlib's `WStarAlgebra`, not a competing definition of the same one; connecting the two — every
`WStarAlgebraStructure A` gives a proof of `WStarAlgebra A` — needs converting our `≃ₗᵢ[ℂ]`
(linear) identification to Mathlib's `≃ₗᵢ⋆[ℂ]` (conjugate-linear) one, genuine linear-algebra work
not attempted here.

Mathlib's own weak-⋆ topology machinery for the dual of a normed space
(`Mathlib.Analysis.Normed.Module.WeakDual`, `WeakDual`/`StrongDual`) does essentially all of the
topological work once the predual identification is in hand — genuinely no new topology needed,
only the identification and its transport back along it.

## Definitions

- `WStarAlgebraStructure A` : `A` together with a chosen predual `Predual A` and an isometric
  linear identification `toDual : A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)`.
- `WStarAlgebraStructure.weakStarTopology A` : the weak-⋆ topology on `A`, pulled back through
  `toDual` from `WeakDual ℂ (Predual A)`. Deliberately *not* a `TopologicalSpace A` instance — `A`
  already has its norm topology (from `CStarAlgebra`), and the entire point here is to compare the
  two, so they must coexist rather than compete for instance resolution.
- `WStarAlgebraStructure.norm_le_weakStarTopology` : the weak-⋆ topology is coarser than the norm
  topology — proved outright from Mathlib's `toDual`-is-an-isometry and
  `StrongDual.toWeakDual`-is-continuous facts, no new hard analysis needed.
- `NormalState A` : a state (`𝓢[A]`, `Basic/OrderUnit/State/Basic.lean`) continuous for
  `weakStarTopology` — the honest, Sakai-style definition of "normal state".
  `NormalState.continuous` recovers norm-continuity as a corollary, for free, from
  `norm_le_weakStarTopology`.

## Concrete realization

The genuinely concrete instance — `A := B(H)` with predual the trace-class operators `𝒮₁(H)` and
`toDual` the trace pairing `a ↦ (ρ ↦ Tr(aρ))` — needs a `TraceClass H` Banach space this repo does
not yet have. This file stays at the abstract weak-⋆ and normal-state layer.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder Topology
open TopologicalSpace
open Filter

/-! ## W⋆-algebras -/

/-- **A W⋆-algebra, as data**: a C⋆-algebra `A` together with one chosen identification with the
Banach-space dual of some other Banach space `Predual A` — Sakai's characterization of a von
Neumann algebra. See the module docstring for why this is a `class` carrying a chosen predual
rather than a `Prop` asserting one exists (Mathlib's `WStarAlgebra`), and for the name choice. -/
class WStarAlgebraStructure (A : Type*) extends CStarAlgebra A, PartialOrder A, StarOrderedRing A
    where
  /-- The predual: a Banach space `E` with `A ≃ₗᵢ[ℂ] StrongDual ℂ E` isometrically. -/
  Predual : Type*
  predualNormedAddCommGroup : NormedAddCommGroup Predual
  predualNormedSpace : NormedSpace ℂ Predual
  predualCompleteSpace : CompleteSpace Predual
  /-- The defining isometric identification `A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)`, `a ↦ (ξ ↦
  ⟨a, ξ⟩)` for the duality pairing `A` inherits from being `Predual A`'s dual. -/
  toDual : A ≃ₗᵢ[ℂ] StrongDual ℂ Predual

attribute [instance_reducible] WStarAlgebraStructure.predualNormedAddCommGroup
  WStarAlgebraStructure.predualNormedSpace

attribute [instance] WStarAlgebraStructure.predualNormedAddCommGroup
  WStarAlgebraStructure.predualNormedSpace WStarAlgebraStructure.predualCompleteSpace

namespace WStarAlgebraStructure

variable (A : Type*) [WStarAlgebraStructure A]

/-- **The weak-⋆ topology on `A`**: pulled back, through the defining predual isometry `toDual`,
from the weak-⋆ topology on `WeakDual ℂ (Predual A)` (Mathlib's `WeakDual`, the coarsest topology
making every evaluation `f ↦ f ξ`, `ξ : Predual A`, continuous). This models the physically correct
notion of "converges weakly" for states/observables on `A` — e.g. it is exactly the topology in
which a sequence of density operators `ρₙ → ρ` weak-⋆ iff `Tr(ρₙ A) → Tr(ρA)` for every bounded
`A`, the usual sense of convergence of quantum states.

Deliberately *not* registered as a `TopologicalSpace A` instance: see the module docstring. -/
@[instance_reducible]
def weakStarTopology : TopologicalSpace A :=
  TopologicalSpace.induced (fun a => StrongDual.toWeakDual (toDual a)) inferInstance

/-- **The weak-⋆ topology is coarser than the norm topology.** The basic sanity fact making
`weakStarTopology` a genuine weakening of the topology `A` already carries as a C⋆-algebra: the
identity map `A → A`, viewed as `(A, ‖·‖) → (A, \text{weak-⋆})`, is continuous. Proved from two
continuity facts already in Mathlib — `toDual` is a (linear) isometry, hence norm-continuous
(`LinearIsometryEquiv.continuous`), and `StrongDual.toWeakDual` is continuous
(`NormedSpace.Dual.toWeakDual_continuous`) — composing gives continuity of `weakStarTopology`'s
defining map for the *norm* topology on the domain, which is exactly what "coarser" means via
`continuous_iff_le_induced`. No genuinely new analysis: this is Mathlib's own comparison theorem
for the weak-⋆ topology on a dual space, transported along `toDual`. -/
theorem norm_le_weakStarTopology :
    (inferInstance : TopologicalSpace A) ≤ weakStarTopology A :=
  continuous_iff_le_induced.mp
    (NormedSpace.Dual.toWeakDual_continuous.comp (toDual (A := A)).continuous)

end WStarAlgebraStructure

/-! ## The predual pairing -/

namespace WStarAlgebraStructure

variable {A : Type*} [WStarAlgebraStructure A]

/-- The canonical continuous functional on `A` associated with a predual vector. This is the
pairing that later concrete normality theorems use; spelling it out here avoids repeatedly
reconstructing the evaluation map through `toDual`. -/
def predualPairing (ξ : WStarAlgebraStructure.Predual A) : A →L[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ ξ).comp
    ((toDual (A := A)).toLinearIsometry.toContinuousLinearMap)

@[simp]
lemma predualPairing_apply (ξ : WStarAlgebraStructure.Predual A) (a : A) :
    predualPairing ξ a = toDual a ξ := rfl

lemma norm_predualPairing_apply (ξ : WStarAlgebraStructure.Predual A) (a : A) :
    ‖predualPairing ξ a‖ ≤ ‖a‖ * ‖ξ‖ := by
  have h := ContinuousLinearMap.le_opNorm (toDual a) ξ
  simpa [predualPairing] using h

/-- The predual pairing is continuous for the weak-* topology by construction.

This is the basic normal-functional fact behind the von Neumann boundary: unlike a normal state,
which is a positive normalized functional, a predual vector gives an arbitrary (not necessarily
positive) weak-* continuous functional. Keeping this lemma explicit prevents later spectral
measure arguments from silently replacing additivity against all predual functionals by the weaker
statement for states alone. -/
theorem predualPairing_weakStar_continuous (ξ : WStarAlgebraStructure.Predual A) :
    Continuous[WStarAlgebraStructure.weakStarTopology A, inferInstance]
      (predualPairing ξ) := by
  change Continuous[TopologicalSpace.induced
      (fun a => StrongDual.toWeakDual (toDual a)) inferInstance, inferInstance]
      (fun a => (StrongDual.toWeakDual (toDual a)) ξ)
  have hmap : Continuous[TopologicalSpace.induced
      (fun a => StrongDual.toWeakDual (toDual a)) inferInstance, inferInstance]
      (fun a => StrongDual.toWeakDual (toDual a)) :=
    (continuous_induced_dom (f := fun a : A =>
      StrongDual.toWeakDual (toDual a)))
  have heval : Continuous[
      (inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebraStructure.Predual A))),
        inferInstance]
      (fun z : WeakDual ℂ (WStarAlgebraStructure.Predual A) => z ξ) :=
    WeakBilin.eval_continuous _ _
  exact @Continuous.comp A (WeakDual ℂ (WStarAlgebraStructure.Predual A)) ℂ
    (TopologicalSpace.induced (fun a => StrongDual.toWeakDual (toDual a)) inferInstance)
    inferInstance inferInstance _ _ heval hmap

/-- The predual pairings separate points of a W⋆-algebra.

This is the algebraic half of the weak-* interface: equality can be checked against every
predual vector. It is useful when an operator-valued construction is first identified through
its normal matrix coefficients and only then packaged as an element of `A`. -/
theorem ext_of_forall_predualPairing_eq {a b : A}
    (h : ∀ ξ : WStarAlgebraStructure.Predual A, predualPairing ξ a = predualPairing ξ b) :
    a = b := by
  apply (toDual (A := A)).injective
  ext ξ
  exact h ξ

/-! The topology is equivalently characterized by convergence of all canonical predual pairings.
This formulation is deliberately filter-based, so it applies to nets as well as sequences. -/

theorem tendsto_weakStar_iff_forall_predualPairing_tendsto
    {α : Type*} {l : Filter α} {f : α → A} {a : A} :
    Tendsto f l (@nhds A (WStarAlgebraStructure.weakStarTopology A) a) ↔
      ∀ ξ : WStarAlgebraStructure.Predual A,
        Tendsto (fun i => predualPairing ξ (f i)) l
          (𝓝 (predualPairing ξ a)) := by
  change Tendsto f l (@nhds A
      (TopologicalSpace.induced
        (fun b => StrongDual.toWeakDual (toDual b)) inferInstance) a) ↔ _
  rw [nhds_induced, Filter.tendsto_comap_iff]
  change Tendsto (fun i => StrongDual.toWeakDual (toDual (f i))) l
      (𝓝 (StrongDual.toWeakDual (toDual a))) ↔
    ∀ ξ : WStarAlgebraStructure.Predual A,
      Tendsto (fun i => (toDual (f i)) ξ) l (𝓝 ((toDual a) ξ))
  exact tendsto_iff_forall_eval_tendsto_topDualPairing
    (𝕜 := ℂ) (E := WStarAlgebraStructure.Predual A) (l := l)
    (f := fun i => StrongDual.toWeakDual (toDual (f i)))
    (x := StrongDual.toWeakDual (toDual a))

end WStarAlgebraStructure

/-! ## Normal states -/

/-- A state that is continuous for the weak-* topology of the chosen predual. -/
structure NormalState (A : Type*) [WStarAlgebraStructure A] where
  /-- The underlying state. -/
  toState : 𝓢[A]
  /-- The state is continuous for the chosen weak-* topology. -/
  weakStar_continuous :
    Continuous[WStarAlgebraStructure.weakStarTopology A, inferInstance] (⇑toState : A → ℂ)

namespace NormalState

variable {A : Type*} [WStarAlgebraStructure A]

noncomputable instance : CoeFun (NormalState A) (fun _ => A → ℂ) where
  coe ω := ω.toState

@[simp, nolint synTaut]
lemma toState_apply (ω : NormalState A) (a : A) : ω.toState a = ω a := rfl

/-- Weak-* continuity implies ordinary norm continuity because the weak-* topology is coarser. -/
theorem continuous (ω : NormalState A) : Continuous (ω : A → ℂ) :=
  continuous_le_dom (WStarAlgebraStructure.norm_le_weakStarTopology A) ω.weakStar_continuous

end NormalState
