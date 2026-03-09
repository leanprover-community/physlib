/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.AnomalyCancellation.Basic
public import Mathlib.RepresentationTheory.Basic
/-!
# Group actions on ACC systems.

We define a group action on an ACC system as a representation on the vector spaces of charges
under which the anomaly equations are invariant.

From this we define
- The representation acting on the vector space of solutions to the linear ACCs.
- The group action acting on solutions to the linear + quadratic equations.
- The group action acting on solutions to the anomaly cancellation conditions.

-/

@[expose] public section

/-- The type of a group action on a system of charges is defined as a representation on
the vector spaces of charges under which the anomaly equations are invariant.
-/
structure ACCSystemGroupAction (χ : ACCSystem) where
  /-- The underlying type of the group. -/
  group : Type
  /-- An instance given the `group` component the structure of a `Group`. -/
  groupInst : Group group
  /-- The representation of group acting on the vector space of charges. -/
  rep : Representation ℚ group χ.Charges
  /-- The invariance of the linear ACCs under the group action. -/
  linearInvariant : ∀ i g S, χ.linearACCs i (rep g S) = χ.linearACCs i S
  /-- The invariance of the quadratic ACCs under the group action. -/
  quadInvariant : ∀ i g S, (χ.quadraticACCs i) (rep g S) = (χ.quadraticACCs i) S
  /-- The invariance of the cubic ACC under the group action. -/
  cubicInvariant : ∀ g S, χ.cubicACC (rep g S) = χ.cubicACC S

namespace ACCSystemGroupAction

/-- The given instance of a group on the `group` field of a `ACCSystemGroupAction`. -/
instance {χ : ACCSystem} (G : ACCSystemGroupAction χ) : Group G.group := G.groupInst

/-- The action of a group element on the vector space of linear solutions. -/
def linSolMap {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group) :
    χ.LinSols →ₗ[ℚ] χ.LinSols where
  toFun S := ⟨G.rep g S.val, by
    intro i
    rw [G.linearInvariant, S.linearSol]⟩
  map_add' S T := ACCSystemLinear.LinSols.ext ((G.rep g).map_add' _ _)
  map_smul' a S := ACCSystemLinear.LinSols.ext ((G.rep g).map_smul' _ _)

/-- The representation acting on the vector space of solutions to the linear ACCs. -/
@[simps!]
def linSolRep {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    Representation ℚ G.group χ.LinSols where
  toFun := G.linSolMap
  map_mul' g1 g2 := by
    refine LinearMap.ext fun S ↦ ACCSystemLinear.LinSols.ext ?_
    change (G.rep (g1 * g2)) S.val = _
    rw [G.rep.map_mul]
    rfl
  map_one' := by
    refine LinearMap.ext fun S ↦ ACCSystemLinear.LinSols.ext ?_
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl

/-- The representation on the charges and anomaly free solutions
commutes with the inclusion. -/
lemma rep_linSolRep_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.LinSols) : χ.linSolsIncl (G.linSolRep g S) =
    G.rep g (χ.linSolsIncl S) := rfl

/-- A multiplicative action of `G.group` on `quadSols`. -/
instance quadSolAction {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    MulAction G.group χ.QuadSols where
  smul f S := ⟨G.linSolRep f S.1, by simp [linSolRep_apply_apply_val, G.quadInvariant, S.quadSol]⟩
  mul_smul f1 f2 S := by
    apply ACCSystemQuad.QuadSols.ext
    change (G.rep.toFun (f1 * f2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  one_smul S := by
    apply ACCSystemQuad.QuadSols.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl

lemma linSolRep_quadSolAction_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.QuadSols) : χ.quadSolsInclLinSols (G.quadSolAction.toFun _ _ S g) =
    G.linSolRep g (χ.quadSolsInclLinSols S) := rfl

lemma rep_quadSolAction_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.QuadSols) : χ.quadSolsIncl (G.quadSolAction.toFun _ _ S g) =
    G.rep g (χ.quadSolsIncl S) := rfl

/-- The group action acting on solutions to the anomaly cancellation conditions. -/
instance solAction {χ : ACCSystem} (G : ACCSystemGroupAction χ) : MulAction G.group χ.Sols where
  smul g S := ⟨G.quadSolAction.toFun _ _ S.1 g, by
    simp only [MulAction.toFun_apply]
    change χ.cubicACC (G.rep g S.val) = 0
    rw [G.cubicInvariant, S.cubicSol]⟩
  mul_smul f1 f2 S := by
    apply ACCSystem.Sols.ext
    change (G.rep.toFun (f1 * f2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  one_smul S := by
    apply ACCSystem.Sols.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl

lemma quadSolAction_solAction_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.Sols) : χ.solsInclQuadSols (G.solAction.toFun _ _ S g) =
    G.quadSolAction.toFun _ _ (χ.solsInclQuadSols S) g := rfl

lemma linSolRep_solAction_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.Sols) : χ.solsInclLinSols (G.solAction.toFun _ _ S g) =
    G.linSolRep g (χ.solsInclLinSols S) := rfl

lemma rep_solAction_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.Sols) : χ.solsIncl (G.solAction.toFun _ _ S g) = G.rep g (χ.solsIncl S) := rfl

end ACCSystemGroupAction
