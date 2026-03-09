/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
/-!

## Causality of Lorentz vectors

-/

@[expose] public section

noncomputable section

namespace Lorentz
open realLorentzTensor
open InnerProductSpace

namespace Vector

/-- Classification of lorentz vectors based on their causal character. -/
inductive CausalCharacter
  | timeLike
  | lightLike
  | spaceLike

deriving DecidableEq

/-- A Lorentz vector `p` is
- `lightLike` if `⟪p, p⟫ₘ = 0`.
- `timeLike` if `0 < ⟪p, p⟫ₘ`.
- `spaceLike` if `⟪p, p⟫ₘ < 0`.
Note that `⟪p, p⟫ₘ` is defined in the +--- convention.
-/
def causalCharacter {d : ℕ} (p : Vector d) : CausalCharacter :=
  let v0 := ⟪p, p⟫ₘ
  if v0 = 0 then CausalCharacter.lightLike
  else if 0 < v0 then CausalCharacter.timeLike
  else CausalCharacter.spaceLike

/-- `causalCharacter` are invariant under an action of the Lorentz group. -/
lemma causalCharacter_invariant {d : ℕ} (p : Vector d) (Λ : LorentzGroup d) :
    causalCharacter (Λ • p) = causalCharacter p := by
  simp only [causalCharacter, Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [minkowskiProduct_invariant]

lemma spaceLike_iff_norm_sq_neg {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.spaceLike ↔ ⟪p, p⟫ₘ < 0 := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp only [reduceCtorEq, h, lt_self_iff_false]
  · split
    · rename_i h
      simp only [reduceCtorEq, false_iff, not_lt]
      exact le_of_lt h
    · rename_i h1 h2
      simp only [true_iff]
      rw [not_lt_iff_eq_or_lt] at h2
      rw [eq_comm] at h2
      simp_all

/-- The Lorentz vector `p` and `-p` have the same causalCharacter -/
lemma neg_causalCharacter_eq_self {d : ℕ} (p : Vector d) :
    causalCharacter (-p) = causalCharacter p := by
  have h : ⟪-p, -p⟫ₘ = ⟪p, p⟫ₘ := by
    rw [minkowskiProduct_toCoord]
    simp [minkowskiProduct_toCoord]
  simp only [causalCharacter, h]

/-- The future light cone of a Lorentz vector `p` is defined as those
  vectors `q` such that
- `causalCharacter (q - p)` is `timeLike` and
- `(q - p) (Sum.inl 0)` is positive. -/
def interiorFutureLightCone {d : ℕ} (p : Vector d) : Set (Vector d) :=
    {q | causalCharacter (q - p) = .timeLike ∧ 0 < (q - p) (Sum.inl 0)}

/-- The backward light cone of a Lorentz vector `p` is defined as those
  vectors `q` such that
- `causalCharacter (q - p)` is `timeLike` and
- `(q - p) (Sum.inl 0)` is negative. -/
def interiorPastLightCone {d : ℕ} (p : Vector d) : Set (Vector d) :=
    {q | causalCharacter (q - p) = .timeLike ∧ (q - p) (Sum.inl 0) < 0}

/-- The light cone boundary (null surface) of a spacetime point `p`. -/
def lightConeBoundary {d : ℕ} (p : Vector d) : Set (Vector d) :=
  {q | causalCharacter (q - p) = .lightLike}

/-- The future light cone boundary (null surface) of a spacetime point `p`. -/
def futureLightConeBoundary {d : ℕ} (p : Vector d) : Set (Vector d) :=
  {q | causalCharacter (q - p) = .lightLike ∧ 0 ≤ (q - p) (Sum.inl 0)}

/-- The past light cone boundary (null surface) of a spacetime point `p`. -/
def pastLightConeBoundary {d : ℕ} (p : Vector d) : Set (Vector d) :=
  {q | causalCharacter (q - p) = .lightLike ∧ (q - p) (Sum.inl 0) ≤ 0}

/-- Any point `p` lies on its own light cone boundary, as `p - p = 0` has
    zero Minkowski norm squared. -/
lemma self_mem_lightConeBoundary {d : ℕ} (p : Vector d) : p ∈ lightConeBoundary p := by
  simp [causalCharacter, lightConeBoundary]

/-- A proposition which is true if `q` is in the causal future of event `p`. -/
def causallyFollows {d : ℕ} (p q : Vector d) : Prop :=
  q ∈ interiorFutureLightCone p ∨ q ∈ futureLightConeBoundary p

/-- A proposition which is true if `q` is in the causal past of event `p`. -/
def causallyPrecedes {d : ℕ} (p q : Vector d) : Prop :=
  q ∈ interiorPastLightCone p ∨ q ∈ pastLightConeBoundary p

/-- Events `p` and `q` are causally related. -/
def causallyRelated {d : ℕ} (p q : Vector d) : Prop :=
  causallyFollows p q ∨ causallyFollows q p

/-- Events p and q are causally unrelated (spacelike separated). -/
def causallyUnrelated {d : ℕ} (p q : Vector d) : Prop :=
  causalCharacter (p - q) = CausalCharacter.spaceLike

/-- The causal diamond between events p and q, where p is assumed to causally precede q. -/
def causalDiamond {d : ℕ} (p q : Vector d) : Set (Vector d) :=
  {r | causallyFollows p r ∧ causallyFollows r q}

/-- In Minkowski spacetime with (+---) signature, we can define future-directed vectors
    as having positive time components (by convention) -/
def isFutureDirected {d : ℕ} (v : Vector d) : Prop :=
    0 < timeComponent v

/-- In Minkowski spacetime with (+---) signature, we can define past-directed vectors
    as having negative time components (by convention) -/
def isPastDirected {d : ℕ} (v : Vector d) : Prop :=
  timeComponent v < 0

end Vector
end Lorentz
