/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.IsLorentzDeriv
/-!
# Lorentz invariants of a half-integer spin

The other files of this folder classify the invariants of a given index pattern by contracting
the components with a coefficient tensor. This one settles, in one step and for every pattern
at once, the patterns that carry no invariant for the crudest of reasons: they are of
half-integer spin, and a half-integer spin has no invariant because the centre of `SL(2,ℂ)`
already tells integer spin from half-integer spin apart.

The element `-1` of `SL(2,ℂ)` covers the identity Lorentz transformation
(`SL2C.toLorentzGroup_neg_one`), so a representation of `SL(2,ℂ)` that factors through the
Lorentz group — a tensor of four-vector indices — sends it to the identity, while each Weyl
index contributes a sign. A subspace with an odd number of Weyl indices therefore lies in the
`-1` eigenspace of `repLorentz (-1)`, and a vector both fixed by the group and negated by `-1`
is zero. `centreEigenspace` names the eigenspace, `mul_le_centreEigenspace` multiplies the two
signs in a product of subspaces, and `mem_of_invariant_of_mem_sup_centreEigenspace_neg_one` is
the classification modulo a Lorentz-stable subspace `S`, the form the Standard Model files use.

The subspaces that arise there are spans of symbol families, so section B reads the sign of
such a span off the sign of the value space: the covariant-derivative slots of a family
obeying `IsLorentzCovDerivTransforms` are inert at the centre, and only the value index moves.

This replaces, for the Standard Model sectors, the boost-weight parity count: odd boost weight
along a spatial axis and a sign of `-1` at the centre are the same statement about the same
subspaces, and the centre needs neither a grading nor a light-cone basis to say it.

- A. The sign a subspace carries at the centre
- B. The sign of a symbol family
- C. Signs multiply
- D. The classification modulo a Lorentz-stable submodule
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

namespace Invariants

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-!

## A. The sign a subspace carries at the centre

The centre of `SL(2,ℂ)` is `±1` and squares to the identity, so `repLorentz (-1)` is an
involution and the only signs on offer are `±1`. A tensor of four-vector indices carries `1`,
a Weyl index carries `-1`, and nothing else is needed of the pattern.

-/

/-- The subspace on which the centre of `SL(2,ℂ)` acts by the scalar `ε`: an integer spin
  sits at `ε = 1` and a half-integer spin at `ε = -1`. -/
def centreEigenspace (repLorentz : Representation ℂ SL(2,ℂ) V) (ε : ℂ) : Submodule ℂ V :=
  Module.End.eigenspace (repLorentz (-1)) ε

/-- Membership of `centreEigenspace` unfolded: the centre scales the vector by `ε`. -/
lemma mem_centreEigenspace {repLorentz : Representation ℂ SL(2,ℂ) V} {ε : ℂ} {x : V} :
    x ∈ centreEigenspace repLorentz ε ↔ repLorentz (-1) x = ε • x := by
  simp [centreEigenspace]

/-- Dualising a representation preserves the sign at the centre: `-1` is its own inverse, so
  the contragredient action of the centre is the transpose of a scalar. -/
lemma dual_neg_one_eq_smul_id {rep : Representation ℂ SL(2,ℂ) V} {ε : ℂ}
    (hrep : rep (-1) = ε • LinearMap.id) : rep.dual (-1) = ε • LinearMap.id := by
  ext φ x
  have hinv : (-1 : SL(2,ℂ))⁻¹ = -1 := by simp
  simp [Representation.dual_apply, Module.Dual.transpose_apply, hinv, hrep]

/-!

## B. The sign of a symbol family

A family of symbols transforming as the covariant derivatives of a field valued in `V` carries
at the centre the sign that `V` does. The derivative slots mix by the Lorentz matrix, which is
the identity at the centre, so they contribute nothing; the value index moves by `rep.dual`,
which carries the sign of `rep` by section A. Both signs that occur are recorded, `ε = 1` for
the Lorentz-scalar value spaces and `ε = -1` for the Weyl ones.

-/

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- **The span of one symbol family carries the sign of its value space.** -/
lemma range_le_centreEigenspace {repLorentz : Representation ℂ SL(2,ℂ) A}
    {rep : Representation ℂ SL(2,ℂ) V}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] A}
    (hF : IsLorentzCovDerivTransforms repLorentz rep F) {ε : ℂ}
    (hrep : rep (-1) = ε • LinearMap.id) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (F l) ≤ centreEigenspace repLorentz ε := by
  rintro _ ⟨φ, rfl⟩
  rw [mem_centreEigenspace, hF.neg_one_apply l φ, dual_neg_one_eq_smul_id hrep]
  simp

/-- The half-integer case of `range_le_centreEigenspace`, in the form the Weyl value spaces
  state their sign. -/
lemma range_le_centreEigenspace_neg_one {repLorentz : Representation ℂ SL(2,ℂ) A}
    {rep : Representation ℂ SL(2,ℂ) V}
    {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] A}
    (hF : IsLorentzCovDerivTransforms repLorentz rep F)
    (hrep : rep (-1) = -LinearMap.id) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (F l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace hF (by rw [hrep]; module) l

/-!

## C. Signs multiply

The Lorentz action on the field algebra is by algebra maps, so the sign a product carries is
the product of the signs of its factors. This is the whole of the bookkeeping that the
boost-weight convolution used to do: two Weyl indices cancel and an odd number does not.

-/

/-- The sign of a product is the product of the signs. -/
lemma mul_le_centreEigenspace {repLorentz : Representation ℂ SL(2,ℂ) A}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {W₁ W₂ : Submodule ℂ A} {ε₁ ε₂ : ℂ} (h₁ : W₁ ≤ centreEigenspace repLorentz ε₁)
    (h₂ : W₂ ≤ centreEigenspace repLorentz ε₂) :
    W₁ * W₂ ≤ centreEigenspace repLorentz (ε₁ * ε₂) := by
  refine Submodule.mul_le.2 fun a ha b hb => ?_
  rw [mem_centreEigenspace, hmul, mem_centreEigenspace.1 (h₁ ha),
    mem_centreEigenspace.1 (h₂ hb), Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-!

## D. The classification modulo a Lorentz-stable submodule

A vector of a subspace of sign `-1` that the group fixes is negated by `-1` and fixed by it at
once, so it is zero. Modulo a stable subspace `S` the same count leaves twice the vector inside
`S`, and halving is allowed over `ℂ`; no quotient representation is needed.

-/

/-- **A subspace of half-integer spin carries no Lorentz invariant beyond a Lorentz-stable
  submodule `S`**: an invariant of the join with `S` already lies in `S`. Writing the invariant
  as `v + s`, invariance under the centre gives `2 • v = repLorentz (-1) s - s`, which lies in
  `S`, and so does `v`. -/
lemma mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    {repLorentz : Representation ℂ SL(2,ℂ) A} {W : Submodule ℂ A}
    (hW : W ≤ centreEigenspace repLorentz (-1)) (S : Submodule ℂ A)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : A} (hx : x ∈ W ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 hx
  have hcentre : repLorentz (-1) (v + s) = -v + repLorentz (-1) s := by
    rw [map_add, mem_centreEigenspace.1 (hW hv)]
    module
  have htwo : (2 : ℂ) • v = repLorentz (-1) s - s := by
    have hfix := hinv (-1)
    rw [hcentre] at hfix
    linear_combination (norm := module) -hfix
  have hvS : v ∈ S := by
    have : (2 : ℂ) • v ∈ S := htwo ▸ S.sub_mem (hS (-1) s hs) hs
    simpa using S.smul_mem (2 : ℂ)⁻¹ this
  exact S.add_mem hvS hs

end Invariants

end Lorentz
