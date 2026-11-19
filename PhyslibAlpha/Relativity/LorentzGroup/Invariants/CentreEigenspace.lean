/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.InvariantReduction
public import PhyslibAlpha.Relativity.IsLorentzDeriv
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.Reynolds
/-!
# The eigenspaces of the centre of `SL(2,ℂ)`

The subspaces on which the central element `-1` of `SL(2,ℂ)` acts by a scalar, and the Lorentz
invariants of a half-integer spin.

## i. Overview

The classifications of the invariant tensors contract the components with a coefficient tensor.
This file settles, in one step and for every pattern at once, the patterns that carry no
invariant for the crudest of reasons: they are of half-integer spin, and a half-integer spin has
no invariant because the centre of `SL(2,ℂ)` already tells integer spin from half-integer spin
apart.

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

The argument uses the central element alone: it needs neither a grading nor a light-cone
basis. On the complex Lorentz tensors `-1` acts on each Weyl index by `-1` and on each
four-vector index by `1`, so on the tensors with colours `c` by `(-1)` to the number of Weyl
colours of `c`, and with an odd number of Weyl indices there are no invariant tensors but zero
(E).

## ii. Key results

- `centreEigenspace` : the subspace on which the centre of `SL(2,ℂ)` acts by the scalar `ε`: an
  integer spin sits at `ε = 1` and a half-integer spin at `ε = -1`
- `mul_le_centreEigenspace` : the sign of a product is the product of the signs
- `mem_of_invariant_of_mem_sup_centreEigenspace_neg_one` : a subspace of half-integer spin carries
  no Lorentz invariant beyond a Lorentz-stable submodule `S`: an invariant of the join with `S`
  already lies in `S`
- `complexLorentzTensor.tensorRep_neg_one` : `-1` acts on the tensors by `(-1)` to the number of
  Weyl colours
- `complexLorentzTensor.invariants_eq_bot_of_odd_weyl` : tensors with an odd number of Weyl
  indices have no invariants but zero

## iii. Table of contents

- A. The sign a subspace carries at the centre
- B. The sign of a symbol family
- C. Signs multiply
- D. The classification modulo a Lorentz-stable submodule
- E. The centre on the complex Lorentz tensors

## iv. References

* None.

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
the product of the signs of its factors. This is the whole of the bookkeeping: two Weyl
indices cancel and an odd number does not.

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
once, so it is zero. Modulo a stable subspace `S` this is the case `μ = -1` of
`reducesInvariantsTo_bot_of_apply_eq_smul`: the invariance leaves `-2` times the vector inside
`S`, and dividing by `-2` is allowed over `ℂ`; no quotient representation is needed.

-/

/-- A subspace of half-integer spin carries no Lorentz invariant beyond a Lorentz-stable
  submodule `S`: an invariant of the join with `S` already lies in `S`. The centre acts on the
  subspace by `-1 ≠ 1`, so it reduces to `⊥`. -/
lemma mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    {repLorentz : Representation ℂ SL(2,ℂ) A} {W : Submodule ℂ A}
    (hW : W ≤ centreEigenspace repLorentz (-1)) (S : Submodule ℂ A)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : A} (hx : x ∈ W ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  simpa using reducesInvariantsTo_bot_of_apply_eq_smul (σ := fun g => repLorentz g) (-1)
    (by norm_num) (fun v hv => mem_centreEigenspace.1 (hW hv)) S hS x hx hinv

end Invariants

/-!

## E. The centre on the complex Lorentz tensors

The element `-1` covers the identity Lorentz transformation, so it acts on the four-vector colours
by `1`, and on each Weyl colour by `-1`. On the tensors with colours `c` it therefore acts by the
product of these signs, `(-1)` to the number of Weyl colours of `c`
(`TensorSpecies.tensorRep_eq_prod_smul`). With an odd number of Weyl colours this is `-1`, and an
invariant tensor both fixed and negated by `-1` is zero.

-/

open TensorSpecies

/-- The sign by which `-1` acts on a colour: `1` on the four-vector colours and `-1` on the Weyl
  colours. -/
def centreSign (k : complexLorentzTensor.Color) : ℂ :=
  if k = .up ∨ k = .down then 1 else -1

/-- The element `-1` acts on the representation of each colour by its sign. -/
lemma rep_neg_one (k : complexLorentzTensor.Color) :
    complexLorentzTensor.rep k (-1) = centreSign k • LinearMap.id := by
  apply (LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)).injective
  rw [map_smul, LinearMap.toMatrix_id]
  cases k
  · rw [toMatrix_rep_upL]
    simp [centreSign]
  · rw [toMatrix_rep_downL]
    simp only [centreSign]
    have hi : (-1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = -1 :=
      Matrix.inv_eq_left_inv (by rw [neg_mul_neg, one_mul])
    simp [hi]
  · rw [toMatrix_rep_upR]
    ext i j
    simp [centreSign, Matrix.one_apply, apply_ite]
  · rw [toMatrix_rep_downR]
    simp only [centreSign]
    have hi : (-1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = -1 :=
      Matrix.inv_eq_left_inv (by rw [neg_mul_neg, one_mul])
    simp [hi]
  · ext μ ν
    rw [toMatrix_rep_up_apply, SL2C.toLorentzGroup_neg_one]
    simp [centreSign, Matrix.one_apply, apply_ite]
  · ext μ ν
    rw [toMatrix_rep_down_apply, SL2C.toLorentzGroup_neg_one]
    simp [centreSign, Matrix.one_apply, apply_ite, eq_comm]

/-- The element `-1` acts on the tensors with colours `c` by `(-1)` to the number of Weyl colours
  of `c`. -/
lemma _root_.complexLorentzTensor.tensorRep_neg_one {n : ℕ}
    (c : Fin n → complexLorentzTensor.Color) :
    complexLorentzTensor.tensorRep c (-1) =
      (-1 : ℂ) ^ (Finset.univ.filter fun i => ¬ (c i = .up ∨ c i = .down)).card •
        LinearMap.id := by
  rw [tensorRep_eq_prod_smul (fun k v => by rw [rep_neg_one]; rfl) c]
  congr 1
  simp only [centreSign]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

/-- The tensors with an odd number of Weyl indices have no invariants but zero. The element `-1`
  negates them, and an invariant tensor is fixed by it. -/
lemma _root_.complexLorentzTensor.invariants_eq_bot_of_odd_weyl {n : ℕ}
    {c : Fin n → complexLorentzTensor.Color}
    (h : Odd (Finset.univ.filter fun i => ¬ (c i = .up ∨ c i = .down)).card) :
    (complexLorentzTensor.tensorRep c).invariants = ⊥ := by
  refine Representation.invariants_eq_bot_of_forall fun t ht => ?_
  have h1 := ht (-1)
  rw [complexLorentzTensor.tensorRep_neg_one, h.neg_one_pow, LinearMap.smul_apply,
    LinearMap.id_apply, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left two_ne_zero

end Lorentz
