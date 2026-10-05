/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.HomogeneousGenerators
public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Physlib.Particles.StandardModel.JetAlgebra.CovJetAlgebra.Higgs
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Relativity.LightConeDeriv
public import Physlib.Relativity.SL2C.AxisRotations
public import Physlib.Particles.StandardModel.GaugeGroup.JetGaugeGroup.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RepresentationTheory.Invariants
/-!
# The algebra valued Higgs boson

## i. Overview

An algebra `B` carries a Higgs sector when the covariant towers `∇_l H` and `∇_l H̄`, and
every polynomial expression in them, sit inside it compatibly with the global gauge action,
the Lorentz action and the mass-weight grading. `CovHiggsJetAlgebra` is the universal object
with those towers, so the statement is a single one: an algebra map
`CovHiggsJetAlgebra →ₐ[ℂ] B`, equivariant for the global gauge group and the Lorentz group
and compatible with `massWeightPoly`. That is the structure `HiggsAlgebraCovRealization`,
together with the two demands that the group actions be multiplicative on the whole of `B`.

The towers `covH` and `covBarH` are the towers of the covariant jet algebra of the Higgs
field pushed along the map, and every law they satisfy is that algebra's law pushed along
it. From them the file builds the submodules `higgsSubmodule n` and `barHiggsSubmodule n`
of terms linear in `∇_d H` and `∇_d H̄`, the algebra `higgsAlgebra` they generate, and its
mass-weight submodules `massWeightSubmodule n`. Each of these carries a gauge weight
decomposition. The mass-weight submodules are described by the results of
`Physlib.Mathematics.HomogeneousGenerators`, and removing the leftmost Higgs tower of each
product gives them explicitly at weights `2`, `4`, `6` and `8`. These are the pieces from
which the Higgs terms of the Standard Model Lagrangian are assembled downstream.

## ii. Key results

- `HiggsAlgebraCovRealization` : the structure.
- `H_equivariant`, `H_comm_H`, `H_massWeight`, `repLorentz_H` and their conjugates : the
  laws of the towers.
- `higgsSubmoduleGaugeWeight`, `barHiggsSubmoduleGaugeWeight` : the gauge weight
  decompositions of the Higgs submodules.
- `rep_dotGaugeHiggs_invariant`, `repLorentz_dotGaugeHiggs` : the gauge invariance and the
  Lorentz law of the inner product `H† H` with derivatives on the two factors.
- `massWeightSubmodule_eq_iSup_mul`, `massWeightSubmodule_eq` : removing the leftmost Higgs
  tower, and the binary weight recursion.
- `massWeightSubmodule_two_eq` up to `massWeightSubmodule_eight_eq` : the mass weights up to eight.
- `massWeightSubmoduleGaugeWeight` : the gauge weight decomposition of the mass-weight
  submodules.

## iii. Table of contents

- A. The Higgs towers and their laws
  - A.1. The gauge laws
  - A.2. The commutation laws and the mass weights
  - A.3. The Lorentz laws
- B. The Higgs algebra
- C. The components and the Higgs submodules
  - C.1. The gauge action on the components
  - C.2. The Higgs and conjugate Higgs submodules
- D. The gauge weight decomposition of the Higgs submodules
- E. The Higgs inner product
- F. The mass weight submodules
  - F.1. Membership and the grading
  - F.2. The weight decompositions
  - F.3. The odd mass weights vanish
  - F.4. The gauge weight decomposition
  - F.5. Mass weights up to eight
- G. Gauge invariants

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.SL2C

/-- The algebra `B`, with a gauge action, a Lorentz action and a mass-weight grading,
  carries a Higgs sector when it receives an algebra map from the covariant jet algebra of
  the Higgs field which is equivariant for both actions and compatible with the grading.
  The covariant towers `∇_l H` and `∇_l H̄` then sit inside `B` as the images of that
  algebra's own, and every law they satisfy there is its law pushed along the map.

  It is the Higgs-sector counterpart of `CovAlgebraRealization`, and stands to
  `CovHiggsJetAlgebra` as that does to `CovJetAlgebra`.

  The last two fields are not consequences of the first three: an equivariant map forces
  the two actions to be multiplicative only on its image, whereas the sector needs them
  multiplicative on the whole of `B`. -/
structure HiggsAlgebraCovRealization (B : Type) [Ring B] [Algebra ℂ B]
    (rep : Representation ℂ GaugeGroupI B)
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (massWeightPoly : B →ₐ[ℂ] Polynomial B) where
  /-- The algebra map out of the covariant jet algebra of the Higgs field: it is what
    places the Higgs towers, and every polynomial expression in them, inside `B`. -/
  toAlgHom : CovHiggsJetAlgebra →ₐ[ℂ] B
  /-- The map is equivariant for the global gauge group. -/
  map_rep : ∀ (g : GaugeGroupI) (x : CovHiggsJetAlgebra),
    toAlgHom (CovHiggsJetAlgebra.repGaugeGroupI g x) = rep g (toAlgHom x)
  /-- The map is equivariant for the Lorentz group. -/
  map_repLorentz : ∀ (Λ : SL(2,ℂ)) (x : CovHiggsJetAlgebra),
    toAlgHom (CovHiggsJetAlgebra.repLorentzGroup Λ x) = repLorentz Λ (toAlgHom x)
  /-- The map carries the mass-weight grading of the covariant jet algebra of the Higgs
    field to that of `B`. -/
  map_massWeight : ∀ x : CovHiggsJetAlgebra, massWeightPoly (toAlgHom x)
    = Polynomial.mapAlgHom toAlgHom (CovHiggsJetAlgebra.massWeightPoly x)
  /-- Gauge transformations act on `B` by algebra maps. -/
  rep_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B), rep g (b₁ * b₂) = rep g b₁ * rep g b₂
  /-- Lorentz transformations act on `B` by algebra maps. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂

TODO (lines := 96-131) (date := 2026-09-11) "Should be generalized
  to a general gauge theory to `ScalarAlgebraCovRealization`,
  and that instance used here."

set_option linter.unusedVariables false
namespace HiggsAlgebraCovRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)

/-!

## A. The Higgs towers and their laws

The two towers the sector is written in are not data of the structure. They are the towers
of the covariant jet algebra of the Higgs field, carried into `B` along the defining
algebra map, and every law they satisfy is that algebra's law pushed along it.

-/

/-- The covariant derivatives `∇_l H` of the Higgs field inside `B`. -/
noncomputable def covH (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ HiggsVec →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ CovHiggsJetAlgebra.higgsField l

/-- The covariant derivatives `∇_l H̄` of the conjugate Higgs field inside `B`. -/
noncomputable def covBarH (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ CovHiggsJetAlgebra.conjHiggsField l

/-!

### A.1. The gauge laws

-/

/-- A gauge law of the covariant jet algebra of the Higgs field transports along the
  defining map. -/
lemma map_rep_eq {g : GaugeGroupI} {x y : CovHiggsJetAlgebra}
    (hxy : CovHiggsJetAlgebra.repGaugeGroupI g x = y) :
    rep g (h.toAlgHom x) = h.toAlgHom y :=
  (h.map_rep g x).symm.trans (congrArg h.toAlgHom hxy)

/-- The Higgs symbol carries the dual of the gauge representation on `HiggsVec`: the
  `SU(2)` index transforms contragrediently, and the hypercharge character by `u⁻³`. -/
lemma H_equivariant (g : GaugeGroupI) (φ : Module.Dual ℂ HiggsVec) (n : ℕ)
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    rep g (h.covH n l φ) = h.covH n l (HiggsVec.repGaugeGroupI.dual g φ) :=
  h.map_rep_eq (CovHiggsJetAlgebra.repGaugeGroupI_higgsField g l φ)

/-- The conjugate Higgs symbol carries the conjugate-dual of the gauge representation:
  the physicists' `H^† ↦ H^† g^†`. -/
lemma barH_equivariant (g : GaugeGroupI) (φ : Module.Dual ℂ (ConjModule HiggsVec)) (n : ℕ)
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    rep g (h.covBarH n l φ) = h.covBarH n l (HiggsVec.repGaugeGroupI.conj.dual g φ) :=
  h.map_rep_eq (CovHiggsJetAlgebra.repGaugeGroupI_conjHiggsField g l φ)

/-!

### A.2. The commutation laws and the mass weights

-/

/-- The Higgs is bosonic: two Higgs symbols commute. -/
lemma H_comm_H (φ ψ : Module.Dual ℂ HiggsVec) (n1 n2 : ℕ)
    (l1 : Fin n1 → (Fin 1 ⊕ Fin 3)) (l2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    Commute (h.covH n1 l1 φ) (h.covH n2 l2 ψ) :=
  (CovHiggsJetAlgebra.commute_higgsField_higgsField l1 l2 φ ψ).map h.toAlgHom

/-- A Higgs symbol commutes with a conjugate Higgs symbol. -/
lemma H_comm_barH (φ : Module.Dual ℂ HiggsVec) (ψ : Module.Dual ℂ (ConjModule HiggsVec))
    (n1 n2 : ℕ) (l1 : Fin n1 → (Fin 1 ⊕ Fin 3)) (l2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    Commute (h.covH n1 l1 φ) (h.covBarH n2 l2 ψ) :=
  (CovHiggsJetAlgebra.commute_higgsField_conjHiggsField l1 l2 φ ψ).map h.toAlgHom

/-- Two conjugate Higgs symbols commute. -/
lemma barH_comm_barH (φ ψ : Module.Dual ℂ (ConjModule HiggsVec)) (n1 n2 : ℕ)
    (l1 : Fin n1 → (Fin 1 ⊕ Fin 3)) (l2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    Commute (h.covBarH n1 l1 φ) (h.covBarH n2 l2 ψ) :=
  (CovHiggsJetAlgebra.commute_conjHiggsField_conjHiggsField l1 l2 φ ψ).map h.toAlgHom

/-- A mass-weight eigenvalue equation transports along the defining map. -/
lemma map_massWeight_monomial {n : ℕ} {x : CovHiggsJetAlgebra}
    (hx : CovHiggsJetAlgebra.massWeightPoly x = Polynomial.monomial n x) :
    massWeightPoly (h.toAlgHom x) = Polynomial.monomial n (h.toAlgHom x) :=
  (h.map_massWeight x).trans
    ((congrArg (Polynomial.mapAlgHom h.toAlgHom) hx).trans
      (Polynomial.mapAlgHom_monomial h.toAlgHom n x))

/-- The mass weight of the Higgs tower is `2 * (1 + n)`. -/
lemma H_massWeight (φ : Module.Dual ℂ HiggsVec) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    massWeightPoly (h.covH n l φ) = Polynomial.monomial (2 * (1 + n)) (h.covH n l φ) :=
  h.map_massWeight_monomial (CovHiggsJetAlgebra.massWeightPoly_higgsField l φ)

/-- The mass weight of the conjugate Higgs tower is `2 * (1 + n)`. -/
lemma barH_massWeight (φ : Module.Dual ℂ (ConjModule HiggsVec)) (n : ℕ)
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    massWeightPoly (h.covBarH n l φ)
      = Polynomial.monomial (2 * (1 + n)) (h.covBarH n l φ) :=
  h.map_massWeight_monomial (CovHiggsJetAlgebra.massWeightPoly_conjHiggsField l φ)

/-!

### A.3. The Lorentz laws

-/

/-- A Lorentz law of the covariant jet algebra of the Higgs field transports along the
  defining map. -/
lemma map_lorentz {V : Type} [AddCommGroup V] [Module ℂ V]
    {repV : Representation ℂ SL(2,ℂ) V}
    {G : {n : ℕ} → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ V →ₗ[ℂ] CovHiggsJetAlgebra}
    (hG : IsLorentzCovDerivTransforms CovHiggsJetAlgebra.repLorentzGroup repV G) :
    IsLorentzCovDerivTransforms repLorentz repV
      (fun {_n} l => h.toAlgHom.toLinearMap ∘ₗ G l) := by
  intro Λ n l φ
  show repLorentz Λ (h.toAlgHom (G l φ)) = _
  exact (h.map_repLorentz Λ (G l φ)).symm.trans
    ((congrArg h.toAlgHom (hG Λ n l φ)).trans
      ((map_sum h.toAlgHom _ _).trans
        (Finset.sum_congr rfl fun p _ => map_smul h.toAlgHom _ _)))

/-- The Higgs tower transforms under the Lorentz group as the covariant derivatives of a
  Lorentz scalar: each derivative slot mixes by the Lorentz matrix, and the value index is
  inert. -/
lemma repLorentz_H : IsLorentzCovDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec) (fun {n} => h.covH n) :=
  h.map_lorentz CovHiggsJetAlgebra.isLorentzCovDerivTransforms_higgsField

/-- The conjugate Higgs tower transforms as the covariant derivatives of a Lorentz scalar,
  through the conjugate of the trivial representation. -/
lemma repLorentz_barH : IsLorentzCovDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj (fun {n} => h.covBarH n) :=
  h.map_lorentz CovHiggsJetAlgebra.isLorentzCovDerivTransforms_conjHiggsField

include h in
/-- The pointwise form of `repLorentz_H`: the Lorentz action rotates the derivative indices
  of a Higgs symbol, and the value index is inert. -/
lemma repLorentz_H_apply (g : SL(2,ℂ)) (φ : Module.Dual ℂ HiggsVec) (n : ℕ)
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    repLorentz g (h.covH n l φ) = ∑ (a : Fin n → Fin 1 ⊕ Fin 3),
      (∏ (i : Fin n), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • h.covH n a φ := by
  simpa only [Representation.trivial_dual_apply] using h.repLorentz_H g n l φ

include h in
/-- The pointwise form of `repLorentz_barH`. -/
lemma repLorentz_barH_apply (g : SL(2,ℂ)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) :
    repLorentz g (h.covBarH n l φ) = ∑ (a : Fin n → Fin 1 ⊕ Fin 3),
      (∏ (i : Fin n), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • h.covBarH n a φ := by
  simpa only [Representation.conj_trivial_dual_apply] using h.repLorentz_barH g n l φ

/-!

## B. The Higgs algebra

The subalgebra of `B` generated by every `∇_d H` and `∇_d H̄`. Its elements commute with
one another, so any two of its submodules commute as submodules; and a property closed under
sums and products which holds on the symbols and on the scalars holds on all of it.

-/

/-- The subalgebra of `B` generated by the Higgs, its conjugate and all their
  derivatives. -/
def higgsAlgebra (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly) :
    Subalgebra ℂ B := (Algebra.adjoin ℂ (⋃ (k : ℕ) (d : Fin k → (Fin 1 ⊕ Fin 3)),
      Set.range (h.covH k d) ∪ Set.range (h.covBarH k d)))

/-- A Higgs symbol lies in the Higgs algebra. -/
lemma covH_mem_higgsAlgebra {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ HiggsVec) : h.covH n d φ ∈ h.higgsAlgebra :=
  Algebra.subset_adjoin (Set.mem_iUnion₂.mpr ⟨n, d, Set.mem_union_left _ ⟨φ, rfl⟩⟩)

/-- A conjugate Higgs symbol lies in the Higgs algebra. -/
lemma covBarH_mem_higgsAlgebra {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) : h.covBarH n d φ ∈ h.higgsAlgebra :=
  Algebra.subset_adjoin (Set.mem_iUnion₂.mpr ⟨n, d, Set.mem_union_right _ ⟨φ, rfl⟩⟩)

/-- Induction on the Higgs algebra: a property of elements of `B` which holds on every
  Higgs and conjugate Higgs symbol and on every scalar, and is closed under sums and
  products of elements of the algebra, holds on the whole algebra. -/
lemma higgsAlgebra_induction {P : B → Prop}
    (hH : ∀ (n : ℕ) (d : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec),
      P (h.covH n d φ))
    (hbarH : ∀ (n : ℕ) (d : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec)),
      P (h.covBarH n d φ))
    (halg : ∀ r : ℂ, P (algebraMap ℂ B r))
    (hadd : ∀ x y, x ∈ h.higgsAlgebra → y ∈ h.higgsAlgebra → P x → P y → P (x + y))
    (hmul : ∀ x y, x ∈ h.higgsAlgebra → y ∈ h.higgsAlgebra → P x → P y → P (x * y))
    {x : B} (hx : x ∈ h.higgsAlgebra) : P x := by
  rw [higgsAlgebra] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hy
    obtain ⟨k, d, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hy
    exacts [hH k d φ, hbarH k d φ]
  | algebraMap r => exact halg r
  | add x y hx hy ihx ihy => exact hadd x y hx hy ihx ihy
  | mul x y hx hy ihx ihy => exact hmul x y hx hy ihx ihy

/-- Any two elements of the Higgs algebra commute. -/
lemma commute_of_mem_higgsAlgebra {x y : B} (hx : x ∈ h.higgsAlgebra)
    (hy : y ∈ h.higgsAlgebra) : Commute x y := by
  have hH : ∀ (n : ℕ) (d : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec),
      Commute (h.covH n d φ) y := fun n d φ =>
    h.higgsAlgebra_induction (P := fun y => Commute (h.covH n d φ) y)
      (fun _ _ _ => h.H_comm_H _ _ _ _ _ _) (fun _ _ _ => h.H_comm_barH _ _ _ _ _ _)
      (fun r => Algebra.commute_algebraMap_right r _)
      (fun _ _ _ _ => Commute.add_right) (fun _ _ _ _ => Commute.mul_right) hy
  have hbarH : ∀ (n : ℕ) (d : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule HiggsVec)), Commute (h.covBarH n d φ) y := fun n d φ =>
    h.higgsAlgebra_induction (P := fun y => Commute (h.covBarH n d φ) y)
      (fun _ _ _ => (h.H_comm_barH _ _ _ _ _ _).symm) (fun _ _ _ => h.barH_comm_barH _ _ _ _ _ _)
      (fun r => Algebra.commute_algebraMap_right r _)
      (fun _ _ _ _ => Commute.add_right) (fun _ _ _ _ => Commute.mul_right) hy
  exact h.higgsAlgebra_induction (P := fun x => Commute x y) hH hbarH
    (fun r => Algebra.commute_algebraMap_left r y)
    (fun _ _ _ _ => Commute.add_left) (fun _ _ _ _ => Commute.mul_left) hx

/-- Two submodules of the Higgs algebra commute. -/
lemma mul_comm_of_le_higgsAlgebra {M N : Submodule ℂ B}
    (hM : M ≤ Subalgebra.toSubmodule h.higgsAlgebra)
    (hN : N ≤ Subalgebra.toSubmodule h.higgsAlgebra) : M * N = N * M := by
  refine le_antisymm (Submodule.mul_le.mpr fun x hx y hy => ?_)
    (Submodule.mul_le.mpr fun y hy x hx => ?_)
  · rw [(h.commute_of_mem_higgsAlgebra (hM hx) (hN hy)).eq]
    exact Submodule.mul_mem_mul hy hx
  · rw [← (h.commute_of_mem_higgsAlgebra (hM hx) (hN hy)).eq]
    exact Submodule.mul_mem_mul hx hy

/-!

## C. The components and the Higgs submodules

The components `∇_d H^i` and `∇_d H̄^i` are the symbols evaluated on the dual of the standard
basis of `HiggsVec`. The Higgs submodule with `n` derivatives is the span of the symbols
`∇_d H` over all multi-indices `d` of length `n`, equally the span of the components.

-/

/-- The component `∇_d H^i` in the algebra. -/
noncomputable def higgs (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)
    {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) : B :=
  h.covH n d (HiggsVec.orthonormBasis.toBasis.dualBasis i)

/-- The component `∇_d H̄^i` in the algebra. -/
noncomputable def barHiggs (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)
    {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) : B :=
  h.covBarH n d ((Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis i)

/-!

### C.1. The gauge action on the components

-/

/-- The gauge group mixes the components of `∇_d H` by the matrix `u⁻³ g⁻¹` of the
  hypercharge and `SU(2)` parts of `g⁻¹`. -/
lemma rep_higgsComponent (g : GaugeGroupI) {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) :
    rep g (h.higgs d i) =
      ∑ j, (((g⁻¹).toU1 : ℂ) ^ 3 * (g⁻¹).toSU2.1 i j) • h.higgs d j := by
  have key : HiggsVec.repGaugeGroupI.dual g (HiggsVec.orthonormBasis.toBasis.dualBasis i)
      = ∑ j, (((g⁻¹).toU1 : ℂ) ^ 3 * (g⁻¹).toSU2.1 i j) •
          HiggsVec.orthonormBasis.toBasis.dualBasis j := by
    refine HiggsVec.orthonormBasis.toBasis.ext fun k => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, Module.Basis.dualBasis_apply_self,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    simp [Representation.dual, HiggsVec.repGaugeGroupI_apply, HiggsVec.orthonormBasis,
      Submonoid.smul_def, -inv_pow]
  rw [higgs, h.H_equivariant, key, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

/-- The gauge group mixes the components of `∇_d H̄` by the conjugate matrix. -/
lemma rep_barHiggsComponent (g : GaugeGroupI) {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (i : Fin 2) :
    rep g (h.barHiggs d i) =
      ∑ j, (starRingEnd ℂ (((g⁻¹).toU1 : ℂ) ^ 3 * (g⁻¹).toSU2.1 i j)) • h.barHiggs d j := by
  have key : HiggsVec.repGaugeGroupI.conj.dual g
        ((Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis i)
      = ∑ j, (starRingEnd ℂ (((g⁻¹).toU1 : ℂ) ^ 3 * (g⁻¹).toSU2.1 i j)) •
          (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis j := by
    refine (Basis.conj HiggsVec.orthonormBasis.toBasis).ext fun k => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, Module.Basis.dualBasis_apply_self,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    simp [Representation.dual, Representation.conj_apply, HiggsVec.repGaugeGroupI_apply,
      HiggsVec.orthonormBasis, Submonoid.smul_def, -inv_pow]
  rw [barHiggs, h.barH_equivariant, key, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

/-!

### C.2. The Higgs and conjugate Higgs submodules

-/

/-- The submodule of `B` generated by the Higgs symbols carrying `n` derivatives: the join,
  over the Lorentz indices `d`, of the ranges of the symbol maps `H n d`. Its elements are
  the terms linear in `∇_d H` — of mass dimension `1 + n`. -/
noncomputable def higgsSubmodule
    (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly) (n : ℕ) :
    Submodule ℂ B := ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), LinearMap.range (h.covH n d)

/-- The submodule of `B` generated by the conjugate Higgs symbols carrying `n` derivatives:
  the join, over the Lorentz indices `d`, of the ranges of the symbol maps `barH n d`. -/
noncomputable def barHiggsSubmodule
    (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly) (n : ℕ) :
    Submodule ℂ B := ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), LinearMap.range (h.covBarH n d)

/-- The Higgs submodule is spanned by the components `∇_d H^j`. -/
lemma higgsSubmodule_eq_iSup_span (n : ℕ) :
    h.higgsSubmodule n = ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (j : Fin 2), ℂ ∙ h.higgs d j := by
  rw [higgsSubmodule]
  refine iSup_congr fun d => ?_
  rw [LinearMap.range_eq_map, ← HiggsVec.orthonormBasis.toBasis.dualBasis.span_eq,
    Submodule.map_span, ← Set.range_comp, Submodule.span_range_eq_iSup]
  rfl

/-- The conjugate Higgs submodule is spanned by the components `∇_d H̄^j`. -/
lemma barHiggsSubmodule_eq_iSup_span (n : ℕ) :
    h.barHiggsSubmodule n
      = ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (j : Fin 2), ℂ ∙ h.barHiggs d j := by
  rw [barHiggsSubmodule]
  refine iSup_congr fun d => ?_
  rw [LinearMap.range_eq_map, ← (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis.span_eq,
    Submodule.map_span, ← Set.range_comp, Submodule.span_range_eq_iSup]
  rfl

/-- The Higgs submodule lies in the Higgs algebra. -/
lemma higgsSubmodule_le_higgsAlgebra (n : ℕ) :
    h.higgsSubmodule n ≤ Subalgebra.toSubmodule h.higgsAlgebra := by
  rw [higgsSubmodule]
  refine iSup_le fun d => ?_
  rintro _ ⟨φ, rfl⟩
  exact h.covH_mem_higgsAlgebra d φ

/-- The conjugate Higgs submodule lies in the Higgs algebra. -/
lemma barHiggsSubmodule_le_higgsAlgebra (n : ℕ) :
    h.barHiggsSubmodule n ≤ Subalgebra.toSubmodule h.higgsAlgebra := by
  rw [barHiggsSubmodule]
  refine iSup_le fun d => ?_
  rintro _ ⟨φ, rfl⟩
  exact h.covBarH_mem_higgsAlgebra d φ

/-- The conjugate Higgs and Higgs submodules commute. -/
@[simp]
lemma barHiggsSubmodule_comm_higgsSubmodule (n1 n2 : ℕ) :
    (h.barHiggsSubmodule n1) * (h.higgsSubmodule n2)
    =  (h.higgsSubmodule n2)  * (h.barHiggsSubmodule n1) :=
  h.mul_comm_of_le_higgsAlgebra (h.barHiggsSubmodule_le_higgsAlgebra n1)
    (h.higgsSubmodule_le_higgsAlgebra n2)

/-- Two Higgs submodules commute. -/
lemma higgsSubmodule_comm_higgsSubmodule (n1 n2 : ℕ) :
    (h.higgsSubmodule n1) * (h.higgsSubmodule n2)
    =  (h.higgsSubmodule n2)  * (h.higgsSubmodule n1) :=
  h.mul_comm_of_le_higgsAlgebra (h.higgsSubmodule_le_higgsAlgebra n1)
    (h.higgsSubmodule_le_higgsAlgebra n2)

/-- Two conjugate Higgs submodules commute. -/
lemma barHiggsSubmodule_comm_barHiggsSubmodule (n1 n2 : ℕ) :
    (h.barHiggsSubmodule n1) * (h.barHiggsSubmodule n2)
    =  (h.barHiggsSubmodule n2)  * (h.barHiggsSubmodule n1) :=
  h.mul_comm_of_le_higgsAlgebra (h.barHiggsSubmodule_le_higgsAlgebra n1)
    (h.barHiggsSubmodule_le_higgsAlgebra n2)

/-- A conjugate Higgs submodule commutes past a Higgs submodule standing in front of a third
  factor. -/
lemma barHiggs_higgs_left_comm (n1 n2 : ℕ) (C : Submodule ℂ B) :
    h.barHiggsSubmodule n1 * (h.higgsSubmodule n2 * C)
      = h.higgsSubmodule n2 * (h.barHiggsSubmodule n1 * C) :=
  Commute.left_comm (h.barHiggsSubmodule_comm_higgsSubmodule n1 n2) C

/-!

## D. The gauge weight decomposition of the Higgs submodules

The four torus generators `gaugeTorusGen i` act on each component by a character: `∇_d H^j`
has isospin weight `-isoWeight j` and hypercharge weight `-3`, and `∇_d H̄^j` the opposite.
The general construction `doubletGaugeWeight` turns a family of such two-component
eigenvectors into a gauge weight decomposition of its span, and the two Higgs submodules
are instances of it.

-/

/-- The torus generators act on `∇_d H^j` by the character of weight
  `(0, 0, -isoWeight j, -3)`. -/
lemma rep_gaugeTorusGen_higgs (i : Fin 4) {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3)) (j : Fin 2) :
    rep (gaugeTorusGen i) (h.higgs d j)
      = ((expI : ℂ) ^ GaugeWeight.coord (0, 0, -isoWeight j, -3) i) • h.higgs d j := by
  have hstar : ((starRingEnd ℂ) (expI : ℂ)) ^ 3 = (((expI : ℂ)) ^ 3)⁻¹ := by
    rw [← inv_pow]
    congr 1
    exact expI_inv_eq_star.symm
  rw [h.rep_higgsComponent]
  fin_cases j <;> fin_cases i <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI_inv_coe, isoWeight,
      Fin.sum_univ_two, expI_inv_eq_star, Matrix.one_apply, Unitary.coe_inv, hstar]

/-- The torus generators act on `∇_d H̄^j` by the character of weight
  `(0, 0, isoWeight j, 3)`. -/
lemma rep_gaugeTorusGen_barHiggs (i : Fin 4) {n : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (j : Fin 2) :
    rep (gaugeTorusGen i) (h.barHiggs d j)
      = ((expI : ℂ) ^ GaugeWeight.coord (0, 0, isoWeight j, 3) i) • h.barHiggs d j := by
  have hc : (starRingEnd ℂ) (expI : ℂ) = ((expI : ℂ))⁻¹ := expI_inv_eq_star.symm
  rw [h.rep_barHiggsComponent]
  fin_cases j <;> fin_cases i <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI_inv_coe, isoWeight,
      Fin.sum_univ_two, Matrix.one_apply, Unitary.coe_inv, hc]

/-- The span of a family of eigenvectors of a torus generator lies in its eigenspace. -/
lemma iSup_span_le_eigenspace {ι : Type} (i : Fin 4) (y : ι → B) (w : GaugeWeight)
    (hy : ∀ d, rep (gaugeTorusGen i) (y d) = ((expI : ℂ) ^ w.coord i) • y d) :
    (⨆ d, ℂ ∙ y d) ≤ Module.End.eigenspace (rep (gaugeTorusGen i)) ((expI : ℂ) ^ w.coord i) :=
  iSup_le fun d => (Submodule.span_singleton_le_iff_mem _ _).mpr
    (Module.End.mem_eigenspace_iff.mpr (hy d))

/-- The gauge weight decomposition of the span of a two-component family `x d j` of torus
  eigenvectors, the components `x d 0` of weight `w₀` and `x d 1` of weight `w₁ ≠ w₀`: the
  weight-`w₀` piece is the span of the `x d 0` and the weight-`w₁` piece that of the
  `x d 1`. -/
@[implicit_reducible]
noncomputable def doubletGaugeWeight {ι : Type} (hmul : IsMulRep rep) (x : ι → Fin 2 → B)
    (w₀ w₁ : GaugeWeight) (hw : w₀ ≠ w₁)
    (hx₀ : ∀ (i : Fin 4) (d : ι),
      rep (gaugeTorusGen i) (x d 0) = ((expI : ℂ) ^ w₀.coord i) • x d 0)
    (hx₁ : ∀ (i : Fin 4) (d : ι),
      rep (gaugeTorusGen i) (x d 1) = ((expI : ℂ) ^ w₁.coord i) • x d 1) :
    GaugeWeightDecomposition rep (⨆ (d : ι) (j : Fin 2), ℂ ∙ x d j) where
  piece w := if w = w₀ then ⨆ d, ℂ ∙ x d 0 else if w = w₁ then ⨆ d, ℂ ∙ x d 1 else ⊥
  supp := {w₀, w₁}
  rep_mul := hmul
  piece_le w y hy i := by
    split_ifs at hy with h0 h1
    · rw [h0]
      exact Module.End.mem_eigenspace_iff.mp
        (iSup_span_le_eigenspace i (fun d => x d 0) w₀ (hx₀ i) hy)
    · rw [h1]
      exact Module.End.mem_eigenspace_iff.mp
        (iSup_span_le_eigenspace i (fun d => x d 1) w₁ (hx₁ i) hy)
    · rw [Submodule.mem_bot] at hy
      subst hy
      simp
  piece_eq_bot w hw' := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw'
    rw [ite_eq_right hw'.1, ite_eq_right hw'.2]
  iSup_piece := by
    refine le_antisymm (iSup_le fun w => ?_) (iSup_le fun d => iSup_le fun j => ?_)
    · split_ifs
      · exact iSup_mono fun d => le_iSup (fun j => ℂ ∙ x d j) 0
      · exact iSup_mono fun d => le_iSup (fun j => ℂ ∙ x d j) 1
      · exact bot_le
    · fin_cases j
      · exact le_iSup_of_le w₀ (by rw [ite_eq_left rfl]; exact le_iSup (fun d => ℂ ∙ x d 0) d)
      · exact le_iSup_of_le w₁
          (by rw [ite_eq_right hw.symm, ite_eq_left rfl]; exact le_iSup (fun d => ℂ ∙ x d 1) d)

/-- The gauge weight decomposition of the Higgs submodule: `∇_d H⁰` spans the piece of
  weight `(0, 0, -1, -3)` and `∇_d H¹` that of weight `(0, 0, 1, -3)`. -/
noncomputable instance higgsSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition rep (h.higgsSubmodule n) :=
  (doubletGaugeWeight h.rep_mul (h.higgs (n := n)) (0, 0, -1, -3) (0, 0, 1, -3) (by decide)
    (fun i d => h.rep_gaugeTorusGen_higgs i d 0)
    (fun i d => h.rep_gaugeTorusGen_higgs i d 1)).copy _ (h.higgsSubmodule_eq_iSup_span n)

/-- The gauge weight decomposition of the conjugate Higgs submodule: `∇_d H̄⁰` spans the
  piece of weight `(0, 0, 1, 3)` and `∇_d H̄¹` that of weight `(0, 0, -1, 3)`. -/
noncomputable instance barHiggsSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition rep (h.barHiggsSubmodule n) :=
  (doubletGaugeWeight h.rep_mul (h.barHiggs (n := n)) (0, 0, 1, 3) (0, 0, -1, 3) (by decide)
    (fun i d => h.rep_gaugeTorusGen_barHiggs i d 0)
    (fun i d => h.rep_gaugeTorusGen_barHiggs i d 1)).copy _
    (h.barHiggsSubmodule_eq_iSup_span n)

/-!

## E. The Higgs inner product

The pairing `∇_{d1} H⁰ ∇_{d2} H̄⁰ + ∇_{d1} H¹ ∇_{d2} H̄¹` is invariant under the gauge group,
since `H̄` transforms by the conjugate of the unitary matrix acting on `H`, and its two
derivative multi-indices rotate independently under the Lorentz group.

-/

/-- The gauge-invariant pairing `∇_{d1} H^j ∇_{d2} H̄^j`, summed over the isospin index. -/
noncomputable def dotGaugeHiggs (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)
    {n1 n2 : ℕ} (d1 : Fin n1 → (Fin 1 ⊕ Fin 3)) (d2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    B := h.higgs d1 0 * h.barHiggs d2 0 + h.higgs d1 1 * h.barHiggs d2 1

/-- The pairing is gauge invariant: the matrix acting on `H` is unitary, and `H̄` transforms
  by its conjugate. -/
lemma rep_dotGaugeHiggs_invariant {n1 n2 : ℕ} (g : GaugeGroupI) (d1 : Fin n1 → (Fin 1 ⊕ Fin 3))
    (d2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    rep g (h.dotGaugeHiggs d1 d2) = h.dotGaugeHiggs d1 d2 := by
  have hu : ((g⁻¹).toU1 : ℂ) * (starRingEnd ℂ) ((g⁻¹).toU1 : ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (g⁻¹).toU1.2
  have hM : star ((g⁻¹).toSU2.1) * (g⁻¹).toSU2.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (g⁻¹).toSU2.2.1
  have hM00 := congrFun (congrFun hM 0) 0
  have hM01 := congrFun (congrFun hM 0) 1
  have hM10 := congrFun (congrFun hM 1) 0
  have hM11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, star_eq_conjTranspose,
    Matrix.conjTranspose_apply, reduceIte, Complex.star_def,
    show ¬((0 : Fin 2) = 1) from by decide,
    show ¬((1 : Fin 2) = 0) from by decide] at hM00 hM01 hM10 hM11
  have hM01' := congrArg (starRingEnd ℂ) hM01
  have hM10' := congrArg (starRingEnd ℂ) hM10
  simp only [map_add, map_mul, Complex.conj_conj, map_zero] at hM01' hM10'
  have hu3 : ((g⁻¹).toU1 : ℂ) ^ 3 * (starRingEnd ℂ) (((g⁻¹).toU1 : ℂ) ^ 3) = 1 := by
    rw [map_pow, ← mul_pow, hu, one_pow]
  have key : ∀ a b : ℂ, (((g⁻¹).toU1 : ℂ) ^ 3 * a) * (starRingEnd ℂ) (((g⁻¹).toU1 : ℂ) ^ 3 * b)
      = a * (starRingEnd ℂ) b := by
    intro a b
    rw [map_mul]
    calc (((g⁻¹).toU1 : ℂ) ^ 3 * a) * ((starRingEnd ℂ) (((g⁻¹).toU1 : ℂ) ^ 3)
          * (starRingEnd ℂ) b)
        = (((g⁻¹).toU1 : ℂ) ^ 3 * (starRingEnd ℂ) (((g⁻¹).toU1 : ℂ) ^ 3))
          * (a * (starRingEnd ℂ) b) := by ring
      _ = a * (starRingEnd ℂ) b := by rw [hu3, one_mul]
  rw [dotGaugeHiggs, map_add, h.rep_mul, h.rep_mul, h.rep_higgsComponent,
    h.rep_barHiggsComponent, h.rep_higgsComponent, h.rep_barHiggsComponent]
  simp only [Fin.sum_univ_two, add_mul, mul_add, smul_mul_smul_comm, key]
  match_scalars
  · linear_combination hM00
  · linear_combination hM10'
  · linear_combination hM01'
  · linear_combination hM11

/-- The Lorentz action rotates the derivative indices of a Higgs component. -/
lemma repLorentz_higgs {n : ℕ} (g : SL(2,ℂ)) (d : Fin n → Fin 1 ⊕ Fin 3) (k : Fin 2) :
    repLorentz g (h.higgs d k) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ j, (((SL2C.toLorentzGroup g).1 (a j) (d j) : ℝ) : ℂ)) • h.higgs a k := by
  simp only [higgs]
  rw [h.repLorentz_H_apply]

/-- The Lorentz action rotates the derivative indices of a conjugate Higgs component. -/
lemma repLorentz_barHiggs {n : ℕ} (g : SL(2,ℂ)) (d : Fin n → Fin 1 ⊕ Fin 3) (k : Fin 2) :
    repLorentz g (h.barHiggs d k) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
      (∏ j, (((SL2C.toLorentzGroup g).1 (a j) (d j) : ℝ) : ℂ)) • h.barHiggs a k := by
  simp only [barHiggs]
  rw [h.repLorentz_barH_apply]

/-- The Lorentz action on the Higgs inner product: the two factors' derivative indices
  rotate independently, and the inner product itself is a Lorentz scalar. -/
lemma repLorentz_dotGaugeHiggs {m n : ℕ} (g : SL(2,ℂ))
    (d₁ : Fin m → Fin 1 ⊕ Fin 3) (d₂ : Fin n → Fin 1 ⊕ Fin 3) :
    repLorentz g (h.dotGaugeHiggs d₁ d₂) =
      ∑ a₁ : Fin m → Fin 1 ⊕ Fin 3, ∑ a₂ : Fin n → Fin 1 ⊕ Fin 3,
        ((∏ j, (((SL2C.toLorentzGroup g).1 (a₁ j) (d₁ j) : ℝ) : ℂ)) *
          (∏ j, (((SL2C.toLorentzGroup g).1 (a₂ j) (d₂ j) : ℝ) : ℂ))) •
          h.dotGaugeHiggs a₁ a₂ := by
  simp only [dotGaugeHiggs, map_add, h.repLorentz_mul, repLorentz_higgs, repLorentz_barHiggs,
    Finset.sum_mul_sum, smul_mul_smul_comm, smul_add, Finset.sum_add_distrib]

/-!

## F. The mass weight submodules

A Higgs tower `∇ⁿH` or `∇ⁿH̄` has mass weight `2 * (1 + n)`, twice its mass dimension
`1 + n`; a term of mass dimension four, as in the Lagrangian, has weight eight.

-/

/-- All terms built from the Higgs symbols and their derivatives which have mass weight
  exactly `n`: the intersection of the algebra generated by every `∇_d H` and `∇_d H̄` with
  the part on which `massWeightPoly` is the monomial `X ^ n`. -/
noncomputable def massWeightSubmodule
    (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly) (n : ℕ) :
    Submodule ℂ B :=
  h.higgsAlgebra.toSubmodule
    ⊓ LinearMap.ker (massWeightPoly.toLinearMap
      - (Polynomial.monomial n : B →ₗ[B] Polynomial B).restrictScalars ℂ)

/-!

### F.1. Membership and the grading

-/

/-- An element has mass weight `n` when it lies in the Higgs algebra and `massWeightPoly`
  scales it by `X ^ n`. -/
lemma mem_massWeightSubmodule_iff {n : ℕ} {x : B} :
    x ∈ h.massWeightSubmodule n
      ↔ x ∈ h.higgsAlgebra ∧ massWeightPoly x = Polynomial.monomial n x :=
  Subalgebra.mem_homogeneousSubmodule_iff

/-- The mass weight of an element of the weight-`n` submodule. -/
lemma massWeightPoly_of_mem_massWeightSubmodule {n : ℕ} {x : B}
    (hx : x ∈ h.massWeightSubmodule n) : massWeightPoly x = Polynomial.monomial n x :=
  (h.mem_massWeightSubmodule_iff.mp hx).2

/-- The weight-`n` submodule lies in the Higgs algebra. -/
lemma mem_higgsAlgebra_of_mem_massWeightSubmodule {n : ℕ} {x : B}
    (hx : x ∈ h.massWeightSubmodule n) : x ∈ h.higgsAlgebra :=
  (h.mem_massWeightSubmodule_iff.mp hx).1

/-- Two mass weight submodules commute. -/
lemma massWeightSubmodule_mul_comm (n m : ℕ) :
    h.massWeightSubmodule n * h.massWeightSubmodule m
    = h.massWeightSubmodule m * h.massWeightSubmodule n :=
  h.mul_comm_of_le_higgsAlgebra inf_le_left inf_le_left

/-- The scalars have mass weight zero. -/
lemma one_le_massWeightSubmodule_zero : (1 : Submodule ℂ B) ≤ h.massWeightSubmodule 0 :=
  Subalgebra.one_le_homogeneousSubmodule_zero

/-- Mass weights add under multiplication. -/
lemma massWeightSubmodule_mul_le (m n : ℕ) :
    h.massWeightSubmodule m * h.massWeightSubmodule n ≤ h.massWeightSubmodule (m + n) :=
  Subalgebra.homogeneousSubmodule_mul_le m n

/-- The Higgs symbols with `n` derivatives have mass weight `2 * (1 + n)`. -/
lemma massWeightSubmodule_higgsSubmodule_le (n : ℕ) :
    h.higgsSubmodule n ≤ h.massWeightSubmodule (2 * (1 + n)) := by
  rw [higgsSubmodule]
  refine iSup_le fun d => ?_
  rintro _ ⟨φ, rfl⟩
  exact h.mem_massWeightSubmodule_iff.mpr ⟨h.covH_mem_higgsAlgebra d φ, h.H_massWeight φ n d⟩

/-- The conjugate Higgs symbols with `n` derivatives have mass weight `2 * (1 + n)`. -/
lemma massWeightSubmodule_barHiggsSubmodule_le (n : ℕ) :
    h.barHiggsSubmodule n ≤ h.massWeightSubmodule (2 * (1 + n)) := by
  rw [barHiggsSubmodule]
  refine iSup_le fun d => ?_
  rintro _ ⟨φ, rfl⟩
  exact h.mem_massWeightSubmodule_iff.mpr
    ⟨h.covBarH_mem_higgsAlgebra d φ, h.barH_massWeight φ n d⟩

/-!

### F.2. The weight decompositions

The Higgs algebra is generated by the towers `∇ⁿH ⊔ ∇ⁿH̄`, on which `massWeightPoly` is the
monomial `X ^ (2 * (1 + n))`. The results of `Physlib.Mathematics.HomogeneousGenerators`
then describe every mass weight submodule, as a join of products of towers in the order
written.

-/

/-- The Higgs algebra is generated by the Higgs and conjugate Higgs towers of every
  derivative order. -/
lemma higgsAlgebra_eq_adjoin :
    h.higgsAlgebra = Algebra.adjoin ℂ
      (⋃ n, ((h.higgsSubmodule n ⊔ h.barHiggsSubmodule n : Submodule ℂ B) : Set B)) := by
  refine le_antisymm (Algebra.adjoin_le fun y hy => ?_) (Algebra.adjoin_le fun y hy => ?_)
  · simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hy
    obtain ⟨n, d, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hy
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨n, Submodule.mem_sup_left
        (Submodule.mem_iSup_of_mem d ⟨φ, rfl⟩)⟩)
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨n, Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem d ⟨φ, rfl⟩)⟩)
  · obtain ⟨n, hy⟩ := Set.mem_iUnion.mp hy
    exact sup_le (h.higgsSubmodule_le_higgsAlgebra n) (h.barHiggsSubmodule_le_higgsAlgebra n) hy

/-- `massWeightPoly` is the monomial `X ^ (2 * (1 + n))` on the Higgs and conjugate Higgs
  towers with `n` derivatives. -/
lemma massWeightPoly_of_mem_higgsSubmodule_sup (n : ℕ) :
    ∀ x ∈ h.higgsSubmodule n ⊔ h.barHiggsSubmodule n,
      massWeightPoly x = Polynomial.monomial (2 * (1 + n)) x := fun _ hx =>
  h.massWeightPoly_of_mem_massWeightSubmodule
    (sup_le (h.massWeightSubmodule_higgsSubmodule_le n)
      (h.massWeightSubmodule_barHiggsSubmodule_le n) hx)

/-- Weight zero is the scalars: every Higgs tower has positive weight. -/
lemma massWeightSubmodule_zero_eq : h.massWeightSubmodule 0 = 1 :=
  Subalgebra.homogeneousSubmodule_zero_eq_one h.higgsAlgebra_eq_adjoin
    h.massWeightPoly_of_mem_higgsSubmodule_sup (fun n => by omega)

/-- The weight recursion: a term of positive mass weight `i` is a sum of symbols of weight
  `i` and of products of two terms of lower positive weight adding up to `i`. -/
theorem massWeightSubmodule_eq (i : ℕ) (hi : 0 < i) :
    h.massWeightSubmodule i
      = (⨆ k ∈ Finset.univ.filter (fun k : Fin i => 2 * (1 + (k : ℕ)) = i),
          h.higgsSubmodule (k : ℕ) ⊔ h.barHiggsSubmodule (k : ℕ))
        ⊔ (⨆ p ∈ Finset.univ.filter (fun p : Fin i × Fin i => (p.1 : ℕ) + (p.2 : ℕ) = i),
            h.massWeightSubmodule (p.1 : ℕ) * h.massWeightSubmodule (p.2 : ℕ)) :=
  Subalgebra.homogeneousSubmodule_eq_sup_iSup_mul (deg := fun n => 2 * (1 + n))
    h.higgsAlgebra_eq_adjoin h.massWeightPoly_of_mem_higgsSubmodule_sup
    (fun n => by omega) i hi

/-- Removing the leftmost Higgs tower: a term of positive weight `w` is a sum of products
  of a tower `∇ⁿH` or `∇ⁿH̄`, of weight `2 * (1 + n) ≤ w`, with a term of the remaining
  weight. -/
lemma massWeightSubmodule_eq_iSup_mul (w : ℕ) (hw : 0 < w) :
    h.massWeightSubmodule w
      = ⨆ n ∈ (Finset.range (w + 1)).filter (fun n => 2 * (1 + n) ≤ w),
          (h.higgsSubmodule n ⊔ h.barHiggsSubmodule n) * h.massWeightSubmodule (w - 2 * (1 + n)) :=
  Subalgebra.homogeneousSubmodule_eq_iSup_mul (deg := fun n => 2 * (1 + n))
    h.higgsAlgebra_eq_adjoin h.massWeightPoly_of_mem_higgsSubmodule_sup
    (fun n => by omega) hw

/-!

### F.3. The odd mass weights vanish

-/

/-- The odd mass weight submodules are trivial: every Higgs tower has even weight, and
  weights add under products. -/
lemma massWeightSubmodule_odd_eq_bot (n : ℕ) (hn : Odd n) :
    h.massWeightSubmodule n = ⊥ :=
  Subalgebra.homogeneousSubmodule_eq_bot h.higgsAlgebra_eq_adjoin
    h.massWeightPoly_of_mem_higgsSubmodule_sup (fun w => w % 2 = 0) rfl (fun n => by omega)
    (fun a b ha hb => by omega) (by obtain ⟨r, rfl⟩ := hn; omega)

/-!

### F.4. The gauge weight decomposition

-/

/-- The gauge weight decomposition of the mass weight submodules. By recursion on the
  weight through `massWeightSubmodule_eq`: a term of weight `i` is either a symbol of that
  weight — decomposed by `higgsSubmoduleGaugeWeight` and `barHiggsSubmoduleGaugeWeight` — or
  a product of two terms of lower positive weight, decomposed by `mul` from the
  decompositions supplied by the recursion. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeight :
    (i : ℕ) → 0 < i → GaugeWeightDecomposition rep (h.massWeightSubmodule i) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    refine (GaugeWeightDecomposition.sup (d := ?_) (d' := ?_)).copy _
      (h.massWeightSubmodule_eq i hi)
    · exact GaugeWeightDecomposition.iSup h.rep_mul fun k : Fin i =>
        GaugeWeightDecomposition.iSupProp h.rep_mul fun _ =>
          GaugeWeightDecomposition.sup (d := h.higgsSubmoduleGaugeWeight (k : ℕ))
            (d' := h.barHiggsSubmoduleGaugeWeight (k : ℕ))
    · exact GaugeWeightDecomposition.iSup h.rep_mul fun p : Fin i × Fin i =>
        GaugeWeightDecomposition.iSupProp h.rep_mul fun hp =>
          have hsum : (p.1 : ℕ) + (p.2 : ℕ) = i := (Finset.mem_filter.mp hp).2
          have hj : (p.1 : ℕ) < i := p.1.isLt
          have hl : (p.2 : ℕ) < i := p.2.isLt
          GaugeWeightDecomposition.mul (d := ih (p.1 : ℕ) hj (by omega))
            (d' := ih (p.2 : ℕ) hl (by omega))

/-- The `NeZero` form of `massWeightSubmoduleGaugeWeight`. -/
noncomputable instance massWeightSubmoduleGaugeWeightOfNeZero (i : ℕ) [NeZero i] :
    GaugeWeightDecomposition rep (h.massWeightSubmodule i) :=
  h.massWeightSubmoduleGaugeWeight i (Nat.pos_of_ne_zero (NeZero.ne i))

/-!

### F.5. Mass weights up to eight

Each case removes the leftmost tower. The towers with `0`, `1`, `2` and `3` derivatives
have weights `2`, `4`, `6` and `8`, and the remaining weight is read off from a smaller weight.
Expanding the joins gives the products of `H` and `H̄`; the Higgs algebra is commutative,
so orders differing only by the position of commuting factors are merged, and the products
are written in a fixed order.

-/

/-- Weight two: the underived Higgs and conjugate Higgs. -/
lemma massWeightSubmodule_two_eq :
    h.massWeightSubmodule 2 = h.higgsSubmodule 0 ⊔ h.barHiggsSubmodule 0 := by
  rw [h.massWeightSubmodule_eq_iSup_mul 2 (by decide),
    show (Finset.range 3).filter (fun n => 2 * (1 + n) ≤ 2) = {0} from by decide,
    Finset.iSup_singleton]
  simp [h.massWeightSubmodule_zero_eq]

/-- Weight four: the once-derived symbols and the products of two underived ones. The
  leftmost tower is underived, leaving weight two, or once-derived, leaving weight zero. -/
lemma massWeightSubmodule_four_eq :
    h.massWeightSubmodule 4 = h.higgsSubmodule 1 ⊔ h.barHiggsSubmodule 1 ⊔
    h.higgsSubmodule 0 * h.higgsSubmodule 0 ⊔ h.higgsSubmodule 0 *
    h.barHiggsSubmodule 0 ⊔ h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0:= by
  rw [h.massWeightSubmodule_eq_iSup_mul 4 (by decide),
    show (Finset.range 5).filter (fun n => 2 * (1 + n) ≤ 4) = {0, 1} from by decide,
    Finset.iSup_insert, Finset.iSup_singleton]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, h.massWeightSubmodule_two_eq,
    h.massWeightSubmodule_zero_eq, mul_one, Submodule.sup_mul, Submodule.mul_sup,
    barHiggsSubmodule_comm_higgsSubmodule]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_left_idem]

/-- Weight six: the twice-derived symbols, a once-derived symbol against an underived one,
  and the products of three underived ones. The leftmost tower leaves weight four, two or
  zero. -/
lemma massWeightSubmodule_six_eq : h.massWeightSubmodule 6 =
    -- The derivative terms
    h.higgsSubmodule 2 ⊔ h.barHiggsSubmodule 2 ⊔
    h.higgsSubmodule 1 * h.higgsSubmodule 0 ⊔
    h.higgsSubmodule 1 * h.barHiggsSubmodule 0 ⊔
    h.barHiggsSubmodule 1 * h.higgsSubmodule 0 ⊔
    h.barHiggsSubmodule 1 * h.barHiggsSubmodule 0 ⊔
    -- The potential terms
    h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.higgsSubmodule 0  ⊔
    h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 0 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0  := by
  rw [h.massWeightSubmodule_eq_iSup_mul 6 (by decide),
    show (Finset.range 7).filter (fun n => 2 * (1 + n) ≤ 6) = {0, 1, 2} from by decide,
    Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, h.massWeightSubmodule_four_eq,
    h.massWeightSubmodule_two_eq, h.massWeightSubmodule_zero_eq, mul_one,
    Submodule.sup_mul, Submodule.mul_sup, mul_assoc, barHiggsSubmodule_comm_higgsSubmodule,
    h.barHiggs_higgs_left_comm, h.higgsSubmodule_comm_higgsSubmodule 0 1,
    h.barHiggsSubmodule_comm_barHiggsSubmodule 0 1]
  -- the products are atoms for the final reordering of the join
  generalize h.higgsSubmodule 2 = v1, h.barHiggsSubmodule 2 = v2,
    h.higgsSubmodule 1 * h.higgsSubmodule 0 = v3, h.higgsSubmodule 1 * h.barHiggsSubmodule 0 = v4,
    h.higgsSubmodule 0 * h.barHiggsSubmodule 1 = v5,
    h.barHiggsSubmodule 1 * h.barHiggsSubmodule 0 = v6,
    h.higgsSubmodule 0 * (h.higgsSubmodule 0 * h.higgsSubmodule 0) = v7,
    h.higgsSubmodule 0 * (h.higgsSubmodule 0 * h.barHiggsSubmodule 0) = v8,
    h.higgsSubmodule 0 * (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0) = v9,
    h.barHiggsSubmodule 0 * (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0) = v10
  ac_rfl

/-- Weight eight: the derivative terms with up to three derivatives, and the products of
  four underived symbols. The leftmost tower leaves weight six, four, two or zero. -/
lemma massWeightSubmodule_eight_eq :
    h.massWeightSubmodule 8 =
      -- The derivative terms
    h.higgsSubmodule 3 ⊔ h.barHiggsSubmodule 3 ⊔
    h.higgsSubmodule 2 * h.higgsSubmodule 0 ⊔
    h.higgsSubmodule 2 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 0 * h.barHiggsSubmodule 2 ⊔
    h.barHiggsSubmodule 2 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 1 * h.higgsSubmodule 1 ⊔
    h.higgsSubmodule 1 * h.barHiggsSubmodule 1 ⊔
    h.barHiggsSubmodule 1 * h.barHiggsSubmodule 1 ⊔
    h.higgsSubmodule 1 * h.higgsSubmodule 0 * h.higgsSubmodule 0 ⊔
    h.higgsSubmodule 1 * h.higgsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 1 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.barHiggsSubmodule 1 ⊔
    h.higgsSubmodule 0 * h.barHiggsSubmodule 1 * h.barHiggsSubmodule 0 ⊔
    h.barHiggsSubmodule 1 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    -- The potential terms
    h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.higgsSubmodule 0 ⊔
    h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 0 * h.higgsSubmodule 0 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.higgsSubmodule 0 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 ⊔
    h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0 *
      h.barHiggsSubmodule 0 := by
  rw [h.massWeightSubmodule_eq_iSup_mul 8 (by decide),
    show (Finset.range 9).filter (fun n => 2 * (1 + n) ≤ 8) = {0, 1, 2, 3} from by decide,
    Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
  have hlcH (C : Submodule ℂ B) : h.higgsSubmodule 0 * (h.higgsSubmodule 1 * C)
      = h.higgsSubmodule 1 * (h.higgsSubmodule 0 * C) :=
    Commute.left_comm (h.higgsSubmodule_comm_higgsSubmodule 0 1) C
  have hlcB (C : Submodule ℂ B) : h.barHiggsSubmodule 0 * (h.barHiggsSubmodule 1 * C)
      = h.barHiggsSubmodule 1 * (h.barHiggsSubmodule 0 * C) :=
    Commute.left_comm (h.barHiggsSubmodule_comm_barHiggsSubmodule 0 1) C
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, h.massWeightSubmodule_six_eq,
    h.massWeightSubmodule_four_eq, h.massWeightSubmodule_two_eq,
    h.massWeightSubmodule_zero_eq, mul_one, Submodule.sup_mul, Submodule.mul_sup, mul_assoc,
    barHiggsSubmodule_comm_higgsSubmodule, h.barHiggs_higgs_left_comm, hlcH, hlcB,
    h.higgsSubmodule_comm_higgsSubmodule 0 2, h.barHiggsSubmodule_comm_barHiggsSubmodule 0 1,
    h.barHiggsSubmodule_comm_barHiggsSubmodule 0 2]
  -- the products are atoms for the final reordering of the join
  generalize h.higgsSubmodule 3 = v1, h.barHiggsSubmodule 3 = v2,
    h.higgsSubmodule 2 * h.higgsSubmodule 0 = v3, h.higgsSubmodule 2 * h.barHiggsSubmodule 0 = v4,
    h.higgsSubmodule 0 * h.barHiggsSubmodule 2 = v5,
    h.barHiggsSubmodule 2 * h.barHiggsSubmodule 0 = v6,
    h.higgsSubmodule 1 * h.higgsSubmodule 1 = v7, h.higgsSubmodule 1 * h.barHiggsSubmodule 1 = v8,
    h.barHiggsSubmodule 1 * h.barHiggsSubmodule 1 = v9,
    h.higgsSubmodule 1 * (h.higgsSubmodule 0 * h.higgsSubmodule 0) = v10,
    h.higgsSubmodule 1 * (h.higgsSubmodule 0 * h.barHiggsSubmodule 0) = v11,
    h.higgsSubmodule 1 * (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0) = v12,
    h.higgsSubmodule 0 * (h.higgsSubmodule 0 * h.barHiggsSubmodule 1) = v13,
    h.higgsSubmodule 0 * (h.barHiggsSubmodule 1 * h.barHiggsSubmodule 0) = v14,
    h.barHiggsSubmodule 1 * (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0) = v15,
    h.higgsSubmodule 0 * (h.higgsSubmodule 0 * (h.higgsSubmodule 0 * h.higgsSubmodule 0)) = v16,
    h.higgsSubmodule 0 * (h.higgsSubmodule 0 * (h.higgsSubmodule 0 * h.barHiggsSubmodule 0))
      = v17,
    h.higgsSubmodule 0 * (h.higgsSubmodule 0 * (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0))
      = v18,
    h.higgsSubmodule 0 * (h.barHiggsSubmodule 0 * (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0))
      = v19,
    h.barHiggsSubmodule 0 * (h.barHiggsSubmodule 0 *
      (h.barHiggsSubmodule 0 * h.barHiggsSubmodule 0)) = v20
  ac_rfl

/-!

## G. Gauge invariants

-/

/-- The gauge invariants of a given mass weight. -/
noncomputable def gaugeInvariantOfMassDim (M : ℕ) : Submodule ℂ B :=
  h.massWeightSubmodule M ⊓ Representation.invariants rep

end HiggsAlgebraCovRealization

end StandardModel
