/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalCovFieldAlgebra.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization
/-!
# Realizations of the covariant field algebra

## i. Overview

A complex algebra `B` carries the covariant expressions of a gauge-field datum when the
covariant field algebra maps into it by a complex algebra map equivariant for the ordinary
gauge group `G₀` and for the Lorentz group, both acting on `B` by algebra endomorphisms:
`GaugeFieldData.LocalCovFieldAlgebra.Realization`. The gauge compatibility is with `G₀`
alone because the source action of the ordinary gauge group is the jet action at the
constant jets; the Lorentz action of the source exists only under
`GaugeFieldData.GaugeLorentzCompatible`, which the structure therefore carries.

The covariant field algebra is a subalgebra of `J(T)` and is not free on its five towers,
so a realization is its algebra map and not an assignment of the towers; generation gives
uniqueness only (`Realization.ext_towers`). A realization of the local field algebra
restricts to one of the covariant field algebra
(`GaugeFieldData.Realization.restrict`), with `G₀` acting on the target through the
constant jets. The converse extension is not claimed.

Under `GaugeFieldData.PureJetsActTrivially` the jet action factors through evaluation on
the realized covariant image, in the two forms of section D. That hypothesis is needed
nowhere else.

## ii. Key results

- `GaugeFieldData.LocalCovFieldAlgebra.Realization` : an algebra carrying the covariant
  towers, with the tower images `fieldStrength`, `fermion`, `conjFermion`, `boson`,
  `conjBoson` and their gauge and Lorentz laws.
- `GaugeFieldData.Realization.restrict` : restriction to the covariant field algebra, with
  `restrict_fieldStrength_eq_iteratedCovDerivAdjoint` and
  `restrict_fermion_eq_covDerivIter` identifying its towers.
- `GaugeFieldData.Realization.repJet_restrict_toAlgHom` and
  `GaugeFieldData.LocalCovFieldAlgebra.Realization.map_repJet` : the factorization through
  evaluation under `GaugeFieldData.PureJetsActTrivially`.

## iii. Table of contents

- A. Realizations
- B. The covariant towers of a realization
- C. Restriction from the local field algebra
- D. Factorization through evaluation

-/

@[expose] public section

set_option linter.unusedSectionVars false

open TensorProduct Matrix MatrixGroups Lorentz
open GaugeAlgebraRealization (repDualCoeff)

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets}

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`, as a complex scalar.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => (((SL2C.toLorentzGroup Λ).1 b a : ℝ) : ℂ)

namespace LocalCovFieldAlgebra

/-!

## A. Realizations

-/

/-- A complex algebra `B` carrying the covariant expressions of the datum `T`: a complex
  algebra map out of the covariant field algebra, equivariant for the ordinary gauge group
  and the Lorentz group, both acting on the whole of `B` by algebra endomorphisms. The
  Lorentz action of the source needs `GaugeFieldData.GaugeLorentzCompatible`, which is a
  parameter; no other species condition is used. It is built from the fields `toAlgHom`,
  `map_fst`, `map_snd`, `fst_mul`, `snd_mul` of `Representation.EquivariantAlgHom`, which
  the lemmas `map_repValue`, `map_repLorentz`, `repGauge_mul` and `repLorentz_mul` name. -/
abbrev Realization (T : GaugeFieldData jets) (hGL : T.GaugeLorentzCompatible) (B : Type)
    [Semiring B] [Algebra ℂ B] (repGauge : Representation ℂ G₀ B)
    (repLorentz : Representation ℂ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (repValue T) repGauge (repLorentzGroup T hGL) repLorentz

namespace Realization

variable {B : Type} [Semiring B] [Algebra ℂ B] {repGauge : Representation ℂ G₀ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} {hGL : T.GaugeLorentzCompatible}

variable (T hGL) in
/-- The covariant field algebra realized in itself, by the identity. -/
noncomputable def id : Realization T hGL (↥T.LocalCovFieldAlgebra) (repValue T)
    (repLorentzGroup T hGL) :=
  Representation.EquivariantAlgHom.id _ _ repValue_apply_mul (repLorentzGroup_apply_mul hGL)

@[simp]
lemma id_toAlgHom : (id T hGL).toAlgHom = AlgHom.id ℂ ↥T.LocalCovFieldAlgebra := rfl

variable (k : Realization T hGL B repGauge repLorentz)

/-- The map is equivariant for the ordinary gauge group. -/
lemma map_repValue (g : G₀) (x : ↥T.LocalCovFieldAlgebra) :
    k.toAlgHom (repValue T g x) = repGauge g (k.toAlgHom x) :=
  k.map_fst g x

/-- The map is equivariant for the Lorentz group. -/
lemma map_repLorentz (Λ : SL(2,ℂ)) (x : ↥T.LocalCovFieldAlgebra) :
    k.toAlgHom (repLorentzGroup T hGL Λ x) = repLorentz Λ (k.toAlgHom x) :=
  k.map_snd Λ x

include k in
/-- The ordinary gauge group acts on the whole of `B` by algebra endomorphisms. -/
lemma repGauge_mul (g : G₀) (b₁ b₂ : B) :
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂ :=
  k.fst_mul g b₁ b₂

include k in
/-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
lemma repLorentz_mul (Λ : SL(2,ℂ)) (b₁ b₂ : B) :
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ :=
  k.snd_mul Λ b₁ b₂

/-!

## B. The covariant towers of a realization

-/

/-- The realized field-strength tower `∇_l F_μν^φ`. -/
noncomputable def fieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) : B :=
  k.toAlgHom.toLinearMap (covFieldStrength T l μ ν φ)

/-- The realized covariant tower `∇_l ψ^φ` of a fermionic species. -/
noncomputable def fermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ covFermion T i l

/-- The realized conjugate covariant tower of a fermionic species. -/
noncomputable def conjFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ covConjFermion T i l

/-- The realized covariant tower of a bosonic species. -/
noncomputable def boson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ covBoson T j l

/-- The realized conjugate covariant tower of a bosonic species. -/
noncomputable def conjBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ covConjBoson T j l

lemma fermion_apply (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    k.fermion i l φ = k.toAlgHom (covFermion T i l φ) := rfl

lemma conjFermion_apply (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    k.conjFermion i l φ = k.toAlgHom (covConjFermion T i l φ) := rfl

lemma boson_apply (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    k.boson j l φ = k.toAlgHom (covBoson T j l φ) := rfl

lemma conjBoson_apply (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    k.conjBoson j l φ = k.toAlgHom (covConjBoson T j l φ) := rfl

@[simp]
lemma id_fermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    (id T hGL).fermion i l = covFermion T i l := rfl

@[simp]
lemma id_fieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    (id T hGL).fieldStrength l μ ν = covFieldStrength T l μ ν := rfl

/-- Two realizations with the same five towers are equal. This is uniqueness only: the
  covariant field algebra is not free on its towers, so an assignment of the tower images
  does not by itself define a realization. -/
lemma ext_towers {k₁ k₂ : Realization T hGL B repGauge repLorentz}
    (hF : ∀ (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤),
      k₁.fieldStrength l μ ν φ = k₂.fieldStrength l μ ν φ)
    (hψ : ∀ (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (T.FermionValue i)), k₁.fermion i l φ = k₂.fermion i l φ)
    (hψc : ∀ (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))),
      k₁.conjFermion i l φ = k₂.conjFermion i l φ)
    (hφ : ∀ (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (T.BosonValue j)), k₁.boson j l φ = k₂.boson j l φ)
    (hφc : ∀ (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))),
      k₁.conjBoson j l φ = k₂.conjBoson j l φ) : k₁ = k₂ :=
  Representation.EquivariantAlgHom.ext (algHom_ext_towers hF hψ hψc hφ hφc)

/-- The gauge law of the realized field-strength tower: the adjoint index rotates through
  the dual adjoint action of the inverse. -/
lemma gauge_fieldStrength (g : G₀) (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repGauge g (k.fieldStrength l μ ν φ)
      = k.fieldStrength l μ ν ((jets.adjointValue g⁻¹).dualMap φ) := by
  have key : repGauge g (k.fieldStrength l μ ν φ)
      = k.toAlgHom.toLinearMap (repValue T g (covFieldStrength T l μ ν φ)) :=
    (k.map_repValue g _).symm
  rw [key, repValue_covFieldStrength]
  rfl

/-- The gauge law of a realized matter tower: the value index rotates through the zeroth
  dual Taylor coefficient of the inverse constant jet. -/
lemma gauge_fermion (g : G₀) (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    repGauge g (k.fermion i l φ)
      = k.fermion i l (repDualCoeff (T.fermion i).repJet (jets.ofConstant g)⁻¹ 0 φ) :=
  (k.map_repValue g (covFermion T i l φ)).symm.trans
    (congrArg k.toAlgHom (repJet_covFermion (jets.ofConstant g) i l φ))

lemma gauge_conjFermion (g : G₀) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    repGauge g (k.conjFermion i l φ) = k.conjFermion i l
      (repDualCoeff (JetComponentSpace.repConj (T.fermion i).repJet)
        (jets.ofConstant g)⁻¹ 0 φ) :=
  (k.map_repValue g (covConjFermion T i l φ)).symm.trans
    (congrArg k.toAlgHom (repJet_covConjFermion (jets.ofConstant g) i l φ))

lemma gauge_boson (g : G₀) (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    repGauge g (k.boson j l φ)
      = k.boson j l (repDualCoeff (T.boson j).repJet (jets.ofConstant g)⁻¹ 0 φ) :=
  (k.map_repValue g (covBoson T j l φ)).symm.trans
    (congrArg k.toAlgHom (repJet_covBoson (jets.ofConstant g) j l φ))

lemma gauge_conjBoson (g : G₀) (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    repGauge g (k.conjBoson j l φ) = k.conjBoson j l
      (repDualCoeff (JetComponentSpace.repConj (T.boson j).repJet)
        (jets.ofConstant g)⁻¹ 0 φ) :=
  (k.map_repValue g (covConjBoson T j l φ)).symm.trans
    (congrArg k.toAlgHom (repJet_covConjBoson (jets.ofConstant g) j l φ))

/-- The Lorentz law of the realized field-strength tower: every covariant slot and both
  covector indices mix by the columns of the Lorentz matrix. -/
lemma lorentz_fieldStrength (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repLorentz Λ (k.fieldStrength (List.ofFn l) μ ν φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ a, L[Λ] (p a) (l a)) •
          ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • k.fieldStrength (List.ofFn p) a b φ := by
  have key : repLorentz Λ (k.fieldStrength (List.ofFn l) μ ν φ)
      = k.toAlgHom.toLinearMap
        (repLorentzGroup T hGL Λ (covFieldStrength T (List.ofFn l) μ ν φ)) :=
    (k.map_repLorentz Λ _).symm
  rw [key, repLorentzGroup_covFieldStrength hGL, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun b _ => map_smul _ _ _)

/-- The Lorentz law of a realized matter tower: every covariant slot mixes by the columns of
  the Lorentz matrix and the value index transforms contragrediently. -/
lemma lorentz_fermion (Λ : SL(2,ℂ)) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    repLorentz Λ (k.fermion i l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ a, L[Λ] (p a) (l a)) •
          k.fermion i p ((T.fermion i).repLorentz.dual Λ φ) := by
  have key : repLorentz Λ (k.fermion i l φ) = k.toAlgHom.toLinearMap
      (repLorentzGroup T hGL Λ (covFermion T i l φ)) := (k.map_repLorentz Λ _).symm
  rw [key, repLorentzGroup_covFermion hGL, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

lemma lorentz_conjFermion (Λ : SL(2,ℂ)) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    repLorentz Λ (k.conjFermion i l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ a, L[Λ] (p a) (l a)) •
          k.conjFermion i p ((T.fermion i).repLorentz.conj.dual Λ φ) := by
  have key : repLorentz Λ (k.conjFermion i l φ) = k.toAlgHom.toLinearMap
      (repLorentzGroup T hGL Λ (covConjFermion T i l φ)) := (k.map_repLorentz Λ _).symm
  rw [key, repLorentzGroup_covConjFermion hGL, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

lemma lorentz_boson (Λ : SL(2,ℂ)) (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    repLorentz Λ (k.boson j l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ a, L[Λ] (p a) (l a)) •
          k.boson j p ((T.boson j).repLorentz.dual Λ φ) := by
  have key : repLorentz Λ (k.boson j l φ) = k.toAlgHom.toLinearMap
      (repLorentzGroup T hGL Λ (covBoson T j l φ)) := (k.map_repLorentz Λ _).symm
  rw [key, repLorentzGroup_covBoson hGL, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

lemma lorentz_conjBoson (Λ : SL(2,ℂ)) (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    repLorentz Λ (k.conjBoson j l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ a, L[Λ] (p a) (l a)) •
          k.conjBoson j p ((T.boson j).repLorentz.conj.dual Λ φ) := by
  have key : repLorentz Λ (k.conjBoson j l φ) = k.toAlgHom.toLinearMap
      (repLorentzGroup T hGL Λ (covConjBoson T j l φ)) := (k.map_repLorentz Λ _).symm
  rw [key, repLorentzGroup_covConjBoson hGL, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

end Realization

end LocalCovFieldAlgebra

/-!

## C. Restriction from the local field algebra

-/

namespace Realization

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ GJ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} (h : Realization T B repJet repLorentz)
  (hGL : T.GaugeLorentzCompatible)

/-- The restriction of a realization of the local field algebra to the covariant field
  algebra, along the inclusion; the ordinary gauge group acts on the target through the
  constant jets. No species condition beyond `hGL` is used. -/
noncomputable def restrict :
    LocalCovFieldAlgebra.Realization T hGL B (repJet.comp jets.ofConstant) repLorentz :=
  (h.restrictSubalgebra T.LocalCovFieldAlgebra
    (fun U _ hx => LocalCovFieldAlgebra.repJet_mem U hx)
    (fun Λ _ hx => LocalCovFieldAlgebra.repLorentzGroup_mem hGL Λ hx)).compFst jets.ofConstant

lemma restrict_toAlgHom : (h.restrict hGL).toAlgHom = h.toAlgHom.comp T.LocalCovFieldAlgebra.val :=
  rfl

@[simp]
lemma restrict_toAlgHom_apply (x : ↥T.LocalCovFieldAlgebra) :
    (h.restrict hGL).toAlgHom x = h.toAlgHom x := rfl

lemma restrict_id_toAlgHom :
    ((id T).restrict hGL).toAlgHom = T.LocalCovFieldAlgebra.val :=
  AlgHom.ext fun _ => rfl

lemma restrict_fieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    (h.restrict hGL).fieldStrength l μ ν φ = h.toAlgHom (T.covDerivFieldStrength l μ ν φ) :=
  rfl

lemma restrict_fermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    (h.restrict hGL).fermion i l φ = h.toAlgHom (T.covDerivFermion i l φ) := rfl

lemma restrict_conjFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    (h.restrict hGL).conjFermion i l φ = h.toAlgHom (T.covDerivConjFermion i l φ) := rfl

lemma restrict_boson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    (h.restrict hGL).boson j l φ = h.toAlgHom (T.covDerivBoson j l φ) := rfl

lemma restrict_conjBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    (h.restrict hGL).conjBoson j l φ = h.toAlgHom (T.covDerivConjBoson j l φ) := rfl

/-- The field-strength tower of a restriction is the covariant tower of the realized
  gauge-boson symbols. -/
lemma restrict_fieldStrength_eq_iteratedCovDerivAdjoint (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (h.restrict hGL).fieldStrength l μ ν φ
      = GaugeAlgebraRealization.iteratedCovDerivAdjoint h.gaugeRealization.A l
        (GaugeAlgebraRealization.fieldStrength h.gaugeRealization.A μ ν) 0 φ :=
  h.toAlgHom_covDerivFieldStrength l μ ν φ

/-- A matter tower of a restriction is the covariant tower of the realized symbols of the
  species, computed against the realized gauge-boson symbols. -/
lemma restrict_fermion_eq_covDerivIter (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    (h.restrict hGL).fermion i l φ
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A (T.fermion i).repAlgebra
        (h.fermionSymbol i) n l 0 φ :=
  h.toAlgHom_covDerivFermion i l φ

lemma restrict_conjFermion_eq_covDerivIter (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    (h.restrict hGL).conjFermion i l φ
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A
        (LocalGaugeData.actionConj (T.fermion i).repAlgebra) (h.conjFermionSymbol i) n l 0 φ :=
  h.toAlgHom_covDerivConjFermion i l φ

lemma restrict_boson_eq_covDerivIter (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    (h.restrict hGL).boson j l φ
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A (T.boson j).repAlgebra
        (h.bosonSymbol j) n l 0 φ :=
  h.toAlgHom_covDerivBoson j l φ

lemma restrict_conjBoson_eq_covDerivIter (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    (h.restrict hGL).conjBoson j l φ
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A
        (LocalGaugeData.actionConj (T.boson j).repAlgebra) (h.conjBosonSymbol j) n l 0 φ :=
  h.toAlgHom_covDerivConjBoson j l φ

/-- Full jet equivariance survives restriction, with no species condition. -/
lemma restrict_map_repJet (U : GJ) (x : ↥T.LocalCovFieldAlgebra) :
    (h.restrict hGL).toAlgHom (LocalCovFieldAlgebra.repJet T U x)
      = repJet U ((h.restrict hGL).toAlgHom x) :=
  h.map_repJet U x

/-!

## D. Factorization through evaluation

-/

/-- Under `GaugeFieldData.PureJetsActTrivially`, a jet acts on the realized covariant image
  as the constant jet of its value; nothing is assumed about the jet action elsewhere in
  `B`. -/
lemma repJet_restrict_toAlgHom (hP : T.PureJetsActTrivially) (U : GJ)
    (x : ↥T.LocalCovFieldAlgebra) :
    repJet U ((h.restrict hGL).toAlgHom x)
      = repJet (jets.ofConstant (jets.eval U)) ((h.restrict hGL).toAlgHom x) := by
  rw [restrict_toAlgHom_apply, ← h.map_repJet U (x : T.LocalFieldAlgebra),
    ← h.map_repJet (jets.ofConstant (jets.eval U)) (x : T.LocalFieldAlgebra)]
  exact congrArg h.toAlgHom (congrArg (fun y : ↥T.LocalCovFieldAlgebra =>
    (y : T.LocalFieldAlgebra)) (LocalCovFieldAlgebra.repJet_eq_repValue_eval hP U x))

end Realization

namespace LocalCovFieldAlgebra.Realization

variable {B : Type} [Semiring B] [Algebra ℂ B] {repGauge : Representation ℂ G₀ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} {hGL : T.GaugeLorentzCompatible}

/-- Under `GaugeFieldData.PureJetsActTrivially`, a covariant realization intertwines the
  source jet action with the target action of the ordinary gauge group at the value of the
  jet. -/
lemma map_repJet (k : Realization T hGL B repGauge repLorentz) (hP : T.PureJetsActTrivially)
    (U : GJ) (x : ↥T.LocalCovFieldAlgebra) :
    k.toAlgHom (repJet T U x) = repGauge (jets.eval U) (k.toAlgHom x) := by
  rw [repJet_eq_repValue_eval hP, k.map_repValue]

end LocalCovFieldAlgebra.Realization

end GaugeFieldData
