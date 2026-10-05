/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeCovFieldAlgebra.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.Realization
/-!
# Realizations of the covariant field algebra

## i. Overview

A real algebra `B` carries the covariant gauge-boson tower when the covariant field algebra
maps into it by a real algebra map equivariant for the ordinary gauge group `G₀` (acting on
the source by `repValue`) and for the Lorentz group, both acting on `B` by algebra
endomorphisms: `LocalGaugeCovFieldAlgebra.Realization`. The gauge compatibility is with `G₀`
alone because the jet action on the covariant field algebra factors through evaluation.

The covariant field algebra is not free on its generators, so a realization is its algebra
map and not an assignment of the generators; generation gives uniqueness only
(`Realization.ext_F`). A realization of the local gauge field algebra restricts to one of
the covariant field algebra (`LocalGaugeFieldAlgebra.Realization.restrict`), with `G₀`
acting on the target through the constant jets. The converse extension is not claimed.

## ii. Key results

- `LocalGaugeCovFieldAlgebra.Realization` : an algebra carrying the covariant tower.
- `LocalGaugeCovFieldAlgebra.Realization.F` : the covariant tower of a realization, with the
  laws `gauge_F` and `lorentz_F` and the extensionality `ext_F`.
- `LocalGaugeFieldAlgebra.Realization.restrict` : restriction to the covariant field
  algebra, with `restrict_F_eq_iteratedCovDerivAdjoint` identifying its tower.

## iii. Table of contents

- A. Realizations
- B. The covariant tower of a realization
- C. Restriction from the local gauge field algebra

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

open TensorProduct Matrix MatrixGroups Lorentz
open LocalGaugeFieldAlgebra (fieldStrength covDerivFieldStrength)

namespace LocalGaugeCovFieldAlgebra

/-!

## A. Realizations

-/

/-- A real algebra `B` carrying the covariant gauge-boson tower of the package `jets`: a
  real algebra map out of the covariant field algebra, equivariant for the ordinary gauge
  group and the Lorentz group, both acting on the whole of `B` by algebra endomorphisms. It
  is built from the fields `toAlgHom`, `map_fst`, `map_snd`, `fst_mul`, `snd_mul` of
  `Representation.EquivariantAlgHom`, which the lemmas `map_repValue`, `map_repLorentz`,
  `repGauge_mul` and `repLorentz_mul` name. -/
abbrev Realization (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) (B : Type) [Ring B] [Algebra ℝ B]
    (repGauge : Representation ℝ G₀ B) (repLorentz : Representation ℝ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (repValue jets) repGauge (repLorentzGroup 𝔤) repLorentz

namespace Realization

variable {B : Type} [Ring B] [Algebra ℝ B] {repGauge : Representation ℝ G₀ B}
  {repLorentz : Representation ℝ SL(2,ℂ) B}

variable (jets) in
/-- The covariant field algebra realized in itself, by the identity. -/
noncomputable def id : Realization jets (LocalGaugeCovFieldAlgebra 𝔤) (repValue jets)
    (repLorentzGroup 𝔤) :=
  Representation.EquivariantAlgHom.id _ _ repValue_apply_mul repLorentzGroup_apply_mul

@[simp]
lemma id_toAlgHom : (id jets).toAlgHom = AlgHom.id ℝ (LocalGaugeCovFieldAlgebra 𝔤) := rfl

variable (k : Realization jets B repGauge repLorentz)

/-- The map is equivariant for the ordinary gauge group. -/
lemma map_repValue (g : G₀) (x : LocalGaugeCovFieldAlgebra 𝔤) :
    k.toAlgHom (repValue jets g x) = repGauge g (k.toAlgHom x) :=
  k.map_fst g x

/-- The map is equivariant for the Lorentz group. -/
lemma map_repLorentz (Λ : SL(2,ℂ)) (x : LocalGaugeCovFieldAlgebra 𝔤) :
    k.toAlgHom (repLorentzGroup 𝔤 Λ x) = repLorentz Λ (k.toAlgHom x) :=
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

## B. The covariant tower of a realization

-/

/-- The covariant tower `∇_l F_μν^φ` of a realization: the images of the generators of the
  covariant field algebra. -/
noncomputable def F (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  k.toAlgHom.toLinearMap ∘ₗ covF 𝔤 l μ ν

lemma F_apply (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    k.F l μ ν φ = k.toAlgHom (covF 𝔤 l μ ν φ) := rfl

@[simp]
lemma id_F : (id jets).F = covF 𝔤 := rfl

lemma F_nil (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    k.F [] μ ν φ = k.toAlgHom ⟨fieldStrength 𝔤 μ ν φ, fieldStrength_mem μ ν φ⟩ := rfl

lemma commute_F (l l' : List (Fin 1 ⊕ Fin 3)) (μ ν μ' ν' : Fin 1 ⊕ Fin 3)
    (φ ψ : Module.Dual ℝ 𝔤) : Commute (k.F l μ ν φ) (k.F l' μ' ν' ψ) :=
  (Commute.all _ _).map k.toAlgHom

/-- Two realizations with the same covariant tower are equal. This is uniqueness only: a
  tower in `B` need not come from a realization. -/
lemma ext_F {k₁ k₂ : Realization jets B repGauge repLorentz}
    (hF : ∀ (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤),
      k₁.F l μ ν φ = k₂.F l μ ν φ) : k₁ = k₂ :=
  Representation.EquivariantAlgHom.ext (algHom_ext hF)

/-- The gauge law of the covariant tower: the adjoint index rotates through the dual
  adjoint action of the inverse. -/
lemma gauge_F (g : G₀) (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repGauge g (k.F l μ ν φ) = k.F l μ ν ((jets.adjointValue g⁻¹).dualMap φ) := by
  rw [F_apply, ← k.map_repValue, repValue_covF]
  rfl

/-- The Lorentz law of the covariant tower: every covariant slot and both covector indices
  mix by the columns of the Lorentz matrix. -/
lemma lorentz_F (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repLorentz Λ (k.F (List.ofFn l) μ ν φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, ((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ)) •
          ∑ a, ((SL2C.toLorentzGroup Λ).1 a μ : ℝ) • ∑ b, ((SL2C.toLorentzGroup Λ).1 b ν : ℝ) •
            k.F (List.ofFn p) a b φ := by
  rw [F_apply, ← k.map_repLorentz, repLorentzGroup_covF, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun b _ => map_smul k.toAlgHom _ _)

/-- A covariant realization intertwines the jet action with the `G₀` action at the value
  of the jet. -/
lemma map_repJet (U : GJ) (x : LocalGaugeCovFieldAlgebra 𝔤) :
    k.toAlgHom (repJet jets U x) = repGauge (jets.eval U) (k.toAlgHom x) := by
  rw [repJet_eq_repValue_eval, k.map_repValue]

end Realization

end LocalGaugeCovFieldAlgebra

/-!

## C. Restriction from the local gauge field algebra

-/

namespace LocalGaugeFieldAlgebra.Realization

variable {B : Type} [Ring B] [Algebra ℝ B] {repJet : Representation ℝ GJ B}
  {repLorentz : Representation ℝ SL(2,ℂ) B} (h : Realization jets B repJet repLorentz)

/-- The restriction of a realization of the local gauge field algebra to the covariant
  field algebra, along the inclusion; the ordinary gauge group acts on the target as the
  constant jets. -/
noncomputable def restrict :
    LocalGaugeCovFieldAlgebra.Realization jets B (repJet.comp jets.ofConstant) repLorentz :=
  (h.restrictSubalgebra (LocalGaugeCovFieldAlgebra 𝔤)
    (fun U _ hx => LocalGaugeCovFieldAlgebra.repJet_mem U hx)
    (fun Λ _ hx => LocalGaugeCovFieldAlgebra.repLorentzGroup_mem Λ hx)).compFst jets.ofConstant

@[simp]
lemma restrict_toAlgHom_apply (x : LocalGaugeCovFieldAlgebra 𝔤) :
    h.restrict.toAlgHom x = h.toAlgHom x := rfl

lemma restrict_id_toAlgHom :
    (id jets).restrict.toAlgHom = (LocalGaugeCovFieldAlgebra 𝔤).val :=
  AlgHom.ext fun _ => rfl

lemma restrict_F (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    h.restrict.F l μ ν φ = h.toAlgHom (covDerivFieldStrength 𝔤 l μ ν φ) := rfl

/-- The covariant tower of a restriction is the covariant tower of the symbols of `B`. -/
lemma restrict_F_eq_iteratedCovDerivAdjoint (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    h.restrict.F l μ ν φ = GaugeAlgebraRealization.iteratedCovDerivAdjoint h.A l
      (GaugeAlgebraRealization.fieldStrength h.A μ ν) 0 φ :=
  h.toAlgHom_covDerivFieldStrength l μ ν φ

lemma restrict_F_nil (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    h.restrict.F [] μ ν φ = GaugeAlgebraRealization.fieldStrength h.A μ ν 0 φ :=
  h.toAlgHom_fieldStrength μ ν φ

lemma restrict_map_repJet (U : GJ) (x : LocalGaugeCovFieldAlgebra 𝔤) :
    h.restrict.toAlgHom (LocalGaugeCovFieldAlgebra.repJet jets U x)
      = repJet U (h.restrict.toAlgHom x) :=
  h.map_repJet U x

/-- On the image of the covariant field algebra a jet acts as the constant jet of its
  value; nothing is assumed about the jet action elsewhere in `B`. -/
lemma repJet_restrict_toAlgHom (U : GJ) (x : LocalGaugeCovFieldAlgebra 𝔤) :
    repJet U (h.restrict.toAlgHom x)
      = repJet (jets.ofConstant (jets.eval U)) (h.restrict.toAlgHom x) := by
  rw [← restrict_map_repJet, h.restrict.map_repJet]
  rfl

end LocalGaugeFieldAlgebra.Realization
