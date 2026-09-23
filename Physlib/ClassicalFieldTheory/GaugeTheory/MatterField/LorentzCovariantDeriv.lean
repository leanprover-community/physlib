/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction
public import Physlib.Relativity.LorentzMix
/-!
# The Lorentz law of the covariant derivatives of a matter family

## i. Overview

The covariant derivative of a matter family adds one ordered derivative slot and the
correction `A_ρ · F`, the derived action `actionFamConv` of the gauge field on the value
index. Expanded in bases, the correction is a scalar combination of Leibniz convolutions of
gauge-field symbols against matter symbols, which gives its Lorentz law and its linearity
in the matter family; the contragredient twist `rep.dual Λ` of the value index passes
through it when the infinitesimal gauge action commutes with the Lorentz action on the
value space (`hcomm`), the one hypothesis on the species. These are the inputs of the
abstract induction `Lorentz.repLorentz_tower`, for any realization of the gauge bosons in
a complex algebra `B`.

## ii. Key results

- `GaugeAlgebraRealization.repLorentz_covDerivIter` : the Lorentz law of the iterated
  covariant derivative at every derivative multiset.
- `GaugeAlgebraRealization.isLorentzCovDerivTransforms_covDerivIter`, `..._conj` : the
  covariant tower of a matter family, and of a conjugate family, transforms as the
  covariant derivatives of a Lorentz-covariant field.

## iii. Table of contents

- A. Families in the multiset form of the Lorentz law
- B. The derived action family in bases
- C. The Lorentz law of the covariant tower

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct Lorentz

namespace GaugeAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
variable {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V}
variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ GJ B}
variable (h : GaugeAlgebraRealization jets B repGauge repLorentz)

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`, as a complex scalar.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => (((SL2C.toLorentzGroup Λ).1 b a : ℝ) : ℂ)

/-!

## A. Families in the multiset form of the Lorentz law

-/

/-- A scalar combination of convolutions against the gauge field is linear in the
  right-hand families. -/
lemma sum_derivConv_sum_fam {ι κ ι' : Type} [Fintype ι] [Fintype κ] [Fintype ι']
    (f : ι → Multiset (Fin 1 ⊕ Fin 3) → B) (coef : ι → κ → ℂ) (c : ι' → ℂ)
    (g : ι' → κ → Multiset (Fin 1 ⊕ Fin 3) → B) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    ∑ j, ∑ k, coef j k • derivConv (f j) (fun y => ∑ i, c i • g i k y) s =
      ∑ i, c i • ∑ j, ∑ k, coef j k • derivConv (f j) (g i k) s := by
  simp only [derivConv_sum_right, Finset.smul_sum, smul_smul, mul_comm]
  exact Finset.sum_comm_cycle

/-- A Lorentz law in the tuple form, read on the underlying multisets: the transformed
  family mixes by `lorentzMix`. -/
lemma repLorentz_eq_lorentzMix (Λ : SL(2,ℂ)) (f g : Multiset (Fin 1 ⊕ Fin 3) → B)
    (hfg : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)), repLorentz Λ (f (List.ofFn l)) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, L[Λ] (p i) (l i)) • g (List.ofFn p))
    (x : Multiset (Fin 1 ⊕ Fin 3)) : repLorentz Λ (f x) = lorentzMix Λ g x 0 := by
  obtain ⟨n, l, rfl⟩ : ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)), x = List.ofFn l :=
    ⟨_, x.toList.get, by rw [List.ofFn_get, Multiset.coe_toList]⟩
  rw [hfg n l, lorentzMix_ofFn]
  exact Finset.sum_congr rfl fun p _ => by rw [add_zero]

/-- The Lorentz law of the gauge-field symbols, in the multiset form. -/
lemma repLorentz_apply_mix (Λ : SL(2,ℂ))
    (x : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (χ : Module.Dual ℝ 𝔤) :
    repLorentz Λ (h.A x μ χ) = lorentzMix Λ (fun t => ∑ a, L[Λ] a μ • h.A t a χ) x 0 :=
  repLorentz_eq_lorentzMix Λ (fun x => h.A x μ χ) (fun t => ∑ a, L[Λ] a μ • h.A t a χ)
    (fun n l => h.lorentz_apply Λ n l μ χ) x

omit [FiniteDimensional ℂ V] in
/-- The Lorentz law of a family of derivative symbols, in the multiset form. -/
lemma isLorentzDerivTransforms_mix {rep : Representation ℂ SL(2,ℂ) V}
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : IsLorentzDerivTransforms repLorentz rep F) (Λ : SL(2,ℂ))
    (x : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ V) :
    repLorentz Λ (F x χ) = lorentzMix Λ (fun t => F t (rep.dual Λ χ)) x 0 :=
  repLorentz_eq_lorentzMix Λ (fun x => F x χ) (fun t => F t (rep.dual Λ χ))
    (fun n l => hF Λ n l χ) x

/-- The Lorentz law of a scalar combination of convolutions against the gauge field: the
  direction of the gauge field mixes by its own column, the derivative slots by
  `lorentzMix`, and the right-hand families are replaced by their transforms. -/
lemma repLorentz_sum_derivConv (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    {ι κ : Type} [Fintype ι] [Fintype κ] (bg : Module.Basis ι ℝ 𝔤) (coef : ι → κ → ℂ)
    (g g' : κ → Multiset (Fin 1 ⊕ Fin 3) → B)
    (hg : ∀ k y, repLorentz Λ (g k y) = lorentzMix Λ (g' k) y 0)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repLorentz Λ (∑ j, ∑ k, coef j k • derivConv (fun x => h.A x ρ (bg.coord j)) (g k) s) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ
        (fun t => ∑ j, ∑ k, coef j k • derivConv (fun x => h.A x a (bg.coord j)) (g' k) t)
        s 0 := by
  have h1 : ∀ j k, repLorentz Λ (derivConv (fun x => h.A x ρ (bg.coord j)) (g k) s) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ (derivConv (fun x => h.A x a (bg.coord j)) (g' k)) s 0 := by
    intro j k
    rw [repLorentz_derivConv h.repLorentz_mul Λ _
      (fun t => ∑ a, L[Λ] a ρ • h.A t a (bg.coord j)) _ (g' k)
      (fun x => repLorentz_apply_mix h Λ x ρ _) (hg k)]
    simp only [← lorentzMix_smul_fam, ← lorentzMix_sum_fam]
    exact congrArg (fun G => lorentzMix Λ G s 0) (funext fun r => derivConv_sum_left _ _ _ r)
  simp only [map_sum, map_smul, h1, lorentzMix_sum_fam, lorentzMix_smul_fam, Finset.smul_sum,
    smul_smul, mul_comm]
  exact Finset.sum_comm_cycle

/-!

## B. The derived action family in bases

-/

/-- The action of families expanded in bases of the gauge algebra and the value space. -/
lemma actionFam_apply_eq_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (bg : Module.Basis ι ℝ 𝔤) (bv : Module.Basis κ ℂ V)
    (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B)
    (φ : Module.Dual ℂ V) :
    actionFam act f g φ =
      ∑ j, ∑ k, φ (act (bg j) (bv k)) • (f (bg.coord j) * g (bv.coord k)) := by
  rw [actionFam, dualPairEquiv_symm_eq_sum bg f, dualPairEquivC_symm_eq_sum bv g]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul]
  rw [Finset.sum_comm]

/-- The derived action family expanded in bases. -/
lemma actionFamConv_eq_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (bg : Module.Basis ι ℝ 𝔤) (bv : Module.Basis κ ℂ V)
    (ρ : Fin 1 ⊕ Fin 3) (G : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    actionFamConv A act ρ G s φ = ∑ j, ∑ k, φ (act (bg j) (bv k)) •
      derivConv (fun x => A x ρ (bg.coord j)) (fun y => G y (bv.coord k)) s := by
  simp only [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_def,
    actionFam_apply_eq_sum bg bv, Multiset.sum_map_finsetSum, derivConv, Multiset.smul_sum]

/-- The derived action family is linear in the matter family. -/
lemma actionFamConv_sum_fam {ι : Type} [Fintype ι] (ρ : Fin 1 ⊕ Fin 3) (c : ι → ℂ)
    (H : ι → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    actionFamConv A act ρ (fun t => ∑ i, c i • H i t) s φ =
      ∑ i, c i • actionFamConv A act ρ (H i) s φ := by
  classical
  simp only [actionFamConv_eq_sum (Module.finBasis ℝ 𝔤) (Module.finBasis ℂ V),
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact sum_derivConv_sum_fam _ _ _ _ s

/-- The Lorentz law of the derived action family: the derivative slots mix, the direction
  of the gauge field mixes by its own column, and the value index is carried by the
  transformed matter family. -/
lemma repLorentz_actionFamConv (Λ : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (G G' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (hG : ∀ y χ, repLorentz Λ (G y χ) = lorentzMix Λ (fun t => G' t χ) y 0)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repLorentz Λ (actionFamConv h.A act ρ G s φ) =
      ∑ a, L[Λ] a ρ • lorentzMix Λ (fun t => actionFamConv h.A act a G' t φ) s 0 := by
  classical
  set bg := Module.finBasis ℝ 𝔤
  set bv := Module.finBasis ℂ V
  simp only [actionFamConv_eq_sum bg bv]
  exact repLorentz_sum_derivConv h Λ ρ bg (fun j k => φ (act (bg j) (bv k)))
    (fun k y => G y (bv.coord k)) (fun k t => G' t (bv.coord k)) (fun k y => hG y _) s

omit [FiniteDimensional ℂ V] [Module.Finite ℝ 𝔤] in
/-- The twist of the value index past the gauge action: an endomorphism commuting with
  the gauge action may be moved from the dual basis onto the dual vector. -/
lemma dual_twist {κ : Type} [Fintype κ] (bv : Module.Basis κ ℂ V) (T : V →ₗ[ℂ] V)
    (hT : ∀ (c : 𝔤) (v : V), act c (T v) = T (act c v))
    (ψ : Module.Dual ℂ V →ₗ[ℂ] B) (c : 𝔤) (φ : Module.Dual ℂ V) :
    ∑ k, φ (act c (bv k)) • ψ (T.dualMap (bv.coord k)) =
      ∑ k, (T.dualMap φ) (act c (bv k)) • ψ (bv.coord k) := by
  simp only [← map_smul, ← map_sum]
  rw [show (∑ k, φ (act c (bv k)) • bv.coord k) = φ ∘ₗ act c from
      bv.sum_dual_apply_smul_coord (φ ∘ₗ act c),
    show (∑ k, (T.dualMap φ) (act c (bv k)) • bv.coord k) = (T.dualMap φ) ∘ₗ act c from
      bv.sum_dual_apply_smul_coord ((T.dualMap φ) ∘ₗ act c)]
  exact congrArg ψ (LinearMap.ext fun v => congrArg φ (hT c v))

/-- The contragredient action may be pulled out of an action of families, provided the
  gauge action commutes with it on the value space. -/
lemma actionFam_comp_dual (T : V →ₗ[ℂ] V)
    (hT : ∀ (c : 𝔤) (v : V), act c (T v) = T (act c v))
    (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B)
    (φ : Module.Dual ℂ V) :
    actionFam act f (g ∘ₗ T.dualMap) φ = actionFam act f g (T.dualMap φ) := by
  classical
  simp only [actionFam_apply_eq_sum (Module.finBasis ℝ 𝔤) (Module.finBasis ℂ V),
    LinearMap.comp_apply, ← mul_smul_comm, ← Finset.mul_sum, dual_twist _ T hT g]

/-- The contragredient action may be pulled out of a derived action family. -/
lemma actionFamConv_comp_dual (T : V →ₗ[ℂ] V)
    (hT : ∀ (c : 𝔤) (v : V), act c (T v) = T (act c v)) (ρ : Fin 1 ⊕ Fin 3)
    (K : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    actionFamConv A act ρ (fun t => K t ∘ₗ T.dualMap) s φ =
      actionFamConv A act ρ K s (T.dualMap φ) := by
  simp only [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_def,
    actionFam_comp_dual T hT]

/-!

## C. The Lorentz law of the covariant tower

-/

/-- The Lorentz law of the iterated covariant derivative of a matter family: the ordered
  covariant slots mix by their own columns and the multiset of plain derivative slots
  mixes by `lorentzMix`, while the value index transforms contragrediently. -/
lemma repLorentz_covDerivIter {rep : Representation ℂ SL(2,ℂ) V}
    (hcomm : ∀ (c : 𝔤) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (hF : IsLorentzDerivTransforms repLorentz rep F) (Λ : SL(2,ℂ))
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    repLorentz Λ (covDerivIter h.A act F n l s φ) = ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
      (∏ i, L[Λ] (p i) (l i)) •
        lorentzMix Λ (fun t => covDerivIter h.A act F n p t (rep.dual Λ φ)) s 0 :=
  repLorentz_tower Λ (covDerivIter h.A act F) (covDerivIter h.A act F) (actionFamConv h.A act)
    (rep.dual Λ) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ s φ => isLorentzDerivTransforms_mix hF Λ s φ)
    (fun ρ G G' hG s φ => repLorentz_actionFamConv h Λ ρ G G' hG s φ)
    (fun ρ _ _ c G s φ => actionFamConv_sum_fam ρ c G s φ)
    (fun ρ G s φ => actionFamConv_comp_dual (rep Λ⁻¹) (fun c v => hcomm c Λ⁻¹ v) ρ G s φ)
    n l s φ

/-- The iterated covariant derivative of a matter family transforms as the covariant
  derivatives of a Lorentz-covariant field, given the Lorentz law of the bare symbols,
  the Lorentz law of the gauge field, and the commutation of the infinitesimal gauge
  action with the Lorentz action on the value space. -/
theorem isLorentzCovDerivTransforms_covDerivIter {rep : Representation ℂ SL(2,ℂ) V}
    (hcomm : ∀ (c : 𝔤) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B)
    (hF : IsLorentzDerivTransforms repLorentz rep F) :
    IsLorentzCovDerivTransforms repLorentz rep (fun {n} l => covDerivIter h.A act F n l 0) := by
  intro Λ n l φ
  rw [repLorentz_covDerivIter h hcomm F hF Λ n l 0 φ]
  simp only [lorentzMix_zero]

omit [FiniteDimensional ℂ V] [Module.Finite ℝ 𝔤] in
/-- Conjugation preserves the commutation of the gauge action with the Lorentz action:
  both are read on the conjugate module through the same underlying maps. -/
lemma actionConj_comm_repConj (rep : Representation ℂ SL(2,ℂ) V)
    (hcomm : ∀ (c : 𝔤) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (c : 𝔤) (Λ : SL(2,ℂ)) (v : ConjModule V) :
    LocalGaugeData.actionConj act c (rep.conj Λ v) =
      rep.conj Λ (LocalGaugeData.actionConj act c v) :=
  congrArg (conjEquiv (k := ℂ) (M := V)) (hcomm c Λ _)

/-- The Lorentz law of the covariant tower of a conjugate family, from the commutation of
  the gauge action with the Lorentz action of the unconjugated species. -/
theorem isLorentzCovDerivTransforms_covDerivIter_conj {rep : Representation ℂ SL(2,ℂ) V}
    (hcomm : ∀ (c : 𝔤) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule V) →ₗ[ℂ] B)
    (hF : IsLorentzDerivTransforms repLorentz rep.conj F) :
    IsLorentzCovDerivTransforms repLorentz rep.conj
      (fun {n} l => covDerivIter h.A (LocalGaugeData.actionConj act) F n l 0) :=
  isLorentzCovDerivTransforms_covDerivIter h (actionConj_comm_repConj rep hcomm) F hF

end GaugeAlgebraRealization
