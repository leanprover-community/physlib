/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying two `su(3)` fundamental indices

A quark carries one fundamental colour index, and a product of two quark fields carries two.
There is no colour singlet in `3 ⊗ 3 = 6 ⊕ 3̄`: a colour singlet needs three quarks, or a
quark and an antiquark, never two quarks. This file proves that fact in the form the
Standard Model files consume, modulo a colour-stable submodule.

`IsSU3BiFundamental B repGauge T` records the hypothesis: `T` is a family indexed by two
fundamental colour indices and valued in a module `B` carrying a representation of the gauge
group, and a colour rotation `U ∈ SU(3)` moves its components by one factor of `U` per
index. Nothing is asked of the isospin and hypercharge factors.

The proof is triality. The scalar matrix `ω • 1`, with `ω` a primitive cube root of unity,
lies in `SU(3)` because `ω ^ 3 = 1` is exactly the determinant condition, and it scales a
tensor with `k` fundamental indices by `ω ^ k`. An invariant tensor therefore needs `3 ∣ k`,
and `k = 2` fails: the centre alone scales every component of `T` by `ω ^ 2`, so a colour
invariant of the span equals `ω ^ 2` times itself and vanishes.

Section A gives the transformation law and the span, section B the centre and the
vanishing of the invariants of the span, and section C the form modulo a stable submodule.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The transformation law and the span of the components

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with two
  fundamental indices: one factor of `U` per index. -/
def IsSU3BiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (∏ i : Fin 2, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(3)` fundamental indices, transforms
  as a tensor `T^{a b}` under the colour factor of the gauge group. Nothing is asked of the
  isospin and hypercharge factors. -/
structure IsSU3BiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3BiFundamentalMat g (repGauge (g, 1, 1)) T

namespace IsSU3BiFundamental

/- `span` takes the hypothesis `hT` only to hang off it by dot notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 3) → B}

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU3BiFundamental B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- A vector lies in the span precisely when it is a linear combination of the
  components. -/
lemma mem_span_iff (hT : IsSU3BiFundamental B repGauge T) (x : B) :
    x ∈ hT.span ↔ ∃ c : (Fin 2 → Fin 3) → ℂ, x = ∑ d, c d • T d :=
  Family.mem_iSup_span_singleton_iff T x

/-!

## B. The centre of `SU(3)` forbids an invariant

-/

/-- The primitive cube root of unity has modulus one. -/
lemma su3Omega_mul_star : su3Omega * star su3Omega = 1 := by
  have hnorm : ‖su3Omega‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one su3Omega_pow_three (by norm_num)
  rw [show star su3Omega = (starRingEnd ℂ) su3Omega from rfl, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, hnorm]

/-- The generator `ω • 1` of the centre `ℤ₃` of `SU(3)`: the determinant condition on a
  scalar matrix in three dimensions is exactly `ω ^ 3 = 1`. -/
noncomputable def su3Centre : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal fun _ => su3Omega, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      simp only [Pi.star_apply, su3Omega_mul_star, Matrix.diagonal_one]
    · rw [Matrix.det_diagonal]
      simp⟩

/-- The central element is `ω` times the identity. -/
lemma su3Centre_apply (a b : Fin 3) :
    (su3Centre : specialUnitaryGroup (Fin 3) ℂ).1 a b = if a = b then su3Omega else 0 := by
  simp [su3Centre, Matrix.diagonal_apply]

/-- A map moving the components by the central element scales every one of them by
  `ω ^ 2`, one factor of `ω` for each index. -/
lemma map_su3Centre {f : B →ₗ[ℂ] B} (hf : IsSU3BiFundamentalMat su3Centre f T)
    (l : Fin 2 → Fin 3) : f (T l) = su3Omega ^ 2 • T l := by
  rw [hf l, Finset.sum_eq_single l]
  · rw [Fin.prod_univ_two, su3Centre_apply, su3Centre_apply, if_pos rfl, if_pos rfl, sq]
  · intro a _ hal
    have h : a 0 ≠ l 0 ∨ a 1 ≠ l 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hal (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rw [Fin.prod_univ_two, su3Centre_apply, su3Centre_apply]
    rcases h with h | h
    · rw [if_neg h, zero_mul, zero_smul]
    · rw [if_neg h, mul_zero, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- An invariant of the span of a family obeying the law for a family of linear maps
  `φ U` is zero: the centre scales the whole span by `ω ^ 2 ≠ 1`. -/
theorem eq_zero_of_invariant' {φ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B}
    (hT : ∀ U, IsSU3BiFundamentalMat U (φ U) T) {x : B} (hx : x ∈ ⨆ d, ℂ ∙ T d)
    (hinv : ∀ U, φ U x = x) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Family.mem_iSup_span_singleton_iff T x).1 hx
  have hscale : φ su3Centre (∑ d, c d • T d) = su3Omega ^ 2 • ∑ d, c d • T d := by
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [map_smul, map_su3Centre (hT su3Centre) d, smul_comm]
  have hne : su3Omega ^ 2 - 1 ≠ 0 :=
    sub_ne_zero.2 (su3Omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have h0 : (su3Omega ^ 2 - 1) • ∑ d, c d • T d = 0 := by
    rw [sub_smul, one_smul, ← hscale, hinv, sub_self]
  have h := congrArg (fun y => (su3Omega ^ 2 - 1)⁻¹ • y) h0
  simp only [smul_zero, inv_smul_smul₀ hne] at h
  exact h

/-- A colour invariant in the span of the components is zero: there is no colour singlet
  in `3 ⊗ 3`. -/
theorem eq_zero_of_su3_invariant (hT : IsSU3BiFundamental B repGauge T) {x : B}
    (hx : x ∈ hT.span)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) : x = 0 :=
  eq_zero_of_invariant' hT.repGauge_T hx hinv

/-!

## C. The invariants modulo a stable submodule

The law descends to the quotient by a colour-stable submodule `S`, section B applies there,
and `Family.exists_smul_add_of_mem_sup` lifts the result back: an invariant of the span
joined with `S` lies in `S`, two fundamental colour indices contributing nothing.

-/

/-- The law descends to the quotient by a submodule stable under the map. -/
lemma isSU3BiFundamentalMat_mapQ {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3BiFundamentalMat U f T) (S : Submodule ℂ B) (hS : ∀ y ∈ S, f y ∈ S) :
    IsSU3BiFundamentalMat U (S.mapQ S f hS) fun l => S.mkQ (T l) := by
  intro l
  dsimp only
  rw [← LinearMap.comp_apply, Submodule.mapQ_mkQ, LinearMap.comp_apply, hf l, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- A colour invariant of the span of the components joined with a colour-stable submodule
  `S` lies in `S`. -/
theorem mem_of_mem_span_sup_su3_invariant (hT : IsSU3BiFundamental B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    x ∈ S := by
  obtain ⟨c, y, hyS, hxy, -⟩ := Family.exists_smul_add_of_mem_sup T
    (fun U => repGauge (U, 1, 1)) S hS 0 (fun U => map_zero _)
    (fun x hx hinv => ⟨0, by
      rw [eq_zero_of_invariant'
        (fun U => isSU3BiFundamentalMat_mapQ (hT.repGauge_T U) S (hS U)) hx hinv, zero_smul]⟩)
    hx hinv
  rwa [hxy, smul_zero, zero_add]

/-- The colour invariants of the span of the components joined with a colour-stable
  submodule are exactly the colour invariants of the submodule. -/
theorem mem_span_sup_su3_invariant_iff (hT : IsSU3BiFundamental B repGauge T) (x : B)
    (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S) :
    (x ∈ hT.span ⊔ S ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x)
      ↔ x ∈ S ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x :=
  ⟨fun ⟨hx, hinv⟩ => ⟨hT.mem_of_mem_span_sup_su3_invariant x S hS hx hinv, hinv⟩,
    fun ⟨hx, hinv⟩ => ⟨Submodule.mem_sup_right hx, hinv⟩⟩

end IsSU3BiFundamental

end StandardModel
