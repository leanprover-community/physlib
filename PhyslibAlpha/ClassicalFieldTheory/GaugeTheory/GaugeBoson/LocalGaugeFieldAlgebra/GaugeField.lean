/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.LorentzAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.AdjointFamily.GaugeLaw
/-!
# The gauge-field symbols of the jet algebra and their laws

The derivative symbols `∂_s A_μ^φ` of the complexified gauge-boson jet algebra, with their
Lorentz and gauge laws.

## i. Overview

The derivative symbols `∂_s A_μ^φ` of the complexified gauge-boson jet algebra are packaged as
a family over the derivative multiset, the spacetime index and the dual of the gauge
algebra, `LocalGaugeFieldAlgebra.gaugeField`. They satisfy two transformation laws. In the
Lorentz law the symbol carries one covector index and each derivative slot transforms as a
covector. In the gauge law a jet acts by the Leibniz convolution of its adjoint Taylor
coefficients plus the Maurer–Cartan shift.

An algebra map `f` out of the complexified jet algebra carries the symbols into any complex
algebra `B`, as `mapGaugeField f`. When `f` intertwines the gauge and Lorentz actions, the
carried symbols satisfy the same two laws, `GaugeBoson.TransformsAsGaugeField` and
`GaugeBoson.LorentzTransformsAsGaugeField`, and they commute with each other whatever `B` is
(`commute_mapGaugeField`). This is how the gauge fields of the local field algebra of a field
datum, and of any realization of it, inherit their laws, and with them every consequence
proved in the directory `PhyslibAlpha/ClassicalFieldTheory/GaugeTheory/GaugeBoson/AdjointFamily`.
The identity of the jet algebra is the case `transformsAsGaugeField_gaugeField`.

## ii. Key results

- `LocalGaugeFieldAlgebra.gaugeField` : the gauge-field symbols of the jet algebra.
- `LocalGaugeFieldAlgebra.repLorentz_gaugeField` : the Lorentz law.
- `LocalGaugeFieldAlgebra.repJet_gaugeField` : the gauge law.
- `LocalGaugeFieldAlgebra.mapGaugeField` : the symbols carried into another algebra.
- `LocalGaugeFieldAlgebra.transformsAsGaugeField_mapGaugeField`,
  `LocalGaugeFieldAlgebra.lorentzTransformsAsGaugeField_mapGaugeField` : the two laws along an
  equivariant algebra map.

## iii. Table of contents

- A. The gauge-field symbols and their laws
- B. The gauge-field symbols along an algebra map

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

/-!

## A. The gauge-field symbols and their laws

-/

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}

open TensorProduct Matrix MatrixGroups Lorentz

namespace LocalGaugeFieldAlgebra

variable (G) in
/-- The gauge-field derivative symbols of the complexified gauge-boson jet algebra, as a
  family over the derivative multiset, the spacetime index and the dual of the gauge
  algebra, the form consumed by the abstract covariance machinery. -/
noncomputable def gaugeField (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G) :=
  (Lorentz.iteratedD (complexJetDeriv G) complexJetDeriv_comm s).restrictScalars ℝ ∘ₗ
    (TensorProduct.mk ℝ ℂ (LocalGaugeFieldAlgebra G) 1).comp ((ofA G) μ)

@[simp]
lemma gaugeField_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    (gaugeField G) s μ φ = Lorentz.iteratedD (complexJetDeriv G) complexJetDeriv_comm s
      ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) μ φ) := rfl

/-- The Lorentz law of the jet algebra. The symbol `∂_s A_μ^φ` carries one covector index,
  and each derivative slot transforms as a covector, by `IsLorentzDeriv`. -/
lemma repLorentz_gaugeField (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (complexRepLorentzGroup G) Λ (gaugeField G (List.ofFn l) μ φ) =
      ∑ (p : Fin n → (Fin 1 ⊕ Fin 3)),
        (∏ (i : Fin n), (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        gaugeField G (List.ofFn p) a φ := by
  calc (complexRepLorentzGroup G) Λ ((gaugeField G) (List.ofFn l) μ φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
          (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
          Lorentz.iteratedD (complexJetDeriv G) complexJetDeriv_comm (List.ofFn p)
            ((complexRepLorentzGroup G) Λ ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) μ φ)) :=
        Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn complexJetDeriv_comm Λ l
          ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) μ φ)
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [complexRepLorentzGroup_one_tmul_ofA, map_sum]
        refine congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun a _ => ?_)
        rw [map_smul]
        rfl

variable (G) in
/-- The gauge law of the jet algebra. A jet `U` acts on `∂_s A_μ^φ` by the Leibniz
  convolution of the dual adjoint Taylor coefficients of `U⁻¹` against lower symbols, plus
  the base-point value of the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
lemma repJet_gaugeField (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    complexRepJet G U (gaugeField G s μ φ) =
      (s.antidiagonal.map fun p => gaugeField G p.2 μ (G.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + algebraMap ℂ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G)
          (φ (G.evalLie (G.iteratedDerivJ s
            (-G.maurerCartan U⁻¹ μ)))) :=
  complexRepJet_iteratedD_one_tmul_ofA U s μ φ

variable (G) in
/-- The symbols of the jet algebra transform as a gauge field. -/
lemma transformsAsGaugeField_gaugeField :
    GaugeBoson.TransformsAsGaugeField G (complexRepJet G) (gaugeField G) :=
  repJet_gaugeField G

/-!

## B. The gauge-field symbols along an algebra map

-/

section Map

variable {B : Type} [Ring B] [Algebra ℂ B]

/-- The gauge-field symbols `∂_s A_μ^φ` carried into a complex algebra `B` by an algebra map
  out of the complexified gauge-boson jet algebra. -/
noncomputable def mapGaugeField (f : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G →ₐ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] B :=
  f.toLinearMap.restrictScalars ℝ ∘ₗ gaugeField G s μ

@[simp]
lemma mapGaugeField_apply (f : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G →ₐ[ℂ] B)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    mapGaugeField f s μ φ = f (gaugeField G s μ φ) := rfl

/-- The carried gauge-field symbols commute with each other, being images of a commutative
  algebra. -/
lemma commute_mapGaugeField (f : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G →ₐ[ℂ] B)
    (p q : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ ψ : Module.Dual ℝ G.lieSubalgebra) :
    Commute (mapGaugeField f p μ φ) (mapGaugeField f q ν ψ) := by
  rw [mapGaugeField_apply, mapGaugeField_apply]
  exact (Commute.all _ _).map f

variable {repGauge : Representation ℂ G.gaugeJetGroup B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The gauge law along an algebra map intertwining the gauge actions. A jet `U` acts on the
  carried symbol `∂_s A_μ^φ` by the Leibniz convolution of the dual adjoint Taylor coefficients
  of `U⁻¹` against lower symbols, plus the base-point value of the `s`-th derivative of the
  Maurer–Cartan form of `U⁻¹`. -/
lemma transformsAsGaugeField_mapGaugeField (f : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G →ₐ[ℂ] B)
    (hf : ∀ (U : G.gaugeJetGroup) (x : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G),
      f (complexRepJet G U x) = repGauge U (f x)) :
    GaugeBoson.TransformsAsGaugeField G repGauge (mapGaugeField f) := by
  intro U s μ φ
  have key := congrArg f (repJet_gaugeField G U s μ φ)
  rw [hf] at key
  simp only [mapGaugeField_apply]
  refine key.trans ?_
  rw [map_add, map_multiset_sum, Multiset.map_map, AlgHom.commutes]
  rfl

/-- The Lorentz law along an algebra map intertwining the Lorentz actions. The carried symbol
  carries one covector index, and each derivative slot transforms as a covector. -/
lemma lorentzTransformsAsGaugeField_mapGaugeField (f : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G →ₐ[ℂ] B)
    (hf : ∀ (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G),
      f (complexRepLorentzGroup G Λ x) = repLorentz Λ (f x)) :
    GaugeBoson.LorentzTransformsAsGaugeField repLorentz (mapGaugeField f) := by
  intro Λ n l μ φ
  have key := congrArg f (repLorentz_gaugeField (G := G) Λ l μ φ)
  rw [hf] at key
  simp only [mapGaugeField_apply]
  refine key.trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul f _ _)

end Map

end LocalGaugeFieldAlgebra
