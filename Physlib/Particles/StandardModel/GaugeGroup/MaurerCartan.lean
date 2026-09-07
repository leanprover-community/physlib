/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms of the jet gauge group

The Maurer-Cartan form is a map
`ω : JetGaugeGroupI → (Fin 1 ⊕ Fin 3) → JetLieAlgebra`
defined as `ω_μ(U) := i (∂_μ U) U†`.

We will use `ω^a_ν` to denote the `a`-th component of the Maurer–Cartan form in the
basis of the jet Lie algebra, and `f^a_{b c}` to denote the structure constants of the
jet Lie algebra in that basis.

It satisfies the following properties:
- *Cocycle law*: `ω_μ(UV) = ω_μ(U) + U ω_μ(V) U†`
- *Value on the identity*: `ω_μ(1) = 0`
- *Value on constant gauge transformations*: `ω_μ(U₀) = 0`
- *Value on the inverse*: `ω_μ(U⁻¹) = -U⁻¹ ω_μ(U) U`
- *Structural equation*: `∂_μ ω^a_ν(U) − ∂_ν ω^a_μ(U) = ∑_{b c} f^a_{b c} · ω^b_μ(U) · ω^c_ν(U)`

-/

@[expose] public section
namespace StandardModel
open MvPowerSeries



/-!
# THis file is OLD!!!!!!!!!!!


!!!!!!!!!!!!!

## The Maurer–Cartan forms of the jet gauge group

-/




/-- The `U(1)` Maurer–Cartan form of a jet of gauge transformations in the
  direction `ν`: the series `i (∂_ν u) ū` for `u` the hypercharge factor of the
  jet. -/
noncomputable def maurerCartanU1 (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) : JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) * (pderiv ℂ ν (g.2.2 : JetRing) * star (g.2.2 : JetRing))

/-- The `SU(3)` Maurer–Cartan form of a jet of gauge transformations in the
  direction `ν`: the matrix-valued series `i (∂_ν U) U†` for `U` the colour factor
  of the jet, with the formal partial derivative applied entrywise and `star` the
  conjugate transpose. -/
noncomputable def maurerCartanSU3 (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    Matrix (Fin 3) (Fin 3) JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) •
    ((g.1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ ν) *
      star (g.1 : Matrix (Fin 3) (Fin 3) JetRing))

/-- The `SU(2)` Maurer–Cartan form of a jet of gauge transformations in the
  direction `ν`: the matrix-valued series `i (∂_ν U) U†` for `U` the weak factor
  of the jet, with the formal partial derivative applied entrywise and `star` the
  conjugate transpose. -/
noncomputable def maurerCartanSU2 (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    Matrix (Fin 2) (Fin 2) JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) •
    ((g.2.1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ ν) *
      star (g.2.1 : Matrix (Fin 2) (Fin 2) JetRing))

/-!

### Basic properties of the Maurer–Cartan forms

-/

@[simp]
lemma maurerCartanU1_one (ν : Fin 1 ⊕ Fin 3) : maurerCartanU1 1 ν = 0 := by
  simp [maurerCartanU1, star_one]

@[simp]
lemma maurerCartanSU3_one (ν : Fin 1 ⊕ Fin 3) : maurerCartanSU3 1 ν = 0 := by
  ext i j
  simp [maurerCartanSU3, Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]

@[simp]
lemma maurerCartanSU2_one (ν : Fin 1 ⊕ Fin 3) : maurerCartanSU2 1 ν = 0 := by
  ext i j
  simp [maurerCartanSU2, Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]

lemma maurerCartanU1_mul (g1 g2 : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1 (g1 * g2) ν = maurerCartanU1 g1 ν + maurerCartanU1 g2 ν := by
  have hcoe : ((g1 * g2).2.2 : JetRing) = (g1.2.2 : JetRing) * (g2.2.2 : JetRing) := rfl
  have h1 : (g1.2.2 : JetRing) * star (g1.2.2 : JetRing) = 1 :=
    (Unitary.mem_iff.mp g1.2.2.2).2
  have h2 : (g2.2.2 : JetRing) * star (g2.2.2 : JetRing) = 1 :=
    (Unitary.mem_iff.mp g2.2.2.2).2
  rw [maurerCartanU1, maurerCartanU1, maurerCartanU1, hcoe, Derivation.leibniz, star_mul']
  simp only [smul_eq_mul]
  linear_combination ((MvPowerSeries.C Complex.I : JetRing) *
      pderiv ℂ ν (g2.2.2 : JetRing) * star (g2.2.2 : JetRing)) * h1 +
    ((MvPowerSeries.C Complex.I : JetRing) *
      pderiv ℂ ν (g1.2.2 : JetRing) * star (g1.2.2 : JetRing)) * h2

/-- The cocycle law of the `SU(3)` Maurer–Cartan form: it is additive only up to
  conjugating the second factor's form by the first factor,
  `mc(UV) = mc(U) + U mc(V) U†`. -/
lemma maurerCartanSU3_mul (g1 g2 : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanSU3 (g1 * g2) ν =
      maurerCartanSU3 g1 ν +
        (g1.1 : Matrix (Fin 3) (Fin 3) JetRing) * maurerCartanSU3 g2 ν *
          star (g1.1 : Matrix (Fin 3) (Fin 3) JetRing) := by
  have hcoe : ((g1 * g2).1 : Matrix (Fin 3) (Fin 3) JetRing) =
      (g1.1 : Matrix (Fin 3) (Fin 3) JetRing) * (g2.1 : Matrix (Fin 3) (Fin 3) JetRing) := rfl
  rw [maurerCartanSU3, maurerCartanSU3, maurerCartanSU3, hcoe]
  set U : Matrix (Fin 3) (Fin 3) JetRing := (g1.1 : Matrix (Fin 3) (Fin 3) JetRing)
  set V : Matrix (Fin 3) (Fin 3) JetRing := (g2.1 : Matrix (Fin 3) (Fin 3) JetRing)
  have hV : V * star V = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp g2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hleib : (U * V).map (pderiv ℂ ν) =
      U.map (pderiv ℂ ν) * V + U * V.map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  rw [hleib, star_mul, Matrix.add_mul, smul_add]
  congr 1
  · rw [mul_assoc, ← mul_assoc V, hV, one_mul]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_assoc, ← mul_assoc (V.map (pderiv ℂ ν)), ← mul_assoc U]

lemma maurerCartanSU2_mul (g1 g2 : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanSU2 (g1 * g2) ν =
      maurerCartanSU2 g1 ν + (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing) * maurerCartanSU2 g2 ν *
        star (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing) := by
  have hcoe : ((g1 * g2).2.1 : Matrix (Fin 2) (Fin 2) JetRing) =
      (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing) * (g2.2.1 : Matrix (Fin 2) (Fin 2) JetRing) := rfl
  rw [maurerCartanSU2, maurerCartanSU2, maurerCartanSU2, hcoe]
  set U : Matrix (Fin 2) (Fin 2) JetRing := (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing)
  set V : Matrix (Fin 2) (Fin 2) JetRing := (g2.2.1 : Matrix (Fin 2) (Fin 2) JetRing)
  have hV : V * star V = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp g2.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hleib : (U * V).map (pderiv ℂ ν) =
      U.map (pderiv ℂ ν) * V + U * V.map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  rw [hleib, star_mul, Matrix.add_mul, smul_add]
  congr 1
  · rw [mul_assoc, ← mul_assoc V, hV, one_mul]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_assoc, ← mul_assoc (V.map (pderiv ℂ ν)), ← mul_assoc U]

/-- The `U(1)` Maurer–Cartan form of the inverse jet is the negative: the
  abelian cocycle identity applied to `g g⁻¹ = 1`. -/
lemma maurerCartanU1_inv (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1 g⁻¹ ν = -maurerCartanU1 g ν := by
  have h := maurerCartanU1_mul g g⁻¹ ν
  rw [mul_inv_cancel, maurerCartanU1_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The Maurer–Cartan form vanishes on jets of constant gauge transformations:
  constants have vanishing derivative. -/
@[simp]
lemma maurerCartanU1_ofConstant (g : GaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1 (JetGaugeGroupI.ofConstant g) ν = 0 := by
  rw [maurerCartanU1,
    show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) =
      MvPowerSeries.C ((g.2.2 : ℂ)) from rfl,
    pderiv_C, zero_mul, mul_zero]

/-- The `SU(3)` Maurer–Cartan form vanishes on jets of constant gauge
  transformations: constants have vanishing derivative. -/
@[simp]
lemma maurerCartanSU3_ofConstant (g : GaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanSU3 (JetGaugeGroupI.ofConstant g) ν = 0 := by
  have hmap : ((JetGaugeGroupI.ofConstant g).1 : Matrix (Fin 3) (Fin 3) JetRing).map
      (pderiv ℂ ν) = 0 := by
    ext i j
    rw [Matrix.map_apply,
      show ((JetGaugeGroupI.ofConstant g).1 : Matrix (Fin 3) (Fin 3) JetRing) i j =
        MvPowerSeries.C ((g.1 : Matrix (Fin 3) (Fin 3) ℂ) i j) from rfl,
      pderiv_C]
    rfl
  rw [maurerCartanSU3, hmap, zero_mul, smul_zero]

/-- The `SU(2)` Maurer–Cartan form vanishes on jets of constant gauge
  transformations: constants have vanishing derivative. -/
@[simp]
lemma maurerCartanSU2_ofConstant (g : GaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanSU2 (JetGaugeGroupI.ofConstant g) ν = 0 := by
  have hmap : ((JetGaugeGroupI.ofConstant g).2.1 : Matrix (Fin 2) (Fin 2) JetRing).map
      (pderiv ℂ ν) = 0 := by
    ext i j
    rw [Matrix.map_apply,
      show ((JetGaugeGroupI.ofConstant g).2.1 : Matrix (Fin 2) (Fin 2) JetRing) i j =
        MvPowerSeries.C ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i j) from rfl,
      pderiv_C]
    rfl
  rw [maurerCartanSU2, hmap, zero_mul, smul_zero]

/-- The Maurer–Cartan series is hermitian: `star (i (∂_ν u) ū) = i (∂_ν u) ū`,
  by differentiating the unitarity relation `u ū = 1`. All its Taylor
  coefficients are therefore real. -/
lemma star_maurerCartanU1 (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    star (maurerCartanU1 U ν) = maurerCartanU1 U ν := by
  have hu : (U.2.2 : JetRing) * star (U.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp U.2.2.2).2
  have h0 : pderiv ℂ ν ((U.2.2 : JetRing) * star (U.2.2 : JetRing)) = 0 := by
    rw [hu, pderiv_one]
  rw [Derivation.leibniz] at h0
  simp only [smul_eq_mul] at h0
  have hq : pderiv ℂ ν (star (U.2.2 : JetRing)) * (U.2.2 : JetRing) =
      -(pderiv ℂ ν (U.2.2 : JetRing) * star (U.2.2 : JetRing)) := by
    linear_combination h0
  rw [maurerCartanU1, star_mul', JetRing.star_C, star_mul', star_star, ← JetRing.pderiv_star, hq,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_mul, mul_neg, neg_neg]

/-- The `SU(3)` Maurer–Cartan form is hermitian: `(i (∂_ν U) U†)† = i (∂_ν U) U†`,
  by differentiating the unitarity relation `U U† = 1` entrywise. -/
lemma star_maurerCartanSU3 (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    star (maurerCartanSU3 U ν) = maurerCartanSU3 U ν := by
  rw [maurerCartanSU3]
  set A : Matrix (Fin 3) (Fin 3) JetRing := (U.1 : Matrix (Fin 3) (Fin 3) JetRing) with hA
  have hU : A * star A = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hone : (1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ ν) = 0 := by
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]
  have hleib : (A * star A).map (pderiv ℂ ν) =
      A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have h0 : A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) = 0 := by
    rw [← hleib, hU, hone]
  have hq : A * ((star A).map (pderiv ℂ ν)) = -(A.map (pderiv ℂ ν) * star A) :=
    eq_neg_of_add_eq_zero_right h0
  have hstarmap : star (A.map (pderiv ℂ ν)) = (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.star_apply, Matrix.map_apply]
    exact (JetRing.pderiv_star ν (A j i)).symm
  rw [star_smul, star_mul, star_star, hstarmap, hq, JetRing.star_C,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_smul, smul_neg, neg_neg]

/-- The `SU(2)` Maurer–Cartan form is hermitian; see `star_maurerCartanSU3`. -/
lemma star_maurerCartanSU2 (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    star (maurerCartanSU2 U ν) = maurerCartanSU2 U ν := by
  rw [maurerCartanSU2]
  set A : Matrix (Fin 2) (Fin 2) JetRing := (U.2.1 : Matrix (Fin 2) (Fin 2) JetRing) with hA
  have hU : A * star A = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hone : (1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ ν) = 0 := by
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]
  have hleib : (A * star A).map (pderiv ℂ ν) =
      A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have h0 : A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) = 0 := by
    rw [← hleib, hU, hone]
  have hq : A * ((star A).map (pderiv ℂ ν)) = -(A.map (pderiv ℂ ν) * star A) :=
    eq_neg_of_add_eq_zero_right h0
  have hstarmap : star (A.map (pderiv ℂ ν)) = (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.star_apply, Matrix.map_apply]
    exact (JetRing.pderiv_star ν (A j i)).symm
  rw [star_smul, star_mul, star_star, hstarmap, hq, JetRing.star_C,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_smul, smul_neg, neg_neg]

/-!

### Derivatives of the Maurer–Cartan forms

-/

lemma pderiv_maurerCartanU1_symm (u : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ (maurerCartanU1 u ν) = pderiv ℂ ν (maurerCartanU1 u μ) := by
  have hu : (u.2.2 : JetRing) * star (u.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp u.2.2.2).2
  have hu' : star (u.2.2 : JetRing) * (u.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp u.2.2.2).1
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, pderiv ℂ ρ (star (u.2.2 : JetRing)) =
      -(star (u.2.2 : JetRing) * pderiv ℂ ρ (u.2.2 : JetRing) * star (u.2.2 : JetRing)) := by
    intro ρ
    have h0 : pderiv ℂ ρ ((u.2.2 : JetRing) * star (u.2.2 : JetRing)) = 0 := by
      rw [hu, pderiv_one]
    rw [Derivation.leibniz] at h0
    simp only [smul_eq_mul] at h0
    linear_combination star (u.2.2 : JetRing) * h0 -
      (pderiv ℂ ρ (star (u.2.2 : JetRing))) * hu'
  simp only [maurerCartanU1, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero]
  rw [hstar μ, hstar ν, JetRing.pderiv_comm μ ν]
  ring

/-- The Maurer–Cartan structure equation for the `SU(3)` form: the antisymmetrized
  derivative is the commutator, `∂_μ mc_ν - ∂_ν mc_μ = -i [mc_μ, mc_ν]`, here
  stated additively. In the abelian `U(1)` case the commutator vanishes and this
  reduces to `pderiv_maurerCartanU1_symm`. -/
lemma pderiv_maurerCartanSU3_symm (u : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    (maurerCartanSU3 u ν).map (pderiv ℂ μ) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU3 u μ * maurerCartanSU3 u ν) =
      (maurerCartanSU3 u μ).map (pderiv ℂ ν) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU3 u ν * maurerCartanSU3 u μ) := by
  simp only [maurerCartanSU3]
  set U : Matrix (Fin 3) (Fin 3) JetRing := (u.1 : Matrix (Fin 3) (Fin 3) JetRing)
  have hU : U * star U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hU' : star U * U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h
  have hone : ∀ ρ : Fin 1 ⊕ Fin 3,
      (1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ ρ) = 0 := by
    intro ρ
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)]
  have hleib : ∀ (ρ : Fin 1 ⊕ Fin 3) (A B : Matrix (Fin 3) (Fin 3) JetRing),
      (A * B).map (pderiv ℂ ρ) = A.map (pderiv ℂ ρ) * B + A * B.map (pderiv ℂ ρ) := by
    intro ρ A B
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, (star U).map (pderiv ℂ ρ) =
      -(star U * (U.map (pderiv ℂ ρ) * star U)) := by
    intro ρ
    have h0 : U.map (pderiv ℂ ρ) * star U + U * (star U).map (pderiv ℂ ρ) = 0 := by
      rw [← hleib ρ U (star U), hU, hone]
    have h1 : star U * (U.map (pderiv ℂ ρ) * star U) +
        star U * (U * (star U).map (pderiv ℂ ρ)) = 0 := by
      rw [← Matrix.mul_add, h0, mul_zero]
    rw [show star U * (U * (star U).map (pderiv ℂ ρ)) =
        star U * U * (star U).map (pderiv ℂ ρ) from (mul_assoc _ _ _).symm, hU', one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hCsmul : ∀ (ρ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) JetRing),
      ((MvPowerSeries.C Complex.I : JetRing) • A).map (pderiv ℂ ρ) =
        (MvPowerSeries.C Complex.I : JetRing) • A.map (pderiv ℂ ρ) := by
    intro ρ A
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz,
      pderiv_C, mul_zero, add_zero]
  have hDcomm : (U.map (pderiv ℂ ν)).map (pderiv ℂ μ) =
      (U.map (pderiv ℂ μ)).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply]
    exact JetRing.pderiv_comm μ ν (U i j)
  have hI : (MvPowerSeries.C Complex.I : JetRing) * MvPowerSeries.C Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hprod : ∀ (X Y : Matrix (Fin 3) (Fin 3) JetRing),
      (MvPowerSeries.C Complex.I : JetRing) •
          (((MvPowerSeries.C Complex.I : JetRing) • X) *
            ((MvPowerSeries.C Complex.I : JetRing) • Y)) =
        -((MvPowerSeries.C Complex.I : JetRing) • (X * Y)) := by
    intro X Y
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, hI, neg_one_mul, neg_smul]
  rw [hCsmul μ, hCsmul ν, hleib μ (U.map (pderiv ℂ ν)) (star U),
    hleib ν (U.map (pderiv ℂ μ)) (star U), hstar μ, hstar ν, hDcomm, hprod, hprod]
  simp only [mul_neg, smul_add, smul_neg, mul_assoc]
  abel

/-- The Maurer–Cartan structure equation for the `SU(2)` form; see
  `pderiv_maurerCartanSU3_symm`. -/
lemma pderiv_maurerCartanSU2_symm (u : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    (maurerCartanSU2 u ν).map (pderiv ℂ μ) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU2 u μ * maurerCartanSU2 u ν) =
      (maurerCartanSU2 u μ).map (pderiv ℂ ν) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU2 u ν * maurerCartanSU2 u μ) := by
  simp only [maurerCartanSU2]
  set U : Matrix (Fin 2) (Fin 2) JetRing := (u.2.1 : Matrix (Fin 2) (Fin 2) JetRing)
  have hU : U * star U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hU' : star U * U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h
  have hone : ∀ ρ : Fin 1 ⊕ Fin 3,
      (1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ ρ) = 0 := by
    intro ρ
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)]
  have hleib : ∀ (ρ : Fin 1 ⊕ Fin 3) (A B : Matrix (Fin 2) (Fin 2) JetRing),
      (A * B).map (pderiv ℂ ρ) = A.map (pderiv ℂ ρ) * B + A * B.map (pderiv ℂ ρ) := by
    intro ρ A B
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, (star U).map (pderiv ℂ ρ) =
      -(star U * (U.map (pderiv ℂ ρ) * star U)) := by
    intro ρ
    have h0 : U.map (pderiv ℂ ρ) * star U + U * (star U).map (pderiv ℂ ρ) = 0 := by
      rw [← hleib ρ U (star U), hU, hone]
    have h1 : star U * (U.map (pderiv ℂ ρ) * star U) +
        star U * (U * (star U).map (pderiv ℂ ρ)) = 0 := by
      rw [← Matrix.mul_add, h0, mul_zero]
    rw [show star U * (U * (star U).map (pderiv ℂ ρ)) =
        star U * U * (star U).map (pderiv ℂ ρ) from (mul_assoc _ _ _).symm, hU', one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hCsmul : ∀ (ρ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 2) (Fin 2) JetRing),
      ((MvPowerSeries.C Complex.I : JetRing) • A).map (pderiv ℂ ρ) =
        (MvPowerSeries.C Complex.I : JetRing) • A.map (pderiv ℂ ρ) := by
    intro ρ A
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz,
      pderiv_C, mul_zero, add_zero]
  have hDcomm : (U.map (pderiv ℂ ν)).map (pderiv ℂ μ) =
      (U.map (pderiv ℂ μ)).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply]
    exact JetRing.pderiv_comm μ ν (U i j)
  have hI : (MvPowerSeries.C Complex.I : JetRing) * MvPowerSeries.C Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hprod : ∀ (X Y : Matrix (Fin 2) (Fin 2) JetRing),
      (MvPowerSeries.C Complex.I : JetRing) •
          (((MvPowerSeries.C Complex.I : JetRing) • X) *
            ((MvPowerSeries.C Complex.I : JetRing) • Y)) =
        -((MvPowerSeries.C Complex.I : JetRing) • (X * Y)) := by
    intro X Y
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, hI, neg_one_mul, neg_smul]
  rw [hCsmul μ, hCsmul ν, hleib μ (U.map (pderiv ℂ ν)) (star U),
    hleib ν (U.map (pderiv ℂ μ)) (star U), hstar μ, hstar ν, hDcomm, hprod, hprod]
  simp only [mul_neg, smul_add, smul_neg, mul_assoc]
  abel

/-!

## The coefficents of the Maurer–Cartan forms

-/

open JetRing

/-- The Taylor coefficients of the Maurer–Cartan series, as hermitian scalars. -/
noncomputable def maurerCartanU1Coeff (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) : selfAdjoint ℂ :=
  ⟨coeff m (maurerCartanU1 U ν), by
    rw [selfAdjoint.mem_iff, ← coeff_star, star_maurerCartanU1]⟩

@[simp]
lemma maurerCartanU1Coeff_one (ν : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    maurerCartanU1Coeff 1 ν m = 0 := by
  apply Subtype.ext
  simp [maurerCartanU1Coeff]

@[simp]
lemma maurerCartanU1Coeff_ofConstant (g : GaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    maurerCartanU1Coeff (JetGaugeGroupI.ofConstant g) ν m = 0 := by
  apply Subtype.ext
  simp [maurerCartanU1Coeff, maurerCartanU1_ofConstant]

/-- The Taylor coefficients of the Maurer–Cartan series are additive in the jet. -/
lemma maurerCartanU1Coeff_mul (U V : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    maurerCartanU1Coeff (U * V) ν m = maurerCartanU1Coeff U ν m + maurerCartanU1Coeff V ν m := by
  apply Subtype.ext
  simp [maurerCartanU1Coeff, maurerCartanU1_mul]

/-- The first-order Taylor coefficients of the Maurer–Cartan series are symmetric
  in the two spacetime directions: the shift of `∂_μ B_ν` equals the shift of
  `∂_ν B_μ`. This is the gauge invariance of the abelian field strength, and rests
  on unitarity: the antisymmetric part `∂_νu ∂_μū - ∂_μu ∂_νū` vanishes because
  `∂ū = -ū (∂u) ū`. -/
lemma maurerCartanU1Coeff_single_symm (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1Coeff U ν (Finsupp.single μ 1) = maurerCartanU1Coeff U μ (Finsupp.single ν 1) := by
  rcases eq_or_ne μ ν with rfl | hμν
  · rfl
  apply Subtype.ext
  show coeff (Finsupp.single μ 1) (maurerCartanU1 U ν) = coeff (Finsupp.single ν 1) (maurerCartanU1 U μ)
  have hb : constantCoeff (U.2.2 : JetRing) * star (constantCoeff (U.2.2 : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp U.2.2.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  have hμ := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp U.2.2.2).2
  rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
    show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at hμ
  have hν := congrArg (coeff (Finsupp.single ν 1)) (Unitary.mem_iff.mp U.2.2.2).2
  rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
    show coeff (Finsupp.single ν 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at hν
  have hσμ : star (coeff (Finsupp.single μ 1) (U.2.2 : JetRing)) =
      -(coeff (Finsupp.single μ 1) (U.2.2 : JetRing) * star (constantCoeff (U.2.2 : JetRing)) *
        star (constantCoeff (U.2.2 : JetRing))) := by
    linear_combination star (constantCoeff (U.2.2 : JetRing)) * hμ -
      star (coeff (Finsupp.single μ 1) (U.2.2 : JetRing)) * hb
  have hσν : star (coeff (Finsupp.single ν 1) (U.2.2 : JetRing)) =
      -(coeff (Finsupp.single ν 1) (U.2.2 : JetRing) * star (constantCoeff (U.2.2 : JetRing)) *
        star (constantCoeff (U.2.2 : JetRing))) := by
    linear_combination star (constantCoeff (U.2.2 : JetRing)) * hν -
      star (coeff (Finsupp.single ν 1) (U.2.2 : JetRing)) * hb
  rw [maurerCartanU1, maurerCartanU1,
    show ((C Complex.I : JetRing)) = algebraMap ℂ JetRing Complex.I from rfl,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    coeff_single_one_mul, coeff_single_one_mul, coeff_pderiv, coeff_pderiv,
    coeff_star, coeff_star, constantCoeff_star,
    show constantCoeff (pderiv ℂ ν (U.2.2 : JetRing)) =
      coeff (Finsupp.single ν (1 : ℕ)) (U.2.2 : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    show constantCoeff (pderiv ℂ μ (U.2.2 : JetRing)) =
      coeff (Finsupp.single μ (1 : ℕ)) (U.2.2 : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    show (Finsupp.single μ 1) ν = 0 from Finsupp.single_eq_of_ne hμν.symm,
    show (Finsupp.single ν 1) μ = 0 from Finsupp.single_eq_of_ne hμν,
    show Finsupp.single ν (1 : ℕ) + Finsupp.single μ 1 =
      Finsupp.single μ 1 + Finsupp.single ν 1 from add_comm _ _,
    hσμ, hσν]
  push_cast
  ring

/-- The weighted symmetry of the Maurer–Cartan Taylor coefficients: exchanging the
  field index with a derivative index changes the coefficient by the ratio of the
  corresponding multiplicities. -/
lemma maurerCartanU1Coeff_succ_symm (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    (m μ + 1) • maurerCartanU1Coeff U ν (m + Finsupp.single μ 1) =
      (m ν + 1) • maurerCartanU1Coeff U μ (m + Finsupp.single ν 1) := by
  have h := congrArg (coeff m) (pderiv_maurerCartanU1_symm U μ ν)
  rw [coeff_pderiv, coeff_pderiv] at h
  apply Subtype.ext
  show ((m μ + 1 : ℕ)) • coeff (m + Finsupp.single μ 1) (maurerCartanU1 U ν) =
    ((m ν + 1 : ℕ)) • coeff (m + Finsupp.single ν 1) (maurerCartanU1 U μ)
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linear_combination h


/-- The derivative of a hypercharge power of a `U(1)` jet:
  `∂_ν (u^q) = -q i mc_ν u^q`, the all-orders form of the first-order Taylor
  coefficient formula for the contragredient character. -/
lemma pderiv_pow_unitary (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) (q : ℕ) :
    pderiv ℂ ν ((U.2.2 : JetRing) ^ q) =
      MvPowerSeries.C (-(q : ℂ) * Complex.I) * (maurerCartanU1 U ν * (U.2.2 : JetRing) ^ q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : star (U.2.2 : JetRing) * (U.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp U.2.2.2).1
    have hpow : (U.2.2 : JetRing) ^ q = (U.2.2 : JetRing) * (U.2.2 : JetRing) ^ (q - 1) := by
      conv_lhs => rw [show q = 1 + (q - 1) by omega, pow_add, pow_one]
    have hC : (MvPowerSeries.C (-(q : ℂ) * Complex.I) : JetRing) *
        MvPowerSeries.C Complex.I = MvPowerSeries.C ((q : ℕ) : ℂ) := by
      rw [← map_mul]
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    have hN : (MvPowerSeries.C ((q : ℕ) : ℂ) : JetRing) = ((q : ℕ) : JetRing) :=
      map_natCast _ _
    rw [MvPowerSeries.pderiv_pow, maurerCartanU1, hpow]
    linear_combination
      (-((U.2.2 : JetRing) * (U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing) *
        star (U.2.2 : JetRing))) * hC +
      (-((U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing) *
        MvPowerSeries.C ((q : ℕ) : ℂ))) * h1 +
      (-((U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing))) * hN

/-- The derivative of a hypercharge power of the conjugate `U(1)` jet:
  `∂_ν (ū^q) = q i mc_ν ū^q`, the conjugate-contragredient counterpart of
  `pderiv_pow_unitary`. -/
lemma pderiv_pow_unitary_star (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) (q : ℕ) :
    pderiv ℂ ν (star (U.2.2 : JetRing) ^ q) =
      MvPowerSeries.C ((q : ℂ) * Complex.I) *
        (maurerCartanU1 U ν * star (U.2.2 : JetRing) ^ q) := by
  have h := pderiv_pow_unitary U⁻¹ ν q
  have hcoe : ((U⁻¹.2.2 : unitary JetRing) : JetRing) =
      star ((U.2.2 : unitary JetRing) : JetRing) := by
    rw [show (U⁻¹.2.2 : unitary JetRing) = (U.2.2)⁻¹ from rfl, ← Unitary.star_eq_inv,
      Unitary.coe_star]
  rw [hcoe, maurerCartanU1_inv, neg_mul, map_neg] at h
  linear_combination h
end StandardModel
