/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.Electromagnetism.ThreeDimension.Basic
public import Physlib.Electromagnetism.Dynamics.IsExtrema
/-!

# A. Maxwell's equations in three dimensions

Maxwell's equations relate electric and magnetic fields to electric charge and current. In three
spatial dimensions they can be written using the familiar divergence, curl, and time-derivative
operators of vector calculus.

## A.1. Main results

This module proves the four differential equations:

- `gaussLawElectric`, relating the divergence of the electric field to charge density;
- `gaussLawMagnetic`, stating that the magnetic field is divergence-free;
- `ampereLaw`, including both the electric current and displacement-current terms;
- `faradayLaw`, relating the curl of the electric field to the time derivative of the magnetic
  field.

## A.2. Relation to the covariant formulation

The electric and magnetic fields are obtained from an electromagnetic potential. Gauss's law for
the electric field and Ampère's law are derived from the covariant extremality condition
`IsExtrema`, while the two homogeneous equations follow from the potential definitions and
smoothness assumptions. The results therefore connect the tensorial backend to the standard
three-dimensional presentation.

## A.3. Current scope

The statements here are pointwise differential equations in free space. Integral formulations,
boundary conditions, and constitutive laws for material media are outside the current scope of this
module.

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Time
open Space
open ElectromagneticPotential
open ContDiff

variable {𝓕 : FreeSpace} (V : ElectromagneticPotential 3) (J₄ : LorentzCurrentDensity 3)

local notation "φ" => V.scalarPotential 𝓕.c
local notation "A" => V.vectorPotential 𝓕.c
local notation "E" => V.electricField 𝓕.c
local notation "B" => V.magneticField 𝓕.c
local notation "ρ" => J₄.chargeDensity 𝓕.c
local notation "J" => J₄.currentDensity 𝓕.c
local notation "ε₀" => 𝓕.ε₀
local notation "μ₀" => 𝓕.μ₀

/-- Gauss's law for the electric field. -/
theorem gaussLawElectric (t : Time) (x : Space)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
    (∇ ⬝ E t) x = ρ t x / ε₀ := by
  exact ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).1

/-- Gauss's law for the magnetic field. -/
theorem gaussLawMagnetic (t : Time) (x : Space) (hV : ContDiff ℝ ∞ V) :
    (∇ ⬝ B t) x = 0 := by
  rw [magneticField_eq_3D, div_of_curl_eq_zero _ (by fun_prop), Pi.zero_apply]

/-- Ampère's law. -/
theorem ampereLaw (t : Time) (x : Space)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
      (∇ ⨯ B t) x = μ₀ • J t x + μ₀ • ε₀ • ∂ₜ (fun t => E t x) t := by
  ext i
  have hdE := ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).2 i
  rw [← magneticField_curl_eq_magneticFieldMatrix _ (hV.of_le ENat.LEInfty.out)] at hdE
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ← mul_assoc, hdE, add_sub_cancel]

/-- Faraday's law. -/
theorem faradayLaw (t : Time) (x : Space) (hV : ContDiff ℝ ∞ V) :
    (∇ ⨯ E t) x = - ∂ₜ (fun t => B t x) t := by
  rw [electricField_eq_3D, magneticField_eq_3D, fun_curl_sub, fun_curl_neg,
    curl_of_grad_eq_zero, time_deriv_curl_commute]
  simp only [neg_zero, Pi.zero_apply, zero_sub]
  all_goals fun_prop

end ThreeDimension
end Electromagnetism
