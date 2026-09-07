/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.DownSinglet
public import Physlib.Particles.StandardModel.GaugeAlgebra.InfinitesimalAction
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!

# The infinitesimal gauge action on the down-type singlet

## i. Overview

The infinitesimal `(3, 1)_{-2}` action of the gauge algebra on the down-type singlet,
and the proof that it is the infinitesimal action underlying the jet gauge action
`DownSinglet.repJetGaugeGroupI`, in the sense of
`GaugeAlgebra.IsInfinitesimalActionOf`.

## ii. Key results

- `DownSinglet.gaugeAlgebraAction` : the infinitesimal `(3, 1)_{-2}` action.
- `DownSinglet.isInfinitesimalActionOf` : the action underlies the jet gauge action.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups

namespace DownSinglet

/-!

## The action of the gauge algebra

The infinitesimal `(3, 1)_{-2}` action of the gauge algebra on the down-type singlet:
the colour part of the algebra element acts on the colour index and the hypercharge
part scales, both through the physicists' factor of `i`, matching the group action
`(star u) ^ 2 • U₃` infinitesimally. The compatibility with the jet gauge action —
`GaugeAlgebra.IsInfinitesimalActionOf` — is proved at the end of this file.

-/

/-- The endomorphism of the down singlet defined by a `3 × 3` complex matrix acting on
  the colour index, with the Weyl factor untouched. -/
noncomputable def colourEnd (A : Matrix (Fin 3) (Fin 3) ℂ) :
    DownSinglet →ₗ[ℂ] DownSinglet :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
      (Matrix.toLpLinAlgEquiv 2 A) ∘ₗ valLinEquiv.toLinearMap

lemma colourEnd_apply_mk (A : Matrix (Fin 3) (Fin 3) ℂ) (v : DownSinglet) :
    colourEnd A v
      = valLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
            (Matrix.toLpLinAlgEquiv 2 A) (valLinEquiv v)) := rfl

lemma colourEnd_add (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (A + B) = colourEnd A + colourEnd B := by
  rw [colourEnd, colourEnd, colourEnd, map_add, map_add, LinearMap.add_comp,
    LinearMap.comp_add]

lemma colourEnd_smul (z : ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (z • A) = z • colourEnd A := by
  rw [colourEnd, colourEnd, map_smul, map_smul, LinearMap.smul_comp,
    LinearMap.comp_smul]

lemma colourEnd_zero : colourEnd 0 = 0 := by
  rw [colourEnd, map_zero, map_zero, LinearMap.zero_comp, LinearMap.comp_zero]

lemma colourEnd_neg (A : Matrix (Fin 3) (Fin 3) ℂ) : colourEnd (-A) = -colourEnd A := by
  rw [show (-A : Matrix (Fin 3) (Fin 3) ℂ) = (-1 : ℂ) • A from by rw [neg_one_smul],
    colourEnd_smul, neg_one_smul]

lemma colourEnd_multiset_sum (m : Multiset (Matrix (Fin 3) (Fin 3) ℂ)) :
    colourEnd m.sum = (m.map colourEnd).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [colourEnd_zero]
  | cons A t ih => rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      colourEnd_add, ih]

/-- The colour endomorphisms compose through matrix multiplication. -/
lemma colourEnd_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (A * B) = colourEnd A ∘ₗ colourEnd B := by
  refine LinearMap.ext fun v => ?_
  rw [colourEnd_apply_mk, map_mul, map_mul, LinearMap.comp_apply, colourEnd_apply_mk,
    colourEnd_apply_mk, LinearEquiv.apply_symm_apply]
  rfl

/-- The matrix of the infinitesimal `(3, 1)_{-2}` action of a gauge algebra element on
  the colour index: `i` times the colour part, shifted by `i` times `-2` the
  hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (c.toSU3Matrix - ((2 : ℂ) • c.toU1Value) • 1)

/-- **The infinitesimal action of the gauge algebra on the down-type singlet**: the
  derivative of the `(3, 1)_{-2}` action of the gauge group, real-linear in the
  algebra slot and complex-linear in the value slot — the form consumed by the
  covariant derivative `IsGaugeField.covDerivIter` and by
  `GaugeAlgebra.IsInfinitesimalActionOf`. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] DownSinglet →ₗ[ℂ] DownSinglet where
  toFun c := colourEnd (actionMatrix c)
  map_add' c₁ c₂ := by
    rw [show actionMatrix (c₁ + c₂) = actionMatrix c₁ + actionMatrix c₂ from by
      rw [actionMatrix, actionMatrix, actionMatrix, GaugeAlgebra.add_toSU3Matrix,
        GaugeAlgebra.add_toU1Value]
      module]
    rw [colourEnd_add]
  map_smul' r c := by
    rw [show actionMatrix (r • c) = (r : ℂ) • actionMatrix c from by
      rw [actionMatrix, actionMatrix, GaugeAlgebra.smul_toSU3Matrix,
        GaugeAlgebra.smul_toU1Value,
        show (r • c.toSU3Matrix : Matrix (Fin 3) (Fin 3) ℂ)
          = (r : ℂ) • c.toSU3Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU3Matrix]; rfl,
        show r • c.toU1Value = (r : ℂ) • c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value]; rfl]
      module,
      colourEnd_smul]
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply]
    show (r : ℂ) • colourEnd (actionMatrix c) v = r • colourEnd (actionMatrix c) v
    rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-!

## The infinitesimal action underlies the jet gauge action

The `(3, 1)_{-2}` action of the gauge algebra is the infinitesimal action underlying the
jet gauge action, in the sense of `GaugeAlgebra.IsInfinitesimalActionOf`: the base-point
Taylor coefficients of the jet action satisfy the Maurer–Cartan Leibniz law and
intertwine the action with the adjoint transports. The proofs work through the colour
matrix of the jet action and the all-orders matrix Leibniz rule at the base point.

-/

section InfinitesimalAction

open MvPowerSeries

/-- A single formal derivative commutes with the iterated one. -/
private lemma pderiv_foldl (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3))
    (f : JetRing) :
    pderiv ℂ μ (x.foldl (fun h ρ => pderiv ℂ ρ h) f)
      = x.foldl (fun h ρ => pderiv ℂ ρ h) (pderiv ℂ μ f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih =>
    rw [Multiset.foldl_cons, Multiset.foldl_cons, ih, JetRing.pderiv_comm]

/-- The iterated formal derivative is `ℂ`-homogeneous. -/
private lemma foldl_pderiv_smul (x : Multiset (Fin 1 ⊕ Fin 3)) (z : ℂ) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (z • f)
      = z • x.foldl (fun h ρ => pderiv ℂ ρ h) f := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, Derivation.map_smul, ih, Multiset.foldl_cons]

/-- The iterated formal derivative of a difference. -/
private lemma foldl_pderiv_sub (x : Multiset (Fin 1 ⊕ Fin 3)) (f g : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (f - g)
      = x.foldl (fun h ρ => pderiv ℂ ρ h) f - x.foldl (fun h ρ => pderiv ℂ ρ h) g := by
  induction x using Multiset.induction_on generalizing f g with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_sub, ih, Multiset.foldl_cons,
      Multiset.foldl_cons]

/-- The jet-valued matrix of the infinitesimal `(3, 1)_{-2}` action of a jet of gauge
  algebra elements: the jet analogue of `actionMatrix`. -/
noncomputable def jetActionMatrix (a : JetGaugeAlgebra) : Matrix (Fin 3) (Fin 3) JetRing :=
  Complex.I • (a.toSU3Matrix - ((2 : ℂ) • a.toU1Value) • 1)

/-- The base-point Taylor coefficients of the jet action matrix are the action matrices
  of the base-point Taylor coefficients. -/
lemma jetActionMatrix_map_cc_foldl (p : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    ((jetActionMatrix a).map fun f =>
        constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) f))
      = actionMatrix (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p a)) := by
  ext i j
  rw [Matrix.map_apply, jetActionMatrix, actionMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.smul_apply, foldl_pderiv_smul, constantCoeff_smul, foldl_pderiv_sub,
    map_sub, JetGaugeAlgebra.eval_iteratedDeriv_toSU3Matrix, Matrix.map_apply]
  congr 2
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, smul_eq_mul, mul_one, smul_eq_mul,
      mul_one, foldl_pderiv_smul, constantCoeff_smul,
      JetGaugeAlgebra.eval_iteratedDeriv_toU1Value]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, smul_zero, smul_zero,
      JetRing.foldl_pderiv_zero, map_zero]

/-- The `JetRing`-valued colour matrix of the jet gauge action on the down singlet: the
  colour matrix of the gauge jet carrying the `-2` hypercharge phase. -/
noncomputable def downMatrix (U : JetGaugeGroupI) : Matrix (Fin 3) (Fin 3) JetRing :=
  ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
    ((U.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)

lemma repJetGaugeGroupI_eq_downMatrix (U : JetGaugeGroupI)
    (z : JetRing ⊗[ℂ] DownSinglet) :
    repJetGaugeGroupI U z
      = jetValLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
            Fermion.RightHandedWeyl
            ((Matrix.toLpLinAlgEquiv 2 (downMatrix U)).restrictScalars ℂ)
            (jetValLinEquiv z)) := rfl

/-- The entrywise formal derivative on the colour coordinates, as a `ℂ`-linear map. -/
private noncomputable def pderivColour (μ : Fin 1 ⊕ Fin 3) :
    EuclideanSpace JetRing (Fin 3) →ₗ[ℂ] EuclideanSpace JetRing (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => pderiv ℂ μ (v.ofLp i)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact map_add _ _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact Derivation.map_smul _ _ _

/-- The entrywise iterated formal derivative on the colour coordinates. -/
private noncomputable def foldColour (x : Multiset (Fin 1 ⊕ Fin 3)) :
    EuclideanSpace JetRing (Fin 3) →ₗ[ℂ] EuclideanSpace JetRing (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => x.foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp i)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact JetRing.foldl_pderiv_add x _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact foldl_pderiv_smul x z _

/-- The entrywise base-point evaluation on the colour coordinates. -/
private noncomputable def ccColour :
    EuclideanSpace JetRing (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => constantCoeff (v.ofLp i)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact map_add _ _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact constantCoeff_smul _ _

private lemma pderivColour_comp_foldColour (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    pderivColour μ ∘ₗ foldColour x = foldColour (μ ::ₘ x) := by
  refine LinearMap.ext fun v => ?_
  refine WithLp.ofLp_injective 2 ?_
  funext i
  show pderiv ℂ μ (x.foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp i))
    = (μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp i)
  rw [Multiset.foldl_cons, pderiv_foldl]

/-- The identification of down-singlet jets intertwines the formal derivative with the
  entrywise derivative on the colour coordinates. -/
private lemma jetValLinEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3)
    (z : JetRing ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (StandardModel.jetDeriv μ z)
      = (TensorProduct.map LinearMap.id (pderivColour μ)) (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f d =>
    obtain ⟨w⟩ := d
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero,
        map_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [show StandardModel.jetDeriv μ (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = (pderiv ℂ μ f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet) from rfl,
        show jetValLinEquiv ((pderiv ℂ μ f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • pderiv ℂ μ f) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      exact (Derivation.map_smul (pderiv ℂ μ) (c.ofLp i) f).symm
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, map_add]

/-- The identification of down-singlet jets intertwines the iterated formal derivative
  with the entrywise iterated derivative on the colour coordinates. -/
private lemma jetValLinEquiv_jetIteratedDeriv (x : Multiset (Fin 1 ⊕ Fin 3))
    (z : JetRing ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (StandardModel.jetIteratedDeriv x z)
      = (TensorProduct.map LinearMap.id (foldColour x)) (jetValLinEquiv z) := by
  induction x using Multiset.induction_on with
  | empty =>
    rw [StandardModel.jetIteratedDeriv_zero, LinearMap.id_apply,
      show foldColour 0 = LinearMap.id from LinearMap.ext fun v =>
        WithLp.ofLp_injective 2 rfl,
      TensorProduct.map_id, LinearMap.id_apply]
  | cons μ t ih =>
    rw [StandardModel.jetIteratedDeriv_cons, LinearMap.comp_apply,
      jetValLinEquiv_jetDeriv, ih, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp, pderivColour_comp_foldColour]

/-- The base-point evaluation of a down-singlet jet through the colour coordinates. -/
private lemma valLinEquiv_jetEval (z : JetRing ⊗[ℂ] DownSinglet) :
    valLinEquiv (StandardModel.jetEval z)
      = (TensorProduct.map LinearMap.id ccColour) (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f d =>
    obtain ⟨w⟩ := d
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero]
      simp
      rfl
    | tmul ψ c =>
      rw [StandardModel.jetEval_tmul, map_smul,
        show valLinEquiv (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet) = ψ ⊗ₜ[ℂ] c from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show (constantCoeff f • c).ofLp i = constantCoeff (c.ofLp i • f)
      simp [constantCoeff_smul, mul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, map_add]

set_option maxHeartbeats 1000000 in
/-- **The derivative identity** for the colour matrix of the jet gauge action: the
  formal derivative of the colour matrix is minus the jet action matrix of the
  Maurer–Cartan form times the colour matrix. -/
lemma downMatrix_map_pderiv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (downMatrix U).map (fun f => pderiv ℂ μ f)
      = -(jetActionMatrix (maurerCartanForm U μ) * downMatrix U) := by
  have hleib : ∀ f g : JetRing,
      pderiv ℂ μ (f * g) = pderiv ℂ μ f * g + f * pderiv ℂ μ g := fun f g => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm g]
  have huu : ((U.2.2 : unitary JetRing) : JetRing)
      * star ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Unitary.mul_star_self_of_mem (U.2.2 : unitary JetRing).2
  have hU₃u : star U.1.1 * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
  have h0 : pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
        * star ((U.2.2 : unitary JetRing) : JetRing)
      + ((U.2.2 : unitary JetRing) : JetRing)
        * pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing)) = 0 := by
    have h := congrArg (pderiv ℂ μ) huu
    rw [hleib, Derivation.map_one_eq_zero] at h
    exact h
  have hsu : pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing))
      = -(pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
          * (star ((U.2.2 : unitary JetRing) : JetRing)
            * star ((U.2.2 : unitary JetRing) : JetRing))) := by
    have h1 : star ((U.2.2 : unitary JetRing) : JetRing)
        * (pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
            * star ((U.2.2 : unitary JetRing) : JetRing)
          + ((U.2.2 : unitary JetRing) : JetRing)
            * pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing))) = 0 := by
      rw [h0, mul_zero]
    linear_combination h1
      - pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing)) * huu
  have hm₃U₃ : (maurerCartanForm U μ).toSU3Matrix * U.1.1
      = Complex.I • U.1.1.map (pderiv ℂ μ) := by
    rw [maurerCartanForm_toSU3Matrix, Matrix.smul_mul, Matrix.mul_assoc, hU₃u,
      Matrix.mul_one]
  have hiC : (algebraMap ℂ JetRing) Complex.I * (algebraMap ℂ JetRing) Complex.I
      = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hmap : ((((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
        ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing)).map fun f => pderiv ℂ μ f)
      = (pderiv ℂ μ ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2)) • U.1.1
        + ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2)
          • (U.1.1.map (pderiv ℂ μ)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    exact hleib _ _
  rw [downMatrix, jetActionMatrix, hmap, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.mul_smul, hm₃U₃, Matrix.smul_mul, Matrix.one_mul,
    smul_comm ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) Complex.I,
    smul_sub, smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul,
    ← smul_assoc, neg_sub, sub_neg_eq_add, smul_smul]
  congr 1
  congr 1
  rw [maurerCartanForm_toU1Value, sq, hleib, hsu, Algebra.smul_def,
    Algebra.smul_def, Algebra.smul_def, map_ofNat]
  linear_combination (-(2 * pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
    * star ((U.2.2 : unitary JetRing) : JetRing)
    * star ((U.2.2 : unitary JetRing) : JetRing)
    * star ((U.2.2 : unitary JetRing) : JetRing))) * hiC

/-- **The equivariance identity** for the colour matrix of the jet gauge action: the
  colour matrix intertwines the constant jet action matrix with its adjoint
  transform. -/
lemma downMatrix_mul_jetActionMatrix (U : JetGaugeGroupI) (c : GaugeAlgebra) :
    downMatrix U * jetActionMatrix (JetGaugeAlgebra.ofConstant c)
      = jetActionMatrix (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant c))
        * downMatrix U := by
  have hU₃u : star U.1.1 * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
  rw [downMatrix, jetActionMatrix, jetActionMatrix,
    JetGaugeAlgebra.adjointMap_toSU3Matrix, JetGaugeAlgebra.adjointMap_toU1Value]
  conv_lhs => rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one]
  conv_rhs => rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hU₃u, Matrix.mul_one]
  rw [smul_sub, smul_comm ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2)
    ((2 : ℂ) • (JetGaugeAlgebra.ofConstant c).toU1Value)]

/-- The iterated formal derivative of a negation. -/
private lemma foldl_pderiv_neg (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (-f)
      = -(x.foldl (fun h ρ => pderiv ℂ ρ h) f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_neg, ih, Multiset.foldl_cons]

set_option maxHeartbeats 1000000 in
/-- **The base-point Taylor coefficients of the jet gauge action** on the down-type
  singlet are the colour endomorphisms of the base-point Taylor coefficients of the
  colour matrix. -/
lemma repCoeff_eq (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    IsGaugeField.repCoeff repJetGaugeGroupI U x
      = colourEnd ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) := by
  refine LinearMap.ext fun d => ?_
  apply valLinEquiv.injective
  rw [show IsGaugeField.repCoeff repJetGaugeGroupI U x d
      = StandardModel.jetEval (StandardModel.jetIteratedDeriv x
          (repJetGaugeGroupI U (StandardModel.jetOfConstant d))) from rfl,
    valLinEquiv_jetEval, jetValLinEquiv_jetIteratedDeriv,
    colourEnd_apply_mk, LinearEquiv.apply_symm_apply,
    repJetGaugeGroupI_eq_downMatrix, LinearEquiv.apply_symm_apply,
    StandardModel.jetOfConstant_apply]
  obtain ⟨w⟩ := d
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero]
    simp
    rw [show (0 : DownSinglet).val = 0 from rfl, map_zero]
  | add a b ha hb =>
    rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
      TensorProduct.tmul_add, map_add, map_add, map_add, map_add, ha, hb, map_add,
      map_add]
  | tmul ψ c =>
    rw [show jetValLinEquiv ((1 : JetRing) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
        = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing)) from rfl,
      show (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
          Fermion.RightHandedWeyl
          ((Matrix.toLpLinAlgEquiv 2 (downMatrix U)).restrictScalars ℂ))
          (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing)))
        = ψ ⊗ₜ[ℂ] ((Matrix.toLpLinAlgEquiv 2 (downMatrix U))
            (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing))) from rfl,
      TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.id_apply,
      show valLinEquiv (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet) = ψ ⊗ₜ[ℂ] c from rfl,
      show (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3))
          Fermion.RightHandedWeyl
          (Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))) (ψ ⊗ₜ[ℂ] c)
        = ψ ⊗ₜ[ℂ] ((Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))) c) from rfl]
    congr 1
    refine WithLp.ofLp_injective 2 ?_
    funext j
    show constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h)
        (((Matrix.toLpLinAlgEquiv 2 (downMatrix U))
          (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing))).ofLp j))
      = ((Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))) c).ofLp j
    rw [show ((Matrix.toLpLinAlgEquiv 2 (downMatrix U))
          (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing))).ofLp j
        = ∑ k, downMatrix U j k * (c.ofLp k • (1 : JetRing)) from by
        simp [Matrix.mulVec_eq_sum, Finset.sum_apply, mul_comm],
      show ((Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))) c).ofLp j
        = ∑ k, constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) (downMatrix U j k))
            * c.ofLp k from by
        simp [Matrix.mulVec_eq_sum, Finset.sum_apply, mul_comm],
      JetRing.foldl_pderiv_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, mul_one, foldl_pderiv_smul, constantCoeff_smul, smul_eq_mul,
      mul_comm]

/-- The colour endomorphism of the identity matrix is the identity. -/
lemma colourEnd_one : colourEnd 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [colourEnd_apply_mk, map_one, map_one, Module.End.one_apply,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

/-- At the base point, a gauge jet with trivial value acts trivially: the zeroth
  Taylor coefficient of the jet gauge action is the identity. -/
lemma repCoeff_zero_of_eval_eq_one {U : JetGaugeGroupI} (hU : U.eval = 1) :
    IsGaugeField.repCoeff repJetGaugeGroupI U 0 = LinearMap.id := by
  have h1 : (constantCoeff : JetRing →+* ℂ).mapMatrix
      ((U.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)
        = 1 := Subtype.ext_iff.mp (congrArg Prod.fst hU)
  have hu : constantCoeff ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Subtype.ext_iff.mp (congrArg (fun p : GaugeGroupI => p.2.2) hU)
  have hM : ((downMatrix U).map fun f =>
      constantCoeff ((0 : Multiset (Fin 1 ⊕ Fin 3)).foldl (fun h ρ => pderiv ℂ ρ h) f))
        = 1 := by
    ext i j
    rw [Matrix.map_apply, Multiset.foldl_zero, downMatrix, Matrix.smul_apply,
      smul_eq_mul, map_mul, map_pow, JetRing.constantCoeff_star, hu, star_one,
      one_pow, one_mul]
    exact Matrix.ext_iff.mpr h1 i j
  rw [repCoeff_eq, hM, colourEnd_one]


set_option maxHeartbeats 1000000 in
/-- **The `(3, 1)_{-2}` action of the gauge algebra is the infinitesimal action
  underlying the jet gauge action on the down-type singlet**: its base-point Taylor
  coefficients obey the Maurer–Cartan Leibniz law and intertwine the action with the
  adjoint transports. -/
theorem isInfinitesimalActionOf :
    GaugeAlgebra.IsInfinitesimalActionOf gaugeAlgebraAction repJetGaugeGroupI := by
  constructor
  · intro U μ x
    have hMcons : ((downMatrix U).map fun f =>
        constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) f))
        = -((x.antidiagonal.map fun p =>
            actionMatrix (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (maurerCartanForm U μ)))
            * ((downMatrix U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum) := by
      rw [show ((downMatrix U).map fun f =>
            constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) f))
          = (((downMatrix U).map fun f => pderiv ℂ μ f).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply,
              Multiset.foldl_cons],
        downMatrix_map_pderiv,
        show ((-(jetActionMatrix (maurerCartanForm U μ) * downMatrix U)).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
          = -(((jetActionMatrix (maurerCartanForm U μ) * downMatrix U)).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.neg_apply, Matrix.neg_apply,
              Matrix.map_apply, foldl_pderiv_neg, map_neg],
        matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
        fun p hp => by rw [jetActionMatrix_map_cc_foldl]))
    rw [repCoeff_eq, hMcons, colourEnd_neg, colourEnd_multiset_sum, Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
      fun p hp => ?_))
    rw [Function.comp_apply, colourEnd_mul, repCoeff_eq]
    rfl
  · intro U x c
    have hCsmul : ∀ z w : ℂ, (z • (C w : JetRing)) = C (z * w) := fun z w => by
      rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply,
        Algebra.algebraMap_self_apply, ← map_mul]
    have hconst : jetActionMatrix (JetGaugeAlgebra.ofConstant c)
        = (actionMatrix c).map (C : ℂ → JetRing) := by
      refine Matrix.ext fun i j => ?_
      rw [jetActionMatrix, actionMatrix, JetGaugeAlgebra.ofConstant_toSU3Matrix,
        JetGaugeAlgebra.ofConstant_toU1Value, Matrix.map_apply, Matrix.smul_apply,
        Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.sub_apply, Matrix.smul_apply]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        simp only [smul_eq_mul, mul_one]
        rw [hCsmul, ← map_sub, hCsmul]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, smul_zero, smul_zero,
          sub_zero, sub_zero, hCsmul]
        exact congrArg C (by ring)
    have hcollapse : ∀ (m : Multiset (Fin 1 ⊕ Fin 3)),
        (((actionMatrix c).map (C : ℂ → JetRing)).map fun f =>
          constantCoeff (m.foldl (fun h ρ => pderiv ℂ ρ h) f))
        = if m = 0 then actionMatrix c else 0 := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply, constantCoeff_C]
      · refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply, JetRing.foldl_pderiv_C_of_ne_zero hm, hm]
    have hMact : ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) * actionMatrix c
        = (x.antidiagonal.map fun p =>
            actionMatrix (IsGaugeField.adjointCoeff U p.1 c)
            * ((downMatrix U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum := by
      have h1 : ((downMatrix U * jetActionMatrix (JetGaugeAlgebra.ofConstant c)).map
            fun f => constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
          = ((downMatrix U).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
            * actionMatrix c := by
        rw [hconst, matrix_constantCoeff_foldl_pderiv_mul,
          Multiset.map_congr rfl (fun p hp => by rw [hcollapse p.2]),
          Multiset.sum_antidiagonal_eq_of_snd_ne_zero x
            (fun p => ((downMatrix U).map fun f =>
              constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
                (if p.2 = 0 then actionMatrix c else 0))
            (fun p hp => by rw [if_neg hp, Matrix.mul_zero]),
          if_pos rfl]
      rw [← h1, downMatrix_mul_jetActionMatrix, matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
        rw [jetActionMatrix_map_cc_foldl,
          show JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant c)))
            = IsGaugeField.adjointCoeff U p.1 c from rfl])
    rw [repCoeff_eq,
      show (colourEnd ((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))
          ∘ₗ gaugeAlgebraAction c
        = colourEnd (((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
              * actionMatrix c) from by
        rw [colourEnd_mul]; rfl,
      hMact, colourEnd_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, colourEnd_mul, repCoeff_eq]
    rfl

end InfinitesimalAction

end DownSinglet

end StandardModel
