/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import Physlib.Particles.StandardModel.GaugeAlgebra.InfinitesimalAction
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# The infinitesimal gauge action on the quark doublet

## i. Overview

The `(3, 2)_{1}` action of the gauge algebra on the quark doublet: the colour and weak
parts of the algebra element act on the combined colour–weak index through the Kronecker
sum, and the hypercharge part scales, all through the physicists' factor of `i`, matching
the group action `u • (U₃ ⊗ₖ U₂)` infinitesimally. The main theorem shows this is the
infinitesimal action underlying the jet gauge action `QuarkDoublet.repJetGaugeGroupI`,
in the sense of `GaugeAlgebra.IsInfinitesimalActionOf`.

## ii. Key results

- `colourWeakEnd` : the endomorphism of the quark doublet defined by a colour–weak
  matrix.
- `gaugeAlgebraAction` : the infinitesimal `(3, 2)_{1}` action of the gauge algebra.
- `jetGaugeMatrix_map_pderiv` : the derivative identity for the colour–weak matrix.
- `jetGaugeMatrix_mul_jetActionMatrix` : the equivariance identity for the colour–weak
  matrix.
- `isInfinitesimalActionOf` : the gauge-algebra action is the infinitesimal action
  underlying the jet gauge action.

## iii. Table of contents

- A. The action of the gauge algebra
- B. The colour–weak matrix of the jet gauge action
- C. The infinitesimal action underlies the jet gauge action

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace QuarkDoublet

open Matrix MatrixGroups Kronecker

/-!

## A. The action of the gauge algebra

-/

/-- The identification of the quark doublet with a left-handed Weyl spinor tensored with
  a colour–weak vector over the combined index `Fin 3 × Fin 2`: the `ℂ`-level analogue
  of `jetValLinEquiv`. -/
noncomputable def colourWeakValLinEquiv :
    QuarkDoublet ≃ₗ[ℂ] Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3 × Fin 2) :=
  (valLinEquiv.trans (TensorProduct.assoc ℂ Fermion.LeftHandedWeyl
      (EuclideanSpace ℂ (Fin 3)) (EuclideanSpace ℂ (Fin 2)))).trans <|
    TensorProduct.congr (LinearEquiv.refl ℂ Fermion.LeftHandedWeyl)
      (colourWeakEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin 3 × Fin 2 → ℂ)).symm)

/-- The endomorphism of the quark doublet defined by a complex matrix over the
  combined colour–weak index, with the Weyl factor untouched. -/
noncomputable def colourWeakEnd (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    QuarkDoublet →ₗ[ℂ] QuarkDoublet :=
  colourWeakValLinEquiv.symm.toLinearMap ∘ₗ
    Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3 × Fin 2)) Fermion.LeftHandedWeyl
      (Matrix.toLpLinAlgEquiv 2 A) ∘ₗ colourWeakValLinEquiv.toLinearMap

lemma colourWeakEnd_apply_mk (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
    (v : QuarkDoublet) :
    colourWeakEnd A v
      = colourWeakValLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3 × Fin 2))
            Fermion.LeftHandedWeyl
            (Matrix.toLpLinAlgEquiv 2 A) (colourWeakValLinEquiv v)) := rfl

lemma colourWeakEnd_add (A B : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd (A + B) = colourWeakEnd A + colourWeakEnd B := by
  rw [colourWeakEnd, colourWeakEnd, colourWeakEnd, map_add, map_add,
    LinearMap.add_comp, LinearMap.comp_add]

lemma colourWeakEnd_smul (z : ℂ) (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd (z • A) = z • colourWeakEnd A := by
  rw [colourWeakEnd, colourWeakEnd, map_smul, map_smul, LinearMap.smul_comp,
    LinearMap.comp_smul]

lemma colourWeakEnd_zero : colourWeakEnd 0 = 0 := by
  rw [colourWeakEnd, map_zero, map_zero, LinearMap.zero_comp, LinearMap.comp_zero]

lemma colourWeakEnd_neg (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd (-A) = -colourWeakEnd A := by
  rw [show (-A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) = (-1 : ℂ) • A from by
    rw [neg_one_smul], colourWeakEnd_smul, neg_one_smul]

lemma colourWeakEnd_multiset_sum
    (m : Multiset (Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)) :
    colourWeakEnd m.sum = (m.map colourWeakEnd).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [colourWeakEnd_zero]
  | cons A t ih => rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      colourWeakEnd_add, ih]

/-- The colour–weak endomorphisms compose through matrix multiplication. -/
lemma colourWeakEnd_mul (A B : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd (A * B) = colourWeakEnd A ∘ₗ colourWeakEnd B := by
  refine LinearMap.ext fun v => ?_
  rw [colourWeakEnd_apply_mk, map_mul, map_mul, LinearMap.comp_apply,
    colourWeakEnd_apply_mk, colourWeakEnd_apply_mk, LinearEquiv.apply_symm_apply]
  rfl

/-- The matrix of the infinitesimal `(3, 2)_{1}` action of a gauge algebra element on
  the combined colour–weak index: `i` times the Kronecker sum of the colour and weak
  parts, shifted by `i` times the hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  Complex.I • (c.toSU3Matrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ c.toSU2Matrix
    + c.toU1Value • 1)

/-- **The infinitesimal action of the gauge algebra on the quark doublet**: the
  derivative of the `(3, 2)_{1}` action of the gauge group, real-linear in the
  algebra slot and complex-linear in the value slot — the form consumed by the
  covariant derivative `IsGaugeField.covDerivIter` and by
  `GaugeAlgebra.IsInfinitesimalActionOf`. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] QuarkDoublet →ₗ[ℂ] QuarkDoublet where
  toFun c := colourWeakEnd (actionMatrix c)
  map_add' c₁ c₂ := by
    rw [show actionMatrix (c₁ + c₂) = actionMatrix c₁ + actionMatrix c₂ from by
      rw [actionMatrix, actionMatrix, actionMatrix, GaugeAlgebra.add_toSU3Matrix,
        GaugeAlgebra.add_toSU2Matrix, GaugeAlgebra.add_toU1Value,
        Matrix.add_kronecker, Matrix.kronecker_add]
      module]
    rw [colourWeakEnd_add]
  map_smul' r c := by
    rw [show actionMatrix (r • c) = (r : ℂ) • actionMatrix c from by
      rw [actionMatrix, actionMatrix, GaugeAlgebra.smul_toSU3Matrix,
        GaugeAlgebra.smul_toSU2Matrix, GaugeAlgebra.smul_toU1Value,
        show (r • c.toSU3Matrix : Matrix (Fin 3) (Fin 3) ℂ)
          = (r : ℂ) • c.toSU3Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU3Matrix]; rfl,
        show (r • c.toSU2Matrix : Matrix (Fin 2) (Fin 2) ℂ)
          = (r : ℂ) • c.toSU2Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU2Matrix]; rfl,
        show r • c.toU1Value = (r : ℂ) • c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value]; rfl,
        Matrix.smul_kronecker, Matrix.kronecker_smul]
      module,
      colourWeakEnd_smul]
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply]
    show (r : ℂ) • colourWeakEnd (actionMatrix c) v
      = r • colourWeakEnd (actionMatrix c) v
    rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-!

## B. The colour–weak matrix of the jet gauge action

## C. The infinitesimal action underlies the jet gauge action

The `(3, 2)_{1}` action of the gauge algebra is the infinitesimal action underlying the
jet gauge action, in the sense of `GaugeAlgebra.IsInfinitesimalActionOf`: the base-point
Taylor coefficients of the jet action satisfy the Maurer–Cartan Leibniz law and
intertwine the action with the adjoint transports. The proofs work through the
colour–weak matrix `jetGaugeMatrix` of the jet action and the all-orders matrix Leibniz
rule at the base point.

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

/-- The jet-valued matrix of the infinitesimal `(3, 2)_{1}` action of a jet of gauge
  algebra elements: the jet analogue of `actionMatrix`. -/
noncomputable def jetActionMatrix (a : JetGaugeAlgebra) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) JetRing :=
  Complex.I • (a.toSU3Matrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) JetRing)
    + (1 : Matrix (Fin 3) (Fin 3) JetRing) ⊗ₖ a.toSU2Matrix
    + a.toU1Value • 1)

/-- The base-point Taylor coefficients of the jet action matrix are the action matrices
  of the base-point Taylor coefficients. -/
lemma jetActionMatrix_map_cc_foldl (p : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    ((jetActionMatrix a).map fun f =>
        constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) f))
      = actionMatrix (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p a)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, jetActionMatrix, actionMatrix, Matrix.smul_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply,
    Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply,
    Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.smul_apply, foldl_pderiv_smul, constantCoeff_smul,
    JetRing.foldl_pderiv_add, JetRing.foldl_pderiv_add, map_add, map_add]
  congr 1
  congr 1
  · congr 1
    · by_cases h3 : i.2 = j.2
      · rw [h3, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one,
          JetGaugeAlgebra.eval_iteratedDeriv_toSU3Matrix, Matrix.map_apply]
      · rw [Matrix.one_apply_ne h3, Matrix.one_apply_ne h3, mul_zero, mul_zero,
          JetRing.foldl_pderiv_zero, map_zero]
    · by_cases h2 : i.1 = j.1
      · rw [h2, Matrix.one_apply_eq, Matrix.one_apply_eq, one_mul, one_mul,
          JetGaugeAlgebra.eval_iteratedDeriv_toSU2Matrix, Matrix.map_apply]
      · rw [Matrix.one_apply_ne h2, Matrix.one_apply_ne h2, zero_mul, zero_mul,
          JetRing.foldl_pderiv_zero, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        smul_eq_mul, mul_one, JetGaugeAlgebra.eval_iteratedDeriv_toU1Value]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, smul_zero, smul_zero,
        JetRing.foldl_pderiv_zero, map_zero]

lemma repJetGaugeGroupI_eq_jetGaugeMatrix (U : JetGaugeGroupI)
    (z : JetRing ⊗[ℂ] QuarkDoublet) :
    repJetGaugeGroupI U z
      = jetValLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3 × Fin 2))
            Fermion.LeftHandedWeyl
            ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U)).restrictScalars ℂ)
            (jetValLinEquiv z)) := rfl

/-- The entrywise formal derivative on the colour–weak coordinates, as a `ℂ`-linear
  map. -/
private noncomputable def pderivColourWeak (μ : Fin 1 ⊕ Fin 3) :
    EuclideanSpace JetRing (Fin 3 × Fin 2) →ₗ[ℂ]
      EuclideanSpace JetRing (Fin 3 × Fin 2) where
  toFun v := WithLp.toLp 2 fun q => pderiv ℂ μ (v.ofLp q)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext q
    exact map_add _ _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext q
    exact Derivation.map_smul _ _ _

/-- The entrywise iterated formal derivative on the colour–weak coordinates. -/
private noncomputable def foldColourWeak (x : Multiset (Fin 1 ⊕ Fin 3)) :
    EuclideanSpace JetRing (Fin 3 × Fin 2) →ₗ[ℂ]
      EuclideanSpace JetRing (Fin 3 × Fin 2) where
  toFun v := WithLp.toLp 2 fun q => x.foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp q)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext q
    exact JetRing.foldl_pderiv_add x _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext q
    exact foldl_pderiv_smul x z _

/-- The entrywise base-point evaluation on the colour–weak coordinates. -/
private noncomputable def ccColourWeak :
    EuclideanSpace JetRing (Fin 3 × Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3 × Fin 2) where
  toFun v := WithLp.toLp 2 fun q => constantCoeff (v.ofLp q)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext q
    exact map_add _ _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext q
    exact constantCoeff_smul _ _

private lemma pderivColourWeak_comp_foldColourWeak (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    pderivColourWeak μ ∘ₗ foldColourWeak x = foldColourWeak (μ ::ₘ x) := by
  refine LinearMap.ext fun v => ?_
  refine WithLp.ofLp_injective 2 ?_
  funext q
  show pderiv ℂ μ (x.foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp q))
    = (μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp q)
  rw [Multiset.foldl_cons, pderiv_foldl]

/-- The identification of quark-doublet jets intertwines the formal derivative with the
  entrywise derivative on the colour–weak coordinates. -/
private lemma jetValLinEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3)
    (z : JetRing ⊗[ℂ] QuarkDoublet) :
    jetValLinEquiv (StandardModel.jetDeriv μ z)
      = (TensorProduct.map LinearMap.id (pderivColourWeak μ)) (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f d =>
    obtain ⟨v⟩ := d
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : QuarkDoublet) = 0 from rfl, TensorProduct.tmul_zero,
        map_zero, map_zero, map_zero]
    | tmul vc w =>
      induction vc using TensorProduct.induction_on with
      | zero =>
        rw [show ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
            ⊗ₜ[ℂ] w } : QuarkDoublet) = 0 from by
          rw [TensorProduct.zero_tmul]; rfl, TensorProduct.tmul_zero, map_zero,
          map_zero, map_zero]
      | tmul ψ c =>
        rw [show StandardModel.jetDeriv μ
              (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = (pderiv ℂ μ f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet) from rfl,
          show jetValLinEquiv
              ((pderiv ℂ μ f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • pderiv ℂ μ f) from rfl,
          show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f) from rfl,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 1
        refine WithLp.ofLp_injective 2 ?_
        funext q
        exact (Derivation.map_smul (pderiv ℂ μ)
          (colourWeakEquiv (c ⊗ₜ[ℂ] w) q) f).symm
      | add a b ha hb =>
        rw [show ({ val := (a + b) ⊗ₜ[ℂ] w } : QuarkDoublet)
            = ⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ from by
          rw [show (⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
              = ⟨a ⊗ₜ[ℂ] w + b ⊗ₜ[ℂ] w⟩ from rfl, TensorProduct.add_tmul],
          TensorProduct.tmul_add]
        simp only [map_add]
        rw [ha, hb]
    | add a b ha hb =>
      rw [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add]
      simp only [map_add]
      rw [ha, hb]

/-- The identification of quark-doublet jets intertwines the iterated formal derivative
  with the entrywise iterated derivative on the colour–weak coordinates. -/
private lemma jetValLinEquiv_jetIteratedDeriv (x : Multiset (Fin 1 ⊕ Fin 3))
    (z : JetRing ⊗[ℂ] QuarkDoublet) :
    jetValLinEquiv (StandardModel.jetIteratedDeriv x z)
      = (TensorProduct.map LinearMap.id (foldColourWeak x)) (jetValLinEquiv z) := by
  induction x using Multiset.induction_on with
  | empty =>
    rw [StandardModel.jetIteratedDeriv_zero, LinearMap.id_apply,
      show foldColourWeak 0 = LinearMap.id from LinearMap.ext fun v =>
        WithLp.ofLp_injective 2 rfl,
      TensorProduct.map_id, LinearMap.id_apply]
  | cons μ t ih =>
    rw [StandardModel.jetIteratedDeriv_cons, LinearMap.comp_apply,
      jetValLinEquiv_jetDeriv, ih, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp, pderivColourWeak_comp_foldColourWeak]

/-- The base-point evaluation of a quark-doublet jet through the colour–weak
  coordinates. -/
private lemma colourWeakValLinEquiv_jetEval (z : JetRing ⊗[ℂ] QuarkDoublet) :
    colourWeakValLinEquiv (StandardModel.jetEval z)
      = (TensorProduct.map LinearMap.id ccColourWeak) (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f d =>
    obtain ⟨v⟩ := d
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : QuarkDoublet) = 0 from rfl, TensorProduct.tmul_zero]
      simp
    | tmul vc w =>
      induction vc using TensorProduct.induction_on with
      | zero =>
        rw [show ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
            ⊗ₜ[ℂ] w } : QuarkDoublet) = 0 from by
          rw [TensorProduct.zero_tmul]; rfl, TensorProduct.tmul_zero]
        simp
      | tmul ψ c =>
        rw [StandardModel.jetEval_tmul, map_smul,
          show colourWeakValLinEquiv (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q) from rfl,
          show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f) from rfl,
          TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul]
        congr 1
        refine WithLp.ofLp_injective 2 ?_
        funext q
        show constantCoeff f • colourWeakEquiv (c ⊗ₜ[ℂ] w) q
          = constantCoeff (colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f)
        simp [constantCoeff_smul, mul_comm]
      | add a b ha hb =>
        rw [show ({ val := (a + b) ⊗ₜ[ℂ] w } : QuarkDoublet)
            = ⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ from by
          rw [show (⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
              = ⟨a ⊗ₜ[ℂ] w + b ⊗ₜ[ℂ] w⟩ from rfl, TensorProduct.add_tmul],
          TensorProduct.tmul_add]
        simp only [map_add]
        rw [ha, hb]
    | add a b ha hb =>
      rw [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add]
      simp only [map_add]
      rw [ha, hb]

set_option maxHeartbeats 1000000 in
/-- **The derivative identity** for the colour–weak matrix of the jet gauge action: the
  formal derivative of the colour–weak matrix is minus the jet action matrix of the
  Maurer–Cartan form times the colour–weak matrix. -/
lemma jetGaugeMatrix_map_pderiv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (jetGaugeMatrix U).map (fun f => pderiv ℂ μ f)
      = -(jetActionMatrix (maurerCartanForm U μ) * jetGaugeMatrix U) := by
  have hleib : ∀ f g : JetRing,
      pderiv ℂ μ (f * g) = pderiv ℂ μ f * g + f * pderiv ℂ μ g := fun f g => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm g]
  have huu : ((U.2.2 : unitary JetRing) : JetRing)
      * star ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Unitary.mul_star_self_of_mem (U.2.2 : unitary JetRing).2
  have hU₃u : star U.1.1 * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
  have hU₂u : star U.2.1.1 * U.2.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
  have hm₃U₃ : (maurerCartanForm U μ).toSU3Matrix * U.1.1
      = Complex.I • U.1.1.map (pderiv ℂ μ) := by
    rw [maurerCartanForm_toSU3Matrix, Matrix.smul_mul, Matrix.mul_assoc, hU₃u,
      Matrix.mul_one]
  have hm₂U₂ : (maurerCartanForm U μ).toSU2Matrix * U.2.1.1
      = Complex.I • U.2.1.1.map (pderiv ℂ μ) := by
    rw [maurerCartanForm_toSU2Matrix, Matrix.smul_mul, Matrix.mul_assoc, hU₂u,
      Matrix.mul_one]
  have hmap : (jetGaugeMatrix U).map (fun f => pderiv ℂ μ f)
      = (pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)) •
          (((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing) ⊗ₖ
            ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
              Matrix (Fin 2) (Fin 2) JetRing))
        + ((U.2.2 : unitary JetRing) : JetRing) •
          ((((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing) ⊗ₖ
            ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
              Matrix (Fin 2) (Fin 2) JetRing)).map fun f => pderiv ℂ μ f) := by
    refine Matrix.ext fun i j => ?_
    simp only [jetGaugeMatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    exact hleib _ _
  have hkron : ((((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing) ⊗ₖ
        ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) :
          Matrix (Fin 2) (Fin 2) JetRing)).map fun f => pderiv ℂ μ f)
      = (U.1.1.map (pderiv ℂ μ)) ⊗ₖ U.2.1.1
        + U.1.1 ⊗ₖ (U.2.1.1.map (pderiv ℂ μ)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.add_apply]
    exact hleib _ _
  rw [hmap, hkron, jetActionMatrix, jetGaugeMatrix, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_mul, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, hm₃U₃, hm₂U₂, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_kronecker, Matrix.kronecker_smul, maurerCartanForm_toU1Value,
    smul_assoc, ← smul_add, ← smul_add, smul_smul Complex.I Complex.I, Complex.I_mul_I,
    neg_one_smul, smul_neg, neg_neg]
  conv_rhs => rw [smul_add, smul_smul]
  rw [show ((U.2.2 : unitary JetRing) : JetRing)
        * (pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
          * star ((U.2.2 : unitary JetRing) : JetRing))
      = pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing) from by
    linear_combination pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing) * huu]
  exact add_comm _ _

/-- **The equivariance identity** for the colour–weak matrix of the jet gauge action:
  the colour–weak matrix intertwines the constant jet action matrix with its adjoint
  transform. -/
lemma jetGaugeMatrix_mul_jetActionMatrix (U : JetGaugeGroupI) (c : GaugeAlgebra) :
    jetGaugeMatrix U * jetActionMatrix (JetGaugeAlgebra.ofConstant c)
      = jetActionMatrix (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant c))
        * jetGaugeMatrix U := by
  have hU₃u : star U.1.1 * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
  have hU₂u : star U.2.1.1 * U.2.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
  rw [jetGaugeMatrix, jetActionMatrix, jetActionMatrix,
    JetGaugeAlgebra.adjointMap_toSU3Matrix, JetGaugeAlgebra.adjointMap_toSU2Matrix,
    JetGaugeAlgebra.adjointMap_toU1Value]
  conv_lhs => rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one]
  conv_rhs => rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hU₃u,
    Matrix.mul_one, Matrix.mul_assoc, hU₂u, Matrix.mul_one]

/-- The iterated formal derivative of a negation. -/
private lemma foldl_pderiv_neg (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (-f)
      = -(x.foldl (fun h ρ => pderiv ℂ ρ h) f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_neg, ih, Multiset.foldl_cons]

set_option maxHeartbeats 1000000 in
/-- **The base-point Taylor coefficients of the jet gauge action** on the quark
  doublet are the colour–weak endomorphisms of the base-point Taylor coefficients of
  the colour–weak matrix. -/
lemma repCoeff_eq (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    IsGaugeField.repCoeff repJetGaugeGroupI U x
      = colourWeakEnd ((jetGaugeMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) := by
  refine LinearMap.ext fun d => ?_
  apply colourWeakValLinEquiv.injective
  rw [show IsGaugeField.repCoeff repJetGaugeGroupI U x d
      = StandardModel.jetEval (StandardModel.jetIteratedDeriv x
          (repJetGaugeGroupI U (StandardModel.jetOfConstant d))) from rfl,
    colourWeakValLinEquiv_jetEval, jetValLinEquiv_jetIteratedDeriv,
    colourWeakEnd_apply_mk, LinearEquiv.apply_symm_apply,
    repJetGaugeGroupI_eq_jetGaugeMatrix, LinearEquiv.apply_symm_apply,
    StandardModel.jetOfConstant_apply]
  obtain ⟨v⟩ := d
  induction v using TensorProduct.induction_on with
  | zero =>
    rw [show ({ val := 0 } : QuarkDoublet) = 0 from rfl, TensorProduct.tmul_zero]
    simp
  | add a b ha hb =>
    rw [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
      TensorProduct.tmul_add]
    simp only [map_add]
    rw [ha, hb]
  | tmul vc wk =>
    induction vc using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
          ⊗ₜ[ℂ] wk } : QuarkDoublet) = 0 from by
        rw [TensorProduct.zero_tmul]; rfl, TensorProduct.tmul_zero]
      simp
    | tmul ψ cv =>
      rw [show jetValLinEquiv
            ((1 : JetRing) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] cv ⊗ₜ[ℂ] wk⟩ : QuarkDoublet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
              colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q • (1 : JetRing)) from rfl,
        show (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3 × Fin 2))
            Fermion.LeftHandedWeyl
            ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U)).restrictScalars ℂ))
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
              colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q • (1 : JetRing)))
          = ψ ⊗ₜ[ℂ] ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U))
              (WithLp.toLp 2 fun q =>
                colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q • (1 : JetRing))) from rfl,
        TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply,
        show colourWeakValLinEquiv (⟨ψ ⊗ₜ[ℂ] cv ⊗ₜ[ℂ] wk⟩ : QuarkDoublet)
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
              colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q) from rfl,
        show (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3 × Fin 2))
            Fermion.LeftHandedWeyl
            (Matrix.toLpLinAlgEquiv 2 ((jetGaugeMatrix U).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))))
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q => colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q))
          = ψ ⊗ₜ[ℂ] ((Matrix.toLpLinAlgEquiv 2 ((jetGaugeMatrix U).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))
              (WithLp.toLp 2 fun q =>
                colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q)) from rfl]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext j
      show constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h)
          (((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U))
            (WithLp.toLp 2 fun q =>
              colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q • (1 : JetRing))).ofLp j))
        = ((Matrix.toLpLinAlgEquiv 2 ((jetGaugeMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))
            (WithLp.toLp 2 fun q => colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q)).ofLp j
      rw [show ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U))
            (WithLp.toLp 2 fun q =>
              colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q • (1 : JetRing))).ofLp j
          = ∑ k, jetGaugeMatrix U j k *
              (colourWeakEquiv (cv ⊗ₜ[ℂ] wk) k • (1 : JetRing)) from by
          simp [Matrix.mulVec_eq_sum, Finset.sum_apply, mul_comm],
        show ((Matrix.toLpLinAlgEquiv 2 ((jetGaugeMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))
            (WithLp.toLp 2 fun q => colourWeakEquiv (cv ⊗ₜ[ℂ] wk) q)).ofLp j
          = ∑ k, constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h)
              (jetGaugeMatrix U j k)) * colourWeakEquiv (cv ⊗ₜ[ℂ] wk) k from by
          simp [Matrix.mulVec_eq_sum, Finset.sum_apply, mul_comm],
        JetRing.foldl_pderiv_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_smul_comm, mul_one, foldl_pderiv_smul, constantCoeff_smul, smul_eq_mul,
        mul_comm]
    | add a b ha hb =>
      rw [show ({ val := (a + b) ⊗ₜ[ℂ] wk } : QuarkDoublet)
          = ⟨a ⊗ₜ[ℂ] wk⟩ + ⟨b ⊗ₜ[ℂ] wk⟩ from by
        rw [show (⟨a ⊗ₜ[ℂ] wk⟩ + ⟨b ⊗ₜ[ℂ] wk⟩ : QuarkDoublet)
            = ⟨a ⊗ₜ[ℂ] wk + b ⊗ₜ[ℂ] wk⟩ from rfl, TensorProduct.add_tmul],
        TensorProduct.tmul_add]
      simp only [map_add]
      rw [ha, hb]


/-- The colour–weak endomorphism of the identity matrix is the identity. -/
lemma colourWeakEnd_one : colourWeakEnd 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [colourWeakEnd_apply_mk, map_one, map_one, Module.End.one_apply,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

/-- At the base point, a gauge jet with trivial value acts trivially: the zeroth
  Taylor coefficient of the jet gauge action is the identity. -/
lemma repCoeff_zero_of_eval_eq_one {U : JetGaugeGroupI} (hU : U.eval = 1) :
    IsGaugeField.repCoeff repJetGaugeGroupI U 0 = LinearMap.id := by
  have h1 : (constantCoeff : JetRing →+* ℂ).mapMatrix
      ((U.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)
        = 1 := Subtype.ext_iff.mp (congrArg Prod.fst hU)
  have h2 : (constantCoeff : JetRing →+* ℂ).mapMatrix
      ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)
        = 1 := Subtype.ext_iff.mp (congrArg (fun p : GaugeGroupI => p.2.1) hU)
  have hu : constantCoeff ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Subtype.ext_iff.mp (congrArg (fun p : GaugeGroupI => p.2.2) hU)
  have hM : ((jetGaugeMatrix U).map fun f =>
      constantCoeff ((0 : Multiset (Fin 1 ⊕ Fin 3)).foldl (fun h ρ => pderiv ℂ ρ h) f))
        = 1 := by
    rw [show (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
        = (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) from
        (Matrix.one_kronecker_one).symm, ← h1, ← h2]
    ext i j
    rw [Matrix.map_apply, Multiset.foldl_zero, jetGaugeMatrix, Matrix.smul_apply,
      smul_eq_mul, map_mul, hu, one_mul, Matrix.kronecker_apply,
      Matrix.kronecker_apply, map_mul, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
  rw [repCoeff_eq, hM, colourWeakEnd_one]

set_option maxHeartbeats 1000000 in
/-- **The `(3, 2)_{1}` action of the gauge algebra is the infinitesimal action
  underlying the jet gauge action on the quark doublet**: its base-point Taylor
  coefficients obey the Maurer–Cartan Leibniz law and intertwine the action with the
  adjoint transports. -/
theorem isInfinitesimalActionOf :
    GaugeAlgebra.IsInfinitesimalActionOf gaugeAlgebraAction repJetGaugeGroupI := by
  constructor
  · intro U μ x
    have hMcons : ((jetGaugeMatrix U).map fun f =>
        constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) f))
        = -((x.antidiagonal.map fun p =>
            actionMatrix (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (maurerCartanForm U μ)))
            * ((jetGaugeMatrix U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum) := by
      rw [show ((jetGaugeMatrix U).map fun f =>
            constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) f))
          = (((jetGaugeMatrix U).map fun f => pderiv ℂ μ f).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply,
              Multiset.foldl_cons],
        jetGaugeMatrix_map_pderiv,
        show ((-(jetActionMatrix (maurerCartanForm U μ) * jetGaugeMatrix U)).map
            fun f => constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
          = -(((jetActionMatrix (maurerCartanForm U μ) * jetGaugeMatrix U)).map
              fun f => constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.neg_apply, Matrix.neg_apply,
              Matrix.map_apply, foldl_pderiv_neg, map_neg],
        matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
        fun p hp => by rw [jetActionMatrix_map_cc_foldl]))
    rw [repCoeff_eq, hMcons, colourWeakEnd_neg, colourWeakEnd_multiset_sum,
      Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
      fun p hp => ?_))
    rw [Function.comp_apply, colourWeakEnd_mul, repCoeff_eq]
    rfl
  · intro U x c
    have hCsmul : ∀ z w : ℂ, (z • (C w : JetRing)) = C (z * w) := fun z w => by
      rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply,
        Algebra.algebraMap_self_apply, ← map_mul]
    have hconst : jetActionMatrix (JetGaugeAlgebra.ofConstant c)
        = (actionMatrix c).map (C : ℂ → JetRing) := by
      have hone : ∀ {n : Type} [DecidableEq n] (a b : n),
          (1 : Matrix n n JetRing) a b = C ((1 : Matrix n n ℂ) a b) := by
        intro n _ a b
        by_cases h : a = b
        · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
        · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
      refine Matrix.ext fun i j => ?_
      rw [jetActionMatrix, actionMatrix, Matrix.map_apply, Matrix.smul_apply,
        Matrix.smul_apply, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply,
        Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply,
        Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
        Matrix.smul_apply, JetGaugeAlgebra.ofConstant_toSU3Matrix,
        JetGaugeAlgebra.ofConstant_toSU2Matrix, JetGaugeAlgebra.ofConstant_toU1Value,
        Matrix.map_apply, Matrix.map_apply, hone i.2 j.2, hone i.1 j.1, hone i j,
        ← map_mul, ← map_mul,
        show (C c.toU1Value : JetRing)
              • C ((1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) i j)
            = C (c.toU1Value • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) i j)
          from by rw [smul_eq_mul, smul_eq_mul, ← map_mul],
        ← map_add, ← map_add, hCsmul, smul_eq_mul, smul_eq_mul]
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
    have hMact : ((jetGaugeMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) * actionMatrix c
        = (x.antidiagonal.map fun p =>
            actionMatrix (IsGaugeField.adjointCoeff U p.1 c)
            * ((jetGaugeMatrix U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum := by
      have h1 : ((jetGaugeMatrix U
              * jetActionMatrix (JetGaugeAlgebra.ofConstant c)).map
            fun f => constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
          = ((jetGaugeMatrix U).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
            * actionMatrix c := by
        rw [hconst, matrix_constantCoeff_foldl_pderiv_mul,
          Multiset.map_congr rfl (fun p hp => by rw [hcollapse p.2]),
          Multiset.sum_antidiagonal_eq_of_snd_ne_zero x
            (fun p => ((jetGaugeMatrix U).map fun f =>
              constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
                (if p.2 = 0 then actionMatrix c else 0))
            (fun p hp => by rw [if_neg hp, Matrix.mul_zero]),
          if_pos rfl]
      rw [← h1, jetGaugeMatrix_mul_jetActionMatrix,
        matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
        rw [jetActionMatrix_map_cc_foldl,
          show JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant c)))
            = IsGaugeField.adjointCoeff U p.1 c from rfl])
    rw [repCoeff_eq,
      show (colourWeakEnd ((jetGaugeMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))
          ∘ₗ gaugeAlgebraAction c
        = colourWeakEnd (((jetGaugeMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
              * actionMatrix c) from by
        rw [colourWeakEnd_mul]; rfl,
      hMact, colourWeakEnd_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, colourWeakEnd_mul, repCoeff_eq]
    rfl

end InfinitesimalAction

end QuarkDoublet

end StandardModel
