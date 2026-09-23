/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# Matrix representations of a jet gauge group

## i. Overview

A model-building table describes how a field transforms by a *matrix*: the jets of
gauge transformations act on the internal index `ι` of the field through a matrix of
jets `mat U`, the gauge algebra through a matrix of numbers `act c`, and the jets of the
gauge algebra through a matrix of jets `jetAct a`. This file packages such a matrix
representation as `LocalGaugeData.MatrixRep`, together with the two identities that make
`act` the infinitesimal action underlying `mat`: the *derivative identity*
`∂_μ (mat U) = -(jetAct (ω_μ U)) · mat U` in terms of the Maurer–Cartan form, and the
*equivariance identity* `mat U · jetAct c = jetAct (Ad_U c) · mat U`.

The internal index is tensored with a Lorentz representation `S`: the target space of
the field is `S ⊗ (ι → ℂ)`, and the jets of the field are identified with
`S ⊗ (ι → JetRing)`, on which `mat U` acts by matrix–vector multiplication. The main
theorem, `MatrixRep.isInfinitesimalActionOf`, shows that this action of the gauge algebra
is the infinitesimal action underlying the jet gauge action in the sense of
`LocalGaugeData.IsInfinitesimalActionOf`, once and for all matrix representations; the
compilation `MatrixRep.matterField` then produces a `MatterField`.

## ii. Key results

- `LocalGaugeData.MatrixRep` : a matrix representation of the jet gauge group with its
  infinitesimal action.
- `MatrixRep.jetEquiv` : the identification `JetRing ⊗ (S ⊗ (ι → ℂ)) ≃ S ⊗ (ι → JetRing)`.
- `MatrixRep.repJet`, `MatrixRep.repJet_smul` : the fibrewise jet gauge action.
- `MatrixRep.repCoeff_eq` : the base-point Taylor coefficients of the jet gauge action.
- `MatrixRep.isInfinitesimalActionOf` : the gauge-algebra action is the infinitesimal
  action underlying the jet gauge action.
- `MatrixRep.matterField` : the matter field of a matrix representation.
- `MatrixRep.matterField_gaugeLorentzCompatible` : its gauge and Lorentz actions commute,
  acting on different tensor factors.
- `MatrixRep.matterField_pureJetsActTrivially` : pure jets act trivially on it at the base
  point, when their matrices have identity constant term.

## iii. Table of contents

- A. Matrix representations
- B. The target space and its jets
- C. Endomorphisms from matrices
- D. The jet gauge action
- E. The base-point Taylor coefficients
- F. The infinitesimal action underlies the jet gauge action
- G. The matter field

-/

@[expose] public section

open TensorProduct MvPowerSeries MatrixGroups

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]

/-!

## A. Matrix representations

-/

/-- **A matrix representation** of the jets of gauge transformations on an internal index
  `ι`: the jets act by the matrix of jets `mat U`, the gauge algebra by the matrix `act c`,
  and the jets of the gauge algebra by the matrix of jets `jetAct a`, subject to the
  derivative identity and the equivariance identity that make `act` the infinitesimal
  action underlying `mat`. -/
structure MatrixRep (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) (ι : Type) [Fintype ι] [DecidableEq ι]
    where
  /-- The matrix of jets by which a jet of gauge transformations acts. -/
  mat : GJ → Matrix ι ι JetRing
  mat_one : mat 1 = 1
  mat_mul : ∀ U V, mat (U * V) = mat U * mat V
  /-- The matrix by which an element of the gauge algebra acts. -/
  act : 𝔤 →ₗ[ℝ] Matrix ι ι ℂ
  /-- The matrix of jets by which a jet of gauge algebra elements acts. -/
  jetAct : 𝔤J → Matrix ι ι JetRing
  jetAct_ofConstantLie : ∀ c, jetAct (jets.ofConstantLie c) = (act c).map (C : ℂ → JetRing)
  /-- The base-point Taylor coefficients of the jet action matrix are the action matrices
    of the base-point Taylor coefficients. -/
  jetAct_map_cc_foldl : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J),
    ((jetAct a).map fun f => constantCoeff (p.foldl (fun h ρ => pderiv ρ h) f))
      = act (jets.evalLie (jets.iteratedDeriv p a))
  /-- The derivative identity: the formal derivative of the matrix of a gauge jet is minus
    the jet action of its Maurer–Cartan form times the matrix. -/
  mat_map_pderiv : ∀ (U : GJ) (μ : Fin 1 ⊕ Fin 3),
    (mat U).map (fun f => pderiv μ f) = -(jetAct (jets.maurerCartan U μ) * mat U)
  /-- The equivariance identity: the matrix of a gauge jet intertwines the constant jet
    action with its adjoint transform. -/
  mat_mul_jetAct : ∀ (U : GJ) (c : 𝔤),
    mat U * jetAct (jets.ofConstantLie c)
      = jetAct (jets.adjoint U (jets.ofConstantLie c)) * mat U

namespace MatrixRep

variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {ι : Type}

/-!

## B. The target space and its jets

The target space of the field is `S ⊗ (ι → ℂ)` for a Lorentz representation `S`; its
jets `JetRing ⊗ (S ⊗ (ι → ℂ))` are identified with `S ⊗ (ι → JetRing)` by absorbing the
jet ring into the internal index.

-/

/-- The entrywise formal derivative on `ι → JetRing`, as a `ℂ`-linear map. -/
noncomputable def pderivPi (μ : Fin 1 ⊕ Fin 3) : (ι → JetRing) →ₗ[ℂ] (ι → JetRing) where
  toFun w i := pderiv μ (w i)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => Derivation.map_smul _ _ _

lemma pderivPi_apply (μ : Fin 1 ⊕ Fin 3) (w : ι → JetRing) (i : ι) :
    pderivPi μ w i = pderiv μ (w i) := rfl

/-- The entrywise iterated formal derivative on `ι → JetRing`, as a `ℂ`-linear map. -/
noncomputable def foldPi (x : Multiset (Fin 1 ⊕ Fin 3)) :
    (ι → JetRing) →ₗ[ℂ] (ι → JetRing) where
  toFun w i := x.foldl (fun h ρ => pderiv ρ h) (w i)
  map_add' v w := funext fun i => JetRing.foldl_pderiv_add x _ _
  map_smul' z v := funext fun i => by
    simp only [Pi.smul_apply, RingHom.id_apply]
    induction x using Multiset.induction_on generalizing v with
    | empty => rfl
    | cons ν t ih =>
      rw [Multiset.foldl_cons, Multiset.foldl_cons, Derivation.map_smul]
      exact ih (fun i => pderiv ν (v i))

lemma foldPi_apply (x : Multiset (Fin 1 ⊕ Fin 3)) (w : ι → JetRing) (i : ι) :
    foldPi x w i = x.foldl (fun h ρ => pderiv ρ h) (w i) := rfl

lemma foldPi_zero : foldPi (ι := ι) 0 = LinearMap.id := LinearMap.ext fun _ => rfl

lemma pderivPi_comp_foldPi (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    pderivPi (ι := ι) μ ∘ₗ foldPi x = foldPi (μ ::ₘ x) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  simp only [LinearMap.comp_apply, pderivPi_apply, foldPi_apply, Multiset.foldl_cons]
  exact (JetRing.foldl_pderiv_pderiv x μ (w i)).symm

/-- The entrywise base-point evaluation on `ι → JetRing`, as a `ℂ`-linear map. -/
noncomputable def ccPi : (ι → JetRing) →ₗ[ℂ] (ι → ℂ) where
  toFun w i := constantCoeff (w i)
  map_add' v w := funext fun i => map_add _ _ _
  map_smul' z v := funext fun i => by
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact constantCoeff_smul _ _

lemma ccPi_apply (w : ι → JetRing) (i : ι) : ccPi w i = constantCoeff (w i) := rfl

/-- The iterated formal derivative is `ℂ`-homogeneous. -/
lemma foldl_pderiv_smul (x : Multiset (Fin 1 ⊕ Fin 3)) (z : ℂ) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ρ h) (z • f)
      = z • x.foldl (fun h ρ => pderiv ρ h) f := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, Derivation.map_smul, ih, Multiset.foldl_cons]

/-- The iterated formal derivative of a negation. -/
lemma foldl_pderiv_neg (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ρ h) (-f)
      = -(x.foldl (fun h ρ => pderiv ρ h) f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_neg, ih, Multiset.foldl_cons]

/-- A constant jet times a jet is the scalar multiple. -/
lemma C_mul_eq_smul (z : ℂ) (f : JetRing) : (C z : JetRing) * f = z • f := by
  rw [Algebra.smul_def]
  rfl

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The base-point evaluation of the iterated derivative of a matrix–vector product with
  constant entries is the matrix–vector product of the base-point coefficients. -/
lemma ccPi_foldPi_mulVec (x : Multiset (Fin 1 ⊕ Fin 3)) (A : Matrix ι ι JetRing)
    (v : ι → ℂ) :
    ccPi (foldPi x (A.mulVec fun k => (C (v k) : JetRing)))
      = (A.map fun f => constantCoeff (x.foldl (fun h ρ => pderiv ρ h) f)).mulVec v := by
  funext j
  simp only [ccPi_apply, foldPi_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [JetRing.foldl_pderiv_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, C_mul_eq_smul, foldl_pderiv_smul, constantCoeff_smul, smul_eq_mul, mul_comm]

/-!

### The target space

The target space `V` of the field is any complex vector space identified, through `e`,
with `S ⊗ (ι → ℂ)` for a Lorentz representation `S`. Keeping `V` abstract (rather than
taking `V = S ⊗ (ι → ℂ)` itself) keeps the real-scalar structure on `V` the canonical
`Module.complexToReal`, and lets the concrete target spaces of a model serve as `V`.

-/

variable {S : Type} [AddCommGroup S] [Module ℂ S]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The jets of a `V`-valued field as `S ⊗ (ι → JetRing)`, through the identification
  `e : V ≃ S ⊗ (ι → ℂ)`: the jet ring is absorbed into the internal index. -/
noncomputable def jetEquiv (e : V ≃ₗ[ℂ] S ⊗[ℂ] (ι → ℂ)) :
    JetRing ⊗[ℂ] V ≃ₗ[ℂ] S ⊗[ℂ] (ι → JetRing) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) e).trans <|
    (TensorProduct.leftComm ℂ JetRing S (ι → ℂ)).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ S)
        ((TensorProduct.piScalarRight ℂ JetRing JetRing ι).restrictScalars ℂ)

variable (e : V ≃ₗ[ℂ] S ⊗[ℂ] (ι → ℂ))

lemma jetEquiv_tmul (f : JetRing) (s : S) (v : ι → ℂ) :
    jetEquiv e (f ⊗ₜ[ℂ] e.symm (s ⊗ₜ[ℂ] v)) = s ⊗ₜ[ℂ] (fun i => v i • f) := by
  simp [jetEquiv, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

omit [Fintype ι] [DecidableEq ι] in
/-- Induction on the jets of a `V`-valued field through the identification `e`. -/
lemma induction_on {P : JetRing ⊗[ℂ] V → Prop} (z : JetRing ⊗[ℂ] V)
    (zero : P 0)
    (tmul : ∀ (f : JetRing) (s : S) (v : ι → ℂ), P (f ⊗ₜ[ℂ] e.symm (s ⊗ₜ[ℂ] v)))
    (add : ∀ a b, P a → P b → P (a + b)) : P z := by
  induction z using TensorProduct.induction_on with
  | zero => exact zero
  | add a b ha hb => exact add a b ha hb
  | tmul f d =>
    obtain ⟨t, rfl⟩ : ∃ t, d = e.symm t := ⟨e d, (e.symm_apply_apply d).symm⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.tmul_zero]; exact zero
    | add a b ha hb => rw [map_add, TensorProduct.tmul_add]; exact add _ _ ha hb
    | tmul s v => exact tmul f s v

/-- The identification of jets intertwines the formal derivative with the entrywise
  derivative. -/
lemma jetEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (z : JetRing ⊗[ℂ] V) :
    jetEquiv e (jetDeriv μ z) = LinearMap.lTensor S (pderivPi μ) (jetEquiv e z) := by
  induction z using induction_on e with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f s v =>
    rw [jetDeriv_tmul, jetEquiv_tmul, jetEquiv_tmul, LinearMap.lTensor_tmul]
    congr 1
    funext i
    simp [pderivPi_apply, Derivation.map_smul]

/-- The identification of jets intertwines the iterated formal derivative with the
  entrywise iterated derivative. -/
lemma jetEquiv_jetIteratedDeriv (x : Multiset (Fin 1 ⊕ Fin 3)) (z : JetRing ⊗[ℂ] V) :
    jetEquiv e (jetIteratedDeriv x z) = LinearMap.lTensor S (foldPi x) (jetEquiv e z) := by
  induction x using Multiset.induction_on generalizing z with
  | empty => rw [jetIteratedDeriv_zero, LinearMap.id_apply, foldPi_zero, LinearMap.lTensor_id,
      LinearMap.id_apply]
  | cons μ t ih =>
    rw [jetIteratedDeriv_cons, LinearMap.comp_apply, jetEquiv_jetDeriv, ih,
      ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, pderivPi_comp_foldPi]

/-- The base-point evaluation of a jet through the identification. -/
lemma jetEval_eq (z : JetRing ⊗[ℂ] V) :
    jetEval z = e.symm (LinearMap.lTensor S ccPi (jetEquiv e z)) := by
  induction z using induction_on e with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f s v =>
    rw [jetEval_tmul, jetEquiv_tmul, LinearMap.lTensor_tmul,
      show ccPi (fun i => v i • f) = constantCoeff f • v from funext fun i => by
        simp [ccPi_apply, constantCoeff_smul, mul_comm],
      TensorProduct.tmul_smul, map_smul]

/-- Multiplication by a scalar jet through the identification. -/
lemma jetEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] V) :
    jetEquiv e (χ • z)
      = LinearMap.lTensor S ((LinearMap.lsmul JetRing (ι → JetRing) χ).restrictScalars ℂ)
          (jetEquiv e z) := by
  induction z using induction_on e with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, map_add]
  | tmul f s v =>
    rw [TensorProduct.smul_tmul', jetEquiv_tmul, jetEquiv_tmul, LinearMap.lTensor_tmul]
    congr 1
    funext i
    simp [smul_eq_mul]

/-- A jet of a constant through the identification. -/
lemma jetEquiv_jetOfConstant (s : S) (v : ι → ℂ) :
    jetEquiv e (jetOfConstant (e.symm (s ⊗ₜ[ℂ] v))) = s ⊗ₜ[ℂ] (fun i => C (v i)) := by
  rw [jetOfConstant_apply, jetEquiv_tmul]
  congr 1
  funext i
  rw [Algebra.smul_def, mul_one]
  rfl

/-!

## C. Endomorphisms from matrices

-/

/-- The endomorphism of the target space `V ≃ S ⊗ (ι → ℂ)` defined by a complex matrix on
  the internal index, as an algebra map. -/
noncomputable def valEndAlgHom : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ V :=
  (e.symm.conjAlgEquiv (R := ℂ)).toAlgHom.comp <|
    (Module.End.lTensorAlgHom ℂ (ι → ℂ) S).comp
      (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] Module.End ℂ (ι → ℂ)).toAlgHom

/-- The endomorphism of the target space `V ≃ S ⊗ (ι → ℂ)` defined by a complex matrix on
  the internal index, with the Lorentz factor untouched. -/
noncomputable def valEnd (B : Matrix ι ι ℂ) : V →ₗ[ℂ] V := valEndAlgHom e B

lemma valEnd_apply (B : Matrix ι ι ℂ) (d : V) :
    valEnd e B d = e.symm (LinearMap.lTensor S (Matrix.toLin' B) (e d)) := rfl

lemma valEnd_apply_symm_tmul (B : Matrix ι ι ℂ) (s : S) (v : ι → ℂ) :
    valEnd e B (e.symm (s ⊗ₜ[ℂ] v)) = e.symm (s ⊗ₜ[ℂ] (B.mulVec v)) := by
  rw [valEnd_apply, LinearEquiv.apply_symm_apply, LinearMap.lTensor_tmul, Matrix.toLin'_apply]

lemma valEnd_add (A B : Matrix ι ι ℂ) : valEnd e (A + B) = valEnd e A + valEnd e B :=
  map_add (valEndAlgHom e) A B

lemma valEnd_smul (z : ℂ) (A : Matrix ι ι ℂ) : valEnd e (z • A) = z • valEnd e A :=
  map_smul (valEndAlgHom e) z A

lemma valEnd_zero : valEnd e (0 : Matrix ι ι ℂ) = 0 := map_zero (valEndAlgHom e)

lemma valEnd_neg (A : Matrix ι ι ℂ) : valEnd e (-A) = -valEnd e A :=
  map_neg (valEndAlgHom e) A

lemma valEnd_multiset_sum (m : Multiset (Matrix ι ι ℂ)) :
    valEnd e m.sum = (m.map (valEnd e)).sum :=
  map_multiset_sum (valEndAlgHom e) m

lemma valEnd_mul (A B : Matrix ι ι ℂ) : valEnd e (A * B) = valEnd e A ∘ₗ valEnd e B :=
  map_mul (valEndAlgHom e) A B

lemma valEnd_one : valEnd e (1 : Matrix ι ι ℂ) = LinearMap.id := map_one (valEndAlgHom e)

variable (S) in
/-- The endomorphism of `S ⊗ (ι → JetRing)` defined by a matrix of jets on the internal
  index. -/
noncomputable def jetEnd (A : Matrix ι ι JetRing) :
    S ⊗[ℂ] (ι → JetRing) →ₗ[ℂ] S ⊗[ℂ] (ι → JetRing) :=
  Module.End.lTensorAlgHom ℂ (ι → JetRing) S
    ((Matrix.toLinAlgEquiv' A : Module.End JetRing (ι → JetRing)).restrictScalars ℂ)

lemma jetEnd_eq_lTensor (A : Matrix ι ι JetRing) :
    jetEnd S A = LinearMap.lTensor S
      ((Matrix.toLinAlgEquiv' A : Module.End JetRing (ι → JetRing)).restrictScalars ℂ) := rfl

lemma jetEnd_tmul (A : Matrix ι ι JetRing) (s : S) (w : ι → JetRing) :
    jetEnd S A (s ⊗ₜ[ℂ] w) = s ⊗ₜ[ℂ] (A.mulVec w) := by
  rw [jetEnd_eq_lTensor, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply,
    Matrix.toLinAlgEquiv'_apply]

lemma jetEnd_one : jetEnd S (1 : Matrix ι ι JetRing) = LinearMap.id := by
  rw [jetEnd, map_one,
    show ((1 : Module.End JetRing (ι → JetRing)).restrictScalars ℂ) = 1 from rfl, map_one]
  rfl

lemma jetEnd_mul (A B : Matrix ι ι JetRing) : jetEnd S (A * B) = jetEnd S A ∘ₗ jetEnd S B := by
  rw [jetEnd, jetEnd, jetEnd, map_mul,
    show ((Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' B :
        Module.End JetRing (ι → JetRing)).restrictScalars ℂ)
      = (Matrix.toLinAlgEquiv' A : Module.End JetRing (ι → JetRing)).restrictScalars ℂ
        * (Matrix.toLinAlgEquiv' B : Module.End JetRing (ι → JetRing)).restrictScalars ℂ from rfl,
    map_mul]
  rfl

/-- The endomorphism of the jets `JetRing ⊗ V` of the field defined by a matrix of jets
  on the internal index, through `jetEquiv`. -/
noncomputable def matEnd (A : Matrix ι ι JetRing) : JetRing ⊗[ℂ] V →ₗ[ℂ] JetRing ⊗[ℂ] V :=
  (jetEquiv e).symm.toLinearMap ∘ₗ jetEnd S A ∘ₗ (jetEquiv e).toLinearMap

lemma matEnd_apply (A : Matrix ι ι JetRing) (z : JetRing ⊗[ℂ] V) :
    matEnd e A z = (jetEquiv e).symm (jetEnd S A (jetEquiv e z)) := rfl

lemma matEnd_one : matEnd e (1 : Matrix ι ι JetRing) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  rw [matEnd_apply, jetEnd_one, LinearMap.id_apply, LinearEquiv.symm_apply_apply,
    LinearMap.id_apply]

lemma matEnd_mul (A B : Matrix ι ι JetRing) :
    matEnd e (A * B) = matEnd e A ∘ₗ matEnd e B := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, matEnd_apply, matEnd_apply, matEnd_apply, jetEnd_mul,
    LinearEquiv.apply_symm_apply, LinearMap.comp_apply]

/-- The matrix endomorphisms are fibrewise: they commute with multiplication by scalar
  jets. -/
lemma matEnd_smul (A : Matrix ι ι JetRing) (χ : JetRing) (z : JetRing ⊗[ℂ] V) :
    matEnd e A (χ • z) = χ • matEnd e A z := by
  apply (jetEquiv e).injective
  rw [matEnd_apply, LinearEquiv.apply_symm_apply, jetEquiv_smul, jetEquiv_smul, matEnd_apply,
    LinearEquiv.apply_symm_apply, jetEnd_eq_lTensor, ← LinearMap.comp_apply,
    ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]
  congr 2
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
    Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_smul]

/-!

## D. The jet gauge action

-/

variable (R : MatrixRep jets ι)

/-- **The jet gauge action** of a matrix representation on the jets of a `V`-valued
  field: the matrix of jets acts on the internal index by matrix–vector multiplication,
  with the Lorentz factor untouched. -/
noncomputable def repJet : Representation ℂ GJ (JetRing ⊗[ℂ] V) where
  toFun U := matEnd e (R.mat U)
  map_one' := by rw [R.mat_one, matEnd_one]; rfl
  map_mul' U V := by rw [R.mat_mul, matEnd_mul]; rfl

lemma repJet_apply (U : GJ) : R.repJet e U = matEnd e (R.mat U) := rfl

/-- **The jet gauge action is fibrewise**: it commutes with multiplication by scalar
  jets. -/
lemma repJet_smul (U : GJ) (χ : JetRing) (z : JetRing ⊗[ℂ] V) :
    R.repJet e U (χ • z) = χ • R.repJet e U z := by
  rw [repJet_apply, matEnd_smul]

/-- **The action of the gauge algebra** of a matrix representation on the target space
  `V ≃ S ⊗ (ι → ℂ)`: the action matrix acts on the internal index, real-linearly in the
  algebra slot and complex-linearly in the value slot. -/
noncomputable def repAlgebra : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V where
  toFun c := valEnd e (R.act c)
  map_add' c₁ c₂ := by rw [map_add, valEnd_add]
  map_smul' r c := by
    rw [map_smul, ← algebraMap_smul ℂ r (R.act c), valEnd_smul, RingHom.id_apply]
    refine LinearMap.ext fun v => ?_
    show (algebraMap ℝ ℂ r) • valEnd e (R.act c) v = r • valEnd e (R.act c) v
    rw [algebraMap_smul]

lemma repAlgebra_apply (c : 𝔤) : R.repAlgebra e c = valEnd e (R.act c) := rfl

/-!

## E. The base-point Taylor coefficients

-/

/-- **The base-point Taylor coefficients of the jet gauge action** are the endomorphisms
  of the base-point Taylor coefficients of the matrix of jets. -/
lemma repCoeff_eq (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeAlgebraRealization.repCoeff (R.repJet e) U x
      = valEnd e ((R.mat U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ρ h) f)) := by
  refine LinearMap.ext fun d => ?_
  obtain ⟨t, rfl⟩ : ∃ t, d = e.symm t := ⟨e d, (e.symm_apply_apply d).symm⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul s v =>
    rw [show GaugeAlgebraRealization.repCoeff (R.repJet e) U x (e.symm (s ⊗ₜ[ℂ] v))
        = jetEval (jetIteratedDeriv x (R.repJet e U (jetOfConstant (e.symm (s ⊗ₜ[ℂ] v)))))
        from rfl,
      jetEval_eq e, jetEquiv_jetIteratedDeriv, repJet_apply, matEnd_apply,
      LinearEquiv.apply_symm_apply, jetEquiv_jetOfConstant, jetEnd_tmul,
      LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, valEnd_apply_symm_tmul,
      ccPi_foldPi_mulVec]

/-!

## F. The infinitesimal action underlies the jet gauge action

-/

set_option maxHeartbeats 1000000 in
/-- **The action of the gauge algebra of a matrix representation is the infinitesimal
  action underlying its jet gauge action**: the base-point Taylor coefficients obey the
  Maurer–Cartan Leibniz law and intertwine the action with the adjoint transports. -/
theorem isInfinitesimalActionOf :
    jets.IsInfinitesimalActionOf (R.repAlgebra e) (R.repJet e) := by
  constructor
  · intro U μ x
    have hMcons : ((R.mat U).map fun f =>
        constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ρ h) f))
        = -((x.antidiagonal.map fun p =>
            R.act (jets.evalLie (jets.iteratedDeriv p.1 (jets.maurerCartan U μ)))
            * ((R.mat U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ρ h) f))).sum) := by
      rw [show ((R.mat U).map fun f =>
            constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ρ h) f))
          = (((R.mat U).map fun f => pderiv μ f).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, Multiset.foldl_cons],
        R.mat_map_pderiv,
        Matrix.map_neg _ (fun f => by rw [foldl_pderiv_neg, map_neg]),
        JetRing.matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
        fun p hp => by rw [R.jetAct_map_cc_foldl]))
    rw [repCoeff_eq, hMcons, valEnd_neg, valEnd_multiset_sum, Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
      fun p hp => ?_))
    rw [Function.comp_apply, valEnd_mul, repCoeff_eq]
    rfl
  · intro U x c
    have hcollapse : ∀ (m : Multiset (Fin 1 ⊕ Fin 3)),
        (((R.act c).map (C : ℂ → JetRing)).map fun f =>
          constantCoeff (m.foldl (fun h ρ => pderiv ρ h) f))
        = if m = 0 then R.act c else 0 := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply, constantCoeff_C]
      · refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply, JetRing.foldl_pderiv_C_of_ne_zero hm, hm]
    have hMact : ((R.mat U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ρ h) f)) * R.act c
        = (x.antidiagonal.map fun p =>
            R.act (jets.adjointCoeff U p.1 c)
            * ((R.mat U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ρ h) f))).sum := by
      have h1 : ((R.mat U * R.jetAct (jets.ofConstantLie c)).map
            fun f => constantCoeff (x.foldl (fun h ρ => pderiv ρ h) f))
          = ((R.mat U).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ρ h) f)) * R.act c := by
        rw [R.jetAct_ofConstantLie, JetRing.matrix_constantCoeff_foldl_pderiv_mul,
          Multiset.map_congr rfl (fun p hp => by rw [hcollapse p.2]),
          Multiset.sum_antidiagonal_eq_of_snd_ne_zero x
            (fun p => ((R.mat U).map fun f =>
              constantCoeff (p.1.foldl (fun h ρ => pderiv ρ h) f)) *
                (if p.2 = 0 then R.act c else 0))
            (fun p _ hp => by rw [ite_eq_right hp, Matrix.mul_zero]),
          ite_eq_left rfl]
      rw [← h1, R.mat_mul_jetAct, JetRing.matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
        rw [R.jetAct_map_cc_foldl, jets.adjointCoeff_apply])
    rw [repCoeff_eq, repAlgebra_apply, ← valEnd_mul, hMact, valEnd_multiset_sum,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, valEnd_mul, repCoeff_eq]
    rfl

/-!

## G. The matter field

-/

/-- The Lorentz action on the target space `V ≃ S ⊗ (ι → ℂ)`: the given action on the
  Lorentz factor `S`, transported through `e`. -/
noncomputable def repLorentz (ρ : Representation ℂ SL(2,ℂ) S) :
    Representation ℂ SL(2,ℂ) V :=
  (MonoidHomClass.toMonoidHom (e.symm.conjAlgEquiv (R := ℂ))).comp
    (ρ.tprod (Representation.trivial ℂ SL(2,ℂ) (ι → ℂ)))

/-!

### The global action

A matrix representation of jets restricts to the jets of constant gauge transformations;
the constant terms of their matrices are the matrices of a representation of the global
gauge group on the target space. When the matrices of constant jets are constant, the jet
action on a constant jet is this global action on the value factor.

-/

section Global

/-- **The global gauge action** of a matrix representation of jets: a global gauge
  transformation acts by the constant term of the matrix of its constant jet. -/
noncomputable def repGlobal : Representation ℂ G₀ V where
  toFun g := valEnd e ((R.mat (jets.ofConstant g)).map (constantCoeff : JetRing → ℂ))
  map_one' := by
    rw [map_one jets.ofConstant, R.mat_one,
      ← RingHom.mapMatrix_apply (constantCoeff : JetRing →+* ℂ), map_one, valEnd_one]
    rfl
  map_mul' g h := by
    rw [map_mul jets.ofConstant, R.mat_mul,
      ← RingHom.mapMatrix_apply (constantCoeff : JetRing →+* ℂ), map_mul,
      RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, valEnd_mul]
    rfl

lemma repGlobal_apply (g : G₀) :
    R.repGlobal e g = valEnd e ((R.mat (jets.ofConstant g)).map (constantCoeff : JetRing → ℂ)) :=
  rfl

/-- The global action on a pure tensor: the constant term of the matrix acts on the
  internal index. -/
lemma repGlobal_apply_symm_tmul (g : G₀) (s : S) (v : ι → ℂ) :
    R.repGlobal e g (e.symm (s ⊗ₜ[ℂ] v))
      = e.symm (s ⊗ₜ[ℂ] ((R.mat (jets.ofConstant g)).map (constantCoeff : JetRing → ℂ)).mulVec v) :=
  valEnd_apply_symm_tmul e _ s v

omit [DecidableEq ι] in
/-- A matrix of constant jets acts on a scalar jet times a constant vector through its
  constant matrix. -/
lemma map_C_mulVec_smul (B : Matrix ι ι ℂ) (v : ι → ℂ) (χ : JetRing) :
    (B.map (C : ℂ → JetRing)).mulVec (fun i => v i • χ) = fun i => (B.mulVec v) i • χ := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, C_mul_eq_smul,
    smul_smul]

/-- **On jets of constant gauge transformations the jet action is the global action** on
  the value factor, provided the matrices of constant jets are constant. -/
lemma repJet_ofConstant
    (hconst : ∀ g, R.mat (jets.ofConstant g)
      = ((R.mat (jets.ofConstant g)).map (constantCoeff : JetRing → ℂ)).map (C : ℂ → JetRing))
    (g : G₀) :
    R.repJet e (jets.ofConstant g) = TensorProduct.map LinearMap.id (R.repGlobal e g) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul χ v =>
    obtain ⟨t, rfl⟩ := e.symm.surjective v
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [repJet_apply, matEnd_apply, jetEquiv_tmul, jetEnd_tmul, hconst, map_C_mulVec_smul,
        ← jetEquiv_tmul e, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, repGlobal_apply_symm_tmul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end Global

variable [Module.Free ℂ V] [Module.Finite ℂ V]

/-- **The matter field of a matrix representation**: the target space `V ≃ S ⊗ (ι → ℂ)`
  with the Lorentz action on `S`, the jet gauge action of the matrix representation, and
  the given mass weight. -/
noncomputable def matterField (ρ : Representation ℂ SL(2,ℂ) S) (w : ℕ) :
    MatterField jets where
  V := V
  repLorentz := repLorentz e ρ
  repJet := R.repJet e
  repAlgebra := R.repAlgebra e
  repJet_smul := R.repJet_smul e
  repAlgebra_isInfinitesimalAction := R.isInfinitesimalActionOf e
  massWeight := w

variable (ρ : Representation ℂ SL(2,ℂ) S) (w : ℕ)

@[simp]
lemma matterField_V : (R.matterField e ρ w).V = V := rfl

@[simp]
lemma matterField_repLorentz : (R.matterField e ρ w).repLorentz = repLorentz e ρ := rfl

@[simp]
lemma matterField_repJet : (R.matterField e ρ w).repJet = R.repJet e := rfl

@[simp]
lemma matterField_repAlgebra : (R.matterField e ρ w).repAlgebra = R.repAlgebra e := rfl

@[simp]
lemma matterField_massWeight : (R.matterField e ρ w).massWeight = w := rfl

omit [Fintype ι] [DecidableEq ι] [Module.Free ℂ V] [Module.Finite ℂ V] in
lemma repLorentz_apply_symm_tmul (Λ : SL(2,ℂ)) (s : S) (v : ι → ℂ) :
    repLorentz e ρ Λ (e.symm (s ⊗ₜ[ℂ] v)) = e.symm (ρ Λ s ⊗ₜ[ℂ] v) := by
  simp [repLorentz, Representation.tprod_apply]

omit [Module.Free ℂ V] [Module.Finite ℂ V] in
/-- The gauge algebra acts on the internal index and the Lorentz group on the Lorentz
  factor, so the two actions commute. -/
lemma repAlgebra_comm_repLorentz (c : 𝔤) (Λ : SL(2,ℂ)) (v : V) :
    R.repAlgebra e c (repLorentz e ρ Λ v) = repLorentz e ρ Λ (R.repAlgebra e c v) := by
  obtain ⟨t, rfl⟩ : ∃ t, v = e.symm t := ⟨e v, (e.symm_apply_apply v).symm⟩
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, map_add]
  | tmul s w =>
    rw [repAlgebra_apply, repLorentz_apply_symm_tmul, valEnd_apply_symm_tmul,
      valEnd_apply_symm_tmul, repLorentz_apply_symm_tmul]

/-- The matter field of a matrix representation satisfies `MatterField.GaugeLorentzCompatible`,
  for every matrix representation and Lorentz factor: the two actions live on different
  tensor factors. -/
lemma matterField_gaugeLorentzCompatible : (R.matterField e ρ w).GaugeLorentzCompatible :=
  fun c Λ v => repAlgebra_comm_repLorentz e R ρ c Λ v

/-- The matter field of a matrix representation satisfies `MatterField.PureJetsActTrivially`
  as soon as the matrix of every jet with trivial value has identity constant term. This
  hypothesis is not a consequence of the axioms of `MatrixRep`, which fix the constant term
  of `mat` on pure jets only up to a scalar character. -/
lemma matterField_pureJetsActTrivially
    (hmat : ∀ {W : GJ}, jets.eval W = 1 → (R.mat W).map (constantCoeff : JetRing → ℂ) = 1) :
    (R.matterField e ρ w).PureJetsActTrivially := by
  intro W hW
  show GaugeAlgebraRealization.repCoeff (R.repJet e) W 0 = LinearMap.id
  rw [repCoeff_eq]
  simp only [Multiset.foldl_zero]
  rw [hmat hW, valEnd_one]

end MatrixRep

end LocalGaugeData
