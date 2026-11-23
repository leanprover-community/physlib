/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.Compact
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Exponential
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.HolomorphicPart
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Triple
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.DerivRep
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Topology.Algebra.Group.Matrix
public import Physlib.Mathematics.ForMathlib.DataStructures.Matrix.LieTrace
/-!
# Reynolds elements for SL(2, ℂ)

A continuous finite-dimensional representation of `SL(2, ℂ)` has a Reynolds element.

## i. Overview

Let `ρ` be a representation of `SL(2, ℂ)`, the double cover of the proper orthochronous Lorentz
group, and `W` a finite-dimensional subrepresentation on which `ρ` is continuous. We show that
`ρ` has a Reynolds element on `W`. This is an element of the group algebra whose coefficients sum
to one and which projects `W` onto its invariant vectors. Unlike for a compact group, there is no
Haar average, and the projection is built from Casimir operators instead.

The group `SL(2, ℂ)` is realized as the global gauge group `GlobalGaugeGroup.SL 2`, the closed
subgroup of `GL(2, ℂ)` of matrices of determinant one. The continuous representation on `W`
differentiates to a real Lie algebra representation `dρ`. We extend it to all `2 × 2` matrices
through their traceless part. Its holomorphic and antiholomorphic parts
`X_L = (dρ X - i dρ (i X)) / 2` and `X_R = (dρ X + i dρ (i X)) / 2` are two commuting complex
representations of `sl₂`, with `dρ X = X_L + X_R`.

Let `C_L` and `C_R` be the Casimirs of the two `sl₂` actions, and `q_L`, `q_R` polynomials with
constant term one such that `q_L(C_L)` and `q_R(C_R)` project onto the generalized kernels of the
Casimirs. Then `P = q_L(C_L) q_R(C_R)` maps `W` into the joint generalized kernel. There both
`sl₂` actions vanish, so `dρ` vanishes, and `P w` is fixed by every exponential `exp X`. These
generate `SL(2, ℂ)`, since every matrix of determinant one is a product of transvections and a
diagonal matrix of determinant one, each of which is an exponential of a traceless matrix.

The general mathematics used here lives in `PhyslibAlpha.Mathematics.RepresentationTheory.Sl2`.
The generation by exponentials is in `Sl2.Exponential`, the holomorphic and antiholomorphic parts
in `Sl2.HolomorphicPart`, and the standard triple with its Casimir in `Sl2.Triple` and
`Sl2.Casimir`.

Finally `P` lies in `1 + span {ρ g - 1}`. The span of the operators `ρ g - 1` is closed under
products and, being finite-dimensional, closed. It therefore contains each `dρ X`, as the limit of
`(ρ (exp (t X)) - 1) / t`, and every polynomial in the `dρ X` without constant term. So `P` comes
from a Reynolds element.

## ii. Key results

- `GlobalGaugeGroup.SL` : the global gauge group `SL(n, ℂ)`.
- `GlobalGaugeGroup.SL.exists_sub_one_mem_span` : an operator in `1 + span {ρ g - 1}` with image
  in the invariants, for a continuous finite-dimensional representation of `SL(2, ℂ)`.
- `Representation.exists_isReynolds_of_specialLinearGroup` : a representation of `SL(2, ℂ)`
  continuous on a finite-dimensional subrepresentation has a Reynolds element on it.

## iii. Table of contents

- A. The global gauge group SL(n, ℂ)
- B. The span of the operators ρ g - 1
  - B.1. Products and polynomials
  - B.2. Derivatives
- C. Representations of SL(2, ℂ)
  - C.1. The derivative on all matrices
  - C.2. Generation by exponentials
  - C.3. The projection onto the invariants
- D. Reynolds elements for SL(2, ℂ)

## iv. References

- B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).
- J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*.

-/

@[expose] public section

open Matrix NormedSpace Polynomial Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

## A. The global gauge group SL(n, ℂ)

-/

namespace GlobalGaugeGroup

/-- The global gauge group `SL(n, ℂ)`, the complex `n × n` matrices of determinant one. -/
def SL (n : ℕ) : GlobalGaugeGroup (Fin n) where
  group := GeneralLinearGroup.det.ker
  isClosed := by
    have h : ((GeneralLinearGroup.det.ker : Subgroup (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ)) =
        (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det) ⁻¹' {1} := by
      ext g
      simp [Units.ext_iff]
    rw [h]
    exact isClosed_singleton.preimage (Units.continuous_val.matrix_det)

/-- An invertible matrix lies in `SL(n, ℂ)` exactly when it has determinant one. -/
lemma mem_SL_iff {n : ℕ} {g : GL (Fin n) ℂ} :
    g ∈ (SL n).group ↔ (g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  simp [SL, Units.ext_iff]

/-- A traceless matrix is a generator of `SL(n, ℂ)`, since `det (exp (t X)) = exp (t tr X) = 1`. -/
lemma mem_lieAlgebra_SL {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (htr : X.trace = 0) :
    X ∈ (SL n).lieAlgebra := by
  intro t
  have hdet : (exp (t • X)).det = 1 := by
    rw [Matrix.det_exp, trace_smul, htr, smul_zero, exp_zero]
  exact ⟨⟨(isUnit_exp (t • X)).unit, mem_SL_iff.2 hdet⟩, rfl⟩

/-- A traceless matrix lies in the Lie algebra of `SL(n, ℂ)`. -/
lemma mem_lieSubalgebra_SL {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (htr : X.trace = 0) :
    X ∈ (SL n).lieSubalgebra :=
  mem_lieAlgebra_SL htr

/-- The elements of `SL(n, ℂ)` as a global gauge group are those of Mathlib's special linear
group. -/
noncomputable def SL.toSpecialLinearGroup (n : ℕ) :
    (SL n).group ≃* SpecialLinearGroup (Fin n) ℂ where
  toFun g := ⟨g.1.1, mem_SL_iff.1 g.2⟩
  invFun g := ⟨⟨g.1, (g⁻¹ : SpecialLinearGroup (Fin n) ℂ).1,
    congrArg Subtype.val (mul_inv_cancel g), congrArg Subtype.val (inv_mul_cancel g)⟩,
    mem_SL_iff.2 g.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The identification of the two forms of `SL(n, ℂ)` is continuous. -/
lemma continuous_SL_toSpecialLinearGroup (n : ℕ) : Continuous (SL.toSpecialLinearGroup n) :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

end GlobalGaugeGroup

/-!

## B. The span of the operators ρ g - 1

### B.1. Products and polynomials

-/

namespace Submodule

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- The span of `σ h - 1`, for a monoid homomorphism `σ` into an algebra, is closed under
multiplication, since `(σ g - 1) (σ h - 1) = (σ (g h) - 1) - (σ g - 1) - (σ h - 1)`. -/
lemma mul_mem_span_sub_one {H : Type*} [Monoid H] (σ : H →* A) {a b : A}
    (ha : a ∈ span K (Set.range fun h => σ h - 1)) (hb : b ∈ span K (Set.range fun h => σ h - 1)) :
    a * b ∈ span K (Set.range fun h => σ h - 1) := by
  have hle : span K (Set.range fun h => σ h - 1) * span K (Set.range fun h => σ h - 1) ≤
      span K (Set.range fun h => σ h - 1) := by
    rw [span_mul_span]
    refine span_le.2 ?_
    rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
    have e : (σ g - 1) * (σ h - 1) = (σ (g * h) - 1) - (σ g - 1) - (σ h - 1) := by
      rw [map_mul]; noncomm_ring
    change (σ g - 1) * (σ h - 1) ∈ _
    rw [e]
    exact sub_mem (sub_mem (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩)) (subset_span ⟨_, rfl⟩)
  exact hle (mul_mem_mul ha hb)

/-- In a subspace closed under multiplication, a polynomial in an element `x` of it differs from
its constant term by an element of it. -/
lemma aeval_sub_algebraMap_coeff_zero_mem {S : Submodule K A}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {x : A} (hx : x ∈ S) (q : K[X]) :
    aeval x q - algebraMap K A (q.coeff 0) ∈ S := by
  have hpow (i : ℕ) : x ^ (i + 1) ∈ S := by
    induction i with
    | zero => simpa using hx
    | succ i ih => rw [pow_succ]; exact hS _ ih _ hx
  rw [aeval_eq_sum_range, Finset.sum_range_succ', pow_zero, Algebra.algebraMap_eq_smul_one,
    add_sub_cancel_right]
  exact sum_mem fun i _ => smul_mem _ _ (hpow i)

end Submodule

namespace Commute

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- An element commuting with `b` commutes with every polynomial in `b`. -/
lemma aeval_right {a b : A} (h : Commute a b) (p : K[X]) : Commute a (aeval b p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c a).mul_right (h.pow_right n)

end Commute

/-!

### B.2. Derivatives

-/

namespace Submodule

/-- A closed subspace containing every difference `f t - f 0` contains the derivative of `f`
at `0`, the limit of the difference quotients. -/
lemma mem_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Submodule ℂ E} (hS : IsClosed (S : Set E)) {f : ℝ → E} {f' : E}
    (hf : HasDerivAt f f' 0) (hmem : ∀ t, f t - f 0 ∈ S) : f' ∈ S := by
  refine hS.mem_of_tendsto hf.tendsto_slope_zero (Eventually.of_forall fun t => ?_)
  simpa using S.smul_of_tower_mem t⁻¹ (hmem t)

end Submodule

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : G.group →ₜ* (W →L[ℂ] W)ˣ)

/-- The derivative of a representation along a generator lies in the span of the operators
`ρ g - 1`, as the limit of the difference quotients `(ρ (exp (t X)) - 1) / t`. -/
lemma derivRep_mem_span (X : G.lieSubalgebra) :
    derivRep ρ X ∈
      Submodule.span ℂ (Set.range fun g => ((ρ g : (W →L[ℂ] W)ˣ) : W →L[ℂ] W) - 1) := by
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  let X' : G.lieAlgebra := ⟨X.1, X.2⟩
  refine Submodule.mem_of_hasDerivAt (Submodule.isClosed_of_finiteDimensional _)
    (f := fun t => ((ρ (G.oneParameterSubgroup X' t) : (W →L[ℂ] W)ˣ) : W →L[ℂ] W)) ?_
    fun t => by
      simp only [oneParameterSubgroup_zero, map_one, Units.val_one]
      exact Submodule.subset_span (Set.mem_range_self _)
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (derivRep ρ X) (0 : ℝ)
  simp only [zero_smul, exp_zero] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact derivRep_oneParameterSubgroup ρ X' t

end GlobalGaugeGroup

/-!

## C. Representations of SL(2, ℂ)

### C.1. The derivative on all matrices

-/

namespace GlobalGaugeGroup

/-- The traceless part `X - (tr X / 2) 1` of a `2 × 2` complex matrix, as a homomorphism of real
Lie algebras into the Lie algebra of `SL(2, ℂ)`. -/
noncomputable def SL.tracelessPart : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℝ⁆ (SL 2).lieSubalgebra where
  toFun X := ⟨X - (X.trace / 2) • 1, mem_lieSubalgebra_SL (by simp [trace_sub])⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [trace_add, add_div, add_smul, AddMemClass.coe_add]
    abel
  map_smul' r X := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, trace_smul]
    rw [smul_sub, smul_div_assoc, smul_assoc]
  map_lie' {X Y} := by
    apply Subtype.ext
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, trace_sub, trace_mul_comm X Y, sub_self,
      zero_div, zero_smul, sub_zero, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one]
    module

/-- The traceless part of a traceless matrix is the matrix itself. -/
lemma SL.tracelessPart_of_trace_eq_zero {X : Matrix (Fin 2) (Fin 2) ℂ} (htr : X.trace = 0) :
    SL.tracelessPart X = ⟨X, mem_lieSubalgebra_SL htr⟩ :=
  Subtype.ext <| by simp [SL.tracelessPart, htr]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : (SL 2).group →ₜ* (E →L[ℂ] E)ˣ)

/-- The derivative of a continuous representation of `SL(2, ℂ)`, extended to all `2 × 2` complex
matrices through their traceless part. -/
noncomputable def SL.derivRepMatrix : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℝ⁆ E →L[ℂ] E :=
  (derivRep ρ).comp SL.tracelessPart

/-- The derivative lies in the span of the operators `ρ g - 1`. -/
lemma SL.derivRepMatrix_mem_span (X : Matrix (Fin 2) (Fin 2) ℂ) :
    SL.derivRepMatrix ρ X ∈
      Submodule.span ℂ (Set.range fun g => ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) - 1) :=
  derivRep_mem_span ρ _

/-- The representation maps `exp X`, for a traceless `X`, to `exp (dρ X)`. -/
lemma SL.apply_eq_exp_derivRepMatrix {g : (SL 2).group} {X : Matrix (Fin 2) (Fin 2) ℂ}
    (htr : X.trace = 0) (hg : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = exp X) :
    ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) = exp (SL.derivRepMatrix ρ X) := by
  rw [SL.derivRepMatrix, LieHom.comp_apply, SL.tracelessPart_of_trace_eq_zero htr,
    ← one_smul ℝ (derivRep ρ _)]
  exact apply_eq_exp_derivRep ρ (by rw [one_smul]; exact hg)

/-!

### C.2. Generation by exponentials

-/

/-- An induction principle for `SL(2, ℂ)`. A property of group elements which holds for every
exponential of a traceless matrix and is stable under products holds for every element. -/
lemma SL.induction {p : (SL 2).group → Prop}
    (hexp : ∀ (g : (SL 2).group) (X : Matrix (Fin 2) (Fin 2) ℂ), X.trace = 0 →
      ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = exp X → p g)
    (hmul : ∀ g h, p g → p h → p (g * h)) (g : (SL 2).group) : p g := by
  let e := SL.toSpecialLinearGroup 2
  have key (A : Matrix (Fin 2) (Fin 2) ℂ)
      (hA : A ∈ Submonoid.closure {A | ∃ X : Matrix (Fin 2) (Fin 2) ℂ, X.trace = 0 ∧ exp X = A}) :
      A.det = 1 ∧
        ∀ g : (SL 2).group, ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A → p g := by
    induction hA using Submonoid.closure_induction with
    | mem A hA =>
      obtain ⟨X, htr, rfl⟩ := hA
      exact ⟨by rw [det_exp, htr, exp_zero], fun g hg => hexp g X htr hg⟩
    | one => exact ⟨det_one, fun g hg => hexp g 0 (trace_zero _ _) (by rw [hg, exp_zero])⟩
    | mul A B _ _ hA hB =>
      refine ⟨by rw [det_mul, hA.1, hB.1, one_mul], fun g hg => ?_⟩
      have hg' : g = e.symm ⟨A, hA.1⟩ * e.symm ⟨B, hB.1⟩ := Subtype.ext (Units.ext hg)
      rw [hg']
      exact hmul _ _ (hA.2 _ rfl) (hB.2 _ rfl)
  exact (key _ (mem_closure_exp_of_det_eq_one (mem_SL_iff.1 g.2))).2 g rfl

/-!

### C.3. The projection onto the invariants

-/

/-- The algebra isomorphism from the continuous linear maps on `E` to its linear maps. -/
local notation "ψ" => AlgEquiv.symm (Module.End.toContinuousLinearMap E)

/-- A vector killed by the holomorphic and antiholomorphic images of the standard `sl₂` triple is
invariant under the representation. -/
lemma SL.apply_eq_self_of_sl2 {w : E}
    (hL : ∀ X ∈ ({sl2E, sl2F, sl2H} : Set (Matrix (Fin 2) (Fin 2) ℂ)),
      (SL.derivRepMatrix ρ).holPart X w = 0)
    (hR : ∀ X ∈ ({sl2E, sl2F, sl2H} : Set (Matrix (Fin 2) (Fin 2) ℂ)),
      (SL.derivRepMatrix ρ).antiholPart X w = 0) (g : (SL 2).group) :
    ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) w = w := by
  set D := SL.derivRepMatrix ρ
  have hD {X : Matrix (Fin 2) (Fin 2) ℂ} (htr : X.trace = 0) : D X w = 0 := by
    have h1 := Matrix.apply_eq_zero_of_sl2 (φ := fun X => ψ (D.holPart X))
      (fun X Y => by simp [D.holPart_add]) (fun c X => ⟨c, by simp [D.holPart_smul]⟩)
      (hL _ (by simp)) (hL _ (by simp)) (hL _ (by simp)) htr
    have h2 := Matrix.apply_eq_zero_of_sl2 (φ := fun X => ψ (D.antiholPart X))
      (fun X Y => by simp [D.antiholPart_add])
      (fun c X => ⟨starRingEnd ℂ c, by simp [D.antiholPart_smul]⟩)
      (hR _ (by simp)) (hR _ (by simp)) (hR _ (by simp)) htr
    rw [← D.holPart_add_antiholPart, _root_.add_apply]
    rw [Module.End.toContinuousLinearMap_symm_apply] at h1 h2
    rw [h1, h2, add_zero]
  refine SL.induction (p := fun g => ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) w = w)
    (fun g X htr hg => ?_) (fun g h hg hh => ?_) g
  · rw [SL.apply_eq_exp_derivRepMatrix ρ htr hg]
    exact ContinuousLinearMap.exp_apply_of_apply_eq_zero (hD htr)
  · simp [hg, hh]

/-- A vector in the generalized kernel of the Casimir of a map preserving brackets and real
multiples is killed by the images of the standard `sl₂` triple. -/
lemma SL.apply_eq_zero_of_mem_maxGenEigenspace {φ : Matrix (Fin 2) (Fin 2) ℂ → E →L[ℂ] E}
    (hlie : ∀ X Y, ⁅φ X, φ Y⁆ = φ ⁅X, Y⁆) (hsmul : ∀ (r : ℝ) X, φ ((r : ℂ) • X) = (r : ℂ) • φ X)
    {w : E} (hw : w ∈ Module.End.maxGenEigenspace (ψ (sl2Casimir φ)) 0) :
    ∀ X ∈ ({sl2E, sl2F, sl2H} : Set (Matrix (Fin 2) (Fin 2) ℂ)), φ X w = 0 := by
  have hC : ψ (sl2Casimir φ) = sl2Casimir fun X => ψ (φ X) := by
    simp only [sl2Casimir, map_add, map_mul, map_nsmul]
  obtain ⟨hE, hF, hH⟩ := apply_eq_zero_of_mem_maxGenEigenspace_sl2Casimir
    (φ := fun X => ψ (φ X)) (fun X Y => by rw [← hlie, Ring.lie_def, Ring.lie_def]; simp)
    (fun r X => by rw [hsmul, map_smul]) (hC ▸ hw)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [Module.End.toContinuousLinearMap_symm_apply] at hE hF hH
  exact ⟨hE, hF, hH⟩

/-- A continuous finite-dimensional representation of `SL(2, ℂ)` has an operator in
`1 + span {ρ g - 1}` with image in the invariants, the product `q_L(C_L) q_R(C_R)` of the
projections onto the generalized kernels of the two Casimirs. -/
lemma SL.exists_sub_one_mem_span :
    ∃ P : E →L[ℂ] E,
      P - 1 ∈ Submodule.span ℂ (Set.range fun g => ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) - 1) ∧
      ∀ g v, ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) (P v) = P v := by
  set D := SL.derivRepMatrix ρ
  set S := Submodule.span ℂ (Set.range fun g => ((ρ g : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) - 1)
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := fun _ ha _ hb =>
    Submodule.mul_mem_span_sub_one ((Units.coeHom _).comp ρ.toMonoidHom) ha hb
  have hCL : sl2Casimir D.holPart ∈ S := sl2Casimir_mem hS fun X =>
    S.smul_mem _ (sub_mem (SL.derivRepMatrix_mem_span ρ _)
      (S.smul_mem _ (SL.derivRepMatrix_mem_span ρ _)))
  have hCR : sl2Casimir D.antiholPart ∈ S := sl2Casimir_mem hS fun X =>
    S.smul_mem _ (add_mem (SL.derivRepMatrix_mem_span ρ _)
      (S.smul_mem _ (SL.derivRepMatrix_mem_span ρ _)))
  obtain ⟨qL, hqL, -, hmemL, -⟩ :=
    Module.End.exists_polynomial_maxGenEigenspace_zero_proj (ψ (sl2Casimir D.holPart))
  obtain ⟨qR, hqR, -, hmemR, -⟩ :=
    Module.End.exists_polynomial_maxGenEigenspace_zero_proj (ψ (sl2Casimir D.antiholPart))
  refine ⟨aeval (sl2Casimir D.holPart) qL * aeval (sl2Casimir D.antiholPart) qR, ?_,
    fun g v => ?_⟩
  · have h1 := Submodule.aeval_sub_algebraMap_coeff_zero_mem hS hCL qL
    have h2 := Submodule.aeval_sub_algebraMap_coeff_zero_mem hS hCR qR
    rw [hqL, map_one] at h1
    rw [hqR, map_one] at h2
    rw [show ∀ a b : E →L[ℂ] E, a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) by
      intros; noncomm_ring]
    exact add_mem (add_mem (hS _ h1 _ h2) h1) h2
  have hcomm : Commute (ψ (sl2Casimir D.antiholPart)) (aeval (ψ (sl2Casimir D.holPart)) qL) :=
    ((commute_sl2Casimir fun X Y => commute_iff_lie_eq.2
      (D.holPart_lie_antiholPart X Y)).map ψ).symm.aeval_right qL
  have hwL := hmemL (aeval (sl2Casimir D.antiholPart) qR v)
  have hu := hmemR v
  rw [aeval_algEquiv] at hu
  have hwR := Module.End.mapsTo_maxGenEigenspace_of_comm hcomm 0 hu
  rw [aeval_algEquiv] at hwL hwR
  refine SL.apply_eq_self_of_sl2 ρ
    (SL.apply_eq_zero_of_mem_maxGenEigenspace (D.holPart_lie) (fun r X => ?_) hwL)
    (SL.apply_eq_zero_of_mem_maxGenEigenspace (D.antiholPart_lie) (fun r X => ?_) ?_) g
  · exact D.holPart_smul _ X
  · rw [D.antiholPart_smul, Complex.conj_ofReal]
  · exact hwR

end GlobalGaugeGroup

/-!

## D. Reynolds elements for SL(2, ℂ)

-/

namespace Representation

open GlobalGaugeGroup

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (SpecialLinearGroup (Fin 2) ℂ) V}
  (W : Subrepresentation ρ) [FiniteDimensional ℂ W.toSubmodule]

/-- The coordinate form of a continuous finite-dimensional subrepresentation of `SL(2, ℂ)`, as a
continuous homomorphism from `SL(2, ℂ)` as a global gauge group into the invertible operators. -/
noncomputable def coordRepSL (hW : ContinuousMatrixCoeff W) :
    (SL 2).group →ₜ* ((Fin (Module.finrank ℂ W.toSubmodule) → ℂ) →L[ℂ]
      (Fin (Module.finrank ℂ W.toSubmodule) → ℂ))ˣ where
  toMonoidHom := (MonoidHom.toHomUnits
    { toFun := coordRep W
      map_one' := by
        ext x : 1
        simp only [coordRep_apply, map_one, LinearEquiv.apply_symm_apply, one_apply_eq_self]
      map_mul' := coordRep_mul W }).comp (SL.toSpecialLinearGroup 2).toMonoidHom
  continuous_toFun := Units.continuous_iff.2
    ⟨(continuous_coordRep W hW).comp (continuous_SL_toSpecialLinearGroup 2),
      (continuous_coordRep W hW).comp (continuous_inv.comp (continuous_SL_toSpecialLinearGroup 2))⟩

/-- The coordinate form on `SL(2, ℂ)` as a global gauge group is that on Mathlib's special linear
group. -/
lemma coordRepSL_apply (hW : ContinuousMatrixCoeff W) (g : (SL 2).group) :
    ((coordRepSL W hW g : (_ →L[ℂ] _)ˣ) : _ →L[ℂ] _) = coordRep W (SL.toSpecialLinearGroup 2 g) :=
  rfl

/-- A representation of `SL(2, ℂ)` which is continuous on a finite-dimensional
subrepresentation has a Reynolds element on it. -/
lemma exists_isReynolds_of_specialLinearGroup (hW : ContinuousMatrixCoeff W) :
    ∃ r, ρ.IsReynolds W.toSubmodule r := by
  obtain ⟨P, hP, hPinv⟩ := SL.exists_sub_one_mem_span (coordRepSL W hW)
  have hP' : P - 1 ∈ Submodule.span ℂ (Set.range fun h => coordRep W h - 1) := by
    refine Submodule.span_mono ?_ hP
    rintro _ ⟨g, rfl⟩
    exact ⟨SL.toSpecialLinearGroup 2 g, rfl⟩
  have hinv (w : W.toSubmodule) : (Module.finBasis ℂ W.toSubmodule).equivFun.symm.conj
      (P : Module.End ℂ _) w ∈ W.toRepresentation.invariants := by
    rw [mem_invariants]
    intro h
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    rw [toRepresentation_apply_equivFun_symm]
    have := hPinv ((SL.toSpecialLinearGroup 2).symm h)
      ((Module.finBasis ℂ W.toSubmodule).equivFun w)
    rw [coordRepSL_apply, MulEquiv.apply_symm_apply] at this
    rw [this]
  obtain ⟨r, hr, -⟩ := exists_isReynolds_of_sub_one_mem_span W (conj_sub_one_mem_span W hP') hinv
  exact ⟨r, hr⟩

end Representation
