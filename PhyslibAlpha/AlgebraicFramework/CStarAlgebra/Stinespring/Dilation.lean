/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Stinespring.Kernel
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!

# Stinespring's dilation theorem

Ported from `unbounded-alpha-public`'s `QuantumMechanics/Unbounded/OperatorAlgebra/Dynamics/
Stinespring/Core.lean`, restated against this repo's own bare Mathlib hypotheses
(`[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`) instead of the upstream-superseded
`OperatorAlgebra` class — see `Kernel.lean`'s docstring for why this is a pure restatement, not new
mathematics.

Stinespring's theorem is the general statement underlying every physical quantum operation: a
completely positive map `J : A →CP (H →L[ℂ] H)` out of a C⋆-algebra always arises from coupling to
a larger system and applying an ordinary `⋆`-representation. Concretely, it builds a Hilbert space
`K`, a `⋆`-representation `π : A →⋆ₐ[ℂ] (K →L[ℂ] K)`, and an isometry-like embedding
`V : H →L[ℂ] K` with

  `J a = V⋆ π(a) V`      (`canonical_stinespring_identity`).

This subsumes Naimark's dilation theorem as the commutative special case (a POVM is a CP map on
the commutative algebra of bounded measurable functions; positivity there is automatically complete
positivity, and indicator functions recover the projection-valued dilation from `π`).

## Construction

The construction is a vector-valued (operator-valued) generalization of the GNS construction,
built on the algebraic tensor product `A ⊗[ℂ] H`:

- `sesquiBilinear`/`tensorInner` : the (possibly degenerate) `B(H)`-valued-kernel-induced
  sesquilinear form `⟪a ⊗ h, b ⊗ k⟫ := ⟪h, J(a⋆b) k⟫` on `A ⊗[ℂ] H`.
- `tensorCore`/`tensorSeminormed`/`tensorInnerProductSpace` : the pre-Hilbert-space structure this
  form induces (positivity is `Kernel.lean`'s CP-kernel positivity).
- `leftMul`/`leftMulK` : left multiplication by `A` on the tensor product, shown contractive
  (`leftMul_norm_le`) and hence extending to the completion.
- `Canonical.K J` : the completion of `A ⊗[ℂ] H` under the kernel seminorm — the canonical
  Stinespring dilation space.
- `Canonical.canonicalRepresentation`, `Canonical.embedding` : the representation `π` and the
  embedding `V : H →L[ℂ] K J`.
- `Canonical.canonical_stinespring_identity` : the Stinespring identity itself.
- `Canonical.canonicalWitness` : the identity packaged as a `StinespringWitness`.
- `exists_stinespringWitness` : the dilation theorem, stated as an existence theorem.

## Main results

- `Canonical.canonical_stinespring_identity`
- `exists_stinespringWitness`

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra TensorProduct
open ContinuousLinearMap

noncomputable section

namespace Stinespring

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The tensor-product carrier `A ⊗[ℂ] H` the whole construction below lives on. -/
@[nolint unusedArguments]
abbrev T (A H : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] := A ⊗[ℂ] H

/-- The functional `b ⊗ k ↦ ⟪h, J(a⋆b) k⟫`, the building block of the kernel inner product. -/
def baseFunctional (J : A →CP (H →L[ℂ] H)) (a : A) (h : H) :
    T A H →ₗ[ℂ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun b k => inner ℂ h (J (star a * b) k))
    (by intro b₁ b₂ k; simp [mul_add, map_add])
    (by
      intro c b k
      rw [mul_smul_comm, map_smul]
      change inner ℂ h (c • (J (star a * b) k)) = _
      rw [inner_smul_right]
      rfl)
    (by intro b k₁ k₂; simp [map_add])
    (by
      intro c b k
      rw [map_smul]
      rw [inner_smul_right]
      rfl))

@[simp]
lemma baseFunctional_tmul (J : A →CP (H →L[ℂ] H)) (a b : A) (h k : H) :
    baseFunctional J a h (b ⊗ₜ[ℂ] k) = inner ℂ h (J (star a * b) k) := by
  rfl

/-- `baseFunctional`, packaged as a sesquilinear map in `(a, h)`. -/
def sesquiBilinear (J : A →CP (H →L[ℂ] H)) :
    A →ₛₗ[starRingEnd ℂ] H →ₛₗ[starRingEnd ℂ] (T A H →ₗ[ℂ] ℂ) :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (starRingEnd ℂ)
    (fun a h => baseFunctional J a h)
    (by intro a₁ a₂ h; ext x; simp [baseFunctional, star_add, add_mul, map_add])
    (by intro c a h; ext x; simp [baseFunctional, star_smul, map_smul])
    (by intro a h₁ h₂; ext x; simp [baseFunctional])
    (by intro c a h; ext x; simp [baseFunctional]; ring)

/-- The (possibly degenerate) sesquilinear form on `T A H` induced by lifting `sesquiBilinear`
through the tensor product. -/
def tensorInner (J : A →CP (H →L[ℂ] H)) :
    T A H →ₛₗ[starRingEnd ℂ] (T A H →ₗ[ℂ] ℂ) :=
  TensorProduct.lift (sesquiBilinear J)

@[simp]
lemma tensorInner_tmul (J : A →CP (H →L[ℂ] H)) (a b : A) (h k : H) :
    tensorInner J (a ⊗ₜ[ℂ] h) (b ⊗ₜ[ℂ] k) =
      inner ℂ h (J (star a * b) k) := by
  rfl

lemma tensorInner_conj_symm_tmul (J : A →CP (H →L[ℂ] H)) (a b : A) (h k : H) :
    starRingEnd ℂ (tensorInner J (a ⊗ₜ[ℂ] h) (b ⊗ₜ[ℂ] k)) =
      tensorInner J (b ⊗ₜ[ℂ] k) (a ⊗ₜ[ℂ] h) := by
  rw [tensorInner_tmul, tensorInner_tmul]
  rw [inner_conj_symm]
  have hstar : J (star b * a) =
      ContinuousLinearMap.adjoint (J (star a * b)) := by
    calc
      J (star b * a) = J (star (star a * b)) := by
        congr 1
        simp [star_mul]
      _ = star (J (star a * b)) :=
        (completelyPositiveMap_map_star_general J _).symm
      _ = ContinuousLinearMap.adjoint (J (star a * b)) := by rfl
  rw [hstar]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

lemma tensorInner_conj_symm (J : A →CP (H →L[ℂ] H)) (x y : T A H) :
    starRingEnd ℂ (tensorInner J x y) = tensorInner J y x := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a h
    refine TensorProduct.inductionOn y ?_ ?_
    · intro b k
      exact tensorInner_conj_symm_tmul J a b h k
    · intro y z ihy ihz
      simp only [map_add, ihy, ihz]
      rw [LinearMap.add_apply]
  · intro x y ihx ihy
    rw [(tensorInner J).map_add]
    rw [LinearMap.add_apply]
    rw [map_add, ihx, ihy]
    rw [map_add]

lemma tensorInner_nonneg (J : A →CP (H →L[ℂ] H)) (x : T A H) :
    0 ≤ tensorInner J x x := by
  obtain ⟨n, a, h, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  let v : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 h
  have hv (i : Fin n) : v.ofLp i = h i := rfl
  have hp := cpKernel_inner_nonneg_natural' J a v
  rw [Finset.sum_comm] at hp
  simpa [tensorInner, sesquiBilinear, baseFunctional, v, hv,
    Finset.sum_apply, inner_sum, sum_inner] using hp

/-- `tensorInner`, packaged as a `PreInnerProductSpace.Core` on `T A H`. -/
@[instance_reducible]
def tensorCore (J : A →CP (H →L[ℂ] H)) :
    PreInnerProductSpace.Core ℂ (T A H) where
  inner := fun x y => tensorInner J x y
  conj_inner_symm := by
    intro x y
    exact tensorInner_conj_symm J y x
  re_inner_nonneg := by
    intro x
    exact (tensorInner_nonneg J x).1
  add_left := by
    intro x y z
    exact congrArg (fun f => f z) ((tensorInner J).map_add x y)
  smul_left := by
    intro x y r
    have hs := congrArg (fun f : T A H →ₗ[ℂ] ℂ => f y)
      ((tensorInner J).map_smulₛₗ r x)
    simp only [LinearMap.smul_apply, smul_eq_mul] at hs
    exact hs

/-- Left multiplication by `a` on the algebra factor of `T A H`. -/
def leftMul (a : A) : T A H →ₗ[ℂ] T A H :=
  TensorProduct.map (LinearMap.mulLeft ℂ a) (LinearMap.id)

@[simp]
lemma leftMul_tmul (a b : A) (h : H) :
    leftMul a (b ⊗ₜ[ℂ] h) = (a * b) ⊗ₜ[ℂ] h := by
  simp [leftMul]

lemma tensorInner_leftMul (J : A →CP (H →L[ℂ] H)) (a : A) (x y : T A H) :
    tensorInner J (leftMul a x) y = tensorInner J x (leftMul (star a) y) := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro b h
    refine TensorProduct.inductionOn y ?_ ?_
    · intro c k
      simp [leftMul, star_mul, mul_assoc]
    · intro y z ihy ihz
      simp only [map_add, ihy, ihz]
  · intro x z ihx ihz
    rw [(leftMul a).map_add, (tensorInner J).map_add]
    simp only [LinearMap.add_apply, map_add, ihx, ihz]

lemma leftMul_mul (a b : A) (x : T A H) :
    leftMul (a * b) x = leftMul a (leftMul b x) := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro c h
    simp [leftMul]
  · intro x y ihx ihy
    simp only [map_add, ihx, ihy]

lemma leftMul_add (a b : A) (x : T A H) :
    leftMul (a + b) x = leftMul a x + leftMul b x := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro c h
    simp [leftMul, add_mul, TensorProduct.add_tmul]
  · intro x y ihx ihy
    rw [(leftMul (a + b)).map_add, (leftMul a).map_add, (leftMul b).map_add,
      ihx, ihy]
    abel

lemma leftMul_smul (r : ℂ) (a : A) (x : T A H) :
    leftMul (r • a) x = r • leftMul a x := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro b h
    rw [leftMul_tmul, leftMul_tmul]
    rw [smul_mul_assoc]
    rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  · intro x y ihx ihy
    rw [(leftMul (r • a)).map_add, (leftMul a).map_add, ihx, ihy, smul_add]

lemma leftMul_one (x : T A H) : leftMul (1 : A) x = x := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a h
    simp [leftMul]
  · intro x y ihx ihy
    simp only [map_add, ihx, ihy]

lemma leftMul_norm_sub (a : A) (x : T A H) :
    leftMul ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a) x =
      (‖a‖ ^ 2 : ℂ) • x - leftMul (star a * a) x := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro b h
    simp [leftMul, Algebra.smul_def, sub_mul, TensorProduct.sub_tmul]
    simp [Algebra.smul_def, TensorProduct.smul_tmul']
    rw [IsScalarTower.algebraMap_apply ℝ ℂ A]
    simp [mul_assoc]
  · intro x y ihx ihy
    rw [(leftMul ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a)).map_add,
      map_add, ihx, ihy]
    simp only [smul_add]
    abel

lemma tensorInner_leftMul_selfadjoint (J : A →CP (H →L[ℂ] H)) {q : A} (hq : star q = q)
    (x : T A H) :
    tensorInner J (leftMul q x) x = tensorInner J x (leftMul q x) := by
  rw [tensorInner_leftMul J q x x, hq]

lemma tensorInner_leftMul_nonneg (J : A →CP (H →L[ℂ] H)) {q : A} (hq : 0 ≤ q)
    (x : T A H) : 0 ≤ tensorInner J (leftMul q x) x := by
  let s : A := CFC.sqrt q
  have hs : star s = s := by
    dsimp [s]
    exact (CFC.sqrt_nonneg q).isSelfAdjoint.star_eq
  have hsq : star s * s = q := by
    dsimp [s]
    rw [(CFC.sqrt_nonneg q).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have hinner : tensorInner J (leftMul q x) x =
      tensorInner J (leftMul s x) (leftMul s x) := by
    rw [← hsq, leftMul_mul]
    rw [tensorInner_leftMul J (star s) (leftMul s x) x]
    simp [hs]
  rw [hinner]
  exact tensorInner_nonneg J _

/-! ## The seminorm and pre-Hilbert structures induced by the kernel -/

/-- The seminormed-group structure `T A H` inherits from `tensorCore`'s (possibly degenerate)
inner product. -/
@[instance_reducible]
def tensorSeminormed (J : A →CP (H →L[ℂ] H)) :
    SeminormedAddCommGroup (T A H) :=
  letI : PreInnerProductSpace.Core ℂ (T A H) := tensorCore J
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := tensorCore J)

/-- The inner product space structure on `T A H`, with respect to `tensorSeminormed`, coming
from `tensorCore`. -/
@[instance_reducible]
def tensorInnerProductSpace (J : A →CP (H →L[ℂ] H)) :
    @InnerProductSpace ℂ (T A H) inferInstance (tensorSeminormed J) := by
  letI : PreInnerProductSpace.Core ℂ (T A H) := tensorCore J
  letI : Inner ℂ (T A H) := ⟨fun x y => tensorInner J x y⟩
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  exact
    { toNormedSpace := InnerProductSpace.Core.toNormedSpace (c := tensorCore J)
      inner := fun x y => tensorInner J x y
      norm_sq_eq_re_inner := by
        intro x
        have hnorm :=
          (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (c := tensorCore J) x)
        change RCLike.re ((tensorCore J).inner x x) = ‖x‖ * ‖x‖ at hnorm
        rw [pow_two]
        change ‖x‖ * ‖x‖ = RCLike.re ((tensorCore J).inner x x)
        simpa [pow_two] using hnorm.symm
      conj_inner_symm := by
        intro x y
        exact tensorInner_conj_symm J y x
      add_left := by
        intro x y z
        exact congrArg (fun f => f z) ((tensorInner J).map_add x y)
      smul_left := by
        intro x y r
        have hs := congrArg (fun f : T A H →ₗ[ℂ] ℂ => f y)
          ((tensorInner J).map_smulₛₗ r x)
        simpa only [LinearMap.smul_apply, smul_eq_mul] using hs }

lemma leftMul_norm_le (a : A) (J : A →CP (H →L[ℂ] H)) (x : T A H) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    ‖leftMul a x‖ ≤ ‖a‖ * ‖x‖ := by
  let : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let q : A := (‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a
  have hq : 0 ≤ q := by
    dsimp [q]
    have hle : star a * a ≤ algebraMap ℝ A ‖star a * a‖ := by
      exact (CStarAlgebra.norm_le_iff_le_algebraMap (star a * a)
        (norm_nonneg _)).mp le_rfl
    rw [CStarRing.norm_star_mul_self] at hle
    simpa [sq, Algebra.algebraMap_eq_smul_one] using (sub_nonneg.mpr hle)
  have hpos := tensorInner_leftMul_nonneg J hq x
  rw [leftMul_norm_sub] at hpos
  have hleft : tensorInner J (leftMul (star a * a) x) x =
      tensorInner J (leftMul a x) (leftMul a x) := by
    rw [tensorInner_leftMul J (star a * a) x x]
    simp only [star_mul, star_star]
    rw [tensorInner_leftMul J a x (leftMul a x)]
    rw [← leftMul_mul]
  have hident : tensorInner J
      ((‖a‖ ^ 2 : ℂ) • x - leftMul (star a * a) x) x =
      (‖a‖ ^ 2 : ℝ) * tensorInner J x x -
        tensorInner J (leftMul a x) (leftMul a x) := by
    rw [sub_eq_add_neg, (tensorInner J).map_add]
    rw [LinearMap.add_apply, (tensorInner J).map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul]
    rw [← neg_one_smul ℂ, (tensorInner J).map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hleft]
    rw [show starRingEnd ℂ (‖a‖ ^ 2 : ℂ) = (‖a‖ ^ 2 : ℂ) by simp]
    rw [show starRingEnd ℂ (-1 : ℂ) = (-1 : ℂ) by norm_num]
    simp [sub_eq_add_neg]
  rw [hident] at hpos
  have hreal := (RCLike.nonneg_iff.mp hpos).1
  have hselfx : RCLike.re (tensorInner J x x) = ‖x‖ ^ 2 := by
    have hnorm :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (c := tensorCore J) x)
    change RCLike.re ((tensorCore J).inner x x) = ‖x‖ * ‖x‖ at hnorm
    rw [pow_two]
    change RCLike.re ((tensorCore J).inner x x) = ‖x‖ * ‖x‖
    exact hnorm
  have hselfa : RCLike.re (tensorInner J (leftMul a x) (leftMul a x)) =
      ‖leftMul a x‖ ^ 2 := by
    have hnorm :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (c := tensorCore J)
        (leftMul a x))
    change RCLike.re ((tensorCore J).inner (leftMul a x) (leftMul a x)) =
      ‖leftMul a x‖ * ‖leftMul a x‖ at hnorm
    rw [pow_two]
    change RCLike.re ((tensorCore J).inner (leftMul a x) (leftMul a x)) =
      ‖leftMul a x‖ * ‖leftMul a x‖
    exact hnorm
  simp [map_sub, hselfx, hselfa] at hreal
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hreal
  have hreal' : ‖leftMul a x‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [zero_mul, sub_zero, pow_two, mul_assoc] using hreal
  have hax : 0 ≤ ‖a‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hreal']

lemma uniformContinuous_add (J : A →CP (H →L[ℂ] H)) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    UniformContinuous fun p : T A H × T A H => p.1 + p.2 := by
  let : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  refine LipschitzWith.uniformContinuous (K := (2 : NNReal)) ?_
  apply LipschitzWith.of_dist_le_mul (K := (2 : NNReal))
  intro p q
  rw [Prod.dist_eq]
  calc
    dist (p.1 + p.2) (q.1 + q.2) ≤ dist p.1 q.1 + dist p.2 q.2 :=
      dist_add_add_le _ _ _ _
    _ ≤ 2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      nlinarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
        le_max_right (dist p.1 q.1) (dist p.2 q.2)]

lemma uniformContinuous_neg (J : A →CP (H →L[ℂ] H)) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    UniformContinuous fun x : T A H => -x := by
  let : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  refine LipschitzWith.uniformContinuous (K := (1 : NNReal)) ?_
  apply LipschitzWith.of_dist_le_mul (K := (1 : NNReal))
  intro x y
  rw [SeminormedAddCommGroup.dist_eq, SeminormedAddCommGroup.dist_eq]
  calc
    ‖- -x + -y‖ = ‖-((-x) + y)‖ := by rw [neg_add_rev]; simp [add_comm]
    _ = ‖-x + y‖ := norm_neg _
  simp only [NNReal.coe_one, one_mul]
  exact le_rfl

/-- `leftMul a`, bundled as a continuous linear map for the kernel seminorm. -/
def leftMulCLM (J : A →CP (H →L[ℂ] H)) (a : A) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    T A H →L[ℂ] T A H := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  exact (leftMul a).mkContinuous ‖a‖ (fun x => leftMul_norm_le a J x)

lemma leftMulCLM_apply (J : A →CP (H →L[ℂ] H)) (a : A) (x : T A H) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    leftMulCLM J a x = leftMul a x := by
  let : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  rfl

/-- The continuous extension of `leftMulCLM` to the completion of `T A H`. -/
def leftMulCompletion (J : A →CP (H →L[ℂ] H)) (a : A) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
    UniformSpace.Completion (T A H) →L[ℂ] UniformSpace.Completion (T A H) := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
  letI : IsUniformAddGroup (T A H) := IsUniformAddGroup.mk'
    (uniformContinuous_add J) (uniformContinuous_neg J)
  letI : IsBoundedSMul ℂ (T A H) := NormSMulClass.toIsBoundedSMul
  letI : UniformContinuousConstSMul ℂ (T A H) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  exact (leftMulCLM J a).completion

@[simp]
lemma leftMulCompletion_coe (J : A →CP (H →L[ℂ] H)) (a : A) (x : T A H) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    leftMulCompletion J a (x : UniformSpace.Completion (T A H)) = leftMulCLM J a x := by
  let : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  let : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  let : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
  let : IsUniformAddGroup (T A H) := IsUniformAddGroup.mk'
    (uniformContinuous_add J) (uniformContinuous_neg J)
  let : IsBoundedSMul ℂ (T A H) := NormSMulClass.toIsBoundedSMul
  let : UniformContinuousConstSMul ℂ (T A H) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  change (leftMulCLM J a).completion (x : UniformSpace.Completion (T A H)) =
    (leftMulCLM J a) x
  exact ContinuousLinearMap.completion_apply_coe (leftMulCLM J a) x

lemma leftMulCompletion_mul (J : A →CP (H →L[ℂ] H)) (a b : A) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
    leftMulCompletion J (a * b) =
      (leftMulCompletion J a).comp (leftMulCompletion J b) := by
  let : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  let : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  let : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
  let : IsUniformAddGroup (T A H) := IsUniformAddGroup.mk'
    (uniformContinuous_add J) (uniformContinuous_neg J)
  let : IsBoundedSMul ℂ (T A H) := NormSMulClass.toIsBoundedSMul
  let : UniformContinuousConstSMul ℂ (T A H) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulCompletion J (a * b)).continuous
    · exact ((leftMulCompletion J a).comp (leftMulCompletion J b)).continuous
  · intro x
    change (leftMulCLM J (a * b)).completion (x : UniformSpace.Completion (T A H)) =
      (leftMulCLM J a).completion
        ((leftMulCLM J b).completion (x : UniformSpace.Completion (T A H)))
    rw [ContinuousLinearMap.completion_apply_coe]
    rw [ContinuousLinearMap.completion_apply_coe]
    rw [ContinuousLinearMap.completion_apply_coe]
    rw [leftMulCLM_apply, leftMulCLM_apply, leftMulCLM_apply]
    exact congrArg (fun y : T A H => (y : UniformSpace.Completion (T A H)))
      (leftMul_mul a b x)

/-! ## The canonical CP-dependent Hilbert space

The CP kernel changes the norm, so its pre-Hilbert space is made a type synonym. This is the same
pattern used by Mathlib's own scalar GNS construction (`PositiveLinearMap.PreGNS`): the synonym
lets the tensor product retain its original module structure while carrying a CP-dependent
seminorm and inner product. -/

namespace Canonical

/-- A type synonym for `T A H` carrying the CP-kernel-dependent seminorm and inner product,
kept separate so the tensor product retains its own module structure. -/
@[nolint unusedArguments]
def Pre (_J : A →CP (H →L[ℂ] H)) := T A H

instance (J : A →CP (H →L[ℂ] H)) : AddCommGroup (Pre J) :=
  inferInstanceAs (AddCommGroup (T A H))

instance (J : A →CP (H →L[ℂ] H)) : Module ℂ (Pre J) :=
  inferInstanceAs (Module ℂ (T A H))

instance (J : A →CP (H →L[ℂ] H)) : SeminormedAddCommGroup (Pre J) :=
  tensorSeminormed J

instance (J : A →CP (H →L[ℂ] H)) : InnerProductSpace ℂ (Pre J) :=
  InnerProductSpace.ofCore (tensorCore J)

instance (J : A →CP (H →L[ℂ] H)) : IsUniformAddGroup (Pre J) :=
  IsUniformAddGroup.mk' (uniformContinuous_add J) (uniformContinuous_neg J)

instance (J : A →CP (H →L[ℂ] H)) : IsBoundedSMul ℂ (Pre J) :=
  NormSMulClass.toIsBoundedSMul

instance (J : A →CP (H →L[ℂ] H)) : UniformContinuousConstSMul ℂ (Pre J) :=
  IsBoundedSMul.toUniformContinuousConstSMul

/-- The completion of `Pre J`: the canonical Stinespring Hilbert space attached to `J`. -/
abbrev K (J : A →CP (H →L[ℂ] H)) := UniformSpace.Completion (Pre J)

/-- `leftMul a`, viewed as an operator on `Pre J`. -/
def preLeftMul (J : A →CP (H →L[ℂ] H)) (a : A) :
    Pre J →ₗ[ℂ] Pre J := leftMul a

@[simp]
lemma preLeftMul_apply (J : A →CP (H →L[ℂ] H)) (a : A) (x : Pre J) :
    preLeftMul J a x = leftMul a x := rfl

/-- `preLeftMul`, bundled as a continuous linear map. -/
def preLeftMulCLM (J : A →CP (H →L[ℂ] H)) (a : A) :
    Pre J →L[ℂ] Pre J :=
  (preLeftMul J a).mkContinuous ‖a‖ (fun x => leftMul_norm_le a J x)

@[simp]
lemma preLeftMulCLM_apply (J : A →CP (H →L[ℂ] H)) (a : A) (x : Pre J) :
    preLeftMulCLM J a x = preLeftMul J a x := rfl

lemma completion_leftMul_norm_le (J : A →CP (H →L[ℂ] H)) (a : A) (x : K J) :
    ‖(preLeftMulCLM J a).completion x‖ ≤ ‖a‖ * ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · apply isClosed_le
    · exact (preLeftMulCLM J a).completion.continuous.norm
    · exact (continuous_const.mul continuous_norm)
  · intro y
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      preLeftMulCLM_apply, preLeftMul_apply, UniformSpace.Completion.norm_coe]
    exact leftMul_norm_le a J y

/-- The continuous extension of `preLeftMulCLM` to the completion `K J`. -/
def leftMulK (J : A →CP (H →L[ℂ] H)) (a : A) : K J →L[ℂ] K J :=
  ((preLeftMulCLM J a).completion.toLinearMap).mkContinuous ‖a‖
    (completion_leftMul_norm_le J a)

@[simp]
lemma leftMulK_coe (J : A →CP (H →L[ℂ] H)) (a : A) (x : Pre J) :
    leftMulK J a (x : K J) = preLeftMulCLM J a x :=
  ContinuousLinearMap.completion_apply_coe (preLeftMulCLM J a) x

lemma leftMulK_mul (J : A →CP (H →L[ℂ] H)) (a b : A) :
    leftMulK J (a * b) = (leftMulK J a).comp (leftMulK J b) := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (a * b)).continuous
    · exact ((leftMulK J a).comp (leftMulK J b)).continuous
  · intro x
    rw [leftMulK_coe, ContinuousLinearMap.comp_apply, leftMulK_coe, leftMulK_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply, preLeftMulCLM_apply]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_mul a b x)

lemma leftMulK_one (J : A →CP (H →L[ℂ] H)) :
    leftMulK J (1 : A) = ContinuousLinearMap.id ℂ (K J) := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (1 : A)).continuous
    · fun_prop
  · intro x
    rw [leftMulK_coe]
    change ((preLeftMulCLM J (1 : A)) x : K J) = (x : K J)
    rw [preLeftMulCLM_apply, preLeftMul_apply]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_one x)

lemma leftMulK_add (J : A →CP (H →L[ℂ] H)) (a b : A) :
    leftMulK J (a + b) = leftMulK J a + leftMulK J b := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (a + b)).continuous
    · fun_prop
  · intro x
    rw [leftMulK_coe]
    rw [add_apply, leftMulK_coe, leftMulK_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply, preLeftMulCLM_apply]
    rw [← UniformSpace.Completion.coe_add]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_add a b x)

lemma leftMulK_smul (J : A →CP (H →L[ℂ] H)) (r : ℂ) (a : A) :
    leftMulK J (r • a) = r • leftMulK J a := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (r • a)).continuous
    · exact (leftMulK J a).continuous.const_smul r
  · intro x
    rw [leftMulK_coe]
    rw [smul_apply, leftMulK_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply]
    rw [← UniformSpace.Completion.coe_smul]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_smul r a x)

set_option backward.isDefEq.respectTransparency false in
lemma leftMulK_star (J : A →CP (H →L[ℂ] H)) (a : A) :
    leftMulK J (star a) = (leftMulK J a).adjoint := by
  refine (eq_adjoint_iff (leftMulK J (star a)) (leftMulK J a)).mpr ?_
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · apply isClosed_eq
    · fun_prop
    · fun_prop
  · intro u v
    rw [leftMulK_coe, UniformSpace.Completion.inner_coe,
      leftMulK_coe, UniformSpace.Completion.inner_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply]
    change tensorInner J (leftMul (star a) u) v = tensorInner J u (leftMul a v)
    rw [tensorInner_leftMul]
    simp only [star_star]

/-- The canonical embedding `H → Pre J`, `h ↦ 1 ⊗ h`. -/
def preEmbedding (J : A →CP (H →L[ℂ] H)) : H →ₗ[ℂ] Pre J :=
  (TensorProduct.mk ℂ A H) 1

@[simp]
lemma preEmbedding_apply (J : A →CP (H →L[ℂ] H)) (h : H) :
    preEmbedding J h = (1 : A) ⊗ₜ[ℂ] h := rfl

lemma preEmbedding_norm_sq (J : A →CP (H →L[ℂ] H)) (h : H) :
    ‖preEmbedding J h‖ ^ 2 = RCLike.re (inner ℂ h (J (1 : A) h)) := by
  rw [@norm_sq_eq_re_inner ℂ (Pre J) _ _]
  change RCLike.re (tensorInner J ((1 : A) ⊗ₜ[ℂ] h) ((1 : A) ⊗ₜ[ℂ] h)) = _
  rw [tensorInner_tmul]
  simp

lemma preEmbedding_norm_le (J : A →CP (H →L[ℂ] H)) (h : H) :
    ‖preEmbedding J h‖ ≤ Real.sqrt ‖J (1 : A)‖ * ‖h‖ := by
  have hsq : ‖preEmbedding J h‖ ^ 2 ≤
      (Real.sqrt ‖J (1 : A)‖ * ‖h‖) ^ 2 := by
    rw [preEmbedding_norm_sq]
    calc
      RCLike.re (inner ℂ h (J (1 : A) h)) ≤ ‖inner ℂ h (J (1 : A) h)‖ :=
        RCLike.re_le_norm _
      _ ≤ ‖h‖ * ‖J (1 : A) h‖ := norm_inner_le_norm _ _
      _ ≤ ‖h‖ * (‖J (1 : A)‖ * ‖h‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm (J (1 : A)) h) (norm_nonneg _)
      _ = (Real.sqrt ‖J (1 : A)‖ * ‖h‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _))).mp hsq

/-- `preEmbedding`, bundled as a continuous linear map. -/
def preEmbeddingCLM (J : A →CP (H →L[ℂ] H)) : H →L[ℂ] Pre J :=
  (preEmbedding J).mkContinuous (Real.sqrt ‖J (1 : A)‖) (preEmbedding_norm_le J)

/-- The canonical embedding `H → K J` into the completed Stinespring space. -/
def embedding (J : A →CP (H →L[ℂ] H)) : H →L[ℂ] K J :=
  (UniformSpace.Completion.toComplL : Pre J →L[ℂ] K J).comp (preEmbeddingCLM J)

@[simp]
lemma embedding_apply (J : A →CP (H →L[ℂ] H)) (h : H) :
    embedding J h = (preEmbedding J h : K J) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The representation of `A` on `K J` by (extended) left multiplication. -/
def canonicalRepresentation (J : A →CP (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (K J →L[ℂ] K J) where
  toFun := leftMulK J
  map_one' := leftMulK_one J
  map_mul' := leftMulK_mul J
  map_zero' := by
    simpa only [map_zero, zero_smul] using (leftMulK_smul J 0 0)
  map_add' := leftMulK_add J
  commutes' := by
    intro r
    calc
      leftMulK J ((algebraMap ℂ A) r) = r • leftMulK J (1 : A) := by
        simpa [Algebra.smul_def] using (leftMulK_smul J r (1 : A))
      _ = (algebraMap ℂ (K J →L[ℂ] K J)) r := by
        rw [leftMulK_one]
        simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
  map_star' := leftMulK_star J

set_option backward.isDefEq.respectTransparency false in
/-- **Stinespring's dilation identity**: `J a = V⋆ π(a) V`, where `π` is `canonicalRepresentation`
and `V` is `embedding`. -/
theorem canonical_stinespring_identity (J : A →CP (H →L[ℂ] H)) (a : A) :
    J a = ContinuousLinearMap.adjoint (embedding J) ∘L
      (canonicalRepresentation J a) ∘L embedding J := by
  apply ContinuousLinearMap.ext
  intro x
  rw [@ext_iff_inner_left ℂ H _ _]
  intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [embedding_apply, embedding_apply]
  change inner ℂ y (J a x) =
    inner ℂ (preEmbedding J y : K J) (leftMulK J a (preEmbedding J x : K J))
  rw [leftMulK_coe]
  rw [UniformSpace.Completion.inner_coe]
  rw [preLeftMulCLM_apply, preLeftMul_apply]
  rw [preEmbedding_apply, preEmbedding_apply]
  change inner ℂ y (J a x) =
    tensorInner J ((1 : A) ⊗ₜ[ℂ] y) (leftMul a ((1 : A) ⊗ₜ[ℂ] x))
  rw [leftMul_tmul, tensorInner_tmul]
  simp

/-- The canonical Stinespring witness assembled from `canonicalRepresentation` and
`embedding`. -/
def canonicalWitness (J : A →CP (H →L[ℂ] H)) :
    StinespringWitness A H (K J) J where
  representation := canonicalRepresentation J
  implementing := embedding J
  map_eq := canonical_stinespring_identity J

end Canonical

/-- **Stinespring's dilation theorem.** Every completely positive map `J : A →CP (H →L[ℂ] H)` out
of a unital C⋆-algebra `A` admits a dilation: an auxiliary Hilbert space `K`, a `⋆`-representation
`π : A →⋆ₐ[ℂ] (K →L[ℂ] K)`, and an implementing operator `V : H →L[ℂ] K` with
`J a = V⋆ π(a) V` for every `a`. The canonical GNS-style construction (`Canonical.canonicalWitness`)
exhibits such a `K`, `π`, `V` concretely; this packages that as a bare existence statement. -/
theorem exists_stinespringWitness (J : A →CP (H →L[ℂ] H)) :
    Nonempty (StinespringWitness A H (Canonical.K J) J) :=
  ⟨Canonical.canonicalWitness J⟩

end Stinespring
