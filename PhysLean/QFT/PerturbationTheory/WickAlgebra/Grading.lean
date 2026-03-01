/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickAlgebra.Basic
/-!

# Grading on the field operation algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open PhysLean.List
open FieldStatistic

namespace WickAlgebra
variable {𝓕 : FieldSpecification}

/-- The submodule of `𝓕.WickAlgebra` spanned by lists of field statistic `f`. -/
def statSubmodule (f : FieldStatistic) : Submodule ℂ 𝓕.WickAlgebra :=
  Submodule.span ℂ {a | ∃ φs, a = ofCrAnList φs ∧ (𝓕 |>ₛ φs) = f}

lemma ofCrAnList_mem_statSubmodule_of_eq (φs : List 𝓕.CrAnFieldOp) (f : FieldStatistic)
    (h : (𝓕 |>ₛ φs) = f) : ofCrAnList φs ∈ statSubmodule f :=
  Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩

lemma ofCrAnList_mem_statSubmodule (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnList φs ∈ statSubmodule (𝓕 |>ₛ φs) :=
  Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, rfl⟩⟩

lemma mem_bosonic_of_mem_free_bosonic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule bosonic) : ι a ∈ statSubmodule .bosonic := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    ι a ∈ statSubmodule .bosonic
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p]
    apply ofCrAnList_mem_statSubmodule_of_eq
    exact h
  · simp only [map_zero, p]
    exact Submodule.zero_mem (statSubmodule bosonic)
  · intro x y hx hy hpx hpy
    simp_all only [p, map_add]
    exact Submodule.add_mem _ hpx hpy
  · intro a x hx hy
    simp_all only [p, map_smul]
    exact Submodule.smul_mem _ _ hy

lemma mem_fermionic_of_mem_free_fermionic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule fermionic) : ι a ∈ statSubmodule .fermionic := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    ι a ∈ statSubmodule .fermionic
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p]
    apply ofCrAnList_mem_statSubmodule_of_eq
    exact h
  · simp only [map_zero, p]
    exact Submodule.zero_mem (statSubmodule fermionic)
  · intro x y hx hy hpx hpy
    simp_all only [p, map_add]
    exact Submodule.add_mem _ hpx hpy
  · intro a x hx hy
    simp_all only [p, map_smul]
    exact Submodule.smul_mem _ _ hy

lemma mem_statSubmodule_of_mem_statisticSubmodule (f : FieldStatistic) (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule f) : ι a ∈ statSubmodule f := by
  fin_cases f
  · exact mem_bosonic_of_mem_free_bosonic a h
  · exact mem_fermionic_of_mem_free_fermionic a h

/-- The projection of `statisticSubmodule (𝓕 := 𝓕) f` defined in the free algebra to
  `statSubmodule (𝓕 := 𝓕) f`. -/
def ιStateSubmodule (f : FieldStatistic) :
    statisticSubmodule (𝓕 := 𝓕) f →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) f where
  toFun a := ⟨a.1, mem_statSubmodule_of_mem_statisticSubmodule f a.1 a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable section

/-!

## Defining bosonicProj

-/

/-- The projection of `𝓕.FieldOpFreeAlgebra` to `statSubmodule (𝓕 := 𝓕) bosonic`. -/
def bosonicProjFree : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) bosonic :=
  ιStateSubmodule .bosonic ∘ₗ bosonicProjF

lemma bosonicProjFree_eq_ι_bosonicProjF (a : 𝓕.FieldOpFreeAlgebra) :
    (bosonicProjFree a).1 = ι (bosonicProjF a) := rfl

lemma bosonicProjFree_zero_of_ι_zero (a : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    bosonicProjFree a = 0 := by
  rw [ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero] at h
  apply Subtype.ext
  rw [bosonicProjFree_eq_ι_bosonicProjF]
  exact h.1

lemma bosonicProjFree_eq_of_equiv (a b : 𝓕.FieldOpFreeAlgebra) (h : a ≈ b) :
    bosonicProjFree a = bosonicProjFree b := by
  rw [equiv_iff_sub_mem_ideal, ← ι_eq_zero_iff_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker]
  exact bosonicProjFree_zero_of_ι_zero (a - b) h

/-- The projection of `𝓕.WickAlgebra` to `statSubmodule (𝓕 := 𝓕) bosonic`. -/
def bosonicProj : 𝓕.WickAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) bosonic where
  toFun := Quotient.lift bosonicProjFree bosonicProjFree_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

lemma bosonicProj_eq_bosonicProjFree (a : 𝓕.FieldOpFreeAlgebra) :
    bosonicProj (ι a) = bosonicProjFree a := rfl

/-!

## Defining fermionicProj

-/

/-- The projection of `𝓕.FieldOpFreeAlgebra` to `statSubmodule (𝓕 := 𝓕) fermionic`. -/
def fermionicProjFree : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) fermionic :=
  ιStateSubmodule .fermionic ∘ₗ fermionicProjF

lemma fermionicProjFree_eq_ι_fermionicProjF (a : 𝓕.FieldOpFreeAlgebra) :
    (fermionicProjFree a).1 = ι (fermionicProjF a) := rfl

lemma fermionicProjFree_zero_of_ι_zero (a : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    fermionicProjFree a = 0 := by
  rw [ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero] at h
  apply Subtype.ext
  rw [fermionicProjFree_eq_ι_fermionicProjF]
  exact h.2

lemma fermionicProjFree_eq_of_equiv (a b : 𝓕.FieldOpFreeAlgebra) (h : a ≈ b) :
    fermionicProjFree a = fermionicProjFree b := by
  rw [equiv_iff_sub_mem_ideal, ← ι_eq_zero_iff_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker]
  exact fermionicProjFree_zero_of_ι_zero (a - b) h

/-- The projection of `𝓕.WickAlgebra` to `statSubmodule (𝓕 := 𝓕) fermionic`. -/
def fermionicProj : 𝓕.WickAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) fermionic where
  toFun := Quotient.lift fermionicProjFree fermionicProjFree_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

lemma fermionicProj_eq_fermionicProjFree (a : 𝓕.FieldOpFreeAlgebra) :
    fermionicProj (ι a) = fermionicProjFree a := rfl

/-!

## Interaction between bosonicProj and fermionicProj

-/

lemma bosonicProj_add_fermionicProj (a : 𝓕.WickAlgebra) :
    bosonicProj a + (fermionicProj a).1 = a := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  rw [fermionicProj_eq_fermionicProjFree, bosonicProj_eq_bosonicProjFree]
  rw [bosonicProjFree_eq_ι_bosonicProjF, fermionicProjFree_eq_ι_fermionicProjF]
  rw [← map_add, bosonicProjF_add_fermionicProjF]

lemma bosonicProj_mem_bosonic (a : 𝓕.WickAlgebra) (ha : a ∈ statSubmodule .bosonic) :
    bosonicProj a = ⟨a, ha⟩ := by
  let p (a : 𝓕.WickAlgebra) (hx : a ∈ statSubmodule bosonic) : Prop :=
    (bosonicProj a) = ⟨a, hx⟩
  change p a ha
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp only [p]
    apply Subtype.ext
    simp only
    rw [ofCrAnList]
    rw [bosonicProj_eq_bosonicProjFree]
    rw [bosonicProjFree_eq_ι_bosonicProjF]
    rw [bosonicProjF_of_mem_bosonic]
    exact ofCrAnListF_mem_statisticSubmodule_of _ _ h
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma fermionicProj_mem_fermionic (a : 𝓕.WickAlgebra) (ha : a ∈ statSubmodule .fermionic) :
    fermionicProj a = ⟨a, ha⟩ := by
  let p (a : 𝓕.WickAlgebra) (hx : a ∈ statSubmodule fermionic) : Prop :=
    (fermionicProj a) = ⟨a, hx⟩
  change p a ha
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp only [p]
    apply Subtype.ext
    simp only
    rw [ofCrAnList]
    rw [fermionicProj_eq_fermionicProjFree]
    rw [fermionicProjFree_eq_ι_fermionicProjF]
    rw [fermionicProjF_of_mem_fermionic]
    exact ofCrAnListF_mem_statisticSubmodule_of _ _ h
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma bosonicProj_mem_fermionic (a : 𝓕.WickAlgebra) (ha : a ∈ statSubmodule .fermionic) :
    bosonicProj a = 0 := by
  have h := bosonicProj_add_fermionicProj a
  rw [fermionicProj_mem_fermionic a ha] at h
  simpa using h

lemma fermionicProj_mem_bosonic (a : 𝓕.WickAlgebra) (ha : a ∈ statSubmodule .bosonic) :
    fermionicProj a = 0 := by
  have h := bosonicProj_add_fermionicProj a
  rw [bosonicProj_mem_bosonic a ha] at h
  simpa using h

lemma mem_bosonic_iff_fermionicProj_eq_zero (a : 𝓕.WickAlgebra) :
    a ∈ statSubmodule bosonic ↔ fermionicProj a = 0 := by
  apply Iff.intro
  · intro h
    exact fermionicProj_mem_bosonic a h
  · intro h
    have ha := bosonicProj_add_fermionicProj a
    rw [h] at ha
    simp_all
    rw [← ha]
    exact (bosonicProj a).2

lemma mem_fermionic_iff_bosonicProj_eq_zero (a : 𝓕.WickAlgebra) :
    a ∈ statSubmodule fermionic ↔ bosonicProj a = 0 := by
  apply Iff.intro
  · intro h
    exact bosonicProj_mem_fermionic a h
  · intro h
    have ha := bosonicProj_add_fermionicProj a
    rw [h] at ha
    simp_all
    rw [← ha]
    exact (fermionicProj a).2

lemma eq_zero_of_bosonic_and_fermionic {a : 𝓕.WickAlgebra}
    (hb : a ∈ statSubmodule bosonic) (hf : a ∈ statSubmodule fermionic) : a = 0 := by
  have ha := bosonicProj_mem_bosonic a hb
  have hb := fermionicProj_mem_fermionic a hf
  have hc := (bosonicProj_add_fermionicProj a)
  rw [ha, hb] at hc
  simpa using hc

@[simp]
lemma bosonicProj_fermionicProj_eq_zero (a : 𝓕.WickAlgebra) :
    bosonicProj (fermionicProj a).1 = 0 := by
  apply bosonicProj_mem_fermionic
  exact Submodule.coe_mem (fermionicProj a)

@[simp]
lemma fermionicProj_bosonicProj_eq_zero (a : 𝓕.WickAlgebra) :
    fermionicProj (bosonicProj a).1 = 0 := by
  apply fermionicProj_mem_bosonic
  exact Submodule.coe_mem (bosonicProj a)

@[simp]
lemma bosonicProj_bosonicProj_eq_bosonicProj (a : 𝓕.WickAlgebra) :
    bosonicProj (bosonicProj a).1 = bosonicProj a := by
  apply bosonicProj_mem_bosonic

@[simp]
lemma fermionicProj_fermionicProj_eq_fermionicProj (a : 𝓕.WickAlgebra) :
    fermionicProj (fermionicProj a).1 = fermionicProj a := by
  apply fermionicProj_mem_fermionic

@[simp]
lemma bosonicProj_of_bosonic_part
    (a : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i))) :
    bosonicProj (a bosonic).1 = (a bosonic) := by
  apply bosonicProj_mem_bosonic

@[simp]
lemma bosonicProj_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i))) :
    bosonicProj (a fermionic).1 = 0 := by
  apply bosonicProj_mem_fermionic
  exact Submodule.coe_mem (a.toFun fermionic)

@[simp]
lemma fermionicProj_of_bosonic_part
    (a : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i))) :
    fermionicProj (a bosonic).1 = 0 := by
  apply fermionicProj_mem_bosonic
  exact Submodule.coe_mem (a.toFun bosonic)

@[simp]
lemma fermionicProj_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i))) :
    fermionicProj (a fermionic).1 = (a fermionic) := by
  apply fermionicProj_mem_fermionic

/-!

## The grading

-/

lemma coeAddMonoidHom_apply_eq_bosonic_plus_fermionic
    (a : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i))) :
    DirectSum.coeAddMonoidHom statSubmodule a = a.1 bosonic + a.1 fermionic := by
  let C : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i)) → Prop :=
    fun a => DirectSum.coeAddMonoidHom statSubmodule a = a.1 bosonic + a.1 fermionic
  change C a
  apply DirectSum.induction_on
  · simp [C]
  · intro i x
    simp only [DFinsupp.toFun_eq_coe, DirectSum.coeAddMonoidHom_of, C]
    rw [DirectSum.of_apply, DirectSum.of_apply]
    match i with
    | bosonic => simp
    | fermionic => simp
  · intro x y hx hy
    simp_all only [C, DFinsupp.toFun_eq_coe, map_add, DirectSum.add_apply, Submodule.coe_add]
    abel

lemma directSum_eq_bosonic_plus_fermionic
    (a : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i))) :
    a = (DirectSum.of (fun i => ↥(statSubmodule (𝓕 := 𝓕) i)) bosonic) (a bosonic) +
    (DirectSum.of (fun i => ↥(statSubmodule (𝓕 := 𝓕) i)) fermionic) (a fermionic) := by
  let C : DirectSum FieldStatistic (fun i => (statSubmodule (𝓕 := 𝓕) i)) → Prop :=
    fun a => a = (DirectSum.of (fun i => ↥(statSubmodule (𝓕 := 𝓕) i)) bosonic) (a bosonic) +
    (DirectSum.of (fun i => ↥(statSubmodule (𝓕 := 𝓕) i)) fermionic) (a fermionic)
  change C a
  apply DirectSum.induction_on
  · simp [C]
  · intro i x
    simp only [C]
    match i with
    | bosonic =>
      simp only [DirectSum.of_eq_same, left_eq_add]
      rw [DirectSum.of_eq_of_ne]
      simp only [map_zero]
      simp
    | fermionic =>
      simp only [DirectSum.of_eq_same]
      rw [DirectSum.of_eq_of_ne]
      simp only [map_zero, zero_add]
      simp
  · intro x y hx hy
    simp only [DirectSum.add_apply, map_add, C] at hx hy ⊢
    conv_lhs => rw [hx, hy]
    abel

/-- For a field statistic `𝓕`, the algebra `𝓕.WickAlgebra` is graded by `FieldStatistic`.
  Those `ofCrAnList φs` for which `φs` has an overall `bosonic` statistic
  (i.e. `𝓕 |>ₛ φs = bosonic`) span `bosonic`
  submodule, whilst those `ofCrAnList φs` for which `φs` has an overall `fermionic` statistic
  (i.e. `𝓕 |>ₛ φs = fermionic`) span the `fermionic` submodule. -/
instance WickAlgebraGrade : GradedAlgebra (A := 𝓕.WickAlgebra) statSubmodule where
  one_mem := by
    simp only [statSubmodule]
    refine Submodule.mem_span.mpr fun p a => a ?_
    simp only [Set.mem_setOf_eq]
    use []
    simp only [ofCrAnList, ofCrAnListF_nil, map_one, ofList_empty, true_and]
    rfl
  mul_mem f1 f2 a1 a2 h1 h2 := by
    let p (a2 : 𝓕.WickAlgebra) (hx : a2 ∈ statSubmodule f2) : Prop :=
      a1 * a2 ∈ statSubmodule (f1 + f2)
    change p a2 h2
    apply Submodule.span_induction
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨φs, rfl, h⟩ := hx
      simp only [p]
      let p (a1 : 𝓕.WickAlgebra) (hx : a1 ∈ statSubmodule f1) : Prop :=
        a1 * ofCrAnList φs ∈ statSubmodule (f1 + f2)
      change p a1 h1
      apply Submodule.span_induction (p := p)
      · intro y hy
        obtain ⟨φs', rfl, h'⟩ := hy
        simp only [p]
        rw [← ofCrAnList_append]
        refine Submodule.mem_span.mpr fun p a => a ?_
        simp only [Set.mem_setOf_eq]
        use φs' ++ φs
        simp only [ofList_append, h', h, true_and]
        cases f1 <;> cases f2 <;> rfl
      · simp [p]
      · intro x y hx hy hx1 hx2
        simp only [add_mul, p]
        exact Submodule.add_mem _ hx1 hx2
      · intro c a hx h1
        simp only [Algebra.smul_mul_assoc, p]
        exact Submodule.smul_mem _ _ h1
      · exact h1
    · simp [p]
    · intro x y hx hy hx1 hx2
      simp only [mul_add, p]
      exact Submodule.add_mem _ hx1 hx2
    · intro c a hx h1
      simp only [Algebra.mul_smul_comm, p]
      exact Submodule.smul_mem _ _ h1
  decompose' a := DirectSum.of (fun i => (statSubmodule (𝓕 := 𝓕) i)) bosonic (bosonicProj a)
    + DirectSum.of (fun i => (statSubmodule (𝓕 := 𝓕) i)) fermionic (fermionicProj a)
  left_inv a := by
    trans a.bosonicProj + a.fermionicProj
    · simp
    · exact bosonicProj_add_fermionicProj a
  right_inv a := by
    rw [coeAddMonoidHom_apply_eq_bosonic_plus_fermionic]
    simp only [DFinsupp.toFun_eq_coe, map_add, bosonicProj_of_bosonic_part,
      bosonicProj_of_fermionic_part, add_zero, fermionicProj_of_bosonic_part,
      fermionicProj_of_fermionic_part, zero_add]
    conv_rhs => rw [directSum_eq_bosonic_plus_fermionic a]

end
end WickAlgebra
end FieldSpecification
