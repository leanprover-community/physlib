/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.QuasiLocal.Instances
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!

# Symmetries of the quantum net

A group acting on the sites acts on the operators of regions by `*`-isomorphisms, compatibly with
the inclusions.

## i. Overview

Let a group `Γ` act on the sites, all of which carry the same finite configuration space `Ω₀`. The
group moves a region `X` to `γ • X`, and a configuration of `γ • X` to one of `X` by reading the
value at `γ • x` for `x ∈ X`. This moves an operator of `X` to an operator of `γ • X`: it is a
`*`-isomorphism `A X → A (γ • X)`. It is compatible with the inclusion of regions, because it moves
the sites outside `X` to the sites outside `γ • X`.

## ii. Key results

- `cfgEquiv` : a configuration of `γ • X` is a configuration of `X`.
- `quantumIso` : the `*`-homomorphism of operators carried by `γ`.
- `quantumIso_incl` : naturality with respect to the inclusions of regions.
- `symAction` : the group acts on the quasi-local algebra by `*`-automorphisms.

## iii. Table of contents

- A. Configurations of a moved region
- B. The moved operators
- C. The action on the quasi-local algebra

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory.QuasiLocal

open scoped Matrix Pointwise

variable {S : Type*} [DecidableEq S] (Γ : Type*) [Group Γ] [MulAction Γ S]
variable (Ω₀ : Type*) [Fintype Ω₀] [DecidableEq Ω₀]

/-! ## A. Configurations of a moved region -/

/-- A configuration of the region `γ • X` is a configuration of `X`: read it at `γ • x`. -/
def cfgEquiv (γ : Γ) (X : Finset S) : Cfg (fun _ : S => Ω₀) (γ • X) ≃ Cfg (fun _ : S => Ω₀) X where
  toFun c x := c ⟨γ • x.1, Finset.smul_mem_smul_finset x.2⟩
  invFun c y := c ⟨γ⁻¹ • y.1, Finset.inv_smul_mem_iff.2 y.2⟩
  left_inv c := by
    funext y
    exact congrArg c (Subtype.ext (smul_inv_smul γ y.1))
  right_inv c := by
    funext x
    exact congrArg c (Subtype.ext (inv_smul_smul γ x.1))

variable {Γ Ω₀}

/-! ## B. The moved operators -/

/-- The operator of `γ • X` that acts as `M` after moving the configurations back to `X`. -/
def quantumIso (γ : Γ) (X : Finset S) :
    Alg (fun _ : S => Ω₀) X →⋆ₐ[ℂ] Alg (fun _ : S => Ω₀) (γ • X) where
  toFun M := Matrix.of fun c c' => M (cfgEquiv Γ Ω₀ γ X c) (cfgEquiv Γ Ω₀ γ X c')
  map_one' := by
    ext c c'
    simp only [Matrix.of_apply, Matrix.one_apply, (cfgEquiv Γ Ω₀ γ X).injective.eq_iff]
  map_mul' M N := by
    ext c c''
    simp only [Matrix.of_apply, Matrix.mul_apply]
    symm
    apply Fintype.sum_equiv (cfgEquiv Γ Ω₀ γ X)
    intro c'
    rfl
  map_zero' := by ext; simp
  map_add' M N := by ext; simp
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext c c'
    simp [Matrix.one_apply, (cfgEquiv Γ Ω₀ γ X).injective.eq_iff]
  map_star' M := by
    ext c c'
    simp

lemma smul_mono (γ : Γ) {X Y : Finset S} (h : X ≤ Y) : γ • X ≤ γ • Y :=
  Finset.smul_finset_subset_smul_finset h

omit [Fintype Ω₀] in
omit [DecidableEq Ω₀] in
lemma restr_cfgEquiv (γ : Γ) {X Y : Finset S} (h : X ≤ Y)
    (c : Cfg (fun _ : S => Ω₀) (γ • Y)) :
    restr h (cfgEquiv Γ Ω₀ γ Y c) = cfgEquiv Γ Ω₀ γ X (restr (smul_mono γ h) c) := rfl

omit [Fintype Ω₀] in
omit [DecidableEq Ω₀] in
lemma agree_cfgEquiv (γ : Γ) {X Y : Finset S} (h : X ≤ Y)
    (c c' : Cfg (fun _ : S => Ω₀) (γ • Y)) :
    Agree h (cfgEquiv Γ Ω₀ γ Y c) (cfgEquiv Γ Ω₀ γ Y c') ↔ Agree (smul_mono γ h) c c' := by
  constructor
  · intro hc y hy
    obtain ⟨y₀, hy₀, hyy⟩ := Finset.mem_smul_finset.1 y.2
    have hy' : y = ⟨γ • y₀, Finset.smul_mem_smul_finset hy₀⟩ := Subtype.ext hyy.symm
    subst hy'
    have hy₀X : y₀ ∉ X := fun hx => hy (Finset.smul_mem_smul_finset hx)
    exact hc ⟨y₀, hy₀⟩ hy₀X
  · intro hc y hy
    refine hc ⟨γ • y.1, Finset.smul_mem_smul_finset y.2⟩ fun hx => hy ?_
    exact (Finset.smul_mem_smul_finset_iff γ).1 hx

/-- **Naturality**: moving operators commutes with extending them by the identity. -/
lemma quantumIso_incl (γ : Γ) {X Y : Finset S} (h : X ≤ Y) (M : Alg (fun _ : S => Ω₀) X) :
    quantumIso γ Y (inclMat h M) = inclMat (smul_mono γ h) (quantumIso γ X M) := by
  ext c c'
  simp only [quantumIso, StarAlgHom.coe_mk,
    Matrix.of_apply, inclMat_apply]
  by_cases hc : Agree (smul_mono γ h) c c'
  · rw [ite_eq_left ((agree_cfgEquiv γ h c c').2 hc), ite_eq_left hc, restr_cfgEquiv,
      restr_cfgEquiv]
  · rw [ite_eq_right (fun h' => hc ((agree_cfgEquiv γ h c c').1 h')), ite_eq_right hc]

/-! ## C. The action on the quasi-local algebra -/

/-- Transport of configurations along an equality of regions. -/
def cfgCast {X Y : Finset S} (e : X = Y) (c : Cfg (fun _ : S => Ω₀) Y) :
    Cfg (fun _ : S => Ω₀) X :=
  fun x => c ⟨x.1, e ▸ x.2⟩

/-- Transport of operators along an equality of regions. -/
def regionIso {X Y : Finset S} (e : X = Y) :
    Alg (fun _ : S => Ω₀) X →⋆ₐ[ℂ] Alg (fun _ : S => Ω₀) Y := by
  subst e
  exact StarAlgHom.id ℂ _

lemma regionIso_apply {X Y : Finset S} (e : X = Y) (M : Alg (fun _ : S => Ω₀) X)
    (c c' : Cfg (fun _ : S => Ω₀) Y) :
    regionIso e M c c' = M (cfgCast e c) (cfgCast e c') := by
  subst e; rfl

/-- The quantum net of a system whose sites all carry the same finite configuration space. -/
abbrev uniformNet (Ω₀ : Type*) [Fintype Ω₀] [DecidableEq Ω₀] : AlgebraNet S :=
  quantumNet (fun _ : S => Ω₀)

lemma of_regionIso {X Y : Finset S} (e : X = Y) (M : Alg (fun _ : S => Ω₀) X) :
    (uniformNet Ω₀).of Y (regionIso e M) = (uniformNet Ω₀).of X M := by
  subst e; rfl

/-- **The action of a site symmetry on the quasi-local algebra**: an endomorphism that moves the
observables of a region `X` to those of `γ • X`. -/
def symAct (γ : Γ) :
    (uniformNet (S := S) Ω₀).Quasilocal →⋆ₐ[ℂ] (uniformNet (S := S) Ω₀).Quasilocal :=
  (uniformNet (S := S) Ω₀).moveHom (fun X => γ • X) (fun _ _ h => smul_mono γ h)
    (fun X => quantumIso γ X) (fun h a => quantumIso_incl γ h a)

lemma symAct_of (γ : Γ) (X : Finset S) (M : Alg (fun _ : S => Ω₀) X) :
    symAct (Ω₀ := Ω₀) γ ((uniformNet Ω₀).of X M) = (uniformNet Ω₀).of (γ • X) (quantumIso γ X M) :=
  rfl

lemma quantumIso_mul (γ₁ γ₂ : Γ) (X : Finset S) (M : Alg (fun _ : S => Ω₀) X) :
    regionIso (mul_smul γ₁ γ₂ X) (quantumIso (γ₁ * γ₂) X M) =
      quantumIso γ₁ (γ₂ • X) (quantumIso γ₂ X M) := by
  ext c c'
  rw [regionIso_apply]
  have key : ∀ c : Cfg (fun _ : S => Ω₀) (γ₁ • γ₂ • X),
      cfgEquiv Γ Ω₀ (γ₁ * γ₂) X (cfgCast (mul_smul γ₁ γ₂ X) c) =
        cfgEquiv Γ Ω₀ γ₂ X (cfgEquiv Γ Ω₀ γ₁ (γ₂ • X) c) := fun c => by
    funext x
    exact congrArg c (Subtype.ext (mul_smul γ₁ γ₂ x.1))
  simp only [quantumIso, StarAlgHom.coe_mk,
    Matrix.of_apply, key]

lemma quantumIso_one (X : Finset S) (M : Alg (fun _ : S => Ω₀) X) :
    regionIso (one_smul Γ X) (quantumIso (1 : Γ) X M) = M := by
  ext c c'
  rw [regionIso_apply]
  have key : ∀ c : Cfg (fun _ : S => Ω₀) X,
      cfgEquiv Γ Ω₀ 1 X (cfgCast (one_smul Γ X) c) = c := fun c => by
    funext x
    exact congrArg c (Subtype.ext (one_smul Γ x.1))
  simp only [quantumIso, StarAlgHom.coe_mk,
    Matrix.of_apply, key]

/-- The action of site symmetries is multiplicative. -/
lemma symAct_mul (γ₁ γ₂ : Γ) :
    symAct (Ω₀ := Ω₀) (S := S) (γ₁ * γ₂) = (symAct γ₁).comp (symAct γ₂) := by
  refine StarAlgHom.ext fun x => ?_
  obtain ⟨X, a, rfl⟩ := (uniformNet (S := S) Ω₀).exists_of x
  calc symAct (Ω₀ := Ω₀) (γ₁ * γ₂) ((uniformNet Ω₀).of X a)
      = (uniformNet Ω₀).of ((γ₁ * γ₂) • X) (quantumIso (γ₁ * γ₂) X a) := symAct_of _ _ _
    _ = (uniformNet Ω₀).of (γ₁ • γ₂ • X)
          (regionIso (mul_smul γ₁ γ₂ X) (quantumIso (γ₁ * γ₂) X a)) :=
        (of_regionIso (S := S) (Ω₀ := Ω₀) _ _).symm
    _ = (uniformNet Ω₀).of (γ₁ • γ₂ • X) (quantumIso γ₁ (γ₂ • X) (quantumIso γ₂ X a)) := by
        exact congrArg ((uniformNet (S := S) Ω₀).of (γ₁ • γ₂ • X)) (quantumIso_mul γ₁ γ₂ X a)
    _ = symAct (Ω₀ := Ω₀) γ₁ ((uniformNet Ω₀).of (γ₂ • X) (quantumIso γ₂ X a)) :=
        (symAct_of _ _ _).symm
    _ = ((symAct (Ω₀ := Ω₀) γ₁).comp (symAct γ₂)) ((uniformNet Ω₀).of X a) := by
        rw [StarAlgHom.comp_apply, symAct_of γ₂ X a]

lemma symAct_one : symAct (Ω₀ := Ω₀) (S := S) (1 : Γ) = StarAlgHom.id ℂ _ := by
  refine StarAlgHom.ext fun x => ?_
  obtain ⟨X, a, rfl⟩ := (uniformNet (S := S) Ω₀).exists_of x
  calc symAct (Ω₀ := Ω₀) (1 : Γ) ((uniformNet Ω₀).of X a)
      = (uniformNet Ω₀).of ((1 : Γ) • X) (quantumIso 1 X a) := symAct_of _ _ _
    _ = (uniformNet Ω₀).of X (regionIso (one_smul Γ X) (quantumIso (1 : Γ) X a)) :=
        (of_regionIso (S := S) (Ω₀ := Ω₀) _ _).symm
    _ = (uniformNet Ω₀).of X a := congrArg ((uniformNet (S := S) Ω₀).of X) (quantumIso_one X a)

/-- **A group acting on the sites acts on the quasi-local algebra by automorphisms.** -/
def symEquiv (γ : Γ) : (uniformNet (S := S) Ω₀).Quasilocal ≃⋆ₐ[ℂ]
    (uniformNet (S := S) Ω₀).Quasilocal :=
  StarAlgEquiv.ofStarAlgHom (symAct γ) (symAct γ⁻¹)
    (by rw [← symAct_mul, inv_mul_cancel, symAct_one])
    (by rw [← symAct_mul, mul_inv_cancel, symAct_one])

/-- **The symmetry action** of a group on the sites, as a homomorphism to the automorphisms of the
quasi-local algebra. -/
def symAction : Γ →* ((uniformNet (S := S) Ω₀).Quasilocal ≃⋆ₐ[ℂ]
    (uniformNet (S := S) Ω₀).Quasilocal) where
  toFun := symEquiv
  map_one' := StarAlgEquiv.ext fun x => by
    change symAct (1 : Γ) x = x
    rw [symAct_one]; rfl
  map_mul' γ₁ γ₂ := StarAlgEquiv.ext fun x => by
    change symAct (γ₁ * γ₂) x = symAct γ₁ (symAct γ₂ x)
    rw [symAct_mul]; rfl

end QuasiLocal

end CondensedMatter

end
