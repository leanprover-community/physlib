/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.CauchyInterfaces
public import Mathlib.Order.Zorn

/-!

# M5: Maximal development via Choquet–Bruhat–Geroch Zorn argument

## i. Overview

This module formalises the Choquet–Bruhat–Geroch (1969) maximal-development
construction at the extension/amalgamation interface level and inhabits
`MaximalDevelopmentCertificate` in two settings:

1. **Abstract Choquet–Bruhat–Geroch Zorn theorem (`OrderedDevelopmentSystem`)**:
   given a development relation `IsDevelopment` determining unique Cauchy data,
   a transitive extension preorder `Extends` in which every nonempty chain has
   an upper bound and any two developments of the same data admit a common
   extension (`amalgamate`), Mathlib's
   `exists_maximal_of_nonempty_chains_bounded` yields a maximal development
   (`exists_maximal`), amalgamation + maximality proves uniqueness up to isometry
   (`unique_up_to_isometry`), and together they inhabit
   `MaximalDevelopmentCertificate S.toDevelopmentInterface`.
2. **Concrete open-domain instantiation (`intervalMaximalDevelopmentCertificate`)**:
   zero-hypothesis instantiation on open subsets `U ⊆ ℝ` containing `0` ordered
   by `⊆` (`⋃₀ c` for chain upper bounds, `U ∪ V` for amalgamation), inhabiting
   `MaximalDevelopmentCertificate`.

Scope boundary: proving the geometric extension, isometric-amalgamation, and
Zorn/Sbierski patching axioms for general globally hyperbolic 4D Lorentzian
Einstein developments of arbitrary smooth 3-manifold data remains outside this
abstract/1D domain layer.

## ii. Key results

- `OrderedDevelopmentSystem`, `OrderedDevelopmentSystem.exists_maximal`,
  `unique_up_to_isometry` : the abstract Choquet–Bruhat–Geroch Zorn argument.
- `OrderedDevelopmentSystem.maximalDevelopmentCertificate` : the abstract M5
  certificate.
- `chartDevelopmentInterface`, `ChartMaximalDevelopmentCertificate` : the
  chart-level M5 interface, with `ChartSpacetime.IsIsometric` as its uniqueness
  relation.
- `intervalDevelopmentSystem`, `intervalMaximalDevelopmentCertificate` : the
  concrete zero-hypothesis open-domain instance.

## iii. Table of contents

- A. Abstract Choquet–Bruhat–Geroch Zorn maximal development theorem
- B. Chart-level isometry interface
- C. Concrete zero-hypothesis open-domain maximal development

## iv. References

* J. Sbierski, *On the existence of a maximal Cauchy development for the
  Einstein equations — a dezornification*, arXiv:1309.7591, §2, p. 2.
  [ref: sbierski_2013, p. 2]
-/

@[expose] public section

open Set

namespace GeneralRelativity

universe u v

/-! ## A. Abstract Choquet–Bruhat–Geroch Zorn maximal development theorem -/

/-- Abstract Choquet–Bruhat–Geroch development system: a relation `IsDevelopment`
(determining unique Cauchy data on the slice) equipped with a transitive
extension preorder `Extends`, an isometry predicate forced by mutual
extension, chain upper bounds, and pairwise amalgamation of developments of the
same initial data. -/
structure OrderedDevelopmentSystem where
  /-- Initial-data type. -/
  Data : Type u
  /-- Candidate spacetime-domain type. -/
  Spacetime : Type v
  /-- Development relation `IsDevelopment M d`. -/
  IsDevelopment : Spacetime → Data → Prop
  /-- Every development uniquely determines the initial data on its slice. -/
  unique_data : ∀ {M d₁ d₂}, IsDevelopment M d₁ → IsDevelopment M d₂ → d₁ = d₂
  /-- Extension preorder `Extends M N` (`M` embeds/extends into `N`). -/
  Extends : Spacetime → Spacetime → Prop
  /-- Reflexivity of extension. -/
  extends_refl : ∀ M, Extends M M
  /-- Transitivity of extension. -/
  extends_trans : ∀ {M N P}, Extends M N → Extends N P → Extends M P
  /-- Isometry relation between developments. -/
  IsIsometric : Spacetime → Spacetime → Prop
  /-- Mutual extension implies isometry. -/
  isometric_of_antisymm : ∀ {M N}, Extends M N → Extends N M → IsIsometric M N
  /-- Existence of at least one local development for every initial-data set. -/
  exists_dev : ∀ d : Data, ∃ M : Spacetime, IsDevelopment M d
  /-- Every nonempty chain of developments of `d` has an upper bound developing `d`. -/
  chain_ub : ∀ (d : Data) (c : Set Spacetime),
    (∀ M ∈ c, IsDevelopment M d) →
    IsChain Extends c →
    c.Nonempty →
    ∃ U : Spacetime, IsDevelopment U d ∧ ∀ M ∈ c, Extends M U
  /-- Any two developments of the same `d` admit a common extension developing `d`. -/
  amalgamate : ∀ (d : Data) (M N : Spacetime),
    IsDevelopment M d → IsDevelopment N d →
    ∃ W : Spacetime, IsDevelopment W d ∧ Extends M W ∧ Extends N W

/-- A development `M` is maximal in `S` if every same-data extension `N` extends
back into `M` (`Extends M N → Extends N M`). -/
def OrderedDevelopmentSystem.IsMaximal (S : OrderedDevelopmentSystem)
    (M : S.Spacetime) : Prop :=
  ∀ (d : S.Data) (N : S.Spacetime),
    S.IsDevelopment M d → S.IsDevelopment N d → S.Extends M N → S.Extends N M

/-- Package an `OrderedDevelopmentSystem` as an M5 `DevelopmentInterface`. -/
def OrderedDevelopmentSystem.toDevelopmentInterface
    (S : OrderedDevelopmentSystem.{u, v}) : DevelopmentInterface.{u, v} where
  Data := S.Data
  Spacetime := S.Spacetime
  IsDevelopment := S.IsDevelopment
  IsMaximal := S.IsMaximal
  IsIsometric := S.IsIsometric

/-- **Zorn existence of a maximal development** (abstract 1969
Choquet–Bruhat–Geroch argument): every initial-data set admits a maximal
development via `exists_maximal_of_nonempty_chains_bounded`. -/
lemma OrderedDevelopmentSystem.exists_maximal
    (S : OrderedDevelopmentSystem) (d : S.Data) :
    ∃ M : S.Spacetime, S.IsDevelopment M d ∧ S.IsMaximal M := by
  let Dev := {M : S.Spacetime // S.IsDevelopment M d}
  obtain ⟨M₀, hM₀⟩ := S.exists_dev d
  have : Nonempty Dev := ⟨⟨M₀, hM₀⟩⟩
  let r : Dev → Dev → Prop := fun x y => S.Extends x.1 y.1
  have hchain : ∀ c : Set Dev, IsChain r c → c.Nonempty → ∃ ub : Dev, ∀ a ∈ c, r a ub := by
    intro c hc hne
    let c' : Set S.Spacetime := Subtype.val '' c
    have hc'_dev : ∀ M ∈ c', S.IsDevelopment M d := by
      rintro M ⟨x, _, rfl⟩
      exact x.2
    have hc'_chain : IsChain S.Extends c' := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne_xy
      have hne_dev : x ≠ y := fun h => hne_xy (congrArg Subtype.val h)
      exact hc hx hy hne_dev
    have hc'_ne : c'.Nonempty := by
      rcases hne with ⟨x, hx⟩
      exact ⟨x.1, x, hx, rfl⟩
    obtain ⟨U, hU_dev, hU_ub⟩ := S.chain_ub d c' hc'_dev hc'_chain hc'_ne
    refine ⟨⟨U, hU_dev⟩, fun a ha => hU_ub a.1 ⟨a, ha, rfl⟩⟩
  have htrans : ∀ {x y z : Dev}, r x y → r y z → r x z := fun hxy hyz =>
    S.extends_trans hxy hyz
  obtain ⟨⟨M, hM_dev⟩, hM_max⟩ := exists_maximal_of_nonempty_chains_bounded hchain htrans
  refine ⟨M, hM_dev, fun d' N hMd' hNd' hMN => ?_⟩
  have hd_eq : d' = d := S.unique_data hMd' hM_dev
  subst hd_eq
  exact hM_max ⟨N, hNd'⟩ hMN

/-- **Uniqueness up to isometry** of maximal developments: any two maximal
developments `M, N` of `d` amalgamate into a common extension `W`, forcing
mutual extensions `M ↔ N` and hence `IsIsometric M N`. -/
lemma OrderedDevelopmentSystem.unique_up_to_isometry
    (S : OrderedDevelopmentSystem) (M N : S.Spacetime) (d : S.Data)
    (hM : S.IsDevelopment M d) (hN : S.IsDevelopment N d)
    (hmaxM : S.IsMaximal M) (hmaxN : S.IsMaximal N) :
    S.IsIsometric M N := by
  obtain ⟨W, hW, hMW, hNW⟩ := S.amalgamate d M N hM hN
  have hWM : S.Extends W M := hmaxM d W hM hW hMW
  have hWN : S.Extends W N := hmaxN d W hN hW hNW
  exact S.isometric_of_antisymm (S.extends_trans hMW hWN) (S.extends_trans hNW hWM)

/-- **M5 Certificate (Abstract Choquet–Bruhat–Geroch)**: every
`OrderedDevelopmentSystem` inhabits `MaximalDevelopmentCertificate`. -/
lemma OrderedDevelopmentSystem.maximalDevelopmentCertificate
    (S : OrderedDevelopmentSystem) :
    MaximalDevelopmentCertificate S.toDevelopmentInterface where
  maximal_existence := fun d => S.exists_maximal d
  uniqueness_up_to_isometry := fun M N d hM hN hmaxM hmaxN =>
    S.unique_up_to_isometry M N d hM hN hmaxM hmaxN

/-! ## B. Chart-level isometry interface -/

/-- The chart-level M5 development interface: chart developments are chart
initial data whose induced spatial metric is the chart metric, and its isometry
relation is the chart-level `ChartSpacetime.IsIsometric` API.
See arXiv:1309.7591, p. 2. [ref: sbierski_2013, p. 2] -/
def chartDevelopmentInterface
    (IsMaximal : ChartSpacetime → Prop) : DevelopmentInterface where
  Data := Unit
  Spacetime := ChartSpacetime
  IsDevelopment := fun Y _ => ∃ D : ChartInitialData Y, Y.IsChartDevelopment D
  IsMaximal := IsMaximal
  IsIsometric := ChartSpacetime.IsIsometric

/-- A chart-level maximal-development certificate, using the chart isometry API
for uniqueness.  See arXiv:1309.7591, p. 2. [ref: sbierski_2013, p. 2] -/
abbrev ChartMaximalDevelopmentCertificate
    (IsMaximal : ChartSpacetime → Prop) : Prop :=
  MaximalDevelopmentCertificate (chartDevelopmentInterface IsMaximal)

/-- **Chart-level uniqueness up to isometry**: a maximal-development certificate
for the chart interface yields an actual `ChartSpacetime.IsIsometric` witness.
See arXiv:1309.7591, p. 2. [ref: sbierski_2013, p. 2] -/
lemma ChartMaximalDevelopmentCertificate.unique_up_to_isometry
    {IsMaximal : ChartSpacetime → Prop}
    (h : ChartMaximalDevelopmentCertificate IsMaximal)
    {M N : ChartSpacetime}
    (hM : ∃ D : ChartInitialData M, M.IsChartDevelopment D)
    (hN : ∃ D : ChartInitialData N, N.IsChartDevelopment D)
    (hmaxM : IsMaximal M) (hmaxN : IsMaximal N) :
    ChartSpacetime.IsIsometric M N :=
  MaximalDevelopmentCertificate.unique_up_to_isometry (data := ()) h hM hN hmaxM hmaxN

/-! ## C. Concrete zero-hypothesis open-domain maximal development -/

/-- Concrete `OrderedDevelopmentSystem` on open time-evolution domains
`U : Set ℝ` containing `t = 0`, ordered by inclusion `⊆` with union
amalgamation and `⋃₀` chain upper bounds. -/
def intervalDevelopmentSystem : OrderedDevelopmentSystem where
  Data := Unit
  Spacetime := Set ℝ
  IsDevelopment := fun U _ => IsOpen U ∧ (0 : ℝ) ∈ U
  unique_data := fun _ _ => rfl
  Extends := fun U V => U ⊆ V
  extends_refl := fun _ => Subset.rfl
  extends_trans := fun hUV hVW => Subset.trans hUV hVW
  IsIsometric := fun U V => U = V
  isometric_of_antisymm := fun hUV hVU => Subset.antisymm hUV hVU
  exists_dev := fun _ => ⟨Set.univ, isOpen_univ, Set.mem_univ 0⟩
  chain_ub := fun _ c hc _ hne => by
    refine ⟨⋃₀ c, ⟨isOpen_sUnion fun U hU => (hc U hU).1, ?_⟩,
      fun U hU => subset_sUnion_of_mem hU⟩
    rcases hne with ⟨U₀, hU₀⟩
    exact Set.mem_sUnion.mpr ⟨U₀, hU₀, (hc U₀ hU₀).2⟩
  amalgamate := fun _ U V hU hV =>
    ⟨U ∪ V, ⟨hU.1.union hV.1, Or.inl hU.2⟩, subset_union_left, subset_union_right⟩

/-- **M5 Concrete Certificate**: zero-hypothesis `MaximalDevelopmentCertificate`
for open time-evolution domains containing `t = 0` (witnessed uniquely by
`Set.univ`). -/
lemma intervalMaximalDevelopmentCertificate :
    MaximalDevelopmentCertificate intervalDevelopmentSystem.toDevelopmentInterface :=
  intervalDevelopmentSystem.maximalDevelopmentCertificate

end GeneralRelativity
