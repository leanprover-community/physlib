# Title: Formalization of the Standard Model
authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith

JTS: (Author list alphabetical by last name matching conventions in this area.)

## Abstract

The Standard Model of particle physics is our most successful theory of elementary physics. The key ingredient is the Standard Model Lagrangian. We formalize this in the interactive theorem prover Lean 4. This opens the door to .....

## 1. Introduction

The Standard Model of particle physics consists of the gauge group `G := SU(3) × SU(2) × U(1)` acting on a matter content consisting of 45 Weyl-fermions which collect into 15 irreducible representations of `G`, conventionally written as `Q_i`, `u_i`, `d_i`, `L_i`, and `e_i` for `i ∈ {0, 1, 2}`. The gauge group itself contributes the gauge bosons `G^a_μ`, `W^a_μ` and `B^a_μ`. There is also the Higgs boson `H` which is a complex scalar.

At each point `x` in space the Lagrangian is a polynomial function in the values of these fields at `x` as well as all of their derivatives at `x` which is invariant under the local action of the gauge group and the (global) action of the Lorentz group. The aim of this project is to formally verify that the only terms which can appear in such a Lagrangian are those known to appear in the SM Lagrangian, up-to total derivatives. In this sense we 'formally verify the Standard Model'.

Along the way we will also prove another theorem about the SM Lagrangian. In any oder of an EFT expansion gauge invariance implies that the lagrangian can be written as a polynomial in terms of just the field strengths, the matter fields, including the Higgs and their covariant derivatives. In other words, the gauge bosons must come packaged as a field strength or a covariant derivative. After this, only the global action of the gauge group matters for invariance.

Of course, there is no question of the actual correctness of these theorems. Thus we want the reader of this project to take away two things: 1) That we are now at a stage where we can formally verify the standard model Lagrangian, and 2) That we have built a reusable API so that one can formally verify (with the help of AI or by hand) other similar problems in high-energy physics, such as EFT expansions, or allowed terms in BSM theories.



## 2. Overview

In this paper we formalize the Standard Model Lagrangian. To do that we must first say what a Lagrangian is, and it is worth building that up from what is actually in front of us.

At the point `x` we have the fields: the gauge bosons, the fermions and the Higgs. We also have their conjugates, and all of their derivatives — `∂_μ H`, `∂_μ∂_ν H`, and so on. These are the ingredients, and a Lagrangian is built from nothing else.

To build one we add these ingredients, scale them by complex numbers, and multiply them together. Those three operations are exactly what an associative algebra over `ℂ` provides — so whatever the fields are, they are elements of such an algebra, which we call `B`.

Nothing further about B is ever used: no norm, no topology, no involution, and no commitment as to what its elements are. We therefore do not fix it. B is an arbitrary `ℂ`-algebra, and the fields are an arbitrary family of its elements, labelled the way the Standard Model fields are labelled.

What we do need to know is how those elements behave inside `B`:

- how they multiply past one another — the fermionic ones anticommute, the bosonic ones commute;
- how the gauge group acts on them;
- how the Lorentz group acts on them;
- what mass dimension each one carries.

`IsStandardModel` is precisely this package: an algebra `B`, a family of elements in it, an action of the gauge group and an action of the Lorentz group, together with the requirement that they fit together as the Standard Model fields do.




**The data structures**

The main story is carried by three data structures. The first two are predicates — conditions on an arbitrary algebra B and a family of operators in it — while the third is a concrete algebra.

- `IsStandardModel`: the condition that a family of operators in an algebra `B` behaves like the Standard Model fields — the gauge bosons, fermions and Higgs, together with their conjugates and all their derivatives, at a single implicit space-time point. It records how these operators commute, and how the full gauge group and the Lorentz group act on them.
- `IsCovStandardModel`: the same in covariant form. The gauge bosons are replaced by their field strengths, every derivative by a covariant derivative, and correspondingly only the global gauge group acts rather than the full one.
- `JetAlgebra`: the smallest concrete `B` containing all of these operators, subject to no relations beyond their statistics — bosonic generators commute, fermionic ones anticommute.

**The connecting theorems**

These three structures are interconnected to one another through a series of theorems:
1. `IsStandardModel.isCovStandardModel` — Every `IsStandardModel` defines a `IsCovStandardModel`, through the field strengths and the covariant derivatives.
2. `JetAlgebra.isStandardModel` — Within `JetAlgebra` there is an instance of `IsStandardModel`.
3. `JetAlgebra.isStandardModel_fieldAlgebra_eq_top` — Furthermore, the adjoin of the fields in `IsStandardModel` fully describe `JetAlgebra`.


**The reduction of invariants**

These connecting theorems can be used
to form a reduction in the invariances:
1. `IsStandardModel.forall_repJet_and_repLorentz_eq_iff` — Every invariant under the full gauge group and the Lorentz group defined through the fields in `IsStandardModel` descends from an invariant of `IsCovStandardModel` under the global gauge group and the Lorentz group. This means we only have to deal with covariant derivatives, the field strengths, the global gauge group, and the Lorentz group when looking for invariants.
2. `JetAlgebra.isStandardModel_fieldAlgebra_eq_top`(corollary of this) — Every invariant of `JetAlgebra` is an invariant defined through `IsStandardModel`.


**The invariants theorems**

Working back up the chain, we get an explict form of the invariants. Each of these give the explicit classification of the terms in the SM lagrangian up to total-derivatives, in the corresponding (general) contexts.
1. `IsCovStandardModel.mem_massWeightSubmoduleLE_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian` — The full classification of the invariants of `IsCovStandardModel` up to mass-dimension 4. They are spanned by
    - the constant `1`;
    - the Higgs mass term `H†H`;
    - the Higgs quartic `(H†H)²`, the Higgs kinetic term `∂^μH† ∂_μH`, and the two box terms `(□H†)H` and `H†□H`;
    - the gauge kinetic terms `G^a_μν G^a^μν`, `W^a_μν W^a^μν`, `B_μν B^μν`, the corresponding θ-terms `ε^μνρσ G^a_μν G^a_ρσ` and its `W`, `B` analogues, and the contractions of the twice-derived hypercharge field `∂_μ∂_ν B_ρσ`;
    - the fermion kinetic terms `ψ̄ σ̄^μ ∂_μ ψ`, one for each of the ten species and each pair of generations;
    - the Yukawa couplings `H†Q d̄`, `ε H Q ū`, `H†L ē` and their conjugates, over each pair of generations.
2. `IsStandardModel.mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian` — From this, the full classification of the invariants of `IsStandardModel` up to mass-dimension 4.
3. `JetAlgebra.mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian` — Then, from this, the full classification of the invariants of `JetAlgebra`.


**Supporting API**
All of the above are supported by API around the Gauge group, the Lorentz group, and the individual matter fields. We discuss the main API here:
- *Lorentz group invariants*: Explicit classification of the full-group invariants in an algebra of terms which transform in certain representations.
- *Global gauge group invariants*: Explicit classification of the full-group invariants in an algebra of terms which transform in certain representations.
- *Fermions*: Specification of the underlying vector spaces, the Lorentz group action, the local and global gauge group actions on them.
- *Higgs*: Specification of the underlying vector space of the Higgs, the Lorentz group action, the local and global gauge group actions on it.
- *Gauge boson*: Specification of the Gauge algebra, the adjoint action, Maurer-Cartan terms etc, in this specific setting.

## 3. The details

## 4. Future work

- BSM
- EFTs
- Improvements to group theory & algebra
- Symmetry breaking
- Connection to Feynman diagrams
- QED and the connection to EM
- Appropaite inclusion of total derivative removals.
