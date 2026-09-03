# Symmetry, Covariance, and Representation Theory: a Roadmap

This is the design document for the next layer on top of `OVERVIEW.md`: measurement theory
(§9–§10) plus the symmetry layer (§13's "Symmetry" paragraph, `OrderUnit/Symmetry.lean`), combined
with representation theory to classify covariant objects and reduce infinite-dimensional problems
to irreducible sectors. Recorded here verbatim (lightly reformatted) as the reference for
formalization work; see the bottom for the status of what has actually been built against it.

## The clean picture

> review's operational structure + your infinite measurable framework + symmetry actions =
> physical measurement theory with representation theory.

## 1. What the review contributes

The basic system is an ordered observable space $(\mathcal A, \mathcal A_+, 1)$ with enough
monotone structure to define normal states and countably additive measurements. For an outcome
space $X$, use the classical observable system $\mathcal C_X = B_b(X,\mathbb R)$. A measurement of
$\mathcal A$ with outcomes in $X$ is a normal positive unital map $M : \mathcal C_X \to \mathcal A$.
Then:

- $M(\mathbf 1_S)$ is the effect associated with $S \subseteq X$;
- $\omega \circ M$ is the outcome probability measure in state $\omega$;
- composing $M$ with a classical Markov map is measurement post-processing;
- two measurements are compatible if they arise as marginals of one joint measurement;
- an instrument retains both the classical outcome and a quantum output system;
- measure-and-prepare channels factor through some $\mathcal C_X$.

## 2. Add symmetry independently

A topological group $G$ acts on the physical system, $\alpha : G \to \operatorname{Aut}(\mathcal A)$.
The automorphisms should preserve positivity, the unit, relevant countable suprema, and
topology/normality. For quantum systems, $\mathcal A = M_{\mathrm{sa}}$,
$\alpha_g(a) = U_g a U_g^*$, where $U$ is a strongly continuous projective unitary representation.
For a classical $G$-space $X$, $(\beta_g f)(x) = f(g^{-1}x)$ defines the corresponding
representation on $B_b(X)$.

A measurement is **covariant** precisely when $\alpha_g \circ M = M \circ \beta_g$. Equivalently,
its POVM satisfies $E(gS) = \alpha_g(E(S))$. Representation theory studies measurements as
intertwiners.

## 3. First concrete example: the qubit

For the spin-$\tfrac12$ representation of $SU(2)$, $\mathcal H = \mathbb C^2$. The induced
conjugation representation on Hermitian operators decomposes as
$B(\mathbb C^2)_{\mathrm{sa}} = \mathbb R I \oplus \operatorname{span}_{\mathbb R}\{\sigma_x,\sigma_y,\sigma_z\}$
— irreducible sectors of spin $0$ and spin $1$, $0 \oplus 1$. An $SU(2)$-covariant unital channel
must act as the identity on the scalar sector and, by Schur's lemma, as a scalar on the vector
sector: $I \mapsto I$, $\sigma_i \mapsto \lambda \sigma_i$. So the entire family of rotationally
covariant qubit channels reduces to
$\rho = \tfrac12(I + \mathbf r\cdot\boldsymbol\sigma) \mapsto \tfrac12(I + \lambda\,\mathbf
r\cdot\boldsymbol\sigma)$. Complete positivity further restricts $-\tfrac13 \le \lambda \le 1$.
Instead of classifying arbitrary linear maps on a four-dimensional operator space, decomposing the
symmetry representation gives one parameter.

## 4. Covariant measurements on homogeneous spaces

For a transitive outcome space $X = G/H$ ($H$ the stabilizer of a reference outcome $x_0$), a
covariant POVM is often determined by one positive seed $T$:
$E_T(S) = \int_{\{gH : gH\in S\}} U_g T U_g^* \, d\mu(gH)$, where $T \ge 0$,
$U_h T U_h^* = T$ for $h\in H$, and $\int_{G/H} U_g T U_g^* \, d\mu(gH) = I$. The **imprimitivity
theorem**: covariant PVMs on $G/H$ correspond to representations induced from $H$; the generalized
version treats POVMs through dilation to a covariant PVM.

## 5. Position as a covariant measurement

$G = \mathbb R^d$ acting by translation on $X = \mathbb R^d$: a position measurement satisfies
$U(a) E_Q(S) U(a)^* = E_Q(S+a)$, i.e. $\alpha_a M_Q = M_Q \beta_a$. $U$ and $E_Q$ form a **system
of imprimitivity**; representation theory describes which Hilbert-space representations can
support such a position observable (the Schrödinger representation arises as an induced
representation). The translation representation's own spectral decomposition,
$U(a) = \int_{\mathbb R^d} e^{-ia\cdot p}\, dE_P(p)$, is the momentum measurement. Position is a
covariant PVM for the translation action on configuration space; momentum is the spectral measure
diagonalizing the translation representation itself.

## 6. Phase-space POVMs

The projective Weyl representation $W(q,p)$ of phase-space translations gives a covariant
phase-space POVM $E_T(Z) = \frac{1}{(2\pi\hbar)^d}\int_Z W(q,p) T W(q,p)^* \, dq\,dp$ for a density
operator seed $T$: sharply localized $T$ gives good spatial/poor momentum resolution, Gaussian $T$
gives a Gaussian phase-space measurement, the oscillator vacuum gives the coherent-state/Husimi
measurement. Symmetry determines the form of the whole POVM; positivity and normalization
constrain one seed.

## 7. Channels are also intertwiners

A Heisenberg channel $\Phi^* : \mathcal A_B \to \mathcal A_A$ is covariant when
$\alpha_g^A \circ \Phi^* = \Phi^* \circ \alpha_g^B$. The action on operator space,
$a \mapsto U_g a U_g^*$, behaves like $U \otimes \overline U$. If
$U_A \otimes \overline{U_A} \simeq \bigoplus_\lambda V_\lambda \otimes M_\lambda^A$ (similarly for
$B$), a covariant channel can only map equal irreducible sectors to each other; its remaining
freedom lives in the multiplicity spaces $M_\lambda$. Multiplicity-free: Schur's lemma says the
channel acts by one scalar per irreducible sector, and complete positivity becomes a positivity
condition on those few coefficients (the symmetry blocks of the Choi operator).

## 8. Composite systems and angular momentum

$U_{AB} = U_A \otimes U_B$; for $SU(2)$,
$\mathcal H_{j_1}\otimes\mathcal H_{j_2} \simeq \bigoplus_{j=|j_1-j_2|}^{j_1+j_2} \mathcal H_j$,
organizing invariant states/effects, total-spin measurements, selection rules, covariant channels,
invariant interactions, entanglement sectors. Two spin-$\tfrac12$ particles:
$\mathbb C^2\otimes\mathbb C^2 \simeq \mathcal H_0\oplus\mathcal H_1$; every rotationally invariant
observable is $a = \lambda_0 P_0 + \lambda_1 P_1$ (singlet/triplet projections), so every
rotationally invariant binary measurement is determined by two numbers,
$E = e_0 P_0 + e_1 P_1$, $0 \le e_0,e_1 \le 1$.

## 9. Symmetry simplifies compatibility

For covariant $M_1, M_2$, compatibility asks for a joint measurement $J$ with the right marginals.
For compact $G$, if any joint measurement exists, average it:
$\overline J = \int_G \alpha_g \circ J \circ \beta_{g^{-1}} \, dg$. The averaged joint measurement
stays positive, unital, has the same covariant marginals, and is itself covariant — so
compatibility of covariant measurements may be tested only among covariant joint measurements
(same for compatible channels, instruments, incompatibility witnesses, discrimination strategies,
estimation procedures). Noncompact groups have no normalized Haar average, so this needs extra
assumptions or a different construction.

## 10. Symmetry simplifies measurement optimization

If the state ensemble, the cost function, and the admissible measurements are all $G$-invariant,
averaging any measurement gives a covariant one with the same average performance — so one may
optimize over covariant measurements only, i.e. optimize the seed $T$ instead of an arbitrary POVM
$E$. Useful for state discrimination, parameter estimation, symmetric-ensemble tomography,
direction/phase estimation, covariant reconstruction, informationally complete measurements
(checkable representation-theoretically: the measurement orbit must contain every irreducible
component occurring in the observable space).

## 11. Infinite-dimensional representation theory

**Compact $G$**: $\mathcal H \simeq \bigoplus_{\lambda\in\widehat G} V_\lambda \otimes M_\lambda$
(Peter–Weyl), $V_\lambda$ finite-dimensional. The friendly setting: rotations, compact internal
symmetries, angular momentum, compact configuration spaces.

**Noncompact/abelian $G$**: direct integrals, $\mathcal H \simeq \int^\oplus_{\widehat G} \mathcal
H_\lambda \, d\mu(\lambda)$. For locally compact abelian $G$, the spectral theorem for
representations gives a PVM on the dual group: $U_g = \int_{\widehat G} \chi(g)\, dE(\chi)$.
Examples: $G=\mathbb R$ (energy spectrum), $G=\mathbb R^d$ (momentum spectrum), $G=\mathbb Z$
(quasi-momentum on the circle), lattice translations (Bloch decomposition). This is where
representation theory merges completely with spectral-measure theory.

## 12. What to formalize

The basic measurement layer stays symmetry-free: $M : B_b(X) \to \mathcal A$. Then add
`SymmetryAction(G, A)`, `MeasurableAction(G, X)`, and the predicate
`IsCovariant(M) :⟺ ∀g, α_g ∘ M = M ∘ β_g` (similarly for channels and instruments).

Theorem sequence, roughly in order of tractability:
1. a group action induces actions on states and effects;
2. covariance is preserved by composition;
3. post-processing by an equivariant Markov kernel preserves covariance;
4. marginals of a covariant joint measurement are covariant;
5. compact-group averaging produces a covariant measurement/channel;
6. invariant optimization problems admit covariant optimizers;
7. quantum conjugation actions decompose through $U \otimes \overline U$;
8. multiplicity-free decompositions classify covariant channels;
9. covariant PVMs form systems of imprimitivity;
10. one-parameter representations produce spectral measurements.

**Division of labor**: the ordered normal framework (`OVERVIEW.md` §1–§12) defines what states,
measurements, and channels *are*. The operational structure (§9–§10) gives their operational
relations. Representation theory uses symmetry to classify them and reduce otherwise
infinite-dimensional problems to irreducible sectors, multiplicity spaces, and spectral measures.

---

## Status (updated as formalization proceeds)

See `measurement-as-channel-progress.md` (Claude memory) for the full, authoritative,
independently-verified record. Summary of item 12's theorem sequence, and the concretizations
around it:

- **Item 1** (group action induces actions on states and effects) — built. `Symmetry E` already
  acted on states (`OrderUnit/Symmetry.lean`); `Measurement/Covariance.lean` adds the effect action
  (`Symmetry.instSMulEffect`, via `UnitalPositiveLinearMap.mapEffect` — the general "a channel
  sends effects to effects" fact, previously only prose in `OVERVIEW.md`).
- **Item 2 / §7's algebraic core** ("channels are also intertwiners", covariance preserved under
  composition) — built, in the general form: `UnitalPositiveLinearMap.IsCovariant` (a channel
  intertwining two symmetry actions) and `.IsCovariant.comp`.
- **Items 3–4** (post-processing by an equivariant classical channel preserves covariance;
  marginals of a covariant joint measurement are covariant), specialized to finite-outcome
  measurements — **built**, in `Measurement/FiniteCovariance.lean`: the induced action
  `G →* Symmetry (ι → ℝ)` of a `G`-action on a finite outcome-label type `ι` (`inducedAction`),
  `postprocess_isCovariant`, and `marginal_isCovariant` (via `classicalPullback_isCovariant`
  specialized to `Prod.fst` under the diagonal product action on `ι × κ`). Sorry-free, wired into
  `PhyslibAlpha.lean`, full library rebuilds clean.
- **§2's concretization** ($\alpha_g(a) = U_g a U_g^*$ for a unitary representation) — built in
  full in `CStarAlgebra/ConjugationSymmetry.lean`: conjugation by a unitary is a genuine
  `Symmetry (selfAdjoint A)`, the assignment is a group homomorphism `unitary A →* Symmetry
  (selfAdjoint A)` (algebraically confirmed, not just asserted, to be a homomorphism and not an
  anti-homomorphism), and composing with a representation `G →* unitary A` gives exactly
  `G →* Symmetry (selfAdjoint A)`.
- **Item 8 / §3's "Schur's lemma classifies covariant channels"** — the *abstract* version is
  built (`Measurement/Schur.lean`): a finite direct-sum decomposition with an explicit per-block
  Schur hypothesis (plus an explicit block-preservation hypothesis on the map, since killing
  cross-terms between distinct blocks is a separate fact not derived here) gives one scalar per
  block, specialized to `IsCovariant` channels. The *concrete* qubit/$SU(2)$ computation from §3 is
  **not** built: mathlib's own Schur's lemma needs an algebraically closed field, genuinely false
  over $\mathbb R$ (the real Schur hypothesis for the spin-1 sector is representation-theoretic
  input this roadmap cites as given, not something free), and mathlib has no Pauli matrices and
  keeps the C\*-order on matrices behind a separate wrapper type from plain `Matrix`. Both are real
  obstructions, not missing effort.
- **Items 5–6** (compact-group Haar averaging produces a covariant measurement/channel; invariant
  optimization admits covariant optimizers) — **not attempted**. Averaging needs a Bochner integral
  of an $E$-valued function of the group element, which needs completeness of $E$ — the same gap
  `OrderUnit/Effect/Integral.lean` already hit and left open (no `CompleteSpace` structure exists
  for a general order-unit space in this codebase yet).
- **Spotted, not yet done**: `exists_scalar_of_isSchurBlock`'s direct-sum/block-invariance
  hypotheses are currently unused (honestly documented as such in the file) — the theorem only
  pins `f` down block-by-block, when the direct-sum hypothesis could extend that to `f`'s value on
  *all* of `E` via the component decomposition `x = ∑ i, xᵢ`, `f x = ∑ i, cᵢ • xᵢ`. A real,
  well-scoped strengthening worth doing, not just a cosmetic one.
- **Items 9–10** (covariant PVMs as systems of imprimitivity; one-parameter representations as
  spectral measures) and **§4–§6, §8, §11** (the imprimitivity theorem, position/momentum as a
  system of imprimitivity, phase-space POVMs, angular-momentum tensor decomposition, Peter–Weyl
  and the locally-compact-abelian spectral theorem) — **not attempted**. Each is a substantial,
  largely self-contained representation-theory formalization project in its own right, well beyond
  a single pass; genuinely worth doing eventually, but honestly out of scope here.
