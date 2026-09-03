# The Anatomy of a Physical System

A physical theory specifies its states, its possible measurements, and the probability a state
assigns to each measurement outcome. Classical mechanics gets these from phase space, quantum
mechanics from Hilbert space — same three ingredients, different underlying spaces. We give one
construction for both, and only specialize to ordinary quantum mechanics at the end.

It proceeds in physical stages: an order to compare outcomes by size, a unit to mark certainty,
a norm to say how distinguishable two states are.

## 1. An ordered vector space

$E$ is the space of observable quantities: functions on phase space classically, self-adjoint
operators on Hilbert space quantum-mechanically. Both add and rescale the way real numbers do, so
$E$ is a real vector space; both also compare, so $E$ carries a partial order $\le$ compatible with
that vector space structure. $x \ge 0$ means: a quantity that can never be measured negative, like
an energy above the ground state or a photon number.

## 2. The positive cone

$$
\mathrm{Cone}(E) := \{\, x \in E : x \ge 0 \,\}.
$$

These are the physically realizable, never-negative quantities — nonnegative functions
classically, positive operators quantum-mechanically — closed under addition and under scaling by
$\lambda \ge 0$. It is not yet enough on its own: nothing here says how large an outcome can get,
and nothing marks "certainty."

## 3. Add a unit: order-unit spaces

Distinguish one element $1 \in E$ — *the certain event* (the constant function $1$ on a classical
phase space; the identity operator quantum-mechanically) — and demand it dominates everything, in
finite multiples:

$$
\forall x \in E,\ \exists\, n \in \mathbb N: \quad x \le n \cdot 1. \tag{order unit}
$$

That alone is enough to later squeeze anything between $0$ and $1$. One more axiom, Archimedean:

$$
\big(\forall\, \varepsilon > 0,\ x \le \varepsilon \cdot 1\big) \;\implies\; x \le 0. \tag{Archimedean}
$$

Nothing sits infinitesimally below $1$ without being $\le 0$ outright. This alone produces a genuine
norm from the order, with no extra structure assumed:

$$
\|x\| := \inf\{\, r \ge 0 : -r\cdot 1 \le x \le r \cdot 1 \,\}.
$$

$(\text{order unit}) + (\text{Archimedean})$ is the entire structural assumption everything below is
built on.

The order-unit axiom alone, already gives something useful: every $x \in E$ splits into
a difference of two cone elements,

$$
x = x_+ - x_-, \qquad x_+, x_- \ge 0.
$$

$E$ is nothing more than the cone, taken apart this way: applying the axiom to $-x$ gives some $n$
with

$$
x = (n\cdot1 + x) - (n\cdot1),
$$

both terms in the cone.

## 4. Classical systems

$E$ is **classical** when it is a lattice: every pair $x, y \in E$ has a genuine least upper bound
$x \vee y$. An example is $\mathbb R$ itself, with $x \vee y = \max(x, y)$. We meet another instance
in §9. For a C\*-algebra (§12), it turns out to say something more familiar: commutativity.

## 5. Effects: single yes/no outcomes

$$
\mathrm{Eff}(E) := \{\, e \in E : 0 \le e \le 1 \,\}.
$$

Physically: one measurement outcome, one detector click — bounded between "never" and "always."
Effects have a complement and mix probabilistically, staying effects:

$$
e^{\perp} := 1 - e, \qquad e_t := t\, e_1 + (1-t)\, e_2 \in \mathrm{Eff}(E) \quad (t \in [0,1]).
$$

Unlike the cone (§2), which is unbounded, $\mathrm{Eff}(E)$ is bounded — by the norm of §3,
$\|e\| \le 1$ — so it has genuine extreme points. An effect is **sharp** when it cannot be written
as a genuine mixture of two *different* effects — an extreme point of $[0,1]$. Sharp effects are
the abstract stand-in for a projection; $0$ and $1$ are always sharp, and sharpness passes to the
complement.

## 6. Counting probability: weights and states

A **weight** assigns each possible outcome a number:

$$
w : \mathrm{Cone}(E) \to \mathbb R_+ \cup \{\infty\}, \text{ linear on the cone.}
$$

No requirement that $w$ be finite anywhere. On an infinite system the total energy, or the total
particle number, can genuinely be infinite in a given state, while staying finite on any single
bounded piece — the general shape of a statistical weight, or an unnormalized trace.

If $w$ is never infinite, the splitting from §3 lets it enlarge, uniquely, off the cone to all of
$E$. A weight that is also normalized, $w(1) = 1$, enlarges this way to a **state**:

$$
\omega : E \to \mathbb R, \qquad x \ge 0 \implies \omega(x) \ge 0, \qquad \omega(1) = 1.
$$

$$
\{\, w \text{ finite, normalized} \,\} \;\;\simeq\;\; \{\, \text{states } \omega \,\}.
$$

Like effects, states mix and stay states: $\omega_t := t\,\omega_1 + (1-t)\,\omega_2$ is again a
state for $t \in [0,1]$, by linearity and normalization. A state is **pure** when it cannot be
written as a mixture of two *different* states — the state-side mirror of a sharp effect.

## 7. The pairing of states and effects

Any weight $w$ pairs with any effect $e$, since $e$ already sits in the cone, bounded by the weight
of the unit:

$$
w(e) \le w(1),
$$

finite whenever $w$ is finite at $1$.

For a state (§6) — finite everywhere and normalized — the pairing above becomes the abstract Born
rule,

$$
(\omega, e) \;\longmapsto\; \omega(e) \in [0,1],
$$

the probability that $\omega$ assigns to outcome $e$.

## 8. Channels: transformations between systems

Physically, a channel is anything that can happen to a system: letting time pass, averaging over a
measurement's outcomes, coupling to an environment and then losing track of it, sending a signal
down a noisy line. A channel takes system $A$ to system $B$. In the *Schrödinger picture* it moves
states forward; dualize and it moves effects backward instead — a positive, unit-preserving linear
map

$$
\varphi : E_B \longrightarrow E_A, \qquad x \ge 0 \implies \varphi(x) \ge 0, \qquad \varphi(1) = 1,
$$

the *Heisenberg picture*. Precomposing a weight (or state) on $A$ with $\varphi$ pushes it forward
to $B$; the two pictures agree on every predicted number:

$$
\begin{array}{ccc}
 e & \xrightarrow{\ \varphi\ } & \varphi(e) \\
 {\scriptstyle \omega\circ\varphi} \big\downarrow & & \big\downarrow {\scriptstyle \omega} \\
 (\omega\circ\varphi)(e) & = & \omega(\varphi(e))
\end{array}
$$

A channel also sends effects to effects: $0 \le e \le 1$ gives $0 \le \varphi(e) \le \varphi(1) = 1$.

A more general notion, needed for measurement (§9), is an **operation**. A measurement, unlike a
channel between two different systems $A, B$, acts on one system and leaves you inside it — you
measure $E$ and the post-measurement state is again a state of $E$ — so an operation is an
endomorphism of a single $E$, sub-unital instead of unital:

$$
T : E \to E, \qquad x \ge 0 \implies T(x) \ge 0, \qquad T(1) \le 1.
$$

It may lose probability but never gain it — one non-selective branch of a measurement. A channel
$E \to E$ is exactly an operation with $T(1) = 1$.

For an infinite system, built up piece by piece, we want limits to behave: the value on the whole
should be whatever the values on ever-larger pieces are approaching, not something disconnected
from them. A channel is **normal** when it has this property — it commutes with suprema of directed
sets, and composing two normal channels gives another one. This is what we will need once a
measurement (§9) has infinitely many possible outcomes, built up from ever-finer finite
collections of them.

## 9. Measurement, as a channel

We already have effects (§5): a single yes/no outcome. An experiment usually has many possible
outcomes, though, and we want a probability for each of them — an effect not just for one event,
but consistently for every event we could ask about ("did the outcome land in this set"), with
disjoint events adding up and "something happened" landing on the certain event. That consistency
is exactly what a measurable space is for.

Given such a space, its bounded measurable functions $B_b(\Omega, \Sigma)$ form a classical system
(§4). A **measurement** of $E$ on $(\Omega, \Sigma)$ is, most naturally, a normal channel (§8) out
of it,

$$
M : B_b(\Omega, \Sigma) \longrightarrow E.
$$

Concretely this is a positive-operator-valued measure (POVM): $M$'s values on indicator functions
give an assignment of effects to events,

$$
M : \Sigma \to \mathrm{Eff}(E), \qquad M(\varnothing) = 0, \qquad M(\Omega) = 1,
$$

$$
M\Big(\bigcup_n s_n\Big) = \sup_N \sum_{n < N} M(s_n) \quad (s_n \text{ pairwise disjoint}),
$$

normality giving exactly this countable additivity. A **projection-valued measure** (PVM) is one
whose every value is sharp.

The big result: precomposing a normal state $\omega$ of $E$ with $M$ (§8) gives a genuine
probability measure on $(\Omega, \Sigma)$, the outcome distribution of the measurement,

$$
\mu(s) := \omega(M(s)), \qquad \mu(\varnothing) = 0, \qquad \mu(\Omega) = 1,
$$

$$
\mu\Big(\bigcup_n s_n\Big) = \sum_n \mu(s_n) \quad (s_n \text{ pairwise disjoint}).
$$

## 10. Postprocessing, compatibility, and instruments

Reading measurement as a channel (§9) makes several further notions free, instead of needing
separate definitions for each.

Coarse-graining or relabeling outcomes, from a raw measurable space $(\Omega, \Sigma)$ to a coarser
one $(\Omega', \Sigma')$, is itself a classical channel (§4, §8),

$$
K : B_b(\Omega', \Sigma') \longrightarrow B_b(\Omega, \Sigma).
$$

**Postprocessing** a measurement $M$ through it is then literal composition,

$$
M' = M \circ K.
$$

Two measurements $M_1$ on $(\Omega_1, \Sigma_1)$ and $M_2$ on $(\Omega_2, \Sigma_2)$ are
**compatible** exactly when one joint measurement on the product $(\Omega_1 \times \Omega_2,\
\Sigma_1 \otimes \Sigma_2)$ postprocesses, along the two coordinate projections, to each of them —
no composite-system theory needed here, since a product of two measurable spaces is already an
ordinary measure-theoretic construction.

An **instrument** keeps more than a measurement: an operation $T_i$ (§8) per outcome instead of a
bare effect, with

$$
\sum_i T_i(1) = 1,
$$

no probability lost in total, even if a single outcome's $T_i$ loses some. Given a prior state
$\omega$ with $\omega(T_i(1)) > 0$, the renormalized post-measurement state after outcome $i$ is

$$
\omega_i(\,\cdot\,) := \frac{\omega(T_i(\,\cdot\,))}{\omega(T_i(1))}.
$$

## 11. Star-algebras: observables and traciality

Everything above assumed nothing but §3's two order axioms. Quantum mechanics is the case where
$E$ comes from an algebra: a $*$-algebra $A$ — a ring with an involution $a \mapsto a^*$,
conjugate-linear and antimultiplicative, $(ab)^* = b^*a^*$. An **observable** is a self-adjoint
element,

$$
\text{observable} \;:=\; a \in A, \quad a^* = a,
$$

and positivity is algebraic: $a \ge 0$ when $a = c^*c$ for some $c$. None of this needs a norm.
$E = A_{\mathrm{sa}}$ — *not* $A$ itself, since two elements can only be order-compared once both
are self-adjoint.

A **weight** on $A_{\mathrm{sa}}$ (§6) is **tracial** when it treats $x^*x$ and $xx^*$ the same,

$$
w(x^*x) = w(xx^*) \quad \text{for every } x,
$$

the abstract shape of a trace's familiar cyclic property, $\mathrm{Tr}(xy) = \mathrm{Tr}(yx)$ —
stated purely algebraically, before any norm enters.

## 12. Adding a norm: C\*-algebras

Add a norm making $A$ complete, submultiplicative, and tied to the involution by the C\*-identity,

$$
\|x^*x\| = \|x\|^2.
$$

Only now do the order-unit axioms of §3 become genuine theorems rather than assumptions: the
operator norm bounds every self-adjoint element, and the positive cone is norm-closed, exactly
what boundedness and Archimedeanity need. Once this is established, every construction from
§1–§10 — effects, weights, states, channels, classical systems, measurements, instruments, POVMs,
PVMs — is available on $A_{\mathrm{sa}}$ for *any* unital C\*-algebra $A$, with no further work.

Section 5's order-theoretic sharpness now meets the algebraic notion of a projection,

$$
p^* = p = p^2:
$$

every idempotent effect is sharp, so every operator-algebraic projection-valued measure is
a PVM in the §9 sense, for free.

Classicality (§4) has its own payoff here,

$$
A_{\mathrm{sa}} \text{ is a lattice} \iff A \text{ is commutative},
$$

so the order-theoretic definition of classical, stated with no multiplication anywhere in sight,
coincides exactly with the algebraic one: $A$ commutative for classical, non-commutative for
quantum.

## 13. Concrete examples, and where this goes next

Two familiar constructions sit as ordinary instances of §6's state notion. A unit vector
$\psi \in H$ gives the vector state

$$
\omega_\psi(x) = \langle \psi, x\,\psi\rangle.
$$

A positive, trace-one operator $\rho$ gives the density state

$$
\omega_\rho(x) = \mathrm{Tr}(\rho\, x),
$$

with the trace itself an example of an (unnormalized) weight from §6 — and, by cyclicity,
$\mathrm{Tr}(xy) = \mathrm{Tr}(yx)$, exactly the tracial weight of §11.

The classical side gets its own instance, one the document has otherwise only gestured at:
$A = C_b(M, \mathbb C)$ for a phase-space manifold $M$, commutative (§12), with states the
probability measures on $M$. By §6's notion of purity, the *pure* states are exactly the point
evaluations $\omega_x(f) = f(x)$ — the points of $M$ recovered as pure states, not assumed
separately.

Beyond a single algebra, several directions are still missing.

**Composite systems** are only half built: the maximal cone of a tensor product of two order-unit
spaces exists now, generated by declaring every simple tensor of positive elements positive, but
not yet an order unit on top of it — a general order-unit space carries no Jordan-type
decomposition into a difference of two cone elements to fall back on, so bounding an arbitrary
tensor by a multiple of $1\otimes1$ needs more structure than this alone. Without that, complete
positivity, joint measurements without the classical-outcome shortcut of §10, and quantum channels
connected back down to the abstract ones of §8 are all still out of reach.

A **von Neumann algebra** (a C\*-algebra with a predual) is where §6's weight and §8's normal
genuinely earn their keep, rather than being stated in full generality for its own sake: the trace
on $B(H)$ is a weight, not a state, exactly because it is infinite at the identity once $H$ is
infinite-dimensional, and normal there is literally weak-\* continuity.

**Unbounded observables** — position, momentum, most Hamiltonians — never sit in $E$ directly,
since §3's order-unit axiom already forces boundedness; they enter only through the spectral
measure built in §9, as $\int \lambda \, dE(\lambda)$, with any bounded observable recovered as
$\int f(\lambda) \, dE(\lambda)$. The integral of a *simple* function against a POVM is built —
including the crux fact, that two different partitions describing the same function give the same
value — but extending it to all bounded measurable functions by a uniform-limit argument needs a
completeness hypothesis on $E$ that doesn't exist at this level of generality yet, so it stops
there for now.

States don't need a Hilbert space to be defined — the **GNS construction** shows they produce one:
a representation $\pi_\omega$, a Hilbert space $H_\omega$, and a cyclic vector $\Omega_\omega$ with

$$
\omega(a) = \langle \Omega_\omega, \pi_\omega(a)\, \Omega_\omega \rangle.
$$

Built, reusing mathlib's own GNS Hilbert space and representation and supplying the missing
cyclic vector, its unit norm, the identity above, cyclicity itself, and that a faithful state
gives an injective representation.

A group $G$ acting on $A$ by automorphisms organizes the state space into representations.
**Symmetry** is built at the order-unit level: an order-automorphism is a channel with an inverse
that is also a channel, these form a genuine group under composition, and any homomorphism
$G\to$(that group) induces an action on $\mathfrak S[\mathbb R, E]$ for free — pulling a state back
along the inverse automorphism is already positive and normalized, since it is just composition of
channels. Conjugation by a unitary, $a\mapsto uau^*$, is a concrete instance; a measurement is
**covariant** when transforming the outcome and transforming its assigned effect agree, and
covariance is preserved by composition — so post-processing a covariant measurement by an
equivariant classical channel stays covariant, and likewise its marginals. A finite direct-sum
decomposition where each summand admits only scalar equivariant maps (a Schur hypothesis) pins a
covariant channel down to one number per summand — the abstract content behind "symmetry reduces
an operator problem to a few scalars." `SYMMETRY_ROADMAP.md` is the fuller design document this
sits inside; representation theory's real payoff — the concrete qubit/$SU(2)$ computation,
compact-group averaging, systems of imprimitivity, Peter–Weyl — remains untouched, deferred there
with the specific reason each one is currently out of reach.

A **Jordan algebra**, using only the symmetric product $a \circ b := ab+ba$ instead of full
associative multiplication, is a historically earlier and more minimal route to the same
self-adjoint structure — closer in spirit to how little this document has assumed throughout.
Built directly on $A_{\mathrm{sa}}$: the product stays self-adjoint whether or not $a,b$ commute,
is commutative, and satisfies the Jordan identity.

**Dynamics.** The reversible case — a one-parameter group of automorphisms $\alpha_t$, $\alpha_0 =
\mathrm{id}$, $\alpha_{s+t} = \alpha_s \circ \alpha_t$, each $\alpha_t$ an order-automorphism, and
the state evolution it induces — is built, as the one-parameter specialization of symmetry above.
Everything past that is still open: irreversible propagators and semigroups, generators, Stone's
theorem connecting a one-parameter group to a Hamiltonian, and where Lindbladians feed into the
non-reversible case. Further out still, **algebraic quantum field theory** assigns an algebra to
each region of spacetime instead of one global $A$, region inclusion giving algebra inclusion — the
natural target once the rest of dynamics is in place.
