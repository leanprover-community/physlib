# Proof quality

Proofs are an important part of Physlib, and it is important that they stay easy to read. This page covers how to keep proofs clear, maintainable and fast.

## Contents

1. [Keep comments out of proofs](#comments-in-proofs)
2. [Avoid change and erw](#avoid-change-and-erw)
3. [Build API instead of unfolding definitions](#build-api-instead-of-unfolding)
4. [Split the physics out of long proofs](#split-physics-out-of-long-proofs)
5. [Balance length against speed](#balance-length-and-speed)

<a id="comments-in-proofs"></a>

## 1. Keep comments out of proofs

In general, proofs should contain no comments. The only exception is a comment motivated by the physics, and even these should be used very sparingly. Comments add an extra maintenance burden, and a proof should be apparent without them. For example, a one-line comment noting that a step is conservation of energy, placed just before the rewrite that uses it, can show the physics behind what would otherwise look like plain algebra.

<a id="avoid-change-and-erw"></a>

## 2. Avoid change and erw

Avoid tactics such as `change` and `erw`. They are slow, and they are usually a sign that API is missing. When you see them in your proof, ask whether the definitions above are correct, and what could be changed so that these tactics are no longer needed.

<a id="build-api-instead-of-unfolding"></a>

## 3. Build API instead of unfolding definitions

Rather than using `unfold` to reach the underlying definition, ideally write lemmas and build API. A proof that uses `unfold` depends explicitly on the definition, which makes refactoring a lot more difficult and increases the maintenance burden. If the proof uses a lemma instead, the lemma does not have to change when the definition is refactored.

<a id="split-physics-out-of-long-proofs"></a>

## 4. Split the physics out of long proofs

Think about what physics can be split out of a long proof into separate lemmas and results. This makes proofs shorter, and it means other people can reuse these results throughout the project. The clearest sign that a proof needs splitting is that it is getting too long; another is that you keep using the same sorts of statements in proofs. For short math lemmas, see [Little math results](Basic.md#little-math-results).

<a id="balance-length-and-speed"></a>

## 5. Balance length against speed

Proof quality is not all about how short a proof is; the speed of the proof is also important. A longer proof is fine if it makes clearer what is happening and is easier to read. If Lean takes a long time to run a proof on a normal laptop, that is probably a sign the balance between length and speed is wrong.
