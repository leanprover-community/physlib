# Documentation

Clear documentation makes it easier for people to navigate Physlib, to extend the work that is already in it, and to reuse its results elsewhere in the project.

## Contents

1. [Write for a physicist, not a mathematician](#write-for-a-physicist)
2. [Use standard terminology](#use-standard-terminology)
3. [Keep it clear and concise](#keep-it-clear-and-concise)
4. [Let the documentation tell a story](#tell-a-story)
5. [Follow the module documentation structure](#module-documentation-structure)

<a id="write-for-a-physicist"></a>

## 1. Write for a physicist, not a mathematician

A common mistake is to write documentation for a mathematician. When it is written that way, a physicist may not understand why something has been done, which makes it hard to follow how the file progresses, and the underlying physics becomes less clear. Step back and ask whether an undergraduate physicist could read the file and understand what is in it. For example, avoid:

```lean
/-- The function `x ↦ A cos(ωt + φ)` satisfies the second-order
linear ODE with constant coefficients. -/
```

Instead, write

```lean
/-- The trajectory of the harmonic oscillator, oscillating about
equilibrium with amplitude `A` and phase `φ`, solves its
equation of motion. -/
```

<a id="use-standard-terminology"></a>

## 2. Use standard terminology

Documentation should be understandable by an undergraduate with the required background knowledge, without unnecessary expert words or jargon. Jargon is fine when it is standard, or when its meaning is made explicit. Don't invent terms: invented words, which AI tools in particular tend to produce, confuse things rather than help. Using standard terminology lets people read the documentation without having to worry about what each term means.

<a id="keep-it-clear-and-concise"></a>

## 3. Keep it clear and concise

Unclear or wordy documentation tries to over-explain something when a short, good explanation would do. This costs the reader time and effort, when a short explanation could have told them straight away. For example, avoid:

```lean
/-- This definition gives the energy, which is the total energy of
the harmonic oscillator, meaning the sum of its kinetic energy and
its potential energy, which are the two kinds of energy the
oscillator has. -/
```

Instead, write

```lean
/-- The total energy of the harmonic oscillator, the sum of its
kinetic and potential energies. -/
```

<a id="tell-a-story"></a>

## 4. Let the documentation tell a story

Each docstring should work on its own, independently of the others. But read straight through, the documentation in a file should tell a clear story, and it should be a physics story, not a maths story. A good check is to read all of the documentation in the file, even the parts you haven't edited.

<a id="module-documentation-structure"></a>

## 5. Follow the module documentation structure

Module documentation should follow the structure checked by the `module_doc_lint` linter. A consistent structure lets people navigate a file easily, and lets them know what to expect and where to look when they open a file they haven't seen before. For an example, see [the classical harmonic oscillator](../../Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean).
