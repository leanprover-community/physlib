# Contribution tips

A collection of tips from the Physlib community.

## Contents

1. [Don't rush](#dont-rush)
2. [Build reusable foundations](#build-reusable-foundations)
3. [Let API design and formalization inform each other](#let-api-design-and-formalization-inform-each-other)
4. [Contribute in small coherent steps](#contribute-in-small-coherent-steps)
5. [Use structures](#use-structures)
6. [Placement of lemmas](#placement-of-lemmas)
7. [Little  maths results](#little-maths-results)
8. [Namespaces](#namespaces)
9. [Explain the why in documentation](#explain-the-why-in-documentation)
10. [Variable names in doc-strings](#variable-names-in-doc-strings)
11. [Generalizing review comments](#generalizing-review-comments)
12. [Author lists](#author-lists)

<a id="dont-rush"></a>

## 1. Don't rush

The best contributions to the project are often those which are the most well-thought through, and carefully executed. There is no prize for having the most PRs or getting things into the project as fast as possible. An ode to the cliché: quality matters more than quantity.

<a id="build-reusable-foundations"></a>

## 2. Build reusable foundations

Sometimes the most useful contribution is to improve the definitions and basic lemmas that other work depends on. Good foundations make later formalizations easier to write, understand, and review. If you keep running into awkward assumptions, repeating arguments, or converting between incompatible definitions, it may be worth discussing the underlying API. Working through those difficulties is valuable in its own right, even if it doesn’t immediately lead to a major physics result.

<a id="let-api-design-and-formalization-inform-each-other"></a>

## 3. Let API design and formalization inform each other

A rough API map and an early conversation on Zulip can help you work out how to approach an area and they also give others a chance to offer advice or join in. You don’t need to settle the whole design before writing Lean but small examples often reveal difficulties that weren’t obvious on paper, and working through them can suggest a better approach. Let that experience shape the design, and keep the API map up to date as things develop.

<a id="contribute-in-small-coherent-steps"></a>

## 4. Contribute in small coherent steps

A large project is often easier to develop through a series of small contributions. You might begin with a few reusable definitions and supporting lemmas, get feedback on them, and then move on to their applications. Try to give each PR a clear purpose so that a reviewer can understand it without having to untangle the whole project. A little explanation of where it fits, and what other work it depends on, can go a long way.

<a id="use-structures"></a>

## 5. Use structures

It is often best, from the point of view of physics, to represent physical systems using structures. For example, suppose we were writing the energy of a harmonic oscillator. We could write it like this:

```lean
namespace HarmonicOscillator

/-- The total energy of a harmonic oscillator with mass `m`
and spring constant `k`, at position `x` and velocity `v`. -/
def energy (m k : ℝ) (x v : ℝ) : ℝ :=
  m * v ^ 2 / 2 + k * x ^ 2 / 2

end HarmonicOscillator
```

But the following is usually better. The mass and spring constant are now part of the harmonic oscillator, and we can use that same oscillator in other definitions:

```lean
/-- The mass and spring constant of a harmonic oscillator. -/
structure HarmonicOscillator where
  m : ℝ
  k : ℝ

namespace HarmonicOscillator

/-- The total energy of the harmonic oscillator
at position `x` and velocity `v`. -/
def energy (H : HarmonicOscillator) (x v : ℝ) : ℝ :=
  H.m * v ^ 2 / 2 + H.k * x ^ 2 / 2

end HarmonicOscillator
```

<a id="placement-of-lemmas"></a>

## 6. Placement of lemmas

One of the most common review comments on Physlib is the placement of lemmas. As a general rule, every lemma about an object `A` should go directly next to the definition of that object. It is common to see lemmas placed  just above where they are needed, which in general leads to bad API design.

<a id="little-maths-results"></a>

## 7. Little  maths results

It is common to see small maths results with proofs which are 1-5 lines long placed as lemmas in a Physlib file, if they are used to prove some other result. Please don't do this, while it may seem good to separate proofs into small parts, a random math lemma in the middle of a file about physics effects the readability and flow of that file. It is best to either 1) make the lemma directly about the physics quantities involved, or 2) place its proof directly where it is needed instead of having a separate lemma.

<a id="namespaces"></a>

## 8. Namespaces

As a general rule each file should contain one namespace. If you are opening and closing namespaces throughout a file then it is likely that your declarations are in the wrong place. There are exceptions to this rule, but these are rare, and likely do not hold in your case.

<a id="explain-the-why-in-documentation"></a>

## 9. Explain the why in documentation

It's good to think about what someone coming to your code for the first time would need to understand. They may recognize the Lean statement but still wonder what it means physically, why you chose that definition, or which assumptions and conventions are in play. A few sentences explaining those choices can make the code much easier to follow. Where the connection to familiar physics is subtle, a short example or heuristic argument may help. Keep it concise, and make clear where the motivation ends and the formal proof begins.

<a id="variable-names-in-doc-strings"></a>

## 10. Variable names in doc-strings

Be careful not to include variable names in doc strings without explanation. For example, avoid:

```lean
/-- The total energy of `H` -/
def energy (H : HarmonicOscillator) (x v : Real) : Real :=
  H.m * v ^ 2 / 2 + H.k * x ^ 2 / 2
```
instead write
```lean
/-- The total energy of the harmonic oscillator. -/
def energy (H : HarmonicOscillator) (x v : Real) : Real :=
  H.m * v ^ 2 / 2 + H.k * x ^ 2 / 2
```

<a id="generalizing-review-comments"></a>

## 11. Generalizing review comments

If a reviewer asks you to change something, have a look for other places where the same comment might apply. They may have only spotted one example, or expected you to make the corresponding changes elsewhere. You shouldn’t need a separate review comment for every occurrence of the same issue. Make this assessment yourself, and check any changes an LLM makes before asking for another review.

<a id="author-lists"></a>

## 12. Author lists

The author list on a file is there to help answer “who should I contact if I have questions about this code?” Git and GitHub already tell us who wrote which parts. Hence, if you add your name, consider whether you would be happy to help someone understand the file or work on it, and remember to keep the names in alphabetical order by last name.
