# Contribution handbook - the basics

In this file we summarize the basics of contributing to Physlib.
The rest of the directory goes into more specifics on different areas.

This handbook can either be read as a human, or you can see how much
your PR aligns with it using the AI skill `/handbook-alignment`.

## Contents

1. [Don't rush](#dont-rush)
2. [Build reusable foundations](#build-reusable-foundations)
3. [Let API design and formalization inform each other](#let-api-design-and-formalization-inform-each-other)
4. [Contribute in small coherent steps](#contribute-in-small-coherent-steps)
5. [Use structures](#use-structures)
6. [Placement of lemmas](#placement-of-lemmas)
7. [Little math results](#little-math-results)
8. [Namespaces](#namespaces)
9. [Explain the why in documentation](#explain-the-why-in-documentation)
10. [Variable names in docstrings](#variable-names-in-docstrings)
11. [Generalizing review comments](#generalizing-review-comments)
12. [Author lists](#author-lists)

<a id="dont-rush"></a>

## 1. Don't rush

The best contributions to the project are often those which are the most carefully thought through and executed. There is no prize for having the most PRs or getting things into the project as fast as possible. To echo the cliché: quality matters more than quantity.

<a id="build-reusable-foundations"></a>

## 2. Build reusable foundations

At this stage of Physlib, the most useful contribution is to improve the definitions and basic lemmas that other work depends on. Good foundations make later formalizations easier to write, understand, and review. If you keep fighting awkward hypotheses, repeated arguments or mismatched definitions, the API is probably the place to fix it. Working through these difficulties is valuable in its own right, even if it doesn't immediately lead to a major physics result.

<a id="let-api-design-and-formalization-inform-each-other"></a>

## 3. Let API design and formalization inform each other

When you're starting work in a new area, it's a good idea to sketch out a rough API map and start a conversation on Zulip. It gives others a chance to share advice or get involved, and you might discover that Physlib already covers some of what you have in mind, just in a different form. If so, plan to prove that your version and the existing one agree, so the two fit together. Don't worry about settling the whole design before you start writing Lean; small examples often uncover things that weren't obvious on paper, and working through them can lead you to a better approach. Let what you learn shape the design, and keep the API map up to date along the way.

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

One of the most common review comments on Physlib is about the placement of lemmas. As a general rule, every lemma about an object should go directly next to its definition. Lemmas are often placed just above where they are needed instead, which hides them from anyone else using the object, so the same facts get proved again.

<a id="little-math-results"></a>

## 7. Little math results

Please don't put short, single-use math lemmas in physics files. However tidy it seems, a stray math result interrupts the progression of physics for the reader. If you need to write one, check whether the fact is already in Mathlib, perhaps as a special case of something more general. If it isn't, but it is genuinely general, state it in a usable form in the relevant mathematics file. If it only makes sense in context, state it in terms of the physical quantities involved, and if it is used just once, inline the proof.

<a id="namespaces"></a>

## 8. Namespaces

As a general rule each file should contain one namespace. If you are opening and closing namespaces throughout a file, then it is likely that your declarations are in the wrong place. There are exceptions to this rule, but these are rare, and likely do not hold in your case.

<a id="explain-the-why-in-documentation"></a>

## 9. Explain the why in documentation

It's good to think about what someone coming to your code for the first time would need to understand. They may recognize the Lean statement but still wonder what it means physically, why you chose that definition, or which assumptions and conventions are in play. A few sentences on these points can make a big difference, and if your code builds on or relates to other parts of Physlib, pointing to them helps readers find their way around. Where the connection to familiar physics is subtle, a short example or heuristic argument may help. Keep it concise, and make clear where the motivation ends and the formal proof begins.

<a id="variable-names-in-docstrings"></a>

## 10. Variable names in docstrings

Be careful not to include variable names in docstrings without explanation. For example, avoid:

```lean
/-- The total energy of `H` -/
def energy (H : HarmonicOscillator) (x v : ℝ) : ℝ:=
  H.m * v ^ 2 / 2 + H.k * x ^ 2 / 2
```
Instead, write
```lean
/-- The total energy of the harmonic oscillator. -/
def energy (H : HarmonicOscillator) (x v : ℝ) : ℝ :=
  H.m * v ^ 2 / 2 + H.k * x ^ 2 / 2
```

<a id="generalizing-review-comments"></a>

## 11. Generalizing review comments

When a reviewer asks for a change, look for other places where the same comment applies. They may have spotted only one example, or expected you to fix the rest yourself. One comment should be enough for every instance of the same issue. Before asking for another review, check every change yourself, including any made with AI.

<a id="author-lists"></a>

## 12. Author lists

The author list on a file is there to help answer the question "Who should I contact if I have questions about this code?" Git and GitHub already tell us who wrote which parts. Hence, if you add your name, consider whether you would be happy to help someone understand the file or work on it, and remember to keep the names in alphabetical order by last name.
