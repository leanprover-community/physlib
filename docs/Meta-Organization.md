# The organization of Physlib and its related projects

## The core project (leanprover-community/Physlib)

This contains the core Lean project, and its staging ground PhyslibAlpha.

## ./Physlib

This is the core Lean project. It is very heavily human reviewed, and we expect humans to take an active role in the authoring and review process. It can be seen as the collection of results that humans have checked and trust.

The purpose of this is to: Create a readable, human trusted, high quality corpus of knowledge containing the best results possible in a connected and reusable way. In doing so, forming a solid foundation for future formalizations to build on, and leading to discovery by comprehensively covering areas with high quality results, allowing us to see new connections, reductions and methods.

You should contribute to this project if: you have a formalization that has undergone a lot of thought and care about the best way of doing something, and you want it to be part of the human trusted core.

## ./PhyslibAlpha

This is the staging ground for ./Physlib. It is anlagous to things like ./linux/drivers/staging. Results going into it undergo a one-look human review with a binary decision of accept or reject.

The purpose of it is to: Create a connected corpus of physics formalizations, following the best practices learned from Physlib which will one day be cleaned up for Physlib. In doing so, we will have a guide to the new definitions and results that can be added to Physlib. We will also have new lemmas around Physlib's existing trusted definitions, giving others access to a larger pool of results which they can use in their own formalisation.

You should contribute to this project if: You have a formalization that you think one day will want to end up in ./Physlib, but is not quite ready and you intend to improve it until that point, prehapse with a collobration of others.

*misconception:* There is a misconception that this project is about AI generated code. It never has been, but it is naturally more accepting of AI generated code this ./Physlib.


## The community projects (physlib-community/...)

This is a place for projects that have emerged out of the community that are distinct from the core project. They are also distinct from the maintainer team, which run the core project.

These projects live on the *Physlib Lab* page of the website and link out to seperate websites.

### Website

This is the landing page for Physlib.

### PhyslibX (name still undetermined)

This is the AI-generated, AI-reviewed version of Physlib. It's analogous to the Tau Ceti project for Mathlib. Results going into this do not undergo any human review.

The purpose of it is to: Create a monolithic repository of AI-generated physics to the highest quality possible, building on what has been learned from Physlib and the content within that and the PhyslibAlpha project. It is there to act as a source of formalized physics that AI agents can use to answer big, interesting questions in physics and present that information in a way that's usable and understandable to the humans. The project Physlib Arena is the platform where this sort of question asking takes place.

You should contribute to this project if: You are interested in using AI agents to push the frontier of what we know, using physics. This is not a place for code dumps, in the same way that Tau Ceti is not a place for code dumps. Everything must be integrated carefully into the library and connected within it.

### Physlib Arena

This is a place where people can ask the physics-oriented questions they want an answer to. They can vote on other people's questions and can give directions on how certain questions can be answered. Agents will work on PhyslibX to produce human-readable and human-understandable answers to those questions, whilst building up the library to give it a reusable foundation. This project is there to manifest the underlying purpose of the PhyslibX project.

The purpose is to: Use the power of Lean formalization to help answer questions that people have about physics, whether that's whether a given paper is correct or whether there is an easily constructible room-temperature, room-pressure superconductor.

You should contribute to this project if: You want to push forward with AI the questions that we have in physics.
