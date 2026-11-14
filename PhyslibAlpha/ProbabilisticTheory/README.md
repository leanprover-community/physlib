# Independent Alpha probabilistic theory experiment

This folder retains Alpha's earlier carrier-based framework under its own library
namespace, `PhyslibAlpha.ProbabilisticTheory`. It has its own order-unit, effect,
state and channel definitions and its original GNS and model constructions.

It is an independent experiment, not a compatibility layer for the bundled theory
in Physlib. It imports no Physlib probabilistic-theory modules and has no bundle
bridges. Core development does not require updating this API.
The generic tracial-functional construction is restored from the Alpha version
before its extraction into Physlib (the parent of commit 80ca0ab9).
