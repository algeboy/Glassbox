# Glassbox <!-- omit in toc --> 

The aim of the Glassbox project is to build a new model of computation for algebraic structures that requires each input to be passed with 
a certificate of correctness. 

This repository contains an Agda implementation of theory developed in [Categorification of characteristic structures](https://arxiv.org/abs/2502.01138) by the [authors](#authors) and serves, in part, as a proof of the glassbox concept. 

Its specific goal is to produce a type-checked cyclic bicapsule. 

We welcome collaboration on the project, and encourage interested parties to visit the [Issues](https://github.com/algeboy/Glassbox/issues) area to learn more about the outstanding challenges.

This code is compatible with [Agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html) version 2.7 or higher. It also uses the [Agda stdlib](https://github.com/agda/agda-stdlib) and [cubical](https://github.com/agda/cubical).

- [Countable](#countable)
- [Algebraic](#algebraic)
	- [Groups](#groups)
- [Authors](#authors)

## Minimal Working Example

To compile a minimal working example, first install Agda 2.7 or higher, then clone this repo into a working folder with access to your agda installation, and run:
```
git clone https://github.com/algeboy/Glassbox.git
cd Glassbox
agda Algebraic/TerminalCapsules.agda
```
A successful compilation will report no errors found and a list of intermediate compiled files will also be shown. Something like this:
```
Checking Algebraic.TerminalCapsules (/Users/algeboy/CODE/test/Glassbox/Algebraic/TerminalCapsules.agda).
 Checking Algebraic.AbstractCategory (/Users/algeboy/CODE/test/Glassbox/Algebraic/AbstractCategory.agda).
  ...
  Checking Countable.SetCategory (/Users/algeboy/CODE/test/Glassbox/Countable/SetCategory.agda).
```
To see more details, increase the verbosity of the compiler.
```
agda -v 2 Algebraic/TerminalCapsules.agda
```
If you would like to experiment with connecting this code with other software systems such as a computer algebra system, then you can compile the libraries to Haskell.
```
agda --compile Algebraic/TerminalCapsules.agda
```
The generated Haskell code will appear in a new folder probably called `MAlonzo` in the same root folder and contain several necessary files along with those of this project.

The present code compiles the so-called "Terminal Capsule" which encodes the fact that the trivial quotient of any algebraic structure is always characteristic.  While not a surprise, the point of this experiment is to properly develop all of the necessary data types and actions.  Algorithms to compute interesting characteristic structure require either developing computational algebra algorithms within Agda itself (a slow and likely inefficient process) or more practically transporting the computations through the Haskell interface to an existing Computer Algebra System.

---

## Countable 

A minimal demonstration of a category of countable sets.  This is created as an abstract category of functions between natural numbers and intervals.  This is a skeleton category, so it is categorically equivalent to $Sets$ for the Zermelo Set Theory without Replacement or Choice.  However, as this is a minimal example, we do not include most of the necessary enrichments to explore a Set Theory.  In particular, we do not use topos properties.

The relevant files are 
 * `Countable/Sets.agda` which sets up the objects and morphisms of this category. See the documentation [Sets](Countable/Sets.md) for further details.
 * `Countable/SetCategory.agda` which wraps the sets into an abstract category using the algebraic definitions of `Algebraic`. See the documentation in [Set Category](Countable/SetCategory.md). Since `Sets` is an abstract category, it involves only its functions which are called `ConFun` for "constructable functions".
 * `Countable/SetLaws.agda` provides proofs of all the abstract category laws and is a full demonstration of inhabiting the abstract category type.
> **Technical Note.** This file uses the tag `{-# OPTIONS --allow-unsolved-metas #-}` which is to avert warnings about potential holes.  If inspected, the holes in this file are actually confined to proofs of negation to satisfy the type-checker's need to have something to return if a contradiction is raised.  Since contradications cannot arise, such holes are unreachable and thus this does not represent an actual gap.

As implemented, this module assumes function extensionality.  However, we have also tested this under univalence axioms with Cubical agda to remove this postulate. 

## Algebraic 

A minimal demonstration of universal algebra varieties and their associated abstract categories.  This interprets the algebras as objects on [countable sets](#countable).  Since these categories are abstract, we consider only their homomorphisms so they are called `Hom` which is a subtype of `ConFun`.  The abstract categories are then demonstrated to inhabit algebraic structures themselves, but now in a larger universe for which we use Agda's own `Set`.

Relevant files
 * `Algebraic/Structures.agda` develops the relevant data types of algebraic structures in the form of universal algebra.  Specifically instead of a hierarchy of named algebras (such as groups, rings, and monoids) every algebraic structure is a [countable sets](#countable) with operations form a signature; see also `Algebraic/Signatures.agda`.  See [Structures Documentation](Algebraic/Structures.md) for details.
 * `Algebraic/Varieties.agda` adds equations and equational laws to algebraic structures, namely **varieties** in the sense of universal algebra. This file is suuported by `Algebraic/Equations.agda`. See [Varieties Documentation](Algebraic/Varieties.md) for details.
 * `Algebraic/Homomorphism.agda` collects the data types necessary for homomorphisms of algebraic structures.  As these are homomorphisms of [countable sets](#countable) they take the type `ConFun`. See [Homomorphisms](Algebraic/Homomorphism.md) for details.
 * `Algebraic/HomCategories.agda` structures the homomorphisms of algebraic structures on `ConFun` into categories in a variety of abstract categories `AbsCat`. The file is supported by `Algebraic/AbstractCategory.agda`.
 * `Algebraic/Capsules.agda` is the main algebraic vehical to encode natural transformations, and hence to model characteristic structures as aglebraic data.
 * `Algebraic/TerminalCapsules.agda` the capsule representing the trivial quotient of an algebraic structure $A\to 0$ where $0$ is a terminal algebra. This is the algebraic structure on a set of size 1.

### Groups

A special case of the variety of groups demonstrating characteristic structure.  An aspirational future feature is to develop an interface from these Agda types to a Computer Algebra System that computes relevant characteristic structure through efficient means and passes along the data to the certification with types as done in Agda.


---

## Authors

 * Peter A. Brooksbank, Bucknell University
 * Heiko Dietrich, Monash University
 * Joshua Maglione, University of Galway
 * E.A. O'Brien, University of Auckland
 * James B. Wilson, Colorado State University

