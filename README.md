# Glassbox <!-- omit in toc --> 

The aim of the Glassbox project is to build a new model of computation 
for algebraic structures that requires each input to be passed with 
a certificate of correctness. This repository contains an Agda implementation of
theory developed in [Categorification of characteristic structures](https://arxiv.org/abs/2502.01138) by the [authors](#authors) and serves, in part, as a proof of the glassbox concept. 
Its specific goal is to produce a type-checked cyclic bicapsule. The authors welcome collaboration on the project, and encourage interested parties to visit the [Issues](https://github.com/algeboy/Glassbox/issues) area to learn more about the outstanding challenges.

This code is compatible with [Agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html) version 2.8. It also uses the [Agda stdlib](https://github.com/agda/agda-stdlib) and [cubical](https://github.com/agda/cubical).

- [Algebraic](#algebraic)
	- [Groups](#groups)
- [Countable](#countable)
- [Authors](#authors)

## Minimal Working Example

To compile the minimal working example install Agda 2.8, clone this repo into a working folder with access to your agda installation, and run:
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
To see more details you can increase the verbosity of the compiler.
```
agda -v 2 Algebraic/TerminalCapsules.agda
```
If you would like to experiment with connecting this code with other software systems such as a computer algebra system you can compile the libraries to Haskell.
```
agda --compile Algebraic/TerminalCapsules.agda
```
The generated Haskell code will appear in a new folder in the same root folder likely called `MAlonzo` and contain several necessary files along with those of this project.

The present code compiles the so-called "Terminal Capsule" which encode the fact that the trivial quotient of any algebraic structure is always characteristic.  While not a surprise, the point of this experiment is to properly develop all the necessary data types and actions.  Replacing with algorithms to compute interesting characteristic structure requires either developing computational algebra algorithms with Agda itself (a slow and likely inefficient process) or more practically transporting the computations through the Haskell interface to an existing Computer Algebra System.


## Algebraic 

A minimal demonstration of universal algebra varieties and their associated abstract categories.  This interprets the algebras as objects on [countable sets](#countable).  Since these categories are abstract, we  consider only their homomorphisms so they are called `Hom` which is a subtype of `ConFun`.  The abstract categories are then demonstrated to inhabit algebraic structures themselves, but now in a larger universe for which we use Agda's own `Set`.

### Groups

A special case of the variety of groups demonstrating characteristic structure.

## Countable 

A minimal demonstration of a category of countable sets.  This is created as an abstract category of functions between natural numbers and intervals.  This is a skeleton category, so it is categorically equivalent to $Sets$ for the Zermelo Set Theory without Replacement or Choice.  However, as this is a minimal example, we do not include most of the necessary enrichments to explore a Set Theory.  In particular, we do not expose topos properties.

Since it is an abstract category, it involves only its functions which are called `ConFun` for "constructable functions".

*This module assumes function extensionality.*

---

## Authors

 * Peter A. Brooksbank, University of Bucknell
 * Heiko Dietrich, Monash University
 * Joshua Maglione, University of Galway
 * E.A. O'Brien, University of Auckland
 * James B. Wilson, Colorado State University

