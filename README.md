# Glassbox <!-- omit in toc --> 

This is based off of work from [Categorification of characteristic structures](https://arxiv.org/abs/2502.01138) by the [authors](#authors). Our goal is to produce a cyclic bicapsule. There are still holes for proofs; see the [Issues](https://github.com/algeboy/Glassbox/issues) for more details.

This code is compatible with [Agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html) version 2.8. This also uses the [Agda stdlib](https://github.com/agda/agda-stdlib) and [cubical](https://github.com/agda/cubical).

- [Algebraic](#algebraic)
	- [Groups](#groups)
- [Countable](#countable)
- [Practice](#practice)
- [Authors](#authors)
- [Acknowledgements](#acknowledgements)

## Algebraic 

A minimal demonstration of universal algebra varieties and their associated abstract categories.  This interprets the algebras as objects on [countable sets](#countable).  These categories, being abstract, only consider their homomorphisms, so they are called `Hom`, which is a subtype of `ConFun`.  The abstract categories then demonstrated to inhabit algebraic structures themselves, but now in a larger universe for which we use Agda's own `Set`.

### Groups

A special case of the variety of groups demonstrating characteristic structure.

## Countable 

A minimal demonstration of a category of countable sets.  This is created as an abstract category of functions between natural numbers and intervals.  This is a skeleton category, so it is categorically equivalent to $Sets$ for the Zermelo Set Theory without Replacement or Choice.  However, as this is a minimal example, we do not include most of the necessary enrichments to explore a Set Theory.  In particular, we do not expose topos properties.

Since it is an abstract category, it involves only its functions which are called `ConFun` for "constructable functions".

*This module assumes function extensionality.*

## Practice

We have included some of the many files and tests we developed along the way in case anyone might learn from these.

---

## Authors

 * Peter A. Brooksbank, University of Bucknell
 * Heiko Dietrich, Monash University
 * Joshua Maglione, University of Galway
 * E.A. O'Brien, University of Auckland
 * James B. Wilson, Colorado State University

## Acknowledgements

We thank John Power and Mima Stanojkovski for comments on a draft. Brooksbank was supported by NSF grant DMS-2319371. Maglione was supported by DFG grant VO 1248/4-1 (project number 373111162) and DFG-GRK 2297. O’Brien was supported by the Marsden Fund of New Zealand Grant 23-UOA-080 and by a Research Award of the Alexander von Humboldt Foundation. Wilson was supported by a Simons Foundation Grant identifier 636189 and by NSF grant DMS-2319370.
