-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/Shift.lean: two functions of uniform coins that agree up to a bijection of the
coins have the same distribution. General lemmas on probability.
Terms of this folder: Johnson/LinkSim/Spec.lean.

Notation. unif C is the uniform distribution on a finite non-empty type C, and p.map f is the
distribution of f c when c is drawn from p. The coins are the random values drawn uniformly.

Main names (namespace OnBytes.LinkSim).
  map_eq_of_bij     if f c = g (φ c) for all c, with φ a bijection of the coins with themselves
                    (or with a second finite type of coins), then the distribution of f under
                    uniform coins is the distribution of g under uniform coins.
  map_eq_of_shift   the same where the coins form a finite additive group G, not assumed
                    commutative, and φ adds a fixed element s: φ c = c + s.
  map_eq_of_shift_pi   the same where the coins are the functions from a finite index type P to a
                    finite additive group F, added pointwise: |P| independent uniform elements of F.

How it fits. These are general lemmas on finite probability. map_eq_of_bij is used in
Johnson/LinkSim/Bridge.lean, UpTo.lean and SpecStopTests.lean, to turn an agreement after a change
of variables into an equality of distributions. Within Johnson/LinkSim/, map_eq_of_shift is used in
this file only and map_eq_of_shift_pi nowhere.

What they are for. An argument that a masked message has the same distribution whatever it masks
comes down to one such shift of the masks, and to an identity that holds coin by coin.

Limits. Nothing says when such a shift exists: the bijection or shift, and the identity that
relates f and g, are hypotheses of each lemma.
Sources. Two short lemmas here, `map_eq_of_bij` and `map_eq_of_shift`, resemble lemmas of VCV-io:
the same design, step for step. On VCV-io: lean/CREDITS.md, section 4.


Terms: lean/GLOSSARY.md.

-/
import Prob.Linear

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim
open Prob

/-- If f c = g (φ c) for a bijection φ from the coins C onto the coins C', then f and g have the
same distribution under uniform coins. -/
theorem map_eq_of_bij {C C' V : Type} [Fintype C] [Nonempty C] [Fintype C'] [Nonempty C']
    (φ : C → C') (hφ : Function.Bijective φ) (f : C → V) (g : C' → V) (h : ∀ c, f c = g (φ c)) :
    (unif C).map f = (unif C').map g :=
  ((congrArg (PMF.map g) (map_unif_of_bijective hφ)).symm.trans
    ((PMF.map_comp φ (unif C) g).trans
      (congrArg (fun F => (unif C).map F) (funext fun c => (h c).symm)))).symm

/-- If f c = g (c + s) for every c in a finite additive group G, then f and g have the same
distribution under uniform c. -/
theorem map_eq_of_shift {G V : Type} [AddGroup G] [Fintype G] (s : G) (f g : G → V)
    (h : ∀ c, f c = g (c + s)) : (unif G).map f = (unif G).map g :=
  map_eq_of_bij (fun c => c + s) (Equiv.addRight s).bijective f g h

/-- map_eq_of_shift for coins that are functions from a finite type P to a finite additive group,
added pointwise. -/
theorem map_eq_of_shift_pi {P F V : Type} [Fintype P] [DecidableEq P] [AddGroup F] [Fintype F]
    (s : P → F) (f g : (P → F) → V) (h : ∀ c, f c = g (c + s)) :
    (unif (P → F)).map f = (unif (P → F)).map g :=
  map_eq_of_shift s f g h

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.map_eq_of_bij
#print axioms OnBytes.LinkSim.map_eq_of_shift
#print axioms OnBytes.LinkSim.map_eq_of_shift_pi
