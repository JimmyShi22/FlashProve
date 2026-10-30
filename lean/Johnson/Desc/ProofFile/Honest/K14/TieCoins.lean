-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieCoins.lean: kind K14: COINS AT A COUNT, READ AT AN EQUAL COUNT:
the same coin at every number. One definition, and lemmas with their proofs.

Why. Two texts of one sending state how many coins they take by two different sums. Where the two
counts are equal, but not by unfolding, a value of the coins at the one count has to be read at the
other. What a later part is handed of these coins is cut off them BY NUMBER (Cs.cut, cutAll,
Honest/Frame.lean): so the reading must keep every coin's number.

  recount         the coins, read at the equal count
  recount_f, recount_e   each coin by number (cf, ce, Honest/K1/Coins.lean) is the same
  recount_coinsE  the coins of the extension field, as a list of the program's elements, are the
                  same
  recount_cut, recount_cutAll   every run that is cut off by numbers is the same
  recount_bij, recount_unif   the reading is one to one and onto; so it takes uniform coins to
                  uniform coins

Limits. Nothing on any sending. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Desc.ProofFile.Honest.Sum
import Prob.Linear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open ProofFile.Honest.K1 (cf ce)

/-- **Coins at a count, read at an equal count**: the same coin at every number. -/
def recount {d d' : Due} (h : d = d') (c : Cs d') : Cs d := h ▸ c

/-- Each coin of the base field, by number. -/
theorem recount_f {d d' : Due} (h : d = d') (c : Cs d') (i : Nat) :
    cf (recount h c) i = cf c i := by
  subst h
  rfl

/-- **Each coin of the extension field, by number.** -/
theorem recount_e {d d' : Due} (h : d = d') (c : Cs d') (i : Nat) :
    ce (recount h c) i = ce c i := by
  subst h
  rfl

/-- The coins of the extension field as a list of the program's elements. -/
theorem recount_coinsE {d d' : Due} (h : d = d') (c : Cs d') : coinsE (recount h c) = coinsE c := by
  subst h
  rfl

/-- **A run that is cut off by numbers.** -/
theorem recount_cut {d d' : Due} (h : d = d') (c : Cs d') (a n : Due) :
    (recount h c).cut a n = c.cut a n := by
  subst h
  rfl

/-- **The runs that entries of the book cut off.** -/
theorem recount_cutAll {d d' : Due} (h : d = d') (c : Cs d') (es : List Ahead) :
    cutAll (recount h c) es = cutAll c es := by
  subst h
  rfl

/-- The reading is one to one and onto. -/
theorem recount_bij {d d' : Due} (h : d = d') : Function.Bijective (recount h) := by
  subst h
  exact Function.bijective_id

/-- **It takes uniform coins to uniform coins.** -/
theorem recount_unif {d d' : Due} (h : d = d') :
    (Prob.unif (Cs d')).map (recount h) = Prob.unif (Cs d) :=
  Prob.map_unif_of_bijective (recount_bij h)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.recount_f
#print axioms ProofFile.Honest.K14.recount_e
#print axioms ProofFile.Honest.K14.recount_coinsE
#print axioms ProofFile.Honest.K14.recount_cut
#print axioms ProofFile.Honest.K14.recount_cutAll
#print axioms ProofFile.Honest.K14.recount_bij
#print axioms ProofFile.Honest.K14.recount_unif
