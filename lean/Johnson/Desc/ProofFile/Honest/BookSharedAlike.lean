-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookSharedAlike.lean: WHERE TWO DESCRIPTIONS' SHARED CHAINS, AND THEIR
SECOND CHAINS, ARE ALIKE BLOCK BY BLOCK IN ORDER, `sharedAhead` (Honest/BookShared.lean) GIVES ONE
ANSWER AT BOTH: the same list of entries, or the same refusal. Written by the authors of the honest
side of the output head's own rounds (K6), in the frame's folder, not by the frame's authors.
CONDITIONAL: on the likeness of these two pairs of lists.

  `sharedAhead_alike`      the main statement. CONDITIONAL: h₂ (the shared chains' flat lists are
                           alike) · h₃ (the second chains'). The first chains are not asked:
                           `sharedAhead` does not read them
  `sharedAhead_planAlike`  at the library's relation between two descriptions (`PlanAlike`,
                           Johnson/AtFull/ProofPlan/PlanAlike.lean). CONDITIONAL: h
  `sharedAhead_carried`    the form in which it is spent: a return at W is a return at F.
                           CONDITIONAL: h · hW

What it is for. NO RETURN IS HAD HERE. Where one is had elsewhere, at a written description, it is
then a return at every description that is alike to that one.

How. `sharedAhead` reads blocks through `planOf`, `sentIn`, `seedRounds`, `splitEntry` and
`ownFreshIn` at the shared chain and `planOf` at the second; the other makers that it calls take no
block. Each of the five by its congruence (Honest/BookAlike.lean).

Limits. NO RETURN IS HAD, AT ANY DESCRIPTION: ONE IS CARRIED. That a description is alike to a
written one is not had here. Of `Alike₂` "before" and the arrow on the blocks' own tests are idle;
of `PlanAlike` four of its six fields. Nothing on the book's own tests, nor on the whole book's
makers. Bookkeeping: no new mathematics. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookShared
import Johnson.Desc.ProofFile.Honest.BookAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Alike₂ PlanAlike)

/-- **ONE ANSWER AT BOTH.** CONDITIONAL: h₂; h₃. -/
theorem sharedAhead_alike {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder) (p1 : Johnson.G.ChainSends) :
    sharedAhead W p1 = sharedAhead F p1 := by
  unfold sharedAhead
  simp only [planOf_alike h₂, planOf_alike h₃, sentIn_alike h₂, seedRounds_alike h₂,
    splitEntry_alike h₂, ownFreshIn_alike h₂]

/-- At the library's relation. CONDITIONAL: h. -/
theorem sharedAhead_planAlike {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h : PlanAlike W F) (p1 : Johnson.G.ChainSends) : sharedAhead W p1 = sharedAhead F p1 :=
  sharedAhead_alike h.shared h.second p1

/-- **A RETURN IS CARRIED.** CONDITIONAL: h; hW: it returns at W. -/
theorem sharedAhead_carried {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h : PlanAlike W F) {p1 : Johnson.G.ChainSends} {es : List Ahead}
    (hW : sharedAhead W p1 = .ok es) : sharedAhead F p1 = .ok es :=
  (sharedAhead_planAlike h p1).symm.trans hW

end ProofFile.Honest

#print axioms ProofFile.Honest.sharedAhead_alike
#print axioms ProofFile.Honest.sharedAhead_planAlike
#print axioms ProofFile.Honest.sharedAhead_carried
