-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookRawAlike.lean: WHERE TWO DESCRIPTIONS' THREE CHAINS ARE ALIKE
BLOCK BY BLOCK, IN ORDER, THE MAKER OF THE BOOK OF COINS IN FRONT OF THE BOOK's OWN TESTS (bookRaw,
Honest/BookWhole.lean) GIVES ONE ANSWER AT BOTH: the same book, or the same refusal. Written by the
authors of the honest side of the linear claim's shared rounds (K14), in the frame's folder, not by
the frame's authors; the makers are theirs. Five statements with their proofs; no definition.
CONDITIONAL: the first two on alike lists alone; the three at PlanAlike on that relation, whole; the
two "carried" also on hW: it returns at W.

The relation is the library's own, as it stands (Johnson/AtFull/ProofPlan/PlanAlike.lean): Alike₂ b
b': place, rounds, oracles and before are equal, and where b's own test on the plan passes b' 's
does. "before" and that arrow are idle here. PlanAlike W F: the three chains' flat lists are alike
so, and three things more: where W's test on the file passes F's does, the plans are equal, the
depths of the stored parts are equal: THESE THREE FIELDS (fileOk, plans, depth) ARE IDLE HERE TOO:
the relation is taken whole because the library can pay it whole.

  spendingBook_alike   the book as far as its spending entries, rows and cuts go
                  (Honest/BookAll.lean)
  bookRaw_alike   **the top**: three premises, one for each chain
  bookRaw_planAlike   at the library's relation PlanAlike
  bookRaw_carried **a return is carried** from W to F
  bookRaw_carried_guess   the same where the merges are the guess mergesByName at each description's
                  own first chain: the merges that the frame's maker onlineProverFromPublicFiles lays, inside bookWhole
                  (Honest/AtPure.lean)

How. By unfolding and rewriting: whatever reads a block in the two texts has its congruence in
Honest/BookAlike.lean or Honest/BookAlikeRows.lean, or is the library's alike₂_rounds. The makers
over plans and sendings (foldEntries, loneWants, wantsFree, firstCodes, mainRoomFault,
segmentCarries, groupCarries, carryPair, behindFold, codesUnder) take no block. THE ANSWERS ARE
EQUAL AS VALUES, THE REFUSALS' WORDS TOO.
Limits. NO RETURN IS SHOWN BY IT, AT ANY DESCRIPTION: IT CARRIES ONE. That two descriptions are
alike is not had here. Nothing on the verdict of wantsFree or of any test. The book's own tests
(ProverCoinCounts.checked) are not touched. Bookkeeping: no new mathematics. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookAlikeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Alike₂ PlanAlike alike₂_rounds)

variable {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}

/-- CONDITIONAL: h₁ h₂ h₃: the three chains' flat lists are alike. The same book, or the same
refusal. -/
theorem spendingBook_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder)
    (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    spendingBook W p0 p1 p2 M = spendingBook F p0 p1 p2 M := by
  have hL : (W.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts =
      (F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts :=
    partsWhere_alike h₁ fun p => p.link.isNone
  unfold spendingBook
  simp only [rowsIn_alike h₁, rowsIn_alike h₂, rowsIn_alike h₃, alike₂_rounds _ _ h₃,
    ownerOf_alike h₁, linksIn_alike h₁, linksWants_alike h₁, hL, planOf_alike h₁, planOf_alike h₂,
    planOf_alike h₃, splitEntry_alike h₂, cutsOf_alike h₁ h₂ h₃]

/-- **THE TOP.** CONDITIONAL: h₁ h₂ h₃. The same book, or the same refusal. -/
theorem bookRaw_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder)
    (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    bookRaw W p0 p1 p2 M = bookRaw F p0 p1 p2 M := by
  unfold bookRaw
  simp only [spendingBook_alike h₁ h₂ h₃, alike₂_rounds _ _ h₃, sentIn_alike h₁, sentIn_alike h₂,
    switchRows_alike h₁, switchRows_alike h₂, switchRows_alike h₃, planOf_alike h₁,
    planOf_alike h₂, planOf_alike h₃, seedRounds_alike h₂, ownFreshIn_alike h₁,
    ownFreshIn_alike h₂, ownFreshIn_alike h₃]

/-- At the library's relation. CONDITIONAL: h. -/
theorem bookRaw_planAlike (h : PlanAlike W F) (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    bookRaw W p0 p1 p2 M = bookRaw F p0 p1 p2 M :=
  bookRaw_alike h.first h.shared h.second p0 p1 p2 M

/-- **A RETURN IS CARRIED.** CONDITIONAL: h; hW: it returns at W. -/
theorem bookRaw_carried (h : PlanAlike W F) {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (hW : bookRaw W p0 p1 p2 M = .ok B) : bookRaw F p0 p1 p2 M = .ok B :=
  (bookRaw_planAlike h p0 p1 p2 M).symm.trans hW

/-- **A return is carried where the merges are the guess at each description's own first chain.**
CONDITIONAL: h; hW. -/
theorem bookRaw_carried_guess (h : PlanAlike W F) {p0 p1 p2 : Johnson.G.ChainSends} {B : ProverCoinCounts}
    (hW : bookRaw W p0 p1 p2 (mergesByName W.first.blocksInOrder) = .ok B) :
    bookRaw F p0 p1 p2 (mergesByName F.first.blocksInOrder) = .ok B := by
  rw [← mergesByName_alike h.first]
  exact bookRaw_carried h hW

end ProofFile.Honest

#print axioms ProofFile.Honest.spendingBook_alike
#print axioms ProofFile.Honest.bookRaw_alike
#print axioms ProofFile.Honest.bookRaw_planAlike
#print axioms ProofFile.Honest.bookRaw_carried
#print axioms ProofFile.Honest.bookRaw_carried_guess
