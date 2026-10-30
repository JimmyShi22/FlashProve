-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LockAtHead.lean: CONDITIONAL. One statement with its proof.

What is here. `k4Names_at_head_of`: THE TWO NAMES OF THE LOCK OF THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4), `K4MaskLockAt` (Law/W/MaskLockAt.lean) and `K4LastEntryAt`
(Law/W/IndexLockAt.lean), AT THE LETTERS OF THE LIBRARY's HYPOTHESIS h (`AtMgA`,
Johnson/P5J/MgAtAll.lean): at each group g below 12, at the public data Qp that `k4PubG Zp g`
returns (Lot/PubG.lean), and at a book B that the maker `bookWhole` (Honest/BookWhole.lean, of other
writers) returns at the seated description `F0T`, the public part's own three lists of sendings and
the list of merges `mergesByName cF.blocksInOrder` (hB). The index side's number is written as
`k4IndexTakes Zp g` (Lot/IndexNum.lean): how many entries of the index-mask message's ledger are
taken in front of the member, of which K4's lot makes the mask row and the place of its entry. WHAT
IS SHOWN OF IT: TWO PUBLIC COUNTS AGREE: the maker's count of the merges' end values in front, and
that ledger's count: both are g. OF THE BOOK IT ASKS hB ALONE; of the plan, he: e is the maker's
count of the own scalars of the segment's parts in front of K4's row.

How. `k4Names_at_record_gk` (Law/W/MergeEndsAt.lean, of another writer) at the head's own fields:
the scope and the files read are h.scope and h.reads; the opened description is h.laid.opened
(`LaidAt`, Johnson/P5J/LaidOpens.lean); the five equations on Qp are `k4PubG_fields`
(Law/W/PubGOf.lean), carried to the opening's own public data by `IM.Open.W`
(Johnson/IMR/SeatOpen.lean); that the places are in order is `placesOk_of_planOk`
(Johnson/RunOne/Sound/KeyListsAtFK.lean) at h.laid.planOk; the index number is `k4IndexTakes_is`
(Law/W/IndexApart.lean).

Not shown here. hB: THAT THE MAKER RETURNS A BOOK THERE: a hypothesis here; it is worded so that a
law which has that return under h alone can be laid in front in one step. he AT THE NUMBER AT WHICH
Law/W/MaskLockAt.lean's LEMMA TAKES THE NAME (the lookup's scalars, `Forest.elems`): at e := the
maker's own count he asks nothing; at that number it is a fact on the rows of the other kinds in
front: shown nowhere here. THAT `mergesByName` IS THE FORMAT's LIST OF MERGES IS NOT SPOKEN OF. THAT
THE SENDER's COIN NUMBER idx.base.e + n IS ITS ENTRY AT THE ROW AND PLACE THAT K4's LOT MAKES OF n
lies in the sentence hE: not shown. THAT THE MAKER's LETTERS ARE THE SENDERS': that row.owner and
row.base.e, idx.owner and idx.base.e are the letters at which the senders' sentences hE of
Law/W/MaskLockAt.lean and Law/W/IndexLockAt.lean are had: shown nowhere here; nor are these two
sentences. LEFT OF THE JOIN: hB; he at that number; that the maker's letters are the senders'; the
two sentences hE. NEVER TO BE SAID FROM THIS FILE: «K4's coins are the sender's» as had · «lock and
key fit» («as had»: as a thing that is shown). The hypotheses: h; g below 12; hP: a hypothesis here
(under the head at the maker's return (`HeadAtReturn`) `k4PubG` returns at each g below 12:
`k4_member_and_public_data`, Law/ClosingLinePayers.lean); hB; he. That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). No example of the hypotheses together has been through Lean. Beneath it stand closed
facts by evaluation in Lean's kernel, which no independent checker has replayed
(Law/W/MergeEndsAt.lean's six; those beneath `k4IndexTakes_is`: the head of Law/W/IndexApart.lean
says which). THE FULL SIZE ALONE, and the format's second hash function alone. A program's walk from
import to import, which
reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 74 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property. No property is claimed.

  `k4Names_at_head_of`   **both names at the head's own letters**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergeEndsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PubGOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexApart
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.Lot (k4PubG k4IndexTakes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, hg, hP, hB and he. **BOTH NAMES AT THE HEAD's OWN LETTERS.** hB: the maker
returns the book B at the seated description, the public part's own three lists and the list of
merges that it makes of the first chain. -/
theorem k4Names_at_head_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {Qp : K4Pub} (hP : k4PubG Zp g = some Qp) {B : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
        Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok B) {e : ℕ}
    (he : e = ownScalarsOf (partsInFront cF.blocksInOrder (2 * g) (IM.k4Place g))) :
    ∃ row idx,
      ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
          s!"link {2 * g}, moment 0" isMaskRowMsg = some row ∧
        ownerOf indexMaskRun cF.blocksInOrder Zp.made.proof.1
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
          "link 0, moment 0" isIndexMaskMsg = some idx ∧
        K4MaskLockAt B Qp e row.owner row.base.e ∧
        K4LastEntryAt B Qp idx.owner (idx.base.e + k4IndexTakes Zp g) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨f1, f2, f3, f4, f5, _⟩ := k4PubG_fields hP
  rw [k4IndexTakes_is h hg]
  exact k4Names_at_record_gk h.scope h.reads O hg
    ⟨by rw [O.W]; exact f1, by rw [O.W]; exact f2, f3, f4, f5⟩ hB
    (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) he

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Names_at_head_of
