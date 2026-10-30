-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LockAtHeadElems.lean: CONDITIONAL. One statement with its
proof.

What is here. `k4Names_at_head_elems`: THE TWO NAMES OF THE LOCK OF THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4), `K4MaskLockAt` (Law/W/MaskLockAt.lean) and `K4LastEntryAt`
(Law/W/IndexLockAt.lean), UNDER THE LIBRARY's HYPOTHESIS h (`AtMgA`, Johnson/P5J/MgAtAll.lean), AS
IN `k4Names_at_head_of` (Law/W/LockAtHead.lean), WITH THE MASK ROW's NAME AT THE NUMBER OF SCALARS
THAT THE LOOKUP's DECLARED ROUNDS COUNT (`Forest.elems` at the public part's own shape): THE NUMBER
AT WHICH THE LEMMAS OF Law/W/MaskLockAt.lean TAKE THAT NAME. THE HYPOTHESIS he OF
`k4Names_at_head_of` IS GONE. Left as hypotheses: h; g below 12; hP; hB: the maker `bookWhole`
(Honest/BookWhole.lean, of other writers) returns the book B at the seated description, the public
part's own three lists of sendings and the list of merges `mergesByName cF.blocksInOrder`.

How. One line: `k4Names_at_head_of` at he := the equation of `k4_he_at_head` (Law/W/HeAtHead.lean,
of another writer): under h, at each g below 12, the maker's count of the own scalars of the
segment's parts in front of K4's row IS that number.

Not shown here. hB: a hypothesis here; under the head `bookWhole` returns at F0T
(`bookWhole_returns_at_head_ahead`, AtFullSide/K14/WholeAheadAtHead.lean). WHAT `k4_he_at_head`
RESTS ON IS ITS OWN FILE's TO SAY. THAT `mergesByName` IS THE FORMAT's
LIST OF MERGES IS NOT SPOKEN OF. THAT THE SENDER's COIN NUMBER idx.base.e + n IS ITS ENTRY AT THE
ROW AND PLACE THAT K4's LOT MAKES OF n lies in the sentence hE: not shown. THAT THE MAKER's OWNERS
AND STARTS ARE THE SENDERS': that row.owner and row.base.e, idx.owner and idx.base.e are those at
which the senders' sentences hE of Law/W/MaskLockAt.lean and Law/W/IndexLockAt.lean are had: not
shown here; nor are these two sentences. WHAT THE LEMMAS THAT TAKE THE TWO NAMES ASK BESIDES
(`k4MaskOwn_at`, Law/W/MaskLockAt.lean; `k4IndexOwn_at`, Law/W/IndexLockAt.lean), EACH OF THE
SENDER's LOT: hn: the message's number; hA: the sender's text answers at the places that K4 reads;
hE: what it answers is the coin at the owner's address (on the mask row's side from the start on; on
the index's side the one coin at the start); OS: the sender's own lot is `OwnMsgs`; and, on the mask
row's side alone, hL: these places lie below the bound of hE. NONE OF THE NINE IS SHOWN HERE. The
two forms that end in the key turned (`k4MaskTie_at`, `k4IndexTie_at`, the same files) ask besides
Lh and hQ, which h has, and hV and hN on each side and hT on the mask row's: that the thread stands
in front of K4's member, that the sender's Vq holds of its input and that N challenges are heard:
not shown here. On the index's side the like of hT stands in front of that lemma's end, with three
more: the thread stands there, the member's step is taken, a ledger of the index masks is there and
hands out an entry: not shown here. All four lemmas are stated at a Script over the book: none is
laid here. THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS IS NOT SHOWN HERE; nor that B is the book of a
thread. THAT B IS THE BOOK OF WHAT `onlineProverFromPublicFiles` RETURNS: where `onlineProverFromPublicFiles` returns A, `atPure_book_at_head`
(Honest/K14/AtPureBookAtHead.lean, of other writers; read whole by this file's writer) has hB, at
the public part's own three lists, at B := A.B under h: so this law holds at A.B there; that law is
called in Law/W/BookAtPure.lean, which has lends, the cut and the lock at A.B itself; not here. THAT
`onlineProverFromPublicFiles` RETURNS IS SHOWN IN NONE OF THESE FILES; OF A THREAD AT A's PROVER NOTHING IS SAID. (At the
letters of `onlineProverFromPublicFiles`'s own call, the last three of the seven lists of `sendsOf`, this law does not
type as it stands; by that law it need not.) LEFT OF THE JOIN: hB; that the maker's owners and
starts are the senders'; the senders' sentences hn, hA, hE and OS on each of the two sides, and hL
on the mask row's; hV and hN on each side, and hT on the mask row's; on the index's side what stands
in front of that lemma's end; a Script over the book; that B is the book at which these are had (of
what `onlineProverFromPublicFiles` returns: see above; of a thread's book nothing is said). NEVER TO BE SAID FROM THIS
FILE, as a thing that is shown: «K4's coins are the sender's» · «lock and key fit». The hypotheses:
h; g below 12; hP: a hypothesis here (under the head at the maker's return (`HeadAtReturn`) `k4PubG`
returns at each g below 12: `k4_member_and_public_data`, Law/ClosingLinePayers.lean); hB. That h can
hold: the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). No one term of Lean joins that member, hP and a return of the maker.
Beneath it stand closed facts by evaluation in Lean's kernel (Law/W/MergeEndsAt.lean's six; those
beneath `k4IndexTakes_is`; those beneath `k4_he_at_head`: its file's head says which), which none of
the rides beneath this file has put before an independent checker. THE FULL SIZE ALONE, and the
format's second hash function alone. A program's walk from import to import, which reads import
lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and
Cb/Bridge*, stopped at 84 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that
begins Cb.Bridge: these counts are lower bounds. A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one. Nothing on soundness, on completeness or on any
other property. No property is claimed.

  `k4Names_at_head_elems`   **both names under the head, with no hypothesis on the number in front**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LockAtHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.HeAtHead

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

/-- CONDITIONAL on h, hg, hP and hB. **BOTH NAMES OF THE LOCK UNDER THE HEAD, THE MASK ROW's AT THE
NUMBER OF SCALARS THAT THE LOOKUP's DECLARED ROUNDS COUNT**: no hypothesis on that number is left.
-/
theorem k4Names_at_head_elems (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {Qp : K4Pub} (hP : k4PubG Zp g = some Qp) {B : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
        Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok B) :
    ∃ row idx,
      ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
          s!"link {2 * g}, moment 0" isMaskRowMsg = some row ∧
        ownerOf indexMaskRun cF.blocksInOrder Zp.made.proof.1
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
          "link 0, moment 0" isIndexMaskMsg = some idx ∧
        K4MaskLockAt B Qp (OnBytes.Model.Forest.elems (P5J.At.X Zp).y.fo) row.owner row.base.e ∧
        K4LastEntryAt B Qp idx.owner (idx.base.e + k4IndexTakes Zp g) :=
  k4Names_at_head_of h hg hP hB (k4_he_at_head h hg).symm

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Names_at_head_elems
