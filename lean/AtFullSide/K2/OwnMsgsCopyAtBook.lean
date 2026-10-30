-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnMsgsCopyAtBook.lean: the kind "the code switch" (K2): THE TIE AT A KEPT COPY FROM
THE TIE AT THE SENDER IN FRONT, AT A WRITTEN PAIR, AT WHATEVER BOOK bookWhole RETURNS AT F0T, UNDER
THE LIBRARY's HEAD: `ownMsgs_copy_at_pair` (Johnson/Desc/ProofFile/Honest/K2/Law/OwnMsgsAtPair.lean)
CALLED WITH EIGHT OF ITS ELEVEN LEFT PREMISES PAID: the book's five, hc and hw by
`book_five_at_pair` (AtFullSide/K2/CopyBookAtPair.lean); hSz by `leadsW`
(Honest/K2/Law/TiesWritten.lean). THREE STAY: hm₀, hNN, hrun. And a public fact on the written
pairs: at which of them the message that is copied is itself a kept copy of the switch in front (the
second step). It lies in the side library because it imports files of it. One definition, a public
test; one closed fact by evaluation in Lean's kernel: two counts; lemmas.

  `pair_sizes`      hSz: at each written pair the segment's sizes are those of the switch in front
  `ownMsgs_copy_at_book`   THE END
  `copyOfCopy`, `stepsW`   A PUBLIC TEST at a pair and a kept copy: the message that is copied is
                    itself a kept copy of the switch in front; BY LEAN's KERNEL: how many of the
                    written pairs' kept copies are such, and how many are not

By: `ownMsgs_copy_at_pair` · `book_five_at_pair` · `leadsW`, `leadsInto_gives`
(Honest/K2/Law/TiesWritten.lean) · `copyPairs_mem` (Honest/K2/Law/CopyPairsMem.lean).

Limits. WHAT STAYS A PREMISE: hm₀: the tie at the sender: no Script is laid here · hNN · hrun: at
every run that the tie speaks of: shown nowhere by us. ONE STEP BACK: where the message that is
copied is itself a kept copy, hm₀ is this law's own end one pair earlier; that chain is not drawn
here. ONE LETTER num SERVES BOTH TIES. AT THE WRITTEN LISTS: not carried to the head's own. The two
copies at link 1 stand at no pair. All limits of OwnMsgsAtPair.lean and CopyBookAtPair.lean stand.
The head and the book are premises; that they can be met is not said. Nothing on any property.
-/
import AtFullSide.K2.CopyBookAtPair
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnMsgsAtPair
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (Left Sizes mainRows keptNo)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- **At a written pair the segment's sizes are those of the switch in front.** -/
theorem pair_sizes {p₀ p : SwitchPlace} {S : SegmentPub} (hx : (p₀, p, S) ∈ copyPairs) :
    S.sizes = p₀.sizes := by
  obtain ⟨m1, -, hl, hS⟩ := copyPairs_mem hx
  have e : p.link - 1 = p₀.link := by
    have hl' : p₀.link + 1 = p.link := hl
    omega
  have hS' : segsW[p₀.link]? = some S := by
    rw [← e]
    exact hS
  have t := List.all_eq_true.1 leadsW p₀ m1
  rw [Bool.or_eq_true] at t
  rcases t with t | t
  · rw [List.getElem?_eq_none (of_decide_eq_true t)] at hS'
    cases hS'
  · obtain ⟨S', h1, h2, -, -⟩ := leadsInto_gives t
    rw [hS'] at h1
    obtain rfl := Option.some.inj h1
    exact h2

variable {W₀ Rc Xi Tr Cells Tok : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts}

/-- **THE TIE AT A KEPT COPY FROM THE TIE AT THE SENDER IN FRONT, AT A WRITTEN PAIR, AT THE BOOK,
UNDER THE HEAD.** One step back. THREE PREMISES STAY: hm₀: the tie at the sender; hNN; hrun: at
every run that the tie speaks of. -/
theorem ownMsgs_copy_at_book (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (Q : Script B (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N₀ N num fx₀ fx ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) {lay : OnBytes.Params.ReqLayout}
    {p₀ p : SwitchPlace} {S : SegmentPub} (hx : (p₀, p, S) ∈ copyPairs) {i n : Nat}
    (hi : i < p.sizes.kept.length)
    (hnn : n = keptNo (membersOfSeg S true) i)
    (hm₀ : OwnMsgs Q Vd N₀ num fx₀ (switchMsgOff ch D readers (lotClosingAt lay segsW) p₀ n))
    (hNN : N₀ ≤ N)
    (hrun : ∀ (k : Coins B) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn), Vd w → N ≤ hd.length →
      ∀ (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
        (V : Nat → Johnson.Prover.Send.Rows), handed ch p k = some c →
        switchRowsLaid D readers (lotClosingAt lay segsW) p c w (hd.take fx) = .ok V →
        ∃ (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
          (V₀ : Nat → Johnson.Prover.Send.Rows), handed ch p₀ k = some c₀ ∧
          switchRowsLaid D readers (lotClosingAt lay segsW) p₀ c₀ w (hd.take fx₀) = .ok V₀ ∧
          (∀ a, a < (segsW.take p₀.link).length →
            lotOwn segsW p₀ (D w.x) (readers w) ((hd.take fx₀).take ((hd.take fx₀).length - 0))
                (0 + a) =
              lotOwn segsW p (D w.x) (readers w) ((hd.take fx).take ((hd.take fx).length - 0))
                (0 + a)) ∧
          (∀ S ∈ segsW.take p₀.link,
            challengesOr0 ((hd.take fx₀).take ((hd.take fx₀).length - 0)) S.gamma =
              challengesOr0 ((hd.take fx).take ((hd.take fx).length - 0)) S.gamma) ∧
          ∀ Wl : Left,
            mainRows p₀.sizes Wl (lotOwn segsW p (D w.x) (readers w)
                ((hd.take fx).take ((hd.take fx).length - 0))
                (0 + (segsW.take p₀.link).length)) n =
              mainRows p₀.sizes Wl (senderOwn (D w.x) (readers w) p₀) n) :
    OwnMsgs Q Vd N num fx (switchMsgOff ch D readers (lotClosingAt lay segsW) p (1 + i)) := by
  obtain ⟨hT, ⟨e, he, t1, t2, t3⟩, hc, hw⟩ := book_five_at_pair h hB hx hi hnn
  exact ownMsgs_copy_at_pair Q Vd N₀ N num fx₀ fx ch D readers hx hi hnn hm₀ hNN hrun hT
    (pair_sizes hx) hw e he t1 t2 t3 hc

/-- **A PUBLIC TEST** at a pair and a kept copy i of its second switch: the message of the switch in
front that is copied is itself one of that switch's kept copies. -/
def copyOfCopy (x : SwitchPlace × SwitchPlace × SegmentPub) (i : Nat) : Bool :=
  decide (1 ≤ keptNo (membersOfSeg x.2.2 true) i) &&
    decide (keptNo (membersOfSeg x.2.2 true) i ≤ x.1.sizes.target.kept.size)

set_option maxRecDepth 1000000 in
/-- **Of the written pairs' kept copies**: how many there are; how many copy a kept copy. -/
theorem stepsW :
    ((copyPairs.map fun x => x.2.1.sizes.kept.length).sum,
      (copyPairs.map fun x =>
        ((List.range x.2.1.sizes.kept.length).filter (copyOfCopy x)).length).sum) = (34, 12) := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.pair_sizes
#print axioms AtFullSide.K2.ownMsgs_copy_at_book
#print axioms AtFullSide.K2.copyOfCopy
#print axioms AtFullSide.K2.stepsW
