-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnMsgsAtPair.lean: the kind "the code switch" (K2): THE TIE AT
A KEPT COPY FROM THE TIE AT THE SENDER IN FRONT, AT A WRITTEN PAIR, ITS PUBLIC PREMISES ON SHAPES,
NUMBERS AND LINKS PAID: `ownMsgs_copy_of_sender` (Honest/K2/Law/OwnMsgsCopy.lean) called at a member
(p₀, p, S) of `copyPairs` and a kept copy i of p, at the written segments. Two statements with their
proofs; no definition.

  `keptShapes_count`       where the test on the places accepts: as many kept shapes as targets
  `ownMsgs_copy_at_pair`   THE END

PAID HERE, SIXTEEN PREMISES OF THE LAW CALLED: hn₀, hs, hsk, hell, hm, hpad, hdeg, ha', hSent:
`copyFits_gives` at `copyFits_at` (Honest/K2/Law/CopyFitsGives.lean) · h3, hbare, ha1:
`copy_shape_ok` (Honest/K2/Law/KeptCopyShape.lean) at `keptCopies_written`
(Honest/K2/Law/KeptCopiesWritten.lean) · hS, hl: `copyPairs_between`
(Honest/K2/Law/CopyPairsMem.lean) · hn: the sealed `notices_size`
(Johnson/Top/H0/K2Hands/AtYes.lean) · hk: by rfl. SO LEAN ITSELF HOLDS THAT THE NINE ENDS OF
`copyFits_gives` ARE THE LAW's OWN PREMISES: the call would not be taken otherwise.

Limits. WHAT STAYS A PREMISE: hm₀: the tie at the sender: no Script is laid · hNN · hrun: at every
run that the tie speaks of: shown nowhere by us · the book's: hT, he, t1, t2, t3 · PUBLIC, AND NOT
PAID: hSz (the segment's sizes are the sender's) · hc (the two places have one list of codes) · hw.
ONE STEP BACK. ONE LETTER num SERVES BOTH TIES: all limits of OwnMsgsCopy.lean stand. AT THE WRITTEN
LISTS `placesW`, `segsW`: not carried to the head's own. The two copies at link 1 stand at no pair.
It rests on closed facts by evaluation in Lean's kernel. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnMsgsCopy
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyFitsGives
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyPairsMem
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptCopyShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (Left mainRows)
open ProofFile.Honest.FirstThread (Script OwnMsgs)

/-- Where the test on the places accepts there are as many kept shapes as targets. -/
theorem keptShapes_count {ps : List SwitchPlace} (hok : keptCopiesOk ps = true) {p : SwitchPlace}
    (hp : p ∈ ps) : p.sizes.kept.length = p.sizes.target.kept.size := by
  have h1 := List.all_eq_true.1 hok p hp
  rw [Bool.and_eq_true] at h1
  rw [eq_of_beq h1.1]
  simp

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **THE TIE AT A KEPT COPY FROM THE TIE AT THE SENDER IN FRONT, AT A WRITTEN PAIR.** One step
back. -/
theorem ownMsgs_copy_at_pair (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N₀ N num fx₀ fx ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) {lay : OnBytes.Params.ReqLayout}
    {p₀ p : SwitchPlace} {S : SegmentPub} (hx : (p₀, p, S) ∈ copyPairs) {i n : Nat}
    (hi : i < p.sizes.kept.length)
    (hnn : n = VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i)
    (hm₀ : OwnMsgs Q Vd N₀ num fx₀ (switchMsgOff ch D readers (lotClosingAt lay segsW) p₀ n))
    (hNN : N₀ ≤ N)
    (hrun : ∀ (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn), Vd w → N ≤ hd.length →
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
              mainRows p₀.sizes Wl (senderOwn (D w.x) (readers w) p₀) n)
    (hT : ∀ (a : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[a]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[a]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count)
    (hSz : S.sizes = p₀.sizes)
    (hw : NoWord (switchSent p.sizes p.others))
    (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[
      0 + ((segsW.take p₀.link).map (·.messages)).sum + n]? = some e)
    (t1 : e.owner = ⟨p₀.place, 0⟩)
    (t2 : e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) n)
    (t3 : e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD n default).shape
      (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n))
    (hc : p₀.sizes.codes = p.sizes.codes) :
    OwnMsgs Q Vd N num fx (switchMsgOff ch D readers (lotClosingAt lay segsW) p (1 + i)) := by
  subst hnn
  obtain ⟨-, hpW, -, -⟩ := copyPairs_mem hx
  obtain ⟨hS, hl⟩ := copyPairs_between hx
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := copyFits_gives (copyFits_at hx hi)
  have hi' : i < p.sizes.target.kept.size := by
    rw [← keptShapes_count keptCopies_written.2.2 hpW]
    exact hi
  obtain ⟨-, hbare, h3, ha1⟩ := copy_shape_ok keptCopies_written.2.2 hpW hi'
  have hn : 1 + i < (switchSent p.sizes p.others).size := by
    show 1 + i < (Tw.K2.switchNotices p.sizes.target p.others).size
    rw [VerifiableInference.Desc.First.K2.notices_size]
    omega
  exact ownMsgs_copy_of_sender Q Vd N₀ N num fx₀ fx ch D readers p₀ p hm₀ hNN hrun hT hl hS hSz a9
    hw hi hn h3 rfl rfl a8 a1 a7 e he t1 t2 t3 a2 hc hbare ha1 a5 a6 a3 a4

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.keptShapes_count
#print axioms ProofFile.Honest.K2.Law.ownMsgs_copy_at_pair
