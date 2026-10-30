-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Term/MaskRowFromScript.lean: the honest side of the kind "lookup"
(K3): what a lookup asks of the part that SENDS its link's mask row, as one named premise on the
Script, and the bundles' clause on that sender (`SenderLays`, Honest/K3/Law/MasksWorld.lean) from it.

Why. A lookup masks what it sends with entries of its link's mask row. The row is another part's:
the opening's (K1) at link 0, a switch's (K2) at links 1 to 24. The bundles `DigitsRunAll`
(Honest/K3/Law/Thread/ExchangeDigitsAll.lean), `DigitsRunFactsFromSaid`
(Honest/K3/Term/DigitsExchangeFromSaid.lean) and their sisters at the calls ask: "entry j of the mask
table that the verifier's reader reads out of the Script's witness is the owner's coin number
base.e + j". That sentence has two halves. The reader's half speaks of the verifier's state and the
plan (`ReaderAt`, Honest/Law/Rule/ReaderAt.lean). The owner's half speaks of the Script's function
`msg` alone: only the owner's authors, and whoever lays the Script, can show it. Here it gets a name
and a form in which they can: the frame's own `OwnMsgs` (Honest/Thread/ScriptLots.lean) at a text of
ours, which a lot of theirs may cover (`Covers`, Honest/Small/Covers.lean).

  `maskRowEntriesText`                 the text: entry number place of mask row 0 is the owner's coin
                                       number start + place, for place below count; no answer
                                       anywhere else, and NO ANSWER WHERE THE OWNER HAS NO SUCH COIN
  `ScriptLaysOwnersCoinsInMaskRow`     THE NAMED PREMISE, at one message: `OwnMsgs` at that text
  `ScriptLaysEveryLinksMaskRow`        the same at every site of a public part, owner and start being
                                       what the book's maker finds at the written description
  `maskRowEntriesTextAnswers`          where the coin is, the text answers it
  `scriptLaysOwnersCoinsInFewerEntries`  the premise at a count gives it at every smaller count
  `senderLaysFromScript`               the bundles' clause to the letter, with the range

A like join. K4's authors have typed the same join from any sender's lot (their
`senderLays_of_lot`, in a file that is not part of this library): `OwnMsgs` at
the lot's text, that the text answers, and what it answers. Ours is that join at one fixed text,
which is the premise's own; nothing of their file is called or copied.

Limits. The two premises are DEFINITIONS: shown here of no Script. `OwnMsgs` asks nothing at
an input at which `valid` fails, nor at a list of challenges shorter than challengesInFront; where
the owner has fewer coins than start + count the text is silent and the premise asks nothing of the
entries beyond: the join therefore takes the fence (hFence) as a premise of its own. `ReaderAt` is a
premise of the join. One mask row alone. That owner and start are the sending part's own address and
its own start of the mask row, and that messageNumber is that message's number in the witness, is
said nowhere here. A premise that names a run's coins: it may not stand in front of a law over coins
unless it is named there. Nothing is claimed on soundness, completeness, hiding or any other property
of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.BookFenceSite
import Johnson.Desc.ProofFile.Honest.Law.Rule.ReaderAt
import Johnson.Desc.ProofFile.Honest.Small.Covers
import Johnson.Desc.ProofFile.Honest.BookEntries
import Johnson.AtFull.ProofPlan.WP
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes (E zeroE)
open OnBytes.Slice (GE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT Mem tabQ dataQ seatTab)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K3.Law
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-! ## 1 The text, with its fence in it -/

/-- **The mask row's entries number 0, …, count - 1, as the owner's coins number start, start + 1, …
of the extension field**, read in the library's field (`Reading.gl.val`, which the lookups' files
abbreviate as rd). Bk: the book of coins. owner: the address of
the part whose coins they are. The input and the challenges are not read. IT ANSWERS NOTHING where
the owner has no such coin: the list is read by "[…]?", not by a default. It answers nothing at a
main row, at a mask row other than number 0, or from place count on. -/
def maskRowEntriesText (Bk : ProverCoinCounts) {W : Type} (owner : Addr) (start count : Nat) :
    Coins Bk → W → List Fmt.Drawn → Bool → Nat → Nat → Option GE :=
  fun k _ _ mask row place =>
    if mask = true ∧ row = 0 ∧ place < count then
      ((coinsE (k.look 0 owner).2)[start + place]?).map Reading.gl.val
    else none

/-! ## 2 The named premise -/

/-- **THE NAMED PREMISE, GENERAL IN THE SCRIPT: the Script lays the owner's coins in the mask row.**
Q: the Script. messageNumber: the number, in the witness, of the message that holds the mask row.
valid, challengesInFront: at which inputs, and from how many challenges on, it is asked. At all
coins k, every valid input and every such list of challenges: wherever the owner has coin number
start + place, with place below count, the Script's message has it, read in the library's field, as
entry number place of mask row 0. It is a definition: the form of a hypothesis. -/
def ScriptLaysOwnersCoinsInMaskRow {Bk : ProverCoinCounts} {W Cells Tok : Type}
    (Q : Script Bk W Cells Tok MsgT) (valid : W → Prop) (challengesInFront messageNumber : Nat)
    (owner : Addr) (start count : Nat) : Prop :=
  OwnMsgs Q valid challengesInFront messageNumber 0 (maskRowEntriesText Bk owner start count)

/-- **THE SAME AT EVERY LOOKUP OF A PUBLIC PART: one sentence for all sites.** Zp: the public part.
challengesInFront, messageNumber: by the link's number. r: what the book's maker finds as the owner
of the link's mask row (`ownerOf`, Honest/BookEntries.lean) at the written description and the
written sendings: the letter r' of `k3Fits_at_atPure` (AtFullSide/Honest/K3/FitsAtPure.lean), at which
the two tests `bookFits` and `startsFit` are shown. count: up to the lookup's last slot. At a link at
which `ownerOf` returns nothing, nothing is asked. It is a definition: the form of a hypothesis. -/
def ScriptLaysEveryLinksMaskRow {Bk : ProverCoinCounts} {W Cells Tok : Type} (Q : Script Bk W Cells Tok MsgT)
    (valid : W → Prop) (Zp : ProofFile.Pub) (challengesInFront messageNumber : Nat → Nat) : Prop :=
  ∀ s ∈ lookSites Zp, ∀ r : MsgAt,
    ProofFile.Honest.ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1
      (WP.second.blocksInOrder.flatMap (·.rounds)) s!"link {s.link}, moment 0" isMaskRowMsg = some r →
    ScriptLaysOwnersCoinsInMaskRow Q valid (challengesInFront s.link) (messageNumber s.link)
      r.owner r.base.e (s.p.first + s.at_.face.slots)

/-! ## 3 Small laws on the text and the premise -/

/-- Where the coin is, the text answers it: the same element that a reading by default returns. -/
theorem maskRowEntriesTextAnswers {Bk : ProverCoinCounts} {W : Type} (owner : Addr) (start count : Nat)
    (k : Coins Bk) (w : W) (hd : List Fmt.Drawn) {place : Nat} (hPlace : place < count)
    (hCoin : start + place < (coinsE (k.look 0 owner).2).length) :
    maskRowEntriesText Bk owner start count k w hd true 0 place =
      some (rd ((coinsE (k.look 0 owner).2).getD (start + place) zeroE)) := by
  unfold maskRowEntriesText
  rw [if_pos ⟨rfl, rfl, hPlace⟩, List.getElem?_eq_getElem hCoin, List.getD_eq_getElem _ _ hCoin]
  exact rfl

/-- The premise at a count gives it at every smaller count. -/
theorem scriptLaysOwnersCoinsInFewerEntries {Bk : ProverCoinCounts} {W Cells Tok : Type}
    {Q : Script Bk W Cells Tok MsgT} {valid : W → Prop} {challengesInFront messageNumber : Nat}
    {owner : Addr} {start count fewer : Nat} (hFewer : fewer ≤ count)
    (hScript : ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber owner start
      count) :
    ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber owner start fewer := by
  intro k w hd hw hN mask row place y q
  refine hScript k w hd hw hN mask row place y ?_
  unfold maskRowEntriesText at q ⊢
  by_cases c : mask = true ∧ row = 0 ∧ place < fewer
  · rw [if_pos c] at q
    rw [if_pos ⟨c.1, c.2.1, Nat.lt_of_lt_of_le c.2.2 hFewer⟩]
    exact q
  · rw [if_neg c] at q
    exact absurd q (by simp)

/-! ## 4 The bundles' clause on the sender -/

/-- **THE CLAUSE ON THE SENDER, TO THE LETTER, WITH THE RANGE, at every Script.** The lookups' own
`SenderLays` (Honest/K3/Law/MasksWorld.lean: on the table read off the witness), not the frame's
sentence of the same name (Honest/Law/Rule/TiesFall.lean: on the sender's row). CONDITIONAL on:
hScript, the named premise; hReader, the six facts on the verifier's state and the plan, up to entry
free; hFree; ho, the state's own pick of the message; hFence, that the owner has every coin that is
named (the end of `named_reads_site`, Honest/K3/Law/BookFenceSite.lean, to the letter); hValid and
hChallenges, the premise's two guards. The second conjunct is hFence again: it stands in the end so
that whoever holds the clause holds with it that the default in a coin's place is never reached. -/
theorem senderLaysFromScript {Bk : ProverCoinCounts} {W Cells Tok : Type} {Q : Script Bk W Cells Tok MsgT}
    {valid : W → Prop} {challengesInFront messageNumber : Nat} {owner : Addr}
    {start count free : Nat}
    (hScript : ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber owner start
      count)
    {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem} {own : List (ℕ × ℕ)}
    {a : VerifiableInference.Desc.K9.Part}
    (hReader : ReaderAt cs arr ms own a messageNumber free) (hFree : count ≤ free)
    {o : Nat} (ho : maskOracle a.L.check.frame = some o) (k : Coins Bk)
    (hFence : ∀ j, j < count → start + j < (coinsE (k.look 0 owner).2).length)
    {w : W} (hValid : valid w) {hd : List Fmt.Drawn} (hChallenges : challengesInFront ≤ hd.length) :
    K3.Law.SenderLays (tabQ own a.d.st a.d.book (seatTab cs arr ms (Q.wit k w hd))) o 1 count start
        (fun i => rd ((coinsE (k.look 0 owner).2).getD i zeroE)) ∧
      ∀ j, j < count → start + j < (coinsE (k.look 0 owner).2).length := by
  refine ⟨fun j hj => ?_, hFence⟩
  rw [index_one, ← world_mask a.L.check.rows a.L.check.frame a.d.st
    (tabQ own a.d.st a.d.book (seatTab cs arr ms (Q.wit k w hd))) o ho j]
  refine (reader_at hReader (Q.wit k w hd) (Nat.lt_of_lt_of_le hj hFree)).trans ?_
  exact hScript k w hd hValid hChallenges true 0 j _
    (maskRowEntriesTextAnswers owner start count k w _ hj (hFence j hj))

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.maskRowEntriesTextAnswers
#print axioms ProofFile.Honest.K3.Term.scriptLaysOwnersCoinsInFewerEntries
#print axioms ProofFile.Honest.K3.Term.senderLaysFromScript
