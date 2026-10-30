-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/SwitchesLendAtMaker.lean: CONDITIONAL ON ONE NAMED PREMISE, hT2: UNDER THE LIBRARY's
HEAD, WHEREVER THE FRAME's MAKER onlineProverFromPublicFiles RETURNS A, AT WHATEVER FILLING: AT EACH CODE SWITCH OF THE
PLAN THE BOOK A.B LENDS THE SWITCH's FIRST PART, IN CHAIN 0 (the Bool `lendsPart`,
Honest/Small/LendsRow.lean); SO AT EVERY RUN THE FRAME HANDS THAT PART SOMETHING (`K2.handed`).
Three theorems; no definition; calls alone.

  `switch_lends_at_maker`   h, hA, hT2 ⊢ at every p of `K2.switchPlaces` Zp A.G: the Bool at A.B,
                            chain 0
  `switch_handed_at_maker`  h, hA, hT2 ⊢ at every such p and every run: (`K2.handed` 0 p k).isSome
  `switch_lends_there_at_maker`  h, hA, hT2, g < 12 ⊢ there is such a p with p.link = 2 g + 1, and
                            the Bool holds at it

THE PREMISE hT2: the same Bool at the book that `bookWhole` returns at the written description, at
each place of the written list `K2.Law.placesW`. hT2 IS A PREMISE HERE: THIS FILE PROVES IT OF NO
BOOK; nor does a file beneath it.

How. `AtFullSide.K14.bookWhole_returns_written` hands a book B at the written description;
`maker_book_is_written` (MaskRowAtMaker.lean): A.B is B; `places_under_head`
(Johnson/Desc/ProofFile/Honest/K5/Law/MaskRowWritten.lean): the plan's switches are the written
list, at the maker's ground, which hA gives; hT2 at B; `handed_of_lends`
(Johnson/Desc/ProofFile/Honest/K5/Law/HandedIsLends.lean).

Not for nothing. "At every p of the list" holds of nothing where the list is empty.
`switch_lends_there_at_maker` says that it is not: by `switch_there_head` (MaskRowWritten.lean) a
switch of the plan stands at each of the twelve links 2 g + 1. OF THE OTHER LINKS NO LAW HERE SAYS
THAT A SWITCH STANDS THERE; nor how many the list has.

Limits. WHETHER THE PART IS HANDED SOMETHING: NEVER WHAT, NOR WHOSE: the Bool asks name, count and
that the owners' cuts fit: not that the run is the sender's own laying: it holds as well at a book
that lends another owner's stretch of that count: one owner and one start are not said. The first
part of each switch alone; chain 0 alone. hA is a premise: that the maker returns is not said here.
Nothing on whether the part then plays, nor on what it sends. It stands in this side library because
`bookWhole_returns_written` does: no file of the main library can call it. All limits of
BookWholeWritten.lean, MaskRowAtMaker.lean, MaskRowWritten.lean and HandedIsLends.lean hold: the
merges are `mergesByName`'s, which the frame's own text calls a guess; the full size alone; at the
earlier hash `OnBytes.secondHashFunction`. The head is a hypothesis.
Nothing is claimed on soundness, completeness or hiding.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K5.MaskRowAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskRowWritten
import Johnson.Desc.ProofFile.Honest.K5.Law.HandedIsLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- **AT EACH SWITCH OF THE PLAN THE MAKER's BOOK LENDS THE SWITCH's FIRST PART, IN CHAIN 0.** The
Bool asks name, count and that the owners' cuts fit: not that the run is the sender's own laying: it
holds as well at a book that lends another owner's stretch of that count: one owner and one start
are not said. CONDITIONAL: h: the head; hA: the maker returns A at a filling P; hT2: the same at the
written description's book, at the written places. -/
theorem switch_lends_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hT2 : ∀ (B : ProverCoinCounts), bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B → ∀ p ∈ K2.Law.placesW,
      lendsPart B (B.rowsOf 0) (lookDue B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true) :
    ∀ p ∈ K2.switchPlaces Zp A.G,
      lendsPart A.B (A.B.rowsOf 0) (lookDue A.B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true := by
  intro p hp
  obtain ⟨B, hB⟩ := AtFullSide.K14.bookWhole_returns_written
  have eB : A.B = B := maker_book_is_written h hA hB
  have hG : blankBy pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  rw [places_under_head h hG] at hp
  rw [eB]
  exact hT2 B hB p hp

/-- **SO AT EVERY RUN THE FRAME HANDS THAT PART SOMETHING**: whether, never what, nor whose. It says
no more than the Bool `lendsPart` at A.B does (`handed_isSome`, HandedIsLends.lean). The Bool asks
name, count and that the owners' cuts fit: not that the run is the sender's own laying: it holds as
well at a book that lends another owner's stretch of that count: one owner and one start are not
said. CONDITIONAL: h, hA, hT2. -/
theorem switch_handed_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hT2 : ∀ (B : ProverCoinCounts), bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B → ∀ p ∈ K2.Law.placesW,
      lendsPart B (B.rowsOf 0) (lookDue B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true) :
    ∀ p ∈ K2.switchPlaces Zp A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true :=
  fun p hp => handed_of_lends 0 p (switch_lends_at_maker h hA hT2 p hp)

/-- **NOT FOR NOTHING: AT EACH LINK 2 g + 1, g < 12, A SWITCH OF THE PLAN IS THERE, AND THE BOOK
LENDS ITS FIRST PART.** The Bool asks name, count and that the owners' cuts fit: not that the run is
the sender's own laying: it holds as well at a book that lends another owner's stretch of that
count: one owner and one start are not said. CONDITIONAL: h, hA, hT2; hg. -/
theorem switch_lends_there_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hT2 : ∀ (B : ProverCoinCounts), bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B → ∀ p ∈ K2.Law.placesW,
      lendsPart B (B.rowsOf 0) (lookDue B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true)
    {g : ℕ} (hg : g < 12) :
    ∃ p ∈ K2.switchPlaces Zp A.G, p.link = 2 * g + 1 ∧
      lendsPart A.B (A.B.rowsOf 0) (lookDue A.B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true := by
  have hG : blankBy pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  obtain ⟨p, hp, hl⟩ := switch_there_head h hG hg
  exact ⟨p, hp, hl, switch_lends_at_maker h hA hT2 p hp⟩

end AtFullSide.K5

#print axioms AtFullSide.K5.switch_lends_at_maker
#print axioms AtFullSide.K5.switch_handed_at_maker
#print axioms AtFullSide.K5.switch_lends_there_at_maker
