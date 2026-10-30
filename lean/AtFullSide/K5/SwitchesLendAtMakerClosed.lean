-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/SwitchesLendAtMakerClosed.lean: THE THREE LAWS OF SwitchesLendAtMaker.lean WITHOUT
THEIR NAMED PREMISE hT2: UNDER THE LIBRARY's HEAD, WHEREVER THE FRAME's MAKER onlineProverFromPublicFiles RETURNS A, AT
WHATEVER FILLING: AT EACH CODE SWITCH OF THE PLAN THE BOOK A.B LENDS THE SWITCH's FIRST PART, IN
CHAIN 0 (the Bool `lendsPart`, Honest/Small/LendsRow.lean); SO AT EVERY RUN THE FRAME HANDS THAT
PART SOMETHING (`K2.handed`). Three theorems; no definition; one call each.

  `switch_lends_at_maker_closed`   h, hA ⊢ at every p of `K2.switchPlaces` Zp A.G: the Bool at A.B,
                                   chain 0
  `switch_handed_at_maker_closed`  h, hA ⊢ at every such p and every run: (`K2.handed` 0 p k).isSome
  `switch_lends_there_at_maker_closed`  h, hA, g < 12 ⊢ there is such a p with p.link = 2 g + 1,
                                   and the Bool holds at it

How. In hT2's seat: `AtFullSide.K14.switch_lends_at_written` (AtFullSide/K14/SwitchesLend.lean): the
same Bool at the book that `bookWhole` returns at the written description, at each place of the
written list.

Not for nothing. "At every p of the list" holds of nothing where the list is empty.
`switch_lends_there_at_maker_closed` says that it is not: a switch of the plan stands at each of the
twelve links 2 g + 1 (`switch_there_head`, MaskRowWritten.lean). OF THE OTHER LINKS NO LAW HERE SAYS
THAT A SWITCH STANDS THERE; nor how many the list has.

Limits. WHETHER THE PART IS HANDED SOMETHING: NEVER WHAT, NOR WHOSE: the Bool asks name, count and
that the owners' cuts fit: not that the run is the sender's own laying: it holds as well at a book
that lends another owner's stretch of that count: one owner and one start are not said. The first
part of each switch alone; chain 0 alone. hA is a premise: that the maker returns is not said here.
It rests on evaluations in Lean's kernel in SwitchesLend.lean and beneath it: they hold of the
makers' texts as they lie beneath. All limits of SwitchesLend.lean and SwitchesLendAtMaker.lean
hold: the merges are `mergesByName`'s, which the frame's own text calls a guess; the full size
alone; at the earlier hash `OnBytes.secondHashFunction`. It stands in this side library because its imports do.
The head is a hypothesis.
Nothing is claimed on soundness, completeness or hiding.
-/
import AtFullSide.K14.SwitchesLend
import AtFullSide.K5.SwitchesLendAtMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- **AT EACH SWITCH OF THE PLAN THE MAKER's BOOK LENDS THE SWITCH's FIRST PART, IN CHAIN 0.** The
Bool asks name, count and that the owners' cuts fit: not that the run is the sender's own laying: it
holds as well at a book that lends another owner's stretch of that count: one owner and one start
are not said. CONDITIONAL: h: the head; hA: the maker returns A at a filling P. -/
theorem switch_lends_at_maker_closed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ p ∈ K2.switchPlaces Zp A.G,
      lendsPart A.B (A.B.rowsOf 0) (lookDue A.B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true :=
  switch_lends_at_maker h hA fun _ hB _ hp => AtFullSide.K14.switch_lends_at_written hB hp

/-- **SO AT EVERY RUN THE FRAME HANDS THAT PART SOMETHING**: whether, never what, nor whose. It says
no more than the Bool `lendsPart` at A.B does (`handed_isSome`, HandedIsLends.lean). The Bool asks
name, count and that the owners' cuts fit: not that the run is the sender's own laying: it holds as
well at a book that lends another owner's stretch of that count: one owner and one start are not
said. CONDITIONAL: h, hA. -/
theorem switch_handed_at_maker_closed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ p ∈ K2.switchPlaces Zp A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true :=
  switch_handed_at_maker h hA fun _ hB _ hp => AtFullSide.K14.switch_lends_at_written hB hp

/-- **NOT FOR NOTHING: AT EACH LINK 2 g + 1, g < 12, A SWITCH OF THE PLAN IS THERE, AND THE BOOK
LENDS ITS FIRST PART.** The Bool asks name, count and that the owners' cuts fit: not that the run is
the sender's own laying: it holds as well at a book that lends another owner's stretch of that
count: one owner and one start are not said. CONDITIONAL: h, hA; hg. -/
theorem switch_lends_there_at_maker_closed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {g : ℕ} (hg : g < 12) :
    ∃ p ∈ K2.switchPlaces Zp A.G, p.link = 2 * g + 1 ∧
      lendsPart A.B (A.B.rowsOf 0) (lookDue A.B 0) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true :=
  switch_lends_there_at_maker h hA
    (fun _ hB _ hp => AtFullSide.K14.switch_lends_at_written hB hp) hg

end AtFullSide.K5

#print axioms AtFullSide.K5.switch_lends_at_maker_closed
#print axioms AtFullSide.K5.switch_handed_at_maker_closed
#print axioms AtFullSide.K5.switch_lends_there_at_maker_closed
