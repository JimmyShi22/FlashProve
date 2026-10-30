-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/MaskRowAtMaker.lean: CONDITIONAL, under the library's hypothesis h on the public input
(`P5J.AtMgA`), where the honest prover's maker `onlineProverFromPublicFiles` returns A (hA), and UNDER ONE CLOSED PREMISE
hB: THAT `bookWhole` RETURNS A BOOK AT THE WRITTEN DESCRIPTION `WP`: THE MAKER's BOOK A.B IS THAT
BOOK; so what the row at K5's place in each of the twelve attention segments spends in A.B is the
written stretch; so the premise hT of `covers_mask_switch_head`
(Johnson/Desc/ProofFile/Honest/K5/Law/MaskSwitchHead.lean) holds at Bk := A.B. No definition; three
theorems: calls alone.

Main names:
  `maker_book_is_written`: h, hA, and hB at a book B: A.B = B. At every filling P: the maker makes
    its book before it looks at the filling.
  `hT_at_maker_of_written`: h, hA, hB, g < 12: `oneStretch (rowEntries A.B ⟨1, 2 g + 1, 3, K5⟩ 13
    0)` is the part 0 at ⟨1, 2 g + 1, 1, K2⟩, from entry 2251, 1072 entries.
  `covers_mask_switch_at_maker`: `covers_mask_switch_head` at Bk := A.B, without hT.

THE PREMISES.
  h: the library's hypothesis. hA: `onlineProverFromPublicFiles` returns A at h's three files, at whatever filling P.
  hB: A CLOSED SENTENCE ON THE WRITTEN DESCRIPTION: no letter of a plan, a filling or a run. HERE A
    PREMISE: IT IS NOT DERIVED HERE. K14's authors state it as a theorem,
    `bookWhole_returns_written` (AtFullSide/K14/BookWholeWritten.lean): that file is not imported
    here; what it rests on its own head tells.
  The rest of `covers_mask_switch_at_maker`'s: as in MaskSwitchHead.lean, with what is told of each
    there: hnum lays K5's number on the lot of the switch's message 3 BY FIAT; hR is a test with
    code, here on the maker's book; hS: THAT the switch's text answers.

How `maker_book_is_written` goes. `parts_of_atPure` (Honest/K5/Law/ReturnsOf.lean): `onlineDescription`
returns A.F, and `bookWhole A.F p0 p1 p2 (mergesByName A.F.first.blocksInOrder)` returns A.B, p0 p1 p2 the
last three of the seven lists of `sendsOf`. h's field `laid.value`: A.F is the head's description.
The three lists are the library's written ones: `sends_tie`, `sendsWhole_all`, `made_in_scope`,
`pins_of_laid`: THE FIVE LINES OF K14's AUTHORS' OWN PROOF of `book_for_atPure_of_written`
(Honest/K14/BookForAtPure.lean). K14's authors' `bookWhole_carried_guess`
(Honest/BookWholeAlike.lean, in the frame's folder) at their `planAlike_at_laid`
(Honest/K14/WrittenAtHead.lean) carries hB to the head's description; `bookWhole` is a function.
THAT LAST STEP IS K14's AUTHORS' `rawBook_same` (AtFullSide/K14/RawAtTheBookAtHead.lean), RETYPED IN
ONE LINE: that file is not imported here. The second theorem: K14's authors' `rawRowStretchAtK5`
(AtFullSide/K14/RawRowStretch.lean).

Kin. K14's authors' `atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean): under h and hA
`bookWhole` at the head's own three lists returns A.B: the matter of `maker_book_is_written`'s proof
but for its last line, of other bricks: not called here.

Limits. CONDITIONAL. `covers_mask_switch_at_maker` IS AN EXCHANGE, NOT A GAIN, AND NARROWER: hT, a
test on a free book, goes; hA and hB come; the book is pinned to the maker's. The merges are
`mergesByName`'s: by that definition's own docstring a guess; the maker's own text has that very
term. `rawRowStretchAtK5` rests on evaluations in Lean's kernel through `segmentCarries` as it lies
beneath this file: of another text of that definition nothing is said here. That message 3 bears
K5's number, that hR or hS holds, that a lot with that number and text stands in the frame's list:
not said here. The file stands in this side library because its first import does: no file of the
main library can call it. At the full size; at the earlier hash `OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import AtFullSide.K14.RawRowStretch
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitchHead
import Johnson.LPFE1R.RadiiAt
import Johnson.AtFull.Sends.SendsWhole
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.FirstThread (MsgLot Covers)
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- **THE MAKER's BOOK IS THE WRITTEN DESCRIPTION's.** CONDITIONAL: under the hypothesis h; hA: the
maker returns A; hB: `bookWhole` returns B at the written description. -/
theorem maker_book_is_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) : A.B = B := by
  obtain ⟨m, -⟩ := parts_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  obtain ⟨c0, c1, c2, c3, p0, p1, p2, hs, hb⟩ := m.book
  obtain ⟨En, hEn⟩ := Johnson.AtFull.Sends.sendsWhole_all
  have h1 := VerifiableInference.Desc.LinkJoin.sends_tie h.laid.pub hs
  have h2 := hEn _ (VerifiableInference.PlanWritten.Joined.made_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1)
  have hl := Except.ok.inj (h1.symm.trans h2)
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := hl
  rw [eF] at hb
  exact Except.ok.inj
    (hb.symm.trans (bookWhole_carried_guess (K14.planAlike_at_laid h.scope h.laid) hB))

/-- **WHAT K5's ROW SPENDS IN THE MAKER's BOOK IS THE WRITTEN STRETCH**, in each of the twelve
segments. CONDITIONAL: h; hA; hB: `bookWhole` returns a book at the written description; hg. -/
theorem hT_at_maker_of_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {g : ℕ} (hg : g < 12) :
    oneStretch (rowEntries A.B ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072) := by
  obtain ⟨B, hB⟩ := hB
  rw [maker_book_is_written h hA hB]
  exact AtFullSide.K14.rawRowStretchAtK5 hB g hg

/-- **`covers_mask_switch_head` AT THE MAKER's BOOK, WITHOUT hT.** CONDITIONAL: h; hA; hB; the rest
as there. AN EXCHANGE, NOT A GAIN. -/
theorem covers_mask_switch_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) (hx : Z5.P.x = a.own) (hZ : Z5.link = 2 * g + 1)
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) (hl : p.link = 2 * g + 1) {num : ℕ}
    (fx : ℕ) (hnum : num = maskNo5 h x₁ kM hk)
    (cells : Tr → Cells) (hR : lendsRow A.B 0 Z5.place (k5Row Z5) = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ (k : Coins A.B) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      maskAnswers Z5 (OnBytes.Model.Forest.elems a.fs) mask row place = true →
      (K2.switchMsgTxt 0 D₁ rd closing p 3 k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p 3⟩
      (maskLot (Bk := A.B) h x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs)) :=
  covers_mask_switch_head h hG hg ea hx hZ D₁ rd closing hp hl fx hnum
    (hT_at_maker_of_written h hA hB hg) cells hR hS

end AtFullSide.K5

#print axioms AtFullSide.K5.maker_book_is_written
#print axioms AtFullSide.K5.hT_at_maker_of_written
#print axioms AtFullSide.K5.covers_mask_switch_at_maker
