-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersMaskTied.lean: TWO FORMS OF THE SENDERS' PREMISES AT THE
CODE SWITCHES. THE MASK's: WITHOUT ITS TEST hT ON THE BOOK; WITH THE SWITCH's OWN NUMBER OF ITS
MESSAGE 3 ON THE LOT, IN THE PLACE OF K5's NUMBER OF ITS MASK MESSAGE; AND WITH A Bool OF THE BOOK
(hL) WHERE THE ELDER FORM HAS "at every run the frame hands the switch's part something" (hh). THE
FILLINGS': WITH hL WHERE THE ELDER HAS hh. hL IS A PREMISE HERE: THIS FILE PROVES IT OF NO BOOK. hL
STANDS WHERE THE ELDER FORM HAS hh: AN EXCHANGE BY `handed_of_lends` (HandedIsLends.lean in this
folder), NOT A PAYMENT. NO JOINED LAW STANDS IN THIS FILE: no thread and no filling are named in it.
The mask's two arrows are CONDITIONAL: under the hypothesis h, the library's head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). Two definitions, forms of premises; four theorems.

Main names:
  `PlanSwitchLotForMaskTied Zp ml Vd G g lay`: `PlanSwitchLotForMaskPlain` (SendersPlain.lean in
    this folder) with the conjunct hT struck, `K2.switchNum Zp p 3` for `maskNo5 h x₁ kM hk`, and hL
    at the chain 0 for hh. It names the hypothesis h no more, nor K5's letters x₁, kM, hk, nor the
    book's written numbers (13, 2251, 1072); the message's number 3 and the chain's 0 stay. LEFT IN
    IT, behind "there is" D₁, rd', fx: the lot lies in ml; `LotsAgree`; hL; hv.
  `PlanSwitchLotForFillLends Zp ml Vd S G rd Ad l m' lay`: `PlanSwitchLotForFillPlain`
    (SendersPlain.lean) with hL at its own ch, which stays under "there is", for hh. LEFT IN IT: the
    lot lies in ml; `LotsAgree`; hL; hv.
  `planSwitchLotForMaskTied_of_plain`: h; hG; hg; hx₁; hm; the plain form: the tied form.
  `planSwitchLotForMaskPlain_of_tied`: h; hG; hg; hx₁; hm; hT; the tied form: the plain form.
  `planSwitchLotForFillLends_of_plain`, `planSwitchLotForFillPlain_of_lends`: each form gives the
    other: no premise but the form.

How. THE NUMBER: `mask_tie_head` (MaskTie.lean in this folder): under h, hG, the place's membership
in the plan's list, hg, the place's link, hx₁ and hm the two numbers are one; the membership and the
link are what both forms range over. hh AND hL: `handed_of_lends`: hL gives hh; `lends_of_handed`:
hh at one run's letter gives hL, and the frame gives every book one (its `Inhabited` on the runs'
letters of a book, Honest/Frame.lean): called at `default`.

Limits. THE NUMBER: AN EXCHANGE OF EQUALS UNDER hG, hg, hx₁, hm. hh FOR hL: AN EXCHANGE OF EQUALS AT
EVERY BOOK. NO NEW STRENGTH BY EITHER. WHAT hL BUYS IS THE SHAPE: a test with code on the book, the
chain's number, the place and the part's stated counts, where the source has a clause under "for all
k". Four conjuncts behind "there is" in each form, as in the mask's form with hh and in the
fillings' plain form. hT: THE TIED FORM IS THE WEAKER PREMISE BY ONE CONJUNCT; THIS FILE PROVES hT
AT NO BOOK. OF THE BINDERS THAT ARE WRITTEN IN THE TWO FORMS ONE ALONE IS A RUN's LETTER: hv's w.
`LotsAgree`, WHICH STANDS IN BOTH, UNFOLDS TO A CLAUSE UNDER "for all k w": that binding stays. That
the lot which a list of the frame's bears for the switch's message 3 has the number `K2.switchNum Zp
p 3` is not said here. Further texts of the two premises, each tied to its source both ways; the
mask's way back wants hT, which the source holds. ON WHETHER hL AND hv CAN BE MET NOTHING IS HELD
HERE. All limits of SendersPlain.lean, MaskTie.lean and HandedIsLends.lean hold here. Through its
imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/
(lean/LIMITS.md, L15): a fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed
function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersPlain
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskTie
import Johnson.Desc.ProofFile.Honest.K5.Law.HandedIsLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree
  Covers ofLots_hfix)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`PlanSwitchLotForMaskPlain` without hT, with the switch's own number of its message 3, and
with hL for hh.** A premise's form. -/
def PlanSwitchLotForMaskTied
    (Zp : ProofFile.Pub)
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (G : Ground)
    (g : ℕ)
    (lay : OnBytes.Params.ReqLayout) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, p.link = 2 * g + 1 → ∃ (D₁ : RowDataOf ProofFile.Inst) (rd' :
            Local W₀ Rc ProofFile.Inst Tr → Readers) (fx : ℕ), (⟨K2.switchNum Zp p 3, fx, K2.switchMsgTxt 0 D₁
                  rd' (K2.lotClosingAt lay (K2.segmentsOf Zp G)) p 3⟩ : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈
      ml ∧ LotsAgree ml ⟨K2.switchNum Zp p 3, fx, K2.switchMsgTxt 0 D₁ rd' (K2.lotClosingAt lay
      (K2.segmentsOf Zp G)) p 3⟩ ∧ lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) = true ∧ ∀
      w, Vd w → K2.publicOk D₁ lay p ((K2.segmentsOf Zp G).take p.link) w.x = true

/-- **`PlanSwitchLotForFillPlain` with hL for hh.** A premise's form. -/
def PlanSwitchLotForFillLends
    (Zp : ProofFile.Pub)
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (Ad : MsgAddr)
    (l m' : ℕ)
    (lay : OnBytes.Params.ReqLayout) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, ∀ m, Ad = p.ownAddr m → l = p.link → ∃ (D₀ : Pub → Ground →
      RowDataOf ProofFile.Inst) (fx ch : ℕ), (⟨P5J.At.num Zp l m', fx, K2.switchMsgTxt ch
            (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay (K2.segmentsOf Zp G)) p (1 +
            p.sizes.kept.length + m)⟩ : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧ LotsAgree ml
      ⟨P5J.At.num Zp l m', fx, K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt
      lay (K2.segmentsOf Zp G)) p (1 + p.sizes.kept.length + m)⟩ ∧ lendsPart Bk (Bk.rowsOf ch)
      (lookDue Bk ch) ⟨p.place, 0⟩ (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others
      p.foldVars p.carries) = true ∧ ∀ w, Vd w → K2.publicOk (K2.withSwitchData S D₀ Zp G) lay p
      ((K2.segmentsOf Zp G).take p.link) w.x = true

/-- **The plain form gives the form with hL.** No premise but the form. -/
theorem planSwitchLotForFillLends_of_plain
    {Zp : ProofFile.Pub}
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {l m' : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    (H : PlanSwitchLotForFillPlain Zp ml Vd S G rd Ad l m' lay) :
    PlanSwitchLotForFillLends Zp ml Vd S G rd Ad l m' lay := by
  intro p hp m eA el
  obtain ⟨D₀, fx, ch, hmem, ha, hh, hv⟩ := H p hp m eA el
  exact ⟨D₀, fx, ch, hmem, ha, lends_of_handed ch p default (hh default), hv⟩

/-- **The form with hL gives the plain form.** No premise but the form. -/
theorem planSwitchLotForFillPlain_of_lends
    {Zp : ProofFile.Pub}
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {l m' : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    (H : PlanSwitchLotForFillLends Zp ml Vd S G rd Ad l m' lay) :
    PlanSwitchLotForFillPlain Zp ml Vd S G rd Ad l m' lay := by
  intro p hp m eA el
  obtain ⟨D₀, fx, ch, hmem, ha, hL, hv⟩ := H p hp m eA el
  exact ⟨D₀, fx, ch, hmem, ha, handed_of_lends ch p hL, hv⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **The plain form gives the tied one.** CONDITIONAL: h; hG; hg; hx₁; hm. -/
theorem planSwitchLotForMaskTied_of_plain
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {G : Ground}
    {g : ℕ}
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    {lay : OnBytes.Params.ReqLayout}
    (hG : blankBy pureRoad.links Zp = some G)
    (hg : g < 12)
    (hx₁ : x₁.link = 2 * g + 1)
    (hm : maskMsg h.𝔇.sent x₁.link = some kM)
    (H : PlanSwitchLotForMaskPlain h ml Vd G g x₁ kM hk lay) :
    PlanSwitchLotForMaskTied Zp ml Vd G g lay := by
  intro p hp hl
  obtain ⟨D₁, rd', fx, hmem, ha, -, hh, hv⟩ := H p hp hl
  rw [mask_tie_head h hG hp hg hl (hk := hk) hx₁ hm]
  exact ⟨D₁, rd', fx, hmem, ha, lends_of_handed 0 p default (hh default), hv⟩

/-- **hT and the tied form give the plain one.** CONDITIONAL: h; hG; hg; hx₁; hm; hT. -/
theorem planSwitchLotForMaskPlain_of_tied
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {G : Ground}
    {g : ℕ}
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    {lay : OnBytes.Params.ReqLayout}
    (hG : blankBy pureRoad.links Zp = some G)
    (hg : g < 12)
    (hx₁ : x₁.link = 2 * g + 1)
    (hm : maskMsg h.𝔇.sent x₁.link = some kM)
    (hT : oneStretch (rowEntries Bk ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) = some (⟨⟨1, some (2 * g +
      1), 1, .K2⟩, 0⟩, 2251, 1072))
    (H : PlanSwitchLotForMaskTied Zp ml Vd G g lay) :
    PlanSwitchLotForMaskPlain h ml Vd G g x₁ kM hk lay := by
  intro p hp hl
  obtain ⟨D₁, rd', fx, hmem, ha, hL, hv⟩ := H p hp hl
  rw [mask_tie_head h hG hp hg hl (hk := hk) hx₁ hm] at hmem ha
  exact ⟨D₁, rd', fx, hmem, ha, hT, handed_of_lends 0 p hL, hv⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.PlanSwitchLotForMaskTied
#print axioms ProofFile.Honest.K5.PlanSwitchLotForFillLends
#print axioms ProofFile.Honest.K5.planSwitchLotForFillLends_of_plain
#print axioms ProofFile.Honest.K5.planSwitchLotForFillPlain_of_lends
#print axioms ProofFile.Honest.K5.planSwitchLotForMaskTied_of_plain
#print axioms ProofFile.Honest.K5.planSwitchLotForMaskPlain_of_tied
