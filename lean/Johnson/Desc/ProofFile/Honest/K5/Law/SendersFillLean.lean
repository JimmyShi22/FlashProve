-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersFillLean.lean: THE FORM OF THE PREMISE ON THE SWITCHES'
OWN MESSAGES WITHOUT FOUR CLAUSES ON PUBLIC DATA (hn, hl, hmk, hIn): A CURE, AND A WEAKER PREMISE.
`PlanSwitchLotForFillLean` is the body of `PlanSwitchLotForFillTests` (SendersTests.lean in this
folder) less these four conjuncts. WHY: THE ELDER FORM's CLAUSE hmk, "the message has a mask row",
FAILS AT THE LIBRARY's WRITTEN PLAN AT TWO OF THE THREE OWN MESSAGES OF EACH SWITCH THAT LEADS INTO
AN EVEN SEGMENT FROM 2 TO 22 (its field link), AND THE JOINED LAWS ASK THE FORM AT EVERY SEATED
ADDRESS: SO, ARGUED, UNDER h THE LAWS OF THIS FOLDER THAT HAVE THE ELDER FORM HOLD FOR NOTHING AT
ELEVEN OF THE TWELVE GROUPS. THAT IS NOT PROVED HERE: it rests on the request's written shape as it
is read (Johnson/Desc/ReqLit/Full.lean), on an evaluation not in this tree, on the law that under
h the plan's places are the written ones (`places_under_head`, MaskRowWritten.lean in this folder),
and on a tie that is read, not typed: that under h the ground's shape is the written one. NO JOINED
LAW STANDS IN THIS FILE: no thread and no filling are named in it. CONDITIONAL: under the hypothesis
h, the library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). One definition, a
form of a premise; two theorems.

Main names:
  `PlanSwitchLotForFillLean Zp ml Vd S G rd Ad l m' lay segs`: at every member p of `K2.switchPlaces
    Zp G` and every m with Ad = p.ownAddr m and l = p.link there are data, a number of challenges
    and a number of the book's part such that the triple of the filling's number, that number and
    the text of the switch's own message m, at the closing `K2.lotClosingAt lay segs`, lies in ml
    and agrees with ml's other lots; and the six premises of `switch_answers` (SwitchAnswers.lean in
    this folder). It names h no more: a form on Zp, the list and the book.
  `planSwitchLotForFillLean_of_elder`: the elder form gives the leaner.
  `covers_of_planSwitchLotForFillLean`: the leaner form gives the clause of SF0 and SF1 on covering,
    at every segment but the first.

How. `covers_fill_switch_head` (FillSwitchHead.lean in this folder) has the covering at every own
message of every switch of the plan under h, hG, the membership, the seat's equation, an equation
between two numbers and hS alone: the four clauses are derived there. `seated_at_switch`
(SeatedSwitch.lean in this folder) hands the place and the message of a seated address. hS comes
from `switch_answers`, whose end holds at every message and entry. A rider goes with
`covers_fill_switch_head` wherever it is told: it speaks off the pads' places, at moment 0, at an
own message, where the text answers.

Limits. THE FIRST LEMMA SAYS THAT THE LEANER FORM IS THE WEAKER PREMISE, AND NO MORE: where the
fuller form cannot be met it holds from a falsehood. Back no arrow is stated, and none holds there.
WHAT IS LEFT IN THE LEANER FORM: that a lot with the switch's text lies in the list, and `LotsAgree`
of it: the frame's to meet; four tests with code on public data; hh, a clause on the book; hv, on
the valid input's public instance. CAN THE FOUR TESTS BE MET AT THE WRITTEN PLAN? By an evaluation
not in this tree, at the switches' written places and the request's written shape: 46 addresses
are seated, just the switches' own messages; `serves`, `roomy` and `K2.placeFits` say yes at all 25
places. `K2.closingOk` IS NOT HELD HERE: an evaluation of ours at the first three written places did
not end within ten minutes; the switches' authors state it as a law under their head at every place
of the plan, at the plan's own list of segments: NOT CALLED HERE; THREE BOUNDS ON LEANING ON THAT
LAW: it stands at the ground of the head's opening, and this file has no tie of that ground to the G
of this form; this file does not import that law, so a build of this file does not check it; one
list segs must serve the mask's form and both fillings' at once. ON WHETHER hh AND hv CAN BE MET
NOTHING IS HELD HERE. The counts 46, 25 and 22 are read off written values: no theorem of this file
has them. This is a further text of the fillings' premise, beside `SwitchLotForFill`,
`PlanSwitchLotForFill` and `PlanSwitchLotForFillTests`, tied to the last one way. Through its
imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/
(lean/LIMITS.md, L15): a fact on import lines.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersTests
import Johnson.Desc.ProofFile.Honest.K5.Law.FillSwitchHead

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

/-- **`PlanSwitchLotForFillTests` without its clauses hn, hl, hmk, hIn.** A premise's form. -/
def PlanSwitchLotForFillLean
    (Zp : ProofFile.Pub)
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (Ad : MsgAddr)
    (l m' : ℕ)
    (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, ∀ m, Ad = p.ownAddr m → l = p.link → ∃ (D₀ : Pub → Ground →
      RowDataOf ProofFile.Inst) (fx ch : ℕ), (⟨P5J.At.num Zp l m', fx, K2.switchMsgTxt ch
            (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay segs) p (1 + p.sizes.kept.length + m)⟩ :
            MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧ LotsAgree ml ⟨P5J.At.num Zp l m', fx,
                  K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay segs) p (1 +
                  p.sizes.kept.length + m)⟩ ∧ K2.closingOk K2.freshTable (segs.take p.link) p = true ∧
      p.sizes.serves = true ∧ p.sizes.roomy = true ∧ K2.placeFits p = true ∧ (∀ k : Coins Bk,
      (K2.handed ch p k).isSome = true) ∧ ∀ w, Vd w → K2.publicOk (K2.withSwitchData S D₀ Zp G) lay
      p (segs.take p.link) w.x = true

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **The fuller form gives the leaner.** CONDITIONAL: under the hypothesis h, which the fuller
names. Where the elder cannot be met this holds from a falsehood. -/
theorem planSwitchLotForFillLean_of_elder
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {l m' : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    {segs : List K2.SegmentPub}
    (H : PlanSwitchLotForFillTests h ml Vd S G rd Ad l m' lay segs) :
    PlanSwitchLotForFillLean Zp ml Vd S G rd Ad l m' lay segs := by
  intro p hp m eA el
  obtain ⟨D₀, fx, ch, hm, ha, -, -, -, -, rest⟩ := H p hp m eA el
  exact ⟨D₀, fx, ch, hm, ha, rest⟩

/-- **The leaner form gives the clause of SF0 and SF1 on covering.** CONDITIONAL: under the
hypothesis h; hG; l is not the first segment; the typed seat's equation. -/
theorem covers_of_planSwitchLotForFillLean
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G)
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {l m' : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    {segs : List K2.SegmentPub}
    (hl0 : l ≠ 0)
    (hAd : typedSeat h G l Ad = some (l, m'))
    (N : ℕ)
    (H : PlanSwitchLotForFillLean Zp ml Vd S G rd Ad l m' lay segs) :
    ∃ Ls ∈ ml, LotsAgree ml Ls ∧ Covers Vd N Ls (fillLot (Bk := Bk) h S rd (typedSeat h G l) (fun _
      => 0) Ad l m') := by
  have es : typedSeat h G l = K2.switchSeat Zp G := if_neg hl0
  rw [es] at hAd ⊢
  obtain ⟨p, hp, m, eA, el⟩ := seated_at_switch hAd
  obtain ⟨D₀, fx, ch, hm, ha, hc, hs, hr, hf, hh, hv⟩ := H p hp m eA el
  subst eA
  exact ⟨_, hm, ha, covers_fill_switch_head h S hG D₀ rd (K2.lotClosingAt lay segs) hp hAd fx ch rfl
    (fun k w hd hw _ mask row place _ => switch_answers ch (K2.withSwitchData S D₀ Zp G) rd lay
      segs p hc hs hr hf hh hv _ k w _ hw mask row place)⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.planSwitchLotForFillLean_of_elder
#print axioms ProofFile.Honest.K5.covers_of_planSwitchLotForFillLean
