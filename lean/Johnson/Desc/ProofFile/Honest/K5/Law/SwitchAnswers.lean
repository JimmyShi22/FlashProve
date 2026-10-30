-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SwitchAnswers.lean: CONDITIONAL: AN EXCHANGE, NOT A PAYMENT:
THE PREMISE hS OF THE LAWS ON A CODE SWITCH's LOT THAT COVERS OURS ("the switch's text answers
wherever ours does": MaskSwitchBook.lean, FillSwitch.lean), AT THE CLOSING `K2.lotClosingAt` ALONE,
FROM SIX: FOUR Bools ON PUBLIC DATA AT THE PLACE, ONE FACT ON THE BOOK, ONE CLAUSE ON THE VALID
INPUT's PUBLIC INSTANCE.

Why. hS is asked at every run, every valid input, every list of challenges and every entry at which
our text answers. The authors of the code switch's honest side have said by name what the answering
of `K2.switchMsgTxt` hangs on (`msgTxt_isSome`,
Johnson/Desc/ProofFile/Honest/K2/Law/LotsAnswer.lean). By their law it answers at every entry or at
none: so hS's own premise, that our text answers, is not spent.

Main names:
  `switch_answers`: under the six, `K2.switchMsgTxt ch D rd (K2.lotClosingAt lay segs) p n` answers
    at every message number n, every run, every valid input, every list of challenges, every entry.
  `hS_mask_of_six`, `hS_fill_of_six`: the same in hS's two forms, to the sign.

The six:
  hc: `K2.closingOk K2.freshTable (segs.take p.link) p = true`; hs: `p.sizes.serves = true`;
    hr: `p.sizes.roomy = true`; hf: `K2.placeFits p = true`: Bools on public data at the place p.
  hh: `∀ k, (K2.handed ch p k).isSome = true`: the frame hands the switch's part its stretches: on
    the book: by `handed_public` (LotsAnswer.lean) it is the same at all runs.
  hv: `∀ w, Vd w → K2.publicOk D lay p (segs.take p.link) w.x = true`: it takes the input's public
    instance alone.

Which way it goes. The six give hS; nothing here goes back. What goes: "at every input's trace and
index, every list of challenges and every entry"; a run's letter stays in hh alone, where nothing
hangs on it. What comes: six premises, none of which is proved here.

Limits. ON WHETHER A TEXT ANSWERS: NOTHING ON WHAT IT ANSWERS. AT `K2.lotClosingAt lay segs` ALONE:
at another closing nothing is said; lay, segs and p are letters. That the six hold is proved here at
no place, book or input. Payers that are named, not called: under the library's head the same
authors have hc at each of the plan's 25 places of the kind (`closing_at_head`,
Honest/K2/Law/ClosingAtHead.lean: by 25 closed facts of Lean's kernel; by its pack's name half an
hour and 44 GiB a ride), and hs, hr, hf (`serves_at_head`, `roomy_at_head`, `fits_at_head`,
Honest/K2/Law/PublicAtHead.lean): these files do not lie beneath this one. All limits of
LotsAnswer.lean hold. No lot is laid.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitchBook
import Johnson.Desc.ProofFile.Honest.K5.Law.FillSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

section
variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **UNDER THE SIX THE SWITCH's TEXT ANSWERS EVERYWHERE.** Conditional: the six of the file's head.
-/
theorem switch_answers (ch : ℕ) (D : RowDataOf Xi) (rd : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (hc : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : K2.placeFits p = true)
    (hh : ∀ k : Coins Bk, (K2.handed ch p k).isSome = true)
    {Vd : Local W₀ Rc Xi Tr → Prop}
    (hv : ∀ w, Vd w → K2.publicOk D lay p (segs.take p.link) w.x = true) :
    ∀ (n : ℕ) (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → ∀ mask row place,
      (K2.switchMsgTxt ch D rd (K2.lotClosingAt lay segs) p n k w hd mask row place).isSome =
        true := by
  intro n k w hd hw mask row place
  rw [K2.Law.msgTxt_isSome ch D rd lay segs p hc, hh k, hs, hr, hv w hw, hf]
  rfl

end

section
variable {W₀ Rc Tr : Type} {Bk : ProverCoinCounts}

/-- **hS AT THE MASK** (`covers_mask_switch_at_book`, MaskSwitchBook.lean), to the sign, at the
closing `K2.lotClosingAt lay segs`. Conditional: the six. -/
theorem hS_mask_of_six (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (hc : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : K2.placeFits p = true)
    (hh : ∀ k : Coins Bk, (K2.handed 0 p k).isSome = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    (hv : ∀ w, Vd w → K2.publicOk D₁ lay p (segs.take p.link) w.x = true)
    (Z5 : Seat5) (ν₅ n fx N : ℕ) :
    ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      maskAnswers Z5 ν₅ mask row place = true →
      (K2.switchMsgTxt 0 D₁ rd (K2.lotClosingAt lay segs) p n k w (hd.take fx) mask row
        place).isSome = true :=
  fun k w hd hw _ mask row place _ =>
    switch_answers 0 D₁ rd lay segs p hc hs hr hf hh hv n k w (hd.take fx) hw mask row place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **hS AT THE FILLING** (`covers_fill_switch_at`, FillSwitch.lean), to the sign, at the closing
`K2.lotClosingAt lay segs`. Conditional: the six, at the data `K2.withSwitchData S D₀ Zp G`. The
head h stands in the statement for the letters of our text alone. -/
theorem hS_fill_of_six (S : Sz) (G : Ground) (D₀ : Pub → Ground → RowDataOf ProofFile.Inst)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub) (p : K2.SwitchPlace) (ch : ℕ)
    (hc : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : K2.placeFits p = true)
    (hh : ∀ k : Coins Bk, (K2.handed ch p k).isSome = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    (hv : ∀ w, Vd w →
      K2.publicOk (K2.withSwitchData S D₀ Zp G) lay p (segs.take p.link) w.x = true)
    (m l m' fx N : ℕ) :
    ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      fillAnswers S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp G)
        (fun _ => 0) (p.ownAddr m) l m' 0 mask row place = true →
      (K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay segs) p
        (1 + p.sizes.kept.length + m) k w (hd.take fx) mask row place).isSome = true :=
  fun k w hd hw _ mask row place _ =>
    switch_answers ch (K2.withSwitchData S D₀ Zp G) rd lay segs p hc hs hr hf hh hv
      (1 + p.sizes.kept.length + m) k w (hd.take fx) hw mask row place

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.switch_answers
#print axioms ProofFile.Honest.K5.hS_mask_of_six
#print axioms ProofFile.Honest.K5.hS_fill_of_six
