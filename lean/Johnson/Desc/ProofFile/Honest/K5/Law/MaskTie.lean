-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskTie.lean: CONDITIONAL, under the library's hypothesis h on
the public input (`P5J.AtMgA`): THE TIE: THE NUMBER OF MESSAGE 3 OF THE PLAN's CODE SWITCH INTO
ATTENTION SEGMENT 2 g + 1 (`K2.switchNum Zp p 3`) IS K5's OWN NUMBER OF THE MESSAGE THAT HOLDS THAT
SEGMENT's MASK ROW (`maskNo5`). Numbers of a public plan: no run, no input, no book. And so
`covers_mask_switch_head` (MaskSwitchHead.lean in this folder) stands WITHOUT ITS PREMISE hnum, at
the switch's own number. No definition; two theorems: calls alone.

Main names:
  `mask_tie_head`: h; hG; hp: p is one of the plan's switches; hg: g < 12; hl: p leads into 2 g + 1;
    hx₁: the lookup's place has that link; hm: `maskMsg` names kM: the two numbers are one.
  `covers_mask_switch_tied`: `covers_mask_switch_head` with the letter num and hnum struck; hx₁ and
    hm come; the lot bears `K2.switchNum Zp p 3`.

How. Both numbers are the plan's number of (segment 2 g + 1, own message 0), `P5J.At.num Zp (2 * g +
1) 0`. THE SWITCH's HALF IS THE CODE SWITCH's AUTHORS': `K2.Law.num3_at_head`
(Honest/K2/Law/Own0AtOddLinks.lean): under the head and an opening; here the opening is taken out of
h's own field `laid.opened`, and its ground is G (`places_under_head`'s two lines,
MaskRowWritten.lean in this folder). K5's HALF IS OURS: `maskNo5_at_head` (MaskNoZero.lean in this
folder).

What it is for. In MaskSwitchHead.lean K5's number was laid on the lot of the switch's message 3 by
fiat (hnum, at a free letter num). Here it is the switch's own number of that message. So «3» is no
free choice: it is the n whose number is K5's. hx₁ and hm stand where the joined laws stand: the
place is a return of `lookAt … (2 * g + 1) false`, whose link
`VerifiableInference.OnPublicFiles.lookAt_link` (Johnson/Desc/First/Look/K3CallsAddress.lean) gives; hm is
how kM enters.

Limits. CONDITIONAL. THAT THE LOT WHICH THE FRAME's LIST BEARS FOR THE SWITCH's MESSAGE 3 HAS THE
NUMBER `K2.switchNum Zp p 3` IS NOT SAID HERE: in `K2.switchMsgLots` the numbers are a letter, and
that list has a lot for message n only where `K2.firstSender p n` says yes: that 3 passes that test
is `first_sender_three_head` (MaskLotInList.lean in this folder): not called here.
`covers_mask_switch_tied` AGAINST `covers_mask_switch_head`: hnum goes; hx₁ and hm come; num is
pinned: narrower. Its other premises stay, with what is told of each there: hT and hR are tests with
code on the book; hS: THAT the switch's text answers. Both halves rest on closed facts that Lean's
kernel evaluates, in their own files and in files beneath them, the code switch's authors' and ours:
they say what written terms come to. Through MaskSwitchHead.lean it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Own0AtOddLinks
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskNoZero
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitchHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE TIE: THE SWITCH's NUMBER OF ITS MESSAGE 3 IS K5's NUMBER OF ITS MASK MESSAGE.**
CONDITIONAL: under the hypothesis h; hG; hp; hg; hl: the switch leads into 2 g + 1; hx₁: the place's
link; hm: `maskMsg` names member kM. -/
theorem mask_tie_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Zp G) {g : ℕ} (hg : g < 12) (hl : p.link = 2 * g + 1)
    {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hx₁ : x₁.link = 2 * g + 1) (hm : maskMsg h.𝔇.sent x₁.link = some kM) :
    K2.switchNum Zp p 3 = maskNo5 h x₁ kM hk := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e] at hp
  exact (K2.Law.num3_at_head h.toAtMg O p hp g hg hl).trans (maskNo5_at_head h hg hx₁ hm).symm

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`covers_mask_switch_head` AT THE SWITCH's OWN NUMBER, WITHOUT hnum.** CONDITIONAL: under the
hypothesis h; hx₁; hm; the rest as there. -/
theorem covers_mask_switch_tied {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) (hx : Z5.P.x = a.own) (hZ : Z5.link = 2 * g + 1)
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) (hl : p.link = 2 * g + 1)
    (hx₁ : x₁.link = 2 * g + 1) (hm : maskMsg h.𝔇.sent x₁.link = some kM) (fx : ℕ)
    (hT : oneStretch (rowEntries Bk ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072))
    (cells : Tr → Cells) (hR : lendsRow Bk 0 Z5.place (k5Row Z5) = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      maskAnswers Z5 (OnBytes.Model.Forest.elems a.fs) mask row place = true →
      (K2.switchMsgTxt 0 D₁ rd closing p 3 k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨K2.switchNum Zp p 3, fx, K2.switchMsgTxt 0 D₁ rd closing p 3⟩
      (maskLot (Bk := Bk) h x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs)) :=
  covers_mask_switch_head h hG hg ea hx hZ D₁ rd closing hp hl fx
    (mask_tie_head h hG hp hg hl hx₁ hm) hT cells hR hS

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mask_tie_head
#print axioms ProofFile.Honest.K5.covers_mask_switch_tied
