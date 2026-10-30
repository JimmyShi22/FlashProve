-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskLotInList.lean: CONDITIONAL, under the library's hypothesis
h on the public input (`P5J.AtMgA`): THE CODE SWITCH's OWN LIST OF ITS LOTS OF MESSAGES
(`K2.switchMsgLots`) HOLDS A LOT FOR MESSAGE 3, at the plan's switch into each attention segment 2 g
+ 1. Numbers of a public plan and a membership in a list: no run, no input, no book. No definition;
three theorems.

Main names:
  `first_sender_three_written`: A CLOSED FACT; Lean's kernel evaluates it: at each member of the
    code switches' closed list of written places (`K2.Law.placesW`) whose link is odd and below 24
    the switch is message 3's first sender (`K2.firstSender`).
  `first_sender_three_head`: under h, with hG (G is the maker's own ground), at a switch p of the
    plan with p.link = 2 g + 1, g < 12: the same.
  `mask_lot_in_switch_lots`: there, at every ch, D₁, rd, closing, num, fx: the lot ⟨num 3, fx, the
    text of message 3⟩ is a member of `K2.switchMsgLots ch D₁ rd closing p num fx`.

What it is for. `K2.switchMsgLots` has a lot for message n only where n is below the sending's size
and `K2.firstSender p n` says yes. `covers_mask_switch_tied` (MaskTie.lean in this folder) speaks of
the lot ⟨`K2.switchNum Zp p 3`, fx, the text of message 3⟩: at num := `K2.switchNum Zp p` that lot
is a member of the list.

How. The first: an evaluation. The second: `places_under_head` (MaskRowWritten.lean in this folder),
then the first. The third: 3 is below the size, which is 5 (`switch_numbers_head`, in that file);
the second; the list's own text.

Limits. CONDITIONAL. THAT A LIST OF THE FRAME's IS `K2.switchMsgLots` AT THIS p AND AT num :=
`K2.switchNum Zp p` IS NOT SAID HERE. Of other messages than 3, and of switches into other segments,
nothing is said here. That the plan has such a switch at each g below 12 is `switch_there_head`
(MaskRowWritten.lean in this folder): not called here. The closed fact is an evaluation by Lean's
kernel of terms of the code switch's authors' making: it says what these terms come to, not that
they are the right ones. Through it the file stands above Cb/Bridge/CodeListRSProved.lean, and so
above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskRowWritten
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.FirstThread (MsgLot)
open P5J (AtMgA TS)

/-- **AT THE WRITTEN SWITCHES INTO THE ODD SEGMENTS BELOW 24 THE SWITCH IS MESSAGE 3's FIRST
SENDER.** A closed fact. -/
theorem first_sender_three_written : ∀ p ∈ K2.Law.placesW, p.link % 2 = 1 → p.link < 24 →
    K2.firstSender p 3 = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, at a switch of the plan that leads into segment 2 g + 1: the same.**
CONDITIONAL: h; hG; hp; hg; hl: as `switch_numbers_head`. -/
theorem first_sender_three_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Zp G) {g : ℕ} (hg : g < 12) (hl : p.link = 2 * g + 1) :
    K2.firstSender p 3 = true := by
  rw [places_under_head h hG] at hp
  exact first_sender_three_written p hp (by omega) (by omega)

/-- **THE SWITCH's OWN LIST OF LOTS HOLDS THE LOT OF MESSAGE 3.** CONDITIONAL: h; hG; hp; hg; hl: as
`switch_numbers_head`. ch, D₁, rd, closing, num, fx are letters. -/
theorem mask_lot_in_switch_lots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Zp G) {g : ℕ} (hg : g < 12) (hl : p.link = 2 * g + 1)
    {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (ch : ℕ) (D₁ : RowDataOf Xi)
    (rd : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (num : ℕ → ℕ) (fx : ℕ) :
    (⟨num 3, fx, K2.switchMsgTxt ch D₁ rd closing p 3⟩ : MsgLot Bk (Local W₀ Rc Xi Tr)) ∈
      K2.switchMsgLots ch D₁ rd closing p num fx := by
  have h5 := (switch_numbers_head h hG hp hg hl).2.1
  unfold K2.switchMsgLots
  exact List.mem_map.2 ⟨3, List.mem_filter.2 ⟨List.mem_range.2 (by rw [h5]; decide),
    first_sender_three_head h hG hp hg hl⟩, rfl⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.first_sender_three_written
#print axioms ProofFile.Honest.K5.first_sender_three_head
#print axioms ProofFile.Honest.K5.mask_lot_in_switch_lots
