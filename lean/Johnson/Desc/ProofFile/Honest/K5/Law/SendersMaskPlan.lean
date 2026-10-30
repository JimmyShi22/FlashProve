-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersMaskPlan.lean: conditional: the attention sub-protocol's mask
row, at the code switch that leads into its segment. One definition, one theorem.

  PlanSwitchLotForMask             at every switch of the plan that leads into segment 2 g + 1: a lot with
                                   the text of its message 3, in the list, for K5's triple on the mask
                                   row. A premise's form
  covers_of_planSwitchLotForMask   that form gives the covering of the mask's lot

The premises of the theorem: h, the library's head; hG, hg, ea, public; hx, hZ, the seat is the group's;
hR, the frame's test on the lending at K5's row; H, the form itself.

Of the form: «3» is written into it, and it lays K5's number of its mask message on a lot with the text of
the switch's message 3: on whether the two belong together nothing is said. The written numbers (3, 13,
2251, 1072, two places) make it a form for the head's plan alone. The clause on the book is run at no book.
Where no member leads into 2 g + 1 it holds emptily. The reader rd', the data and fx stand under "there
is": nothing ties the mask's lot to the prover's reader.

Limits.
  * Conditional. This file proves none of its premises of any list, reader, book, instance or filling.
  * The index type W₀ is a letter.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, the first chain alone, at the
    earlier hash OnBytes.secondHashFunction, a fixed function.
  * Through its imports it stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersLean
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitchHead

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

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **At every switch of the plan that leads into segment 2 g + 1: a lot with the text of its
message 3, in the list, for K5's triple on the mask row.** A premise's form. Written numbers stand
in it. -/
def PlanSwitchLotForMask
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (G : Ground)
    (g : ℕ)
    (x₁ : VerifiableInference.Desc.First.Look.Place)
    (kM : ℕ)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length)
    (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, p.link = 2 * g + 1 → ∃ (D₁ : RowDataOf ProofFile.Inst) (rd' :
            Local W₀ Rc ProofFile.Inst Tr → Readers) (fx : ℕ), (⟨maskNo5 h x₁ kM hk, fx, K2.switchMsgTxt 0 D₁
                  rd' (K2.lotClosingAt lay segs) p 3⟩ : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml ∧ LotsAgree ml
      ⟨maskNo5 h x₁ kM hk, fx, K2.switchMsgTxt 0 D₁ rd' (K2.lotClosingAt lay segs) p 3⟩ ∧ oneStretch
      (rowEntries Bk ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) = some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩,
      2251, 1072) ∧ K2.closingOk K2.freshTable (segs.take p.link) p = true ∧ p.sizes.serves = true ∧
      p.sizes.roomy = true ∧ K2.placeFits p = true ∧ (∀ k : Coins Bk, (K2.handed 0 p k).isSome =
      true) ∧ ∀ w, Vd w → K2.publicOk D₁ lay p (segs.take p.link) w.x = true

/-- **That form gives the clause of SM on covering.** CONDITIONAL: under the hypothesis h; hG, hg,
ea: public; hx, hZ: the seat is the group's; hR: the frame's test on the lending at K5's row. -/
theorem covers_of_planSwitchLotForMask
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G)
    {g : ℕ}
    (hg : g < 12)
    {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    {Z5 : Seat5}
    (hx : Z5.P.x = a.own)
    (hZ : Z5.link = 2 * g + 1)
    {lay : OnBytes.Params.ReqLayout}
    {segs : List K2.SegmentPub}
    (cells : Tr → Cells)
    (hR : lendsRow Bk 0 Z5.place (k5Row Z5) = true)
    (N : ℕ)
    (H : PlanSwitchLotForMask h ml Vd G g x₁ kM hk lay segs) :
    ∃ Ls ∈ ml, LotsAgree ml Ls ∧ Covers Vd N Ls (maskLot (Bk := Bk) h x₁ kM hk Z5
      (OnBytes.Model.Forest.elems a.fs)) := by
  obtain ⟨p, hp, hl⟩ := switch_there_head h hG hg
  obtain ⟨D₁, rd', fx, hm, ha, hT, hc, hs, hr, hf, hh, hv⟩ := H p hp hl
  exact ⟨_, hm, ha, covers_mask_switch_head h hG hg ea hx hZ D₁ rd' (K2.lotClosingAt lay segs) hp hl
    fx rfl hT cells hR (hS_mask_of_six D₁ rd' lay segs p hc hs hr hf hh hv Z5 _ 3 fx N)⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {G : Ground} {B : ProverCoinCounts}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.covers_of_planSwitchLotForMask
