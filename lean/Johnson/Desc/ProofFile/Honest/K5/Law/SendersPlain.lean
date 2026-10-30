-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersPlain.lean: conditional: the attention sub-protocol's forms on
the senders' lots without their public tests, at the plan's own segments. Two definitions, two theorems.

  PlanSwitchLotForFillPlain, PlanSwitchLotForMaskPlain   PlanSwitchLotForFillLean and
        PlanSwitchLotForMask without their four tests on public data. Premises' forms
  planSwitchLotForFillLean_of_plain, planSwitchLotForMask_of_plain   each plain form gives its source form at
        the plan's own segments: the tests are paid under the head (PublicUnderHead.lean in this folder)

The premises: h, the library's head; hG, G is the ground of the public part; H, the plain form.

The pin reaches the lot's text: the list must hold the lot whose closing is at K2.segmentsOf Zp G. lay
stays a letter. Nothing that is not on public data falls by this step. On
whether the clauses on K2.handed and K2.publicOk can be met nothing is held here. All limits of PublicUnderHead.lean hold here.

Limits.
  * Conditional. This file proves none of its premises of any list, reader, book, instance or filling.
  * The reader rd is a letter. The index type W₀ is a letter.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, the first chain alone, at the
    earlier hash OnBytes.secondHashFunction, a fixed function.
  * Through its imports it stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersAtFill
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicUnderHead

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
variable {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`PlanSwitchLotForFillLean` without its four tests on public data, at the plan's own
segments.** A premise's form. -/
def PlanSwitchLotForFillPlain
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
      lay (K2.segmentsOf Zp G)) p (1 + p.sizes.kept.length + m)⟩ ∧ (∀ k : Coins Bk, (K2.handed ch p
      k).isSome = true) ∧ ∀ w, Vd w → K2.publicOk (K2.withSwitchData S D₀ Zp G) lay p
      ((K2.segmentsOf Zp G).take p.link) w.x = true

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`PlanSwitchLotForMask` without its four tests on public data, at the plan's own segments.** A
premise's form. -/
def PlanSwitchLotForMaskPlain
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (G : Ground)
    (g : ℕ)
    (x₁ : VerifiableInference.Desc.First.Look.Place)
    (kM : ℕ)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length)
    (lay : OnBytes.Params.ReqLayout) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, p.link = 2 * g + 1 → ∃ (D₁ : RowDataOf ProofFile.Inst) (rd' :
            Local W₀ Rc ProofFile.Inst Tr → Readers) (fx : ℕ), (⟨maskNo5 h x₁ kM hk, fx, K2.switchMsgTxt 0 D₁
                  rd' (K2.lotClosingAt lay (K2.segmentsOf Zp G)) p 3⟩ : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈
      ml ∧ LotsAgree ml ⟨maskNo5 h x₁ kM hk, fx, K2.switchMsgTxt 0 D₁ rd' (K2.lotClosingAt lay
      (K2.segmentsOf Zp G)) p 3⟩ ∧ oneStretch (rowEntries Bk ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072) ∧ (∀ k : Coins Bk, (K2.handed 0 p
      k).isSome = true) ∧ ∀ w, Vd w → K2.publicOk D₁ lay p ((K2.segmentsOf Zp G).take p.link) w.x =
      true

/-- **The plain form gives the source form at the plan's own segments.** CONDITIONAL: h; hG. -/
theorem planSwitchLotForMask_of_plain
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {G : Ground}
    {g : ℕ}
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    {lay : OnBytes.Params.ReqLayout}
    (hG : blankBy pureRoad.links Zp = some G)
    (H : PlanSwitchLotForMaskPlain h ml Vd G g x₁ kM hk lay) :
    PlanSwitchLotForMask h ml Vd G g x₁ kM hk lay (K2.segmentsOf Zp G) := by
  intro p hp hl
  obtain ⟨D₁, rd', fx, hm, ha, hT, rest⟩ := H p hp hl
  exact ⟨D₁, rd', fx, hm, ha, hT, closing_under_head h hG p hp, serves_under_head h hG p hp,
    roomy_under_head h hG p hp, fits_under_head h hG p hp, rest⟩

include h in
/-- **The plain form gives the source form at the plan's own segments.** CONDITIONAL: h; hG. -/
theorem planSwitchLotForFillLean_of_plain
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {l m' : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    (hG : blankBy pureRoad.links Zp = some G)
    (H : PlanSwitchLotForFillPlain Zp ml Vd S G rd Ad l m' lay) :
    PlanSwitchLotForFillLean Zp ml Vd S G rd Ad l m' lay (K2.segmentsOf Zp G) := by
  intro p hp m eA el
  obtain ⟨D₀, fx, ch, hm, ha, rest⟩ := H p hp m eA el
  exact ⟨D₀, fx, ch, hm, ha, closing_under_head h hG p hp, serves_under_head h hG p hp,
    roomy_under_head h hG p hp, fits_under_head h hG p hp, rest⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {S : OnBytes.HonestTrace.Sz} {X₀ X : Type}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat)

section
variable {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}
  (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

section
variable {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.PlanSwitchLotForFillPlain
#print axioms ProofFile.Honest.K5.PlanSwitchLotForMaskPlain
#print axioms ProofFile.Honest.K5.planSwitchLotForMask_of_plain
#print axioms ProofFile.Honest.K5.planSwitchLotForFillLean_of_plain
