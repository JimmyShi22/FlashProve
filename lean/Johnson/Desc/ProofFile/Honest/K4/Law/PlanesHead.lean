-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PlanesHead.lean: CONDITIONAL.

What is here. Two of the eight items that the thread owes behind the member of the layers' own
rounds (kind K4; Law/TableAt.lean lists them), `Item.formsT m 2 "planes"` and `Item.formsT m 2
"join"`: the threads' debt ExchangeAtS at each, at the first chain's thread at the library's own
parameters (`lettersHead`), FROM h AND THE MEMBER's LAYING ALONE. Statements with their proofs:
`k4_exchangeAt_planes` and `k4_exchangeAt_join` (Law/SharesIs.lean: each is proved from a field of
the hypothesis K4Table) called at `k4Table_head` (Law/W/ExchangeParts.lean), at the link that
`nine_head` (Law/ElevenHead.lean) names, then the threads' `exchangeAtS_of`.

  `k4_exchange_planes_head`: ExchangeAtS T Said k (Item.formsT m 2 "planes").
  `k4_exchange_join_head`: ExchangeAtS T Said k (Item.formsT m 2 "join").

Limits. CONDITIONAL: on h and on LaidK4 (h and the member's place give it). At these two items the
table's sentence holds of every state and witness by the table's own text: so the two statements say
little: that nothing is owed there. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h
holds of any files is not shown here: the side library AtFullSide proves, with no hypothesis, that h
has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). LaidK4 is the statements' only other hypothesis: it asks
nothing beyond h and g < 12 (`laid_at`, Law/LaidAtGroup.lean). IT IS A LAW, NOT A PART: it rests on
modules under Johnson/Goal/, as Law/W/ExchangeParts.lean does: no file that defines a part may build
on it. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SharesIs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ExchangeParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Link)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.W (k4Table_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`ExchangeAtS` AT THE ITEM "planes", AT THE THREAD.** CONDITIONAL: on h and Lh. -/
theorem k4_exchange_planes_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.formsT m 2 "planes") := by
  obtain ⟨l, _, _, hl, _⟩ := (nine_head h Lh).runs
  exact exchangeAtS_of _ Said
    (k4_exchangeAt_planes (k4Table_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hl))

/-- **`ExchangeAtS` AT THE ITEM "join", AT THE THREAD.** CONDITIONAL: on h and Lh. -/
theorem k4_exchange_join_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.formsT m 2 "join") := by
  obtain ⟨l, _, _, hl, _⟩ := (nine_head h Lh).runs
  exact exchangeAtS_of _ Said
    (k4_exchangeAt_join (k4Table_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hl))

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_planes_head
#print axioms ProofFile.Honest.K4.k4_exchange_join_head
