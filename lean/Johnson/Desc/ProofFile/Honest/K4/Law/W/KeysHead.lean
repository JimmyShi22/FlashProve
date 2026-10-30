-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/KeysHead.lean: CONDITIONAL.

What is here. THE LOOKUP's OWN SENTENCE ON THE KEYS (`K3Keys`, Johnson/Top/H/K3RowOut.lean: the join
of the lookup's claims with each call's key vector at its point is 0) COMES OUT OF THE THREAD, at
the thread with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean), in front of
the member of the feed-forward layers' own rounds (sub-protocol K4): the item `Item.worth m 2
"keys"` is one of the eight that the member's row asks (`asks_k4`, Law/W/OpenAtHead.lean), so it is
open in front of the member and the thread holds its sentence; by the library's
`mgAll_worth_lay_keys` (Johnson/Desc/Sound/MgAllAt.lean) that sentence is `K3Keys` at all rounds
whose end values are what the lookup has heard, at the reading `layNu` and the key vectors of the
lookup's caller (`layWorthKeys`, Johnson/Desc/First/Look/K3LayTies.lean). Each proof is a chain of
calls.

  `keys_item_head`   the item's sentence out of the thread, at every continuation of the challenges
     heard.
  `keys_lay_head`   **the same in the lookup's own terms.**
  After `rider_item_head` and `rider_lay_head` (Law/W/OpenAtHead.lean) and `planes_item_head` and
  `planes_lay_head` (Law/W/NuHead.lean).

Limits. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on the
public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN: hT :
Thr is a hypothesis. THAT THE ITEM's SENTENCE IS EVER MADE TRUE: it is owed behind the member of the
lookup on the calls, whose row opens the item; no file here shows it there. WHERE THE STATE HOLDS NO
LEDGER OR NOTHING HEARD, AND AT A HEARD STRUCTURE THAT STANDS FOR NO ROUNDS, THE SENTENCE IS TRUE OF
EVERY WITNESS (the head of Johnson/Top/H/K3Worth.lean). THE KEY VECTORS ARE THE CALLER's, in the
caller's letters: that they are the library's key vectors at the honest input's cells and weights is
not shown here. A, hpc, hna, hx, ht: on public lists and numbers. On h: the side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with hT,
A, hpc, hna, hx and ht no example is known to us. THE FULL SIZE ALONE, and the format's second hash function
alone (`OnBytes.secondHashFunction`). The one import is Law/W/OpenAtHead.lean: the import closure is that
file's, and its head says what a walk from import to import reaches. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OpenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (AtK4)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (pubAt stepOf attAt layAt tlAt)
open VerifiableInference.Desc.Sound (MsgT linksFull mgAll mgBase mgAll_worth_lay_keys)
open VerifiableInference.OnPublicFiles (layWorthKeys)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SENTENCE OF `Item.worth m 2 "keys"` OUT OF THE THREAD**, at every continuation of the
challenges heard. CONDITIONAL: on h, A and hT. -/
theorem keys_item_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means mm.st.input
      (Item.worth m 2 "keys") (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) :=
  item_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT
    (open_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) onePass_full
      (i := Item.worth m 2 "keys")
      (by
        rw [asks_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) A]
        exact .tail _ (.tail _ (.head _)))) ds'

/-- **THE SAME IN THE LOOKUP's OWN TERMS.** x: the lookup's place at the segment. tl: the
sub-proof's plan there. CONDITIONAL: on h, A, hT, hpc, hna, hx and ht. -/
theorem keys_lay_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) (hpc : VerifiableInference.Desc.K3.pieceAt (P5J.At.X Zp) m false = 2)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt (P5J.At.X Zp) m = none) (hx : layAt (P5J.At.X Zp) m = some x)
    (ht : tlAt (P5J.At.X Zp) m = some tl) :
    layWorthKeys x (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) tl h.𝔇.sent h.𝔇.l3.rad
      h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat x.link false j.1)
      h.𝔇.l3.arr h.𝔇.l3.msgW (fun t : TS => t.fork?) (fun t : TS => t.lookHeard?) s
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) := by
  have q := keys_item_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT ds'
  have q' : (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
      mgBase).worth m 2 "keys" (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) := q
  rw [← hpc, mgAll_worth_lay_keys _ _ m hna hx ht] at q'
  exact q'

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.keys_item_head
#print axioms ProofFile.Honest.K4.W.keys_lay_head
