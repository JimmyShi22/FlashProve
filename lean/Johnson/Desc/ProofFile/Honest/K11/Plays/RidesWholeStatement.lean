-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/RidesWholeStatement.lean: THE FRAME's DEBT `RidesPastS` AT
NUMBER 346, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD: THE JOIN OF ITS SHARES, AT MOST
SEVENTEEN, OF WHICH THREE STAY PREMISES: STATEMENTS ALONE: two definitions of propositions. NOTHING
IS PROVED IN THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

  `AcrossAt346`      on the written lists alone: every item that is open at 346 and that the forward
                     row number 346 neither shuts nor owes is one of seventeen, written out
  `RidesPastSAtHead` `RidesPastS` at `SaidOk` at 346 FROM: the maker's base · the thread's keeps at
                     346 gives `K11KeepsYes` (the kind's clause, and that the merge's decision has
                     said yes) · THE SHARES AT THREE ITEMS: pile · worth 24 8 "planes" ·
                     worth 24 8 "keys"

WHO PAYS THE OTHER FOURTEEN. The five rows: `k11RowsRide` (RowRides.lean of this folder). The six
forms: `sixFormsRide_at_head` (SixRide.lean of this folder). The two pins and "unmarked": the
frame's authors' `k11_rides_pins` (Honest/Thread/K11PinRides.lean).

Limits. A JOIN. THREE SHARES ARE PREMISES: each belongs with the sub-protocol that opens the item;
none is the merge's. THE PREMISE ON keeps IS SHOWN AT NO FILLING OF THE LETTER Kp. The end is a
premise's form: THAT THE PAIR `ThrS` HOLDS AT ANY STAND IS NOT SAID. The head is a premise, at the
earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SixRideStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.RowRidesStatement
import Johnson.Desc.ProofFile.Honest.Thread.K11PinRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the items that are open across 346. Not proved here; a lemma's statement, none
of the library's goals. -/
def AcrossAt346 : Prop :=
  ∀ i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 346,
    i ∉ (FirstRows.rows P5J.At.links P5J.At.ps 346).shuts →
    i ∉ (FirstRows.rows P5J.At.links P5J.At.ps 346).owes →
    i ∈ [Item.unmarked, Item.pin 24 1, Item.pin 24 2, Item.row 24 .carried,
      Item.row 24 (.sample 0), Item.row 24 (.sample 1), Item.row 24 (.sample 2),
      Item.row 24 .position, Item.forms 24 3 "objects", Item.forms 24 3 "planes",
      Item.forms 24 4 "join", Item.forms 24 4 "own", Item.forms 24 6 "small",
      Item.forms 24 8 "objects", Item.pile, Item.worth 24 8 "planes", Item.worth 24 8 "keys"]

/-- The statement at the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def RidesPastSAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11KeepsYes (_root_.K11.parOf Zp Bs.G₀) s s') →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      Item.pile →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (Item.worth 24 8 "planes") →
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
      (Item.worth 24 8 "keys") →
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346

end ProofFile.Honest.K11
