-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/RideOk.lean: the table for `head_hR_of_ok` (RidesOk.lean):
which kinds of item may pass over a sub-protocol of the first chain, by the kind of the
sub-protocol's place. The column `hR` of `owesS_head` (GatherHead.lean) asks `RidesPastAtS` at
20,176 pairs of a sub-protocol and an item. With this table it is enough to prove it at the
combinations of a kind of item and a kind of place that the table admits.

  1  `rideOk`   the table: a definition
  2  `rideOk_onePass`   along the full size's written lists of places and open items, every open
     item is closed by the forward row, or is in its `owes`, or is admitted by the table. The
     statement has no free variable. It is decided by the kernel's evaluation (`decide +kernel`) at
     the full size's written places, so it is counted apart from the other lemmas
  3  `rideOk_control`   the test can fail: it fails at the table without the item `pile`
  4  `head_hR_of_cells`   the column `hR` from the admitted combinations

What the test can show. A table that admitted too little would make `rideOk_onePass` fail. A table
that admits too much only adds combinations to prove.

Limits.
  * Lists of items only: the file says nothing about what an item means.
  * The table goes by the kind of the place. It does not tell the three sorts of sub-protocol of K9,
    or the five of the kind `frame`, from each other.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- **Which kinds of item may pass over a sub-protocol at a place**, by the place's kind. It is a
definition: a table for a test on the written lists. -/
def rideOk (p : Place) : Item → Bool
  | .unmarked | .pinW | .pile | .pinI => true
  | .constr _ .lookDigits => p.kind == .K1
  | .constr _ .lookCallsHeard => p.kind == .K2
  | .constr _ _ => true
  | .pin _ _ => [KindName.K1, .K9, .K11].contains p.kind
  | .row _ _ => [KindName.K1, .K3, .K4, .K5, .K6, .K8, .K9, .K11, .frame].contains p.kind
  | .formsT _ _ _ => [KindName.K4, .K5, .K6].contains p.kind
  | .forms _ _ _ => [KindName.K1, .K3, .K8, .K11].contains p.kind
  | .wo _ => [KindName.K1, .K3, .K8, .K9, .K10, .frame].contains p.kind
  | .carry _ | .pinKept _ => [KindName.K7, .K9, .frame].contains p.kind
  | .worth _ _ _ => p.kind == .K11
  | .pileOne | .pinV | .wrow => p.kind == .frame
  | .tie _ | .totalB _ | .total _ => false

set_option maxRecDepth 1000000 in
/-- Along the written lists every open item is closed, or owed again, or admitted by the table. -/
theorem rideOk_onePass :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all
      fun x => x.1.all fun i => (FirstRows.rowAt P5J.At.links x.2).shuts.contains i ||
        (FirstRows.rowAt P5J.At.links x.2).owes.contains i || rideOk x.2 i) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the item `pile` struck from the table the same test fails. -/
theorem rideOk_control :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all
      fun x => x.1.all fun i => (FirstRows.rowAt P5J.At.links x.2).shuts.contains i ||
        (FirstRows.rowAt P5J.At.links x.2).owes.contains i ||
        (rideOk x.2 i && !(i == Item.pile))) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The column `hR` from the combinations that the table admits.** -/
theorem head_hR_of_cells (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → rideOk p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i :=
  head_hR_of_ok h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said rideOk rideOk_onePass hok

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rideOk_onePass
#print axioms ProofFile.Honest.FirstThread.rideOk_control
#print axioms ProofFile.Honest.FirstThread.head_hR_of_cells
