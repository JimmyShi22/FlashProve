-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/RideOkFrame.lean: a finer table for the column `hR` of
`owesS_head` (Thread/GatherHead.lean), which asks `RidesPastAtS` (Thread/SharesS.lean) at every pair
of a sub-protocol of the first chain and an item that is open there. The table `rideOk`
(Thread/RideOk.lean) goes by the kind of the sub-protocol's place alone. The kind `frame` has five
sorts of place, and `rideOk` admits every kind of item that passes over one of them at all five.
This file's table tells the five apart, so fewer combinations are left to prove.

  1  `frameOk`, `rideOkF`   the tables: two definitions
  2  `rideOkF_onePass`   along the full size's written lists of places and open items, every open
     item is closed by the forward row, or is in its `owes`, or is admitted by `rideOkF`. The
     statement has no free variable. It is decided by the kernel's evaluation (`decide +kernel`),
     so it is counted apart from the other lemmas
  3  `rideOkF_control`   the test can fail: it fails when the item `pinKept` is struck at the places
     "laid"
  4  `rideOkF_frame`, `rideOkF_else`   the table at a place of the kind `frame`, and at any other
  5  `head_hR_of_cellsF`   the column `hR` from the admitted combinations. Each combination is given
     the place, that the item is open there, and that the row neither closes it nor has it in `owes`

The five sorts of place, in the order of the arms of `keepsFrame` (KeepsFrame.lean): no segment and
piece 0 (number 0); no segment and another piece (number 357); a segment and piece 0 ("laid"); a
segment `l` and piece `hearN P5J.At.links l + 2` (after the batching); a segment and any other piece
("cleared"). At "cleared" the items `pinW`, `pile`, `pinI` are admitted only where the segment hands
on no row (`P1L20.bearing l = false`). At the others they are in the row's `owes`.

Limits.
  * Lists of items only: the file says nothing about what an item means.
  * At the kinds other than `frame` the table is `rideOk`, which does not tell the sorts of place of
    one kind apart.
  * Full size only. Item 5: under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OpenBridge
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrame
import Johnson.P1L20R.RoomFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.LinkJoin (hearN)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- Which kinds of item may pass over a sub-protocol of the kind `frame`, by the place's segment and
piece: the five sorts of such a place, in the order of `keepsFrame`'s arms (KeepsFrame.lean). It is
a definition: a table for a test on the written lists. -/
def frameOk (p : Place) (i : Item) : Bool :=
  match p.link with
  | none =>
    if p.piece == 0 then
      match i with
      | .unmarked | .pinW | .pile => true
      | .constr _ .lookDigits | .constr _ .lookCallsHeard => false
      | .constr _ _ => true
      | _ => false
    else
      match i with
      | .unmarked | .pinW | .pinI | .pileOne | .pinV | .wrow => true
      | _ => false
  | some l =>
    if p.piece == 0 then
      match i with
      | .unmarked | .pinW | .pile | .pinI | .carry _ | .pinKept _ => true
      | .constr _ .lookDigits | .constr _ .lookCallsHeard => false
      | .constr _ _ => true
      | _ => false
    else if p.piece == hearN P5J.At.links l + 2 then
      match i with
      | .unmarked | .pinW | .pile | .pinI | .row _ _ | .wo _ => true
      | .constr _ .lookDigits | .constr _ .lookCallsHeard => false
      | .constr _ _ => true
      | _ => false
    else
      match i with
      | .unmarked | .carry _ | .pinKept _ => true
      | .pinW | .pile | .pinI => !P1L20.bearing l
      | .constr _ .lookDigits | .constr _ .lookCallsHeard => false
      | .constr _ _ => true
      | _ => false

/-- The table `rideOk` (Thread/RideOk.lean), with `frameOk` at the places of the kind `frame`. It is
a definition. -/
def rideOkF (p : Place) (i : Item) : Bool :=
  if p.kind == KindName.frame then frameOk p i else rideOk p i

set_option maxRecDepth 1000000 in
/-- Along the written lists every open item is closed, or owed again, or admitted by the table. -/
theorem rideOkF_onePass :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all
      fun x => x.1.all fun i => (FirstRows.rowAt P5J.At.links x.2).shuts.contains i ||
        (FirstRows.rowAt P5J.At.links x.2).owes.contains i || rideOkF x.2 i) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the item `pinKept` struck at the places "laid" the same test fails. -/
theorem rideOkF_control :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all
      fun x => x.1.all fun i => (FirstRows.rowAt P5J.At.links x.2).shuts.contains i ||
        (FirstRows.rowAt P5J.At.links x.2).owes.contains i ||
        (rideOkF x.2 i && !(x.2.kind == KindName.frame && x.2.link.isSome && x.2.piece == 0 &&
          (match i with
            | .pinKept _ => true
            | _ => false)))) = false := by
  decide +kernel

/-- At a place of the kind `frame`. -/
theorem rideOkF_frame {p : Place} (hk : p.kind = KindName.frame) (i : Item) :
    rideOkF p i = frameOk p i := by
  unfold rideOkF
  rw [hk]
  rfl

/-- At a place of another kind. -/
theorem rideOkF_else {p : Place} (hk : p.kind ≠ KindName.frame) (i : Item) :
    rideOkF p i = rideOk p i := by
  unfold rideOkF
  rw [if_neg (by simpa using hk)]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The column `hR` from the combinations that the finer table admits.** -/
theorem head_hR_of_cellsF (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p →
      i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      rideOkF p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i := by
  intro b hb i hi h1 h2
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (List.getElem?_eq_getElem hb)
  exact hok b _ i hp hi h1 h2
    (head_ok_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w rideOkF rideOkF_onePass hp hi h1 h2)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rideOkF_onePass
#print axioms ProofFile.Honest.FirstThread.rideOkF_control
#print axioms ProofFile.Honest.FirstThread.rideOkF_frame
#print axioms ProofFile.Honest.FirstThread.rideOkF_else
#print axioms ProofFile.Honest.FirstThread.head_hR_of_cellsF
