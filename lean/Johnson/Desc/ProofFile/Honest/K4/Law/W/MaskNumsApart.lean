-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskNumsApart.lean: CONDITIONAL. Two definitions with code,
and statements with their proofs.

What is here. TWELVE NUMBERS DIFFER. `maskNumAt Zp (2 * g)` (Law/W/MaskRowAtSeg.lean) is the number
in the witness of the message at the seat of segment 2 g's first message with mask rows; that the
mask row of the segment of the feed-forward layers' own rounds (sub-protocol K4) lies in the message
of that number is `maskRow_laid`'s (the same file, under h and `LaidK4`). Under h, the library's
hypothesis `P5J.AtMgA` on the public files, it is a different number at each group g below 12
(`maskNum_inj_head`). What it is for: K4's twelve members each ask a run of entries of their
segment's mask row (`K4MaskTieAt`, Law/ScriptAt.lean), and the twelve runs all begin at one place,
which names no group (`ledger_front_head`, Law/W/MaskBelowHead.lean): that no two of these runs meet
at one entry of one message follows from this statement WITH `maskRow_laid`; NOTHING FOLLOWS ON
COINS: two runs in two messages can hold one list of coins.
How. Under h five parts of the public parameters are the library's written values
(`written_of_head`, Johnson/Road/K4/K4HeadWritten.lean). So the plan's seats and the numbering are
the written ones (`seatsAt_written`, `arrAt_written`, Johnson/Road/K4/K4PlanTied.lean), and the
place in the list, which reads the request's shape alone, is the written shape's:
`maskNumAt Zp m = maskNumW m` at every m (`maskNumAt_written`). Then one closed fact on the written
values, by Lean's kernel (`maskNums_apart_written`).

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). `maskNum_inj_head` takes h, g < 12, g' < 12 and the equation of
the two numbers, and nothing else; `maskNum_inj_written` has the same under `WrittenAt Zp` in h's
stead. WHICH NUMBERS THE TWELVE ARE is not said. NOTHING HERE ON ANY OTHER MESSAGE's NUMBER: not on
the index masks' message's, of which K4's members ask an entry too, nor on another kind's. Nothing
on what any entry holds. THE TWO CLOSED FACTS OF THIS FILE ARE PROVED BY EVALUATION IN LEAN's KERNEL
(`decide +kernel`), which no independent checker has replayed; so are closed facts beneath it in the
library (`shape_one`, Johnson/Road/K4/K4PlanTied.lean, among them). `maskNums_written_no` is a
negative test of the definition `maskNumW`: at 25 and 27, beyond the head's segment's number 24
(`P5J.At.mH`), the two numbers are one: so a list of such numbers can hold one twice. THE FULL SIZE
ALONE throughout, and the format's second hash function alone in `maskNum_inj_head`. A program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/,
at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `maskSeatW`, `maskNumW`   the seat and the number at the written values
  `maskPos_shape`, `seatCalls_shape`   the place and the plan's seat read the request's shape alone
  `sentShape_written`, `maskSeatAt_written`, `maskNumAt_written`   under `WrittenAt`
  `maskNums_apart_written`, `maskNums_written_no`   the closed fact; a negative test
  `maskNum_inj_written`, `maskNum_inj_head`   **the twelve numbers differ**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskRowAtSeg
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PlanTied
import Johnson.Road.K4.K4PinsWrittenMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Road.K4 (WrittenAt written_of_head shape_one seatsAt_written arrAt_written seatW sentW
  arrW)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Sent messagesAt keptAt bornAt)
open P5J (AtMgA TS)

/-! ## 1 At the written values -/

/-- The seat of segment m's first message with mask rows, off the written seats and shape. -/
def maskSeatW (m : ℕ) : ℕ × ℕ := seatW m (maskPosOf sentW m)

/-- The number in the witness of the message at that seat, by the written numbering. -/
def maskNumW (m : ℕ) : ℕ := arrW (maskSeatW m).1 (maskSeatW m).2

/-! ## 2 What reads the request's shape alone -/

/-- The place in the list reads the request's shape alone. CONDITIONAL on e. -/
theorem maskPos_shape {D D' : Sent} (e : D.shape = D'.shape) (m : ℕ) :
    maskPosOf D m = maskPosOf D' m := by
  unfold maskPosOf Lot.k4MaskPos Lot.k4MaskMsg keptAt messagesAt
  rw [e]

/-- The plan's seat of a member of the calls' list reads of D the request's shape alone, as in the
library's `H2K5.Door.seatCalls_shape`, whose file is not imported here. CONDITIONAL on e. -/
theorem seatCalls_shape (ps : List P5T.PSeat) {D D' : Sent} (e : D.shape = D'.shape) (l j : ℕ) :
    P6T.seatCallsT ps D l j = P6T.seatCallsT ps D' l j := by
  have c : P6T.isCall D l j = P6T.isCall D' l j := by
    funext p
    unfold P6T.isCall P6T.keptN keptAt bornAt
    rw [e]
  unfold P6T.seatCallsT P6T.callAt
  rw [c]

/-! ## 3 Under `WrittenAt` -/

variable {Zp : ProofFile.Pub}

/-- CONDITIONAL on W. The request's shape at the public part is the written one. -/
theorem sentShape_written (W : WrittenAt Zp) : (P5J.At.sentAt Zp).shape = sentW.shape :=
  W.shape.trans shape_one

/-- CONDITIONAL on W. **The seat is the written one.** -/
theorem maskSeatAt_written (W : WrittenAt Zp) (m : ℕ) : maskSeatAt Zp m = maskSeatW m := by
  show P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) m (maskPosOf (P5J.At.sentAt Zp) m) =
    P6T.seatCallsT P5T.psFull sentW m (maskPosOf sentW m)
  rw [maskPos_shape (sentShape_written W) m, seatCalls_shape _ (sentShape_written W),
    show P5J.At.pseats Zp = P5T.psFull from seatsAt_written W]

/-- CONDITIONAL on W. **The number is the written one.** -/
theorem maskNumAt_written (W : WrittenAt Zp) (m : ℕ) : maskNumAt Zp m = maskNumW m := by
  show P5J.At.arr Zp (maskSeatAt Zp m).1 (maskSeatAt Zp m).2 =
    arrW (maskSeatW m).1 (maskSeatW m).2
  rw [maskSeatAt_written W m, show P5J.At.arr Zp = arrW from arrAt_written W]

/-! ## 4 The closed fact -/

set_option maxRecDepth 1000000 in
/-- By the kernel: **at the written values the twelve numbers differ.** -/
theorem maskNums_apart_written : ((List.range 12).map fun g => maskNumW (2 * g)).Nodup := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel, a negative test: at 25 and 27, which are no links' numbers, the two are one. -/
theorem maskNums_written_no : maskNumW 25 = maskNumW 27 := by decide +kernel

/-- CONDITIONAL on W, hg, hg' and e. The twelve numbers differ, under `WrittenAt` alone. -/
theorem maskNum_inj_written (W : WrittenAt Zp) {g g' : ℕ} (hg : g < 12) (hg' : g' < 12)
    (e : maskNumAt Zp (2 * g) = maskNumAt Zp (2 * g')) : g = g' := by
  rw [maskNumAt_written W, maskNumAt_written W] at e
  exact List.inj_on_of_nodup_map maskNums_apart_written (List.mem_range.2 hg)
    (List.mem_range.2 hg') e

/-! ## 5 Under h -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, hg, hg' and e. **THE TWELVE SEGMENTS' NUMBERS `maskNumAt Zp (2 * g)` ARE
TWELVE DIFFERENT NUMBERS.** -/
theorem maskNum_inj_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g g' : ℕ} (hg : g < 12)
    (hg' : g' < 12) (e : maskNumAt Zp (2 * g) = maskNumAt Zp (2 * g')) : g = g' :=
  maskNum_inj_written (written_of_head h.toAtMg) hg hg' e

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.maskPos_shape
#print axioms ProofFile.Honest.K4.W.seatCalls_shape
#print axioms ProofFile.Honest.K4.W.sentShape_written
#print axioms ProofFile.Honest.K4.W.maskSeatAt_written
#print axioms ProofFile.Honest.K4.W.maskNumAt_written
#print axioms ProofFile.Honest.K4.W.maskNums_apart_written
#print axioms ProofFile.Honest.K4.W.maskNums_written_no
#print axioms ProofFile.Honest.K4.W.maskNum_inj_written
#print axioms ProofFile.Honest.K4.W.maskNum_inj_head
