-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/PadsFreeAt.lean: NO SEAT AT WHICH TWO SEGMENTS READ ONE ARRAY LIES ON A PAD
(`PadsFree`, Johnson/P5J/WordsAtQ.lean), AT THE CLOSED CONSTANT, IN THE WORDS IN WHICH THE
LOOKUP's LAW ASKS IT; and the policy file's public core there. So both premises of "reader's and
owner's readings of any witness agree" (`k03_reads`, Johnson/P5J/K03TermsCalls.lean) are paid:
under one named test with code, or under the pin on what the planner made. Five theorems:
joinings.
  `AtMg.coreScope h : Hd.PublicCore (At.X Zp).P`: from the head's scope, reads and pubOne, by
    `core_of_scope` (Johnson/Goal/Meaning/ScopeCore.lean).


  `AtMgA.padsFree h hp`: `PadsFree` at the parameters under the head, in `k03_reads`' own letters,
    under hp : `OffPad.padsAtZ Zp = true` (Johnson/Desc/Kinds/HeadDoorAtZ.lean). IT IS ANOTHER
    FILE's THEOREM `OffPad.padsFree_atAll` (Johnson/Desc/Kinds/Law/PadsFreeAtAll.lean), up to
    unfolding four parameters and the seats' name.
  `k03_reads_at h hp`: `k03_reads`' conclusion, with both its premises paid.
  `AtMgA.padsFree_pin h hy`, `k03_reads_pin h hy`: the same under hy : `madePinnedAt … = true`, by
    `tests_of_pin` (Johnson/Desc/Kinds/Law/HeadCutsOfPin.lean): no test on the pads
    is left.
Limits: joinings. THE HEAD h IS A PREMISE: a member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/). `padsAtZ` has been
evaluated true at the full-size stored public files BY REPORT (two logs): not
seen here. No soundness is claimed.

-/
import Johnson.P5J.K03TermsCalls
import Johnson.Desc.Kinds.Law.PadsFreeAtAll
import Johnson.Desc.Kinds.Law.HeadCutsOfPin
import Johnson.Goal.Meaning.ScopeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model OnBytes.Road
open Inst.Model Inst.Model.All
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (szOf)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ OffPad.padsFree_atAll tests_of_pin)
open VerifiableInference.PlanWritten (madePinnedAt)
open _root_.Meaning (fLay ReadsOne sizesOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The policy file's public core, under the head. -/
theorem AtMg.coreScope (h : AtMg o Z D r Zp Np cF) : Hd.PublicCore (At.X Zp).P :=
  OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne

/-- **PadsFree at the constant, in the lookup's law's own letters.** -/
theorem AtMgA.padsFree (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true) :
    PadsFree (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
      (h.toAtMg.𝔇 h.𝔇).N (sizesOf (At.X Zp))
      (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
        (sizesOf (At.X Zp))) (At.X Zp) :=
  OffPad.padsFree_atAll h.toAtMg hp

/-- **Reader's and owner's readings of any witness agree, at the constant.** -/
theorem k03_reads_at (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true) :
    ∀ w : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT,
      ReadsOne (At.X Zp) (fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
          fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (fun j => readAt (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
          (h.toAtMg.𝔇 h.𝔇).N j w) :=
  k03_reads h h.toAtMg.coreScope (h.padsFree hp)

/-- The same under the pin on what the planner made. -/
theorem AtMgA.padsFree_pin (h : AtMgA o Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    PadsFree (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
      (h.toAtMg.𝔇 h.𝔇).N (sizesOf (At.X Zp))
      (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
        (sizesOf (At.X Zp))) (At.X Zp) :=
  h.padsFree (tests_of_pin h.toAtMg hy).2

theorem k03_reads_pin (h : AtMgA o Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ∀ w : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT,
      ReadsOne (At.X Zp) (fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (_root_.Meaning.seatBy (fLay (h.toAtMg.𝔇 h.𝔇).sent.layout (At.num Zp)) (At.X Zp)
          fun j => szOf (_root_.Meaning.tlAt (At.X Zp) j))
        (fun j => readAt (h.toAtMg.𝔇 h.𝔇).cs (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms
          (h.toAtMg.𝔇 h.𝔇).N j w) :=
  k03_reads_at h (tests_of_pin h.toAtMg hy).2

end P5J

#print axioms P5J.AtMg.coreScope
#print axioms P5J.AtMgA.padsFree
#print axioms P5J.k03_reads_at
#print axioms P5J.AtMgA.padsFree_pin
#print axioms P5J.k03_reads_pin
