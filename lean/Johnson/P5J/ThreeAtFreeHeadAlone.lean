-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/ThreeAtFreeHeadAlone.lean: `h.Three h.free` FROM THE HEAD ALONE, WHERE THE LAWS ASK
THIRTEEN ROWS OR MORE (by the file's rule that tests are only appended:
Johnson/Desc/Laid/ProofAsks.lean; this library's list has fourteen). One theorem.

`three_at_free_head` (Johnson/P5J/ThreeAtFreeHead.lean) leaves hB: at the head's opening of the
files one test with code accepts (`sendsAreB` at 358). `Meaning.K2.hB_paid`
(Johnson/IMR/EndFiveMade.lean) pays it from the scope, the description's test on the plan and
`madeRow`. Here the three are `h.scope`, `h.laid.planOk` and the first half of `AtMg.pins`, which is
spent as `madeRow Zp = true`.

  **`three_at_free_head_alone`** (h) : h.Three h.free. NO PREMISE STAYS BUT THE HEAD.

WHAT THAT SAYS AND WHAT IT DOES NOT. Nothing is proved here of what the maker makes of given public
files. THE FIVE THAT WERE LEFT FOLLOW FROM THE HEAD's OWN FIELDS (the scope, what is laid, `asks`).
Where the laws ask thirteen rows, `asks` holds two rows of tests that compare with written values
(`madeRow`, `cutRow`): each of the five spends at least one of the two.
The fact on reached states did not move into the head: another file's theorem pays it.
So the whole price is paid in whether the head can be met.
Over eight rows the payers do not compile. The numerals beneath are the written values': the full
size alone.
Read against Johnson/P5J/ThreeAtFreeHead.lean, Johnson/IMR/EndFiveMade.lean and
Johnson/P5J/NumAtHeadCall.lean, which may still turn.
Limits. A joining: it pays nothing by itself. A member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/).
The weight of the fact on reached states rests on `IM.hEnd_paid`.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeAtFreeHead
import Johnson.IMR.EndFiveMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB sendsAreB snAt laidAtCodes
  msgsOfChain)
open Johnson.Desc.First.Walk.Tied (Reach)

open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey)

/-- **`h.Three h.free` from the head alone**, where the laws ask thirteen rows. -/
theorem three_at_free_head_alone : h.Three h.free :=
  three_at_free_head h (Meaning.K2.hB_paid h.scope h.laid.planOk h.toAtMg.pins.1)

end P5J

#print axioms P5J.three_at_free_head_alone
