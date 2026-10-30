-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K8NamesDoorAtHead.lean: the public test `namesDoorB`
(Johnson/Desc/First/K8/PlanDoor.lean) at its own name: it accepts at every description whose first
chain's entries are shaped and whose cut into sub-protocols is the written one; and at the one head
it accepts at the description at which the condition on the kind K8 asks it: the first conjunct of
`K8Cond` (Johnson/Goal/Skeleton/Kinds/K8Bridge.lean), to the letter.


Row or tool. Payers for a premise of another law. Each theorem is a call of
Johnson/HB/LLHARD/K8NamesDoorText.lean; that the test's text there is the test is `namesDoorB_is`,
by definition.

What it spends. Rows are those of the proof file's entry tests, `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean), counted from 1: row 10 holds the cut
into sub-protocols to the written one (`cutRow`). `namesDoorB_at_name` and `namesDoorB_at_head`: row
10, by the second half of `pins_of_laid`, and the field `planOk` of `LaidAt`; the second takes both
off the head's fields `scope` and `laid`. `namesDoorB_is` and `namesDoor_of_cut`: no row and no
field.

`P1K8T.FD` is that of Johnson/P1K8R/FillAt.lean, line 74.

Limits. Those of K8NamesDoorText.lean. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K8NamesDoorText
import Johnson.Desc.First.K8.PlanDoor
import Johnson.P1K8R.FillAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First.K8 (namesDoorB)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Desc.K14.Law (secondAt seatZ)

/-- The test is its text. -/
theorem namesDoorB_is {Xi : Type} (F : FileDescription Xi) : namesDoorB F = doorText F := rfl

/-- **At every description whose first chain is shaped and cut as written.** -/
theorem namesDoor_of_cut {Xi : Type} (F : FileDescription Xi)
    (hs : ∀ b ∈ F.first.blocksInOrder, b.shaped = true) (hc : cutOf F.first.blocksInOrder = cutFirstFull) :
    namesDoorB F = true :=
  doorText_of_cut F hs hc

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- In scope, where the value is laid. -/
theorem namesDoorB_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    namesDoorB (F0T OnBytes.secondHashFunction Zp Np cF) = true :=
  doorText_at_name hZ L

/-- **The first conjunct of `K8Cond`, at the head.** -/
theorem namesDoorB_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    namesDoorB (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true :=
  namesDoor_of_cut _
    (fun b hb => (((FileDescription.planOk_ok _).1 h.laid.planOk).blocks₁ b hb).2)
    (pins_of_laid h.scope h.laid).2

end

end P5J


#print axioms P5J.namesDoorB_is
#print axioms P5J.namesDoor_of_cut
#print axioms P5J.namesDoorB_at_name
#print axioms P5J.namesDoorB_at_head
