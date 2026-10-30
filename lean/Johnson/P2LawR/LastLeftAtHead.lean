-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LastLeftAtHead.lean: THE JOIN lastLeft_at_head: THE STRUCTURE `AtMgA.LastLeftAt`
(Johnson/P5J/L0/LastLeftAt.lean: what is left of the last chain's field at the value, no letter)
FROM THE HEAD AT o := OnBytes.secondHashFunction AND ONE CLOSED TEST BY NAME (structure AtMgA.LastRest: the one
field core). One structure, one theorem: calls.


THE STATEMENT. LastLeftOfTen.lean's form has ten fields. NINE FALL
HERE, EACH BY A CALL: twoTrees, elder, endTests, indexNo, msgs, cutRow, madeRow:
rest_of_door (Johnson/P2LawR/RestOfDoor.lean): other files' ends at the head and the door's two
pins · k2told: the theorem k2Told_paid (Johnson/IMR/ToldPaid.lean) · sits:
sits_at_head (Johnson/P2LawR/SitsAtLeft.lean). WHICH DOOR. THIS FORM STANDS OVER THE DOOR's
LIST OF THIRTEEN ROWS (Johnson/Desc/Laid/ProofAsks.lean) AND OVER THAT OF FOURTEEN (one row
appended): rest_of_door draws the two pins off the head's field laid.asks there.
Over the door's list of eight rows it does not compile: there LastLeftOfTen.lean's, with its ten
fields, is the form. HOW: ONE CALL of lastLeft_of_ten (Johnson/P2LawR/LastLeftOfTen.lean: the
form with ten fields; how each field of LastLeft is had stands in its head), its ten
fields laid: nine by the calls above, core by the field. THE STRETCH IS NOT EMPTY: it comes by hP's
own call: planOk₃_at_join gives ∃ dB dt, PlanOk₃ … dB dt …, and PlanOk₃'s own field stretch says
that L0.l3At … = dB :: dt. (The field core says it too: its arm at [] is False.) A RAISED LIMIT
stands in this file (maxRecDepth 40000), as in the files that it calls.
IS IT EMPTY? NO MEMBER. WHAT IS LEFT IS ONE CLOSED TEST, WHICH CAN BE EVALUATED AND, AS FAR AS IS
KNOWN, HAS NOT BEEN: if core is false at the real files, the theorem says nothing
of them. That the head itself can be met is shown by nobody here. The full size alone (its named
tests are reported false at the small size; not shown here). Nothing on soundness.
-/
import Johnson.P2LawR.LastLeftOfTen
import Johnson.P2LawR.SitsAtLeft
import Johnson.P2LawR.RestOfDoor
import Johnson.IMR.ToldPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers openSets sampledIn start)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE HEAD, BY NAME.** One field: a closed test. -/
structure AtMgA.LastRest (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) : Prop where
  /-- ONE CLOSED TEST, fifteen conjuncts (coreB), at the head and the tail of the
  third piece's stretch itself (L0.l3At): no letter is bound: an evaluation can decide
  it. SPENT BY: hP (planOk₃_at_join over coreB_law). EVALUATED: by nobody at
  these terms. -/
  core : match L0.l3At OnBytes.secondHashFunction D Zp Np cF with
    | [] => False
    | dB :: dt => P2Law.PlanLeft.coreB OnBytes.secondHashFunction ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a)
        (F0T OnBytes.secondHashFunction Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay)
        (L0.ms2J (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) (At.N Zp cF)
        (L0.nsJ (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) H2K.Member.rWFull
        ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) (L0.ldAt Zp) = true

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE VALUE, FROM THE HEAD AND ONE CLOSED TEST.** -/
theorem AtMgA.lastLeft_at_head (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) (R : h.LastRest) :
    h.LastLeftAt := by
  obtain ⟨h2, hE, hEnd, hIdx, hNum, hcut, hmade⟩ := h.rest_of_door
  have hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true :=
    VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [hmade, Bool.or_true])
  exact h.lastLeft_of_ten ⟨_root_.Meaning.Carry.k2Told_paid, h2, hE, hEnd, R.core,
    P2Law.Left.sits_at_head h.toAtMg hy, hIdx, hNum, hcut, hmade⟩

end P5J

#print axioms P5J.AtMgA.lastLeft_at_head
