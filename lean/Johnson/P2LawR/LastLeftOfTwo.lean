-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LastLeftOfTwo.lean: THE JOIN lastLeft_at_head, ITS FIRST HALF:
`AtMgA.LastLeftAt` (Johnson/P5J/L0/LastLeftAt.lean: what is left of the last chain's field at the
value, no letter) FROM THE HEAD, SIX CLOSED FIELDS BY NAME (structure AtMgA.LastRestP) AND THE TWO
FIELDS hRc AND hS OF `AtMgA.LastLeft` IN THEIR OWN TEXTS. One structure, one theorem: calls.


HOW EACH FIELD OF LastLeft IS HAD: row0B: row0B_at_left, through left_of_leftB ·
hB3: three_at_head under K2Told · hT: the field tests · hP:
planOk₃_at_join over coreB_law · hRc, hS: hypotheses here, taken out of P5J/L0/LastLeftB.lean
by program, at o := OnBytes.secondHashFunction and Ld := L0.ldAt Zp: their payers (hRc_at_left_pinned, declared
nowhere in this library; hS_at_left) are not called here: the
second half lays them in. THE STRETCH IS NOT EMPTY: it comes by hP's own call: planOk₃_at_join gives
∃ dB dt, PlanOk₃ … dB dt …, and PlanOk₃'s own field stretch says that L0.l3At … = dB :: dt: so
LastLeftAt's match opens at that pair, never at []. (The field core says it too: its arm at [] is
False; the head alone gives it as well: stretch_at_head.) A RAISED LIMIT stands in
this file (maxRecDepth 40000), as in the files that it calls.
IS IT EMPTY? NO MEMBER: that the head and the six fields can be met together at the real files is
shown by nobody; k2told is a closed sentence: if false, the theorem says nothing. The full size
alone. Nothing on soundness.
-/
import Johnson.P5J.L0.LastLeftB
import Johnson.P5J.L0.PlanAtJoin
import Johnson.P2LawR.PlanCoreOfTests
import Johnson.Desc.Book.ThreeAtHead

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

/-- **WHAT IS LEFT FOR hB3, hT AND hP, BY NAME.** Six fields. No fact on states. -/
structure AtMgA.LastRestP (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) : Prop where
  /-- A CLOSED SENTENCE on the texts, without a letter of the files (Johnson/IMR/MsgsSwitch.lean): A
  LAW IN A FIELD's PLACE: no evaluation can show it: true or false once and for all. SPENT BY: hB3
  (three_at_head). WHOSE: k2Told_paid (IMR/ToldPaid.lean), a call of told_tenants
  (K2C/ToldTenants.lean).
  Where this and lean/THEOREM.md differ,
  the page holds. -/
  k2told : _root_.Meaning.Carry.K2Told
  /-- A CLOSED TEST: all the named tests on the shared table's parameters say true (the public files
  alone). IT IS LastLeft's FIELD hT ITSELF. WHOSE: Sh.tests_at_head
  (K14/Law/SharedConstChainOkAtHead.lean), from the head and one pin.
  Where this and lean/THEOREM.md differ, the page holds.
  It is reported false at the small size (not shown here):
  a premise of the full size alone. -/
  tests : Sh.Tests h.toAtMg.shPlan
  /-- A COMPARISON of two numbers of the data. SPENT BY: hP. WHOSE:
  AtMg.trees_at (Johnson/HB/LLHARD/HeadFacts.lean). -/
  twoTrees : 1 < (D.at frS.P.T.a).t₂
  /-- TWO COMPARISONS. SPENT BY: hP. WHOSE: AtMg.elderBelow_at. -/
  elder : (At.N Zp cF).index.1 < (D.at frS.P.T.a).t₁ ∧ (At.N Zp cF).w.1 < (D.at frS.P.T.a).t₁
  /-- A CLOSED TEST AND TWO MEMBERSHIPS in a closed list. SPENT BY: hP. WHOSE:
  AtMg.endTests_at (Johnson/HB/LLHARD/PlanOk3AtHead.lean). -/
  endTests : sampledBelow ((D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂) (At.N Zp cF) ((openSets
    fullLinks (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true
    fullLinks true).length]?.getD []) = true ∧ (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets
    fullLinks (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true
    fullLinks true).length]?.getD []) ∧ (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets
    fullLinks (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true
    fullLinks true).length]?.getD [])
  /-- ONE CLOSED TEST, fifteen conjuncts (coreB), at the head and the tail of the
  third piece's stretch itself (L0.l3At): no letter is bound: a file of evaluations can evaluate
  it. SPENT BY: hP (planOk₃_at_join over coreB_law). EVALUATED: by nobody at
  these terms. -/
  core : match L0.l3At OnBytes.secondHashFunction D Zp Np cF with
    | [] => False
    | dB :: dt => P2Law.PlanLeft.coreB OnBytes.secondHashFunction ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a)
        (F0T OnBytes.secondHashFunction Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay)
        (L0.ms2J (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) (At.N Zp cF)
        (L0.nsJ (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) H2K.Member.rWFull
        ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) (L0.ldAt Zp) = true

/-- **LastLeftAt from the head, the six, and LastLeft's own hRc and hS.** -/
theorem AtMgA.lastLeft_of_two (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) (R : h.LastRestP) (hRc :
                ∀ q y, ocEnd (L0.getL OnBytes.secondHashFunction Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks
                (First.flatPlaces true fullLinks true) q y → h.toAtMg.rc q → ((L0.getL OnBytes.secondHashFunction Zp Np cF)
                q).2.failed = none → ToldDesc.rcLastB 0 (vAt Zp (At.N Zp cF)) (L0.ldAt Zp) (p14At Zp).codes
                ((L0.getL OnBytes.secondHashFunction Zp Np cF) q).2 = true) (hS : ∀ q y, ocEnd (L0.getL OnBytes.secondHashFunction Zp Np
                            cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces true fullLinks true) q y →
                            h.toAtMg.rc q → ((L0.getL OnBytes.secondHashFunction Zp Np cF) q).2.failed = none → ∀ f, firstOfS ((L0.getL
                                        OnBytes.secondHashFunction Zp Np cF) q).2 = some f → SeatsNumber (At.seats Zp) f.book) :
    h.LastLeftAt := by
  obtain ⟨dB, dt, hP⟩ := L0.planOk₃_at_join h.toAtMg (L0.ldAt Zp) R.twoTrees R.elder R.endTests
    (fun dB dt s => P2Law.PlanLeft.coreB_law _ _ _ _ _ _ _ _ dB dt _ _ _ _ _ _ _ _ _ _ (by
      have c := R.core
      rw [show L0.l3At OnBytes.secondHashFunction D Zp Np cF = dB :: dt from s] at c
      exact c))
  have e : L0.l3At OnBytes.secondHashFunction D Zp Np cF = dB :: dt := hP.stretch
  unfold AtMgA.LastLeftAt
  rw [e]
  exact h.left_of_leftB ⟨R.tests, hRc, hP, hS,
    fun p hp _ => VerifiableInference.Desc.Book.three_at_head h.toAtMg R.k2told p hp.1⟩

end P5J

#print axioms P5J.AtMgA.lastLeft_of_two
