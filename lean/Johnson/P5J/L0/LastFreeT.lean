-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastFreeT.lean: **THE TOWER's FIELD `leads3_last_chains_table` AT THE ONE VALUE, FROM FIVE
PREMISES**: against `free_leads3` (Johnson/P5J/L0/LastFree.lean | LastFreeA.lean [neither is in this
library]): hcs is paid under the head
(`AtMg.hcs`, Johnson/P5J/L0/LastHcs.lean); hX and hN are paid from hT : `Sh.Tests h.shPlan` ("all the
named tests on the shared table's parameters say true") by `leads3_at_sh_tests`
(Johnson/P5J/L0/LastJoinXN.lean).
  `AtMg.free_leads3_tests`, `AtMgA.free_leads3_tests`: WHAT IS LEFT: hT · hRc · hP · hS · row0B, at closed
    letters [their texts: the last table's law's own, its letters replaced by program], and the four
    letters dB · dt · r · Ld, which stand in premises alone.
  `AtMgA.LastLeft`, `AtMgA.leads3_of_left`: the five as one structure, each field marked "a law" | "a fact on
    reached states" | "a closed test"; the field from it.
Limits. THE FULL SIZE ALONE. Calls: none of the five is paid; NO MEMBER is known. Nothing on
soundness, nothing on hiding.

-/
import Johnson.P5J.FreeAll
import Johnson.P5J.FreeSig
import Johnson.P5J.L0.LastHcs
import Johnson.P5J.L0.LastJoinXN

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
open VerifiableInference.Desc.First (ModelPart Item Numbers)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- **THE LAST CHAIN's FIELD AT THE VALUE, FROM FIVE.** -/
theorem AtMg.free_leads3_tests (h : AtMg o Z D r' Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (dB : RDT) (dt : List RDT) (r : Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hT : Sh.Tests h.shPlan)
    (hRc : ∀ q y, ocEnd (L0.getL o Zp Np cF) (At.N Zp cF) (h.mq 𝔇₀) fullLinks (First.flatPlaces true
    fullLinks true) q y → h.rc q → ((L0.getL o Zp Np cF) q).2.failed = none → ToldDesc.rcLastB 0
    (vAt Zp (At.N Zp cF)) Ld (p14At Zp).codes ((L0.getL o Zp Np cF) q).2 = true) (hP : PlanOk₃ o
    ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay)
    (Sh.ms h.shPlan) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.shPlan) (Sh.layU h.shPlan) (Sh.layO
    h.shPlan) (0, 0) (0, 0)) fullLinks (First.flatPlaces true fullLinks true) r ((At.N Zp
    cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld) (hS : ∀ q y, ocEnd (L0.getL o Zp Np cF) (At.N Zp
    cF) (h.mq 𝔇₀) fullLinks (First.flatPlaces true fullLinks true) q y → h.rc q → ((L0.getL o Zp Np
    cF) q).2.failed = none → ∀ f, firstOfS ((L0.getL o Zp Np cF) q).2 = some f → SeatsNumber
    (At.seats Zp) f.book) (row0B : RowZeroOwed (tiedNumbers (At.N Zp cF) (Fence.numbersSh (Sh.t₁
    h.shPlan) (Sh.layU h.shPlan) (Sh.layO h.shPlan) (0, 0) (0, 0))) (tiedMeaning (L0.getL o Zp Np
    cF) (h.mq 𝔇₀) (meaningSigS (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpSt (p14At
    Zp).codes (Sh.oNo h.shPlan) stSh) (Sh.ms h.shPlan) (Sh.decT₂ h.shPlan (h.shOpen 𝔇₀)) (Sh.mg
    h.shPlan (h.shOpen 𝔇₀)))) (⟨rowsOpen (p14At Zp).codes (At.arr Zp) (D.at frS.P.T.a).t₁ (D.at
    frS.P.T.a).t₂⟩ : MeaningL (F0T o Zp Np cF).S₃ (Wit (CellsM numsFull) At.Tok MsgT)) (promSigS
    (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At Zp).codes (Sh.oNo h.shPlan) stSh) (Sh.ms
    h.shPlan) (fun s : St => s.st) (fun s : St => shiftBook (Sh.nums h.shPlan (h.shOpen 𝔇₀)).lo
    s.book) (Sh.pm h.shPlan (h.shOpen 𝔇₀))) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS
    ((L0.getL o Zp Np cF) q).2) (endedX (Sh.X h.shPlan 12))) (fun q y => ocEnd (L0.getL o Zp Np cF)
    (At.N Zp cF) (h.mq 𝔇₀) fullLinks (First.flatPlaces true fullLinks true) q y ∧ h.rc q)
    (pieceZeroAt (F0T o Zp Np cF) (D.at frS.P.T.a) (c0 Zp) (restCap (extsLast (Tok := At.Tok) (F0T o
    Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpLast (p14At
    Zp).codes (smpNamed (p14At Zp).codes (At.seats Zp)) (smpSt (p14At Zp).codes (Sh.oNo h.shPlan)
    stSh) (L0.getL o Zp Np cF) (Fence.numbersSh (Sh.t₁ h.shPlan) (Sh.layU h.shPlan) (Sh.layO
    h.shPlan) (0, 0) (0, 0))) (fun _ _ => none) At.c₀ (mineOf (At.ms Zp Z.lay) (Sh.ms h.shPlan)
    (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.shPlan) (Sh.layU h.shPlan) (Sh.layO h.shPlan) (0, 0) (0,
    0))))))) :
    L0.Leads3 o D Zp Np cF (h.mq 𝔇₀) h.rc (h.free 𝔇₀) :=
  L0.leads3_at_sh_tests o Z D Zp Np cF (h.shOpen 𝔇₀) hT rfl dB dt (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0)
    (h.mq 𝔇₀) r Ld h.rc (h.free 𝔇₀) rfl rfl rfl rfl rfl rfl (free_q₃ h 𝔇₀) (h.free_hSig 𝔇₀ h.hcs) hRc hP
    hS row0B

set_option maxHeartbeats 4000000 in
/-- **THE SAME AT THE COMPOSED MEANING's CLOSED CONSTANT.** -/
theorem AtMgA.free_leads3_tests (h : AtMgA o Z D r' Zp Np cF x)
    (dB : RDT) (dt : List RDT) (r : Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hT : Sh.Tests h.toAtMg.shPlan)
    (hRc : ∀ q y, ocEnd (L0.getL o Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces
    true fullLinks true) q y → h.toAtMg.rc q → ((L0.getL o Zp Np cF) q).2.failed = none →
    ToldDesc.rcLastB 0 (vAt Zp (At.N Zp cF)) Ld (p14At Zp).codes ((L0.getL o Zp Np cF) q).2 = true)
    (hP : PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
    (At.ms Zp Z.lay) (Sh.ms h.toAtMg.shPlan) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan)
    (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0)) fullLinks (First.flatPlaces
    true fullLinks true) r ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld) (hS : ∀ q y,
    ocEnd (L0.getL o Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces true
    fullLinks true) q y → h.toAtMg.rc q → ((L0.getL o Zp Np cF) q).2.failed = none → ∀ f, firstOfS
    ((L0.getL o Zp Np cF) q).2 = some f → SeatsNumber (At.seats Zp) f.book) (row0B : RowZeroOwed
    (tiedNumbers (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU h.toAtMg.shPlan)
    (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))) (tiedMeaning (L0.getL o Zp Np cF) (h.toAtMg.mq h.𝔇)
    (meaningSigS (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpSt (p14At Zp).codes (Sh.oNo
    h.toAtMg.shPlan) stSh) (Sh.ms h.toAtMg.shPlan) (Sh.decT₂ h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇))
    (Sh.mg h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)))) (⟨rowsOpen (p14At Zp).codes (At.arr Zp) (D.at
    frS.P.T.a).t₁ (D.at frS.P.T.a).t₂⟩ : MeaningL (F0T o Zp Np cF).S₃ (Wit (CellsM numsFull) At.Tok
    MsgT)) (promSigS (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At Zp).codes (Sh.oNo
    h.toAtMg.shPlan) stSh) (Sh.ms h.toAtMg.shPlan) (fun s : St => s.st) (fun s : St => shiftBook
    (Sh.nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).lo s.book) (Sh.pm h.toAtMg.shPlan
    (h.toAtMg.shOpen h.𝔇))) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS ((L0.getL o Zp Np
    cF) q).2) (endedX (Sh.X h.toAtMg.shPlan 12))) (fun q y => ocEnd (L0.getL o Zp Np cF) (At.N Zp
    cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces true fullLinks true) q y ∧ h.toAtMg.rc q)
    (pieceZeroAt (F0T o Zp Np cF) (D.at frS.P.T.a) (c0 Zp) (restCap (extsLast (Tok := At.Tok) (F0T o
    Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpLast (p14At
    Zp).codes (smpNamed (p14At Zp).codes (At.seats Zp)) (smpSt (p14At Zp).codes (Sh.oNo
    h.toAtMg.shPlan) stSh) (L0.getL o Zp Np cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU
    h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))) (fun _ _ => none) At.c₀ (mineOf
    (At.ms Zp Z.lay) (Sh.ms h.toAtMg.shPlan) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan)
    (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))))))) :
    L0.Leads3 o D Zp Np cF (h.toAtMg.mq h.𝔇) h.toAtMg.rc h.free :=
  h.toAtMg.free_leads3_tests h.𝔇 dB dt r Ld hT hRc hP hS row0B

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE VALUE**: five premises, by name. dB · dt · r · Ld: letters
that stand in them alone. -/
structure AtMgA.LastLeft (h : AtMgA o Z D r' Zp Np cF x) (dB : RDT) (dt : List RDT)
    (r : Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid) : Prop where
  /-- A CLOSED TEST: all the named tests on the shared table's parameters say true (the public files
  alone; no state). -/
  hT : Sh.Tests h.toAtMg.shPlan
  /-- A FACT ON REACHED STATES: at every last state of the first chain inside its whole last promise, reached
  at a typed instance (`h.rc`) and unmarked, the five tests `rcLastB` say yes. -/
  hRc : ∀ q y, ocEnd (L0.getL o Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces
    true fullLinks true) q y → h.toAtMg.rc q → ((L0.getL o Zp Np cF) q).2.failed = none →
    ToldDesc.rcLastB 0 (vAt Zp (At.N Zp cF)) Ld (p14At Zp).codes ((L0.getL o Zp Np cF) q).2 = true
  /-- A CLOSED TEST: `PlanOk₃`: tests on the plan (the public files alone; no state). -/
  hP : PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
    (At.ms Zp Z.lay) (Sh.ms h.toAtMg.shPlan) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan)
    (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0)) fullLinks (First.flatPlaces
    true fullLinks true) r ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld
  /-- A FACT ON REACHED STATES: at the same states the handed book numbers the messages as the plan's list
  of seats does. -/
  hS : ∀ q y, ocEnd (L0.getL o Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces
    true fullLinks true) q y → h.toAtMg.rc q → ((L0.getL o Zp Np cF) q).2.failed = none → ∀ f,
    firstOfS ((L0.getL o Zp Np cF) q).2 = some f → SeatsNumber (At.seats Zp) f.book
  /-- A LAW: the law of the last chain's piece number 0, between the promises at borders 0 and 1, in the
  form in which the last table's files conclude it. -/
  row0B : RowZeroOwed (tiedNumbers (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU
    h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))) (tiedMeaning (L0.getL o Zp Np cF)
    (h.toAtMg.mq h.𝔇) (meaningSigS (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpSt (p14At
    Zp).codes (Sh.oNo h.toAtMg.shPlan) stSh) (Sh.ms h.toAtMg.shPlan) (Sh.decT₂ h.toAtMg.shPlan
    (h.toAtMg.shOpen h.𝔇)) (Sh.mg h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)))) (⟨rowsOpen (p14At
    Zp).codes (At.arr Zp) (D.at frS.P.T.a).t₁ (D.at frS.P.T.a).t₂⟩ : MeaningL (F0T o Zp Np cF).S₃
    (Wit (CellsM numsFull) At.Tok MsgT)) (promSigS (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At
    Zp).codes (Sh.oNo h.toAtMg.shPlan) stSh) (Sh.ms h.toAtMg.shPlan) (fun s : St => s.st) (fun s :
    St => shiftBook (Sh.nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).lo s.book) (Sh.pm
    h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇))) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS
    ((L0.getL o Zp Np cF) q).2) (endedX (Sh.X h.toAtMg.shPlan 12))) (fun q y => ocEnd (L0.getL o Zp
    Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces true fullLinks true) q y ∧
    h.toAtMg.rc q) (pieceZeroAt (F0T o Zp Np cF) (D.at frS.P.T.a) (c0 Zp) (restCap (extsLast (Tok :=
    At.Tok) (F0T o Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpLast
    (p14At Zp).codes (smpNamed (p14At Zp).codes (At.seats Zp)) (smpSt (p14At Zp).codes (Sh.oNo
    h.toAtMg.shPlan) stSh) (L0.getL o Zp Np cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU
    h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))) (fun _ _ => none) At.c₀ (mineOf
    (At.ms Zp Z.lay) (Sh.ms h.toAtMg.shPlan) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan)
    (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))))))

/-- **THE LAST CHAIN's FIELD AT THE VALUE, FROM WHAT IS LEFT.** -/
theorem AtMgA.leads3_of_left (h : AtMgA o Z D r' Zp Np cF x) {dB : RDT} {dt : List RDT}
    {r : Fmt.M1.Stage → ℕ} {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (L : h.LastLeft dB dt r Ld) :
    L0.Leads3 o D Zp Np cF (h.toAtMg.mq h.𝔇) h.toAtMg.rc h.free :=
  h.free_leads3_tests dB dt r Ld L.hT L.hRc L.hP L.hS L.row0B

end P5J

#print axioms P5J.AtMg.free_leads3_tests
#print axioms P5J.AtMgA.free_leads3_tests
#print axioms P5J.AtMgA.leads3_of_left
