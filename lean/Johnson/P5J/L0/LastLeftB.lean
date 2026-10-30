-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastLeftB.lean: `AtMgA.LastLeft` (Johnson/P5J/L0/LastFreeT.lean) WITH ITS ONE LAW STRUCK: the field
row0B is the theorem `P5J.row0B_at_left` (Johnson/P2LawR/RowZeroBAtLeft.lean), from the head, hP and
ONE fact on reached states, hB3.
  `AtMgA.LastLeftB`: WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE VALUE: FIVE, NONE OF THEM A LAW: hT · hP ("a
    closed test") · hRc · hS · hB3 ("a fact on reached states").
  `AtMgA.left_of_leftB`, `AtMgA.leads3_of_leftB`: `LastLeft`, and the tower's field, from it.
  `AtMgA.LastLeftBAt`, `AtMgA.leads3_of_leftBAt`: the same with the four letters dB · dt · r · Ld laid as in
    Johnson/P5J/L0/LastLeftAt.lean: no letter is left.
Limits. THE FULL SIZE ALONE. Calls: none of the five is paid; NO MEMBER is known. Nothing on
soundness, nothing on hiding.

-/
import Johnson.P5J.L0.LastLeftAt
import Johnson.P2LawR.RowZeroBAtLeft

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

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE VALUE, THE LAW OF ROW 0 STRUCK.** -/
structure AtMgA.LastLeftB (h : AtMgA o Z D r' Zp Np cF x) (dB : RDT) (dt : List RDT)
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
  /-- A FACT ON REACHED STATES: at every last state of the first chain that is reached at a typed
  instance (`h.rc`) and unmarked: three tests on its book. -/
  hB3 : ∀ p, h.toAtMg.rc p → ((L0.getL o Zp Np cF) p).2.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstBook 0 ((L0.getL o Zp Np cF) p).2 = true ∧ bookFitsB
    ((L0.getL o Zp Np cF) p).2.book = true ∧ ((L0.getL o Zp Np cF) p).2.book.place.size = ((L0.getL
    o Zp Np cF) p).2.st.oracles.size

/-- `LastLeft` from it: the law of row 0 is called. -/
theorem AtMgA.left_of_leftB (h : AtMgA o Z D r' Zp Np cF x) {dB : RDT} {dt : List RDT}
    {r : Fmt.M1.Stage → ℕ} {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (L : h.LastLeftB dB dt r Ld) : h.LastLeft dB dt r Ld :=
  ⟨L.hT, L.hRc, L.hP, L.hS, row0B_at_left h dB dt r Ld L.hB3 L.hP⟩

/-- **THE LAST CHAIN's FIELD AT THE VALUE, FROM IT.** -/
theorem AtMgA.leads3_of_leftB (h : AtMgA o Z D r' Zp Np cF x) {dB : RDT} {dt : List RDT}
    {r : Fmt.M1.Stage → ℕ} {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (L : h.LastLeftB dB dt r Ld) :
    L0.Leads3 o D Zp Np cF (h.toAtMg.mq h.𝔇) h.toAtMg.rc h.free :=
  h.leads3_of_left (h.left_of_leftB L)

/-- **THE SAME, NO LETTER.** -/
def AtMgA.LastLeftBAt (h : AtMgA o Z D r' Zp Np cF x) : Prop :=
  match L0.l3At o D Zp Np cF with
  | [] => False
  | dB :: dt => h.LastLeftB dB dt H2K.Member.rWFull (L0.ldAt Zp)

theorem AtMgA.leads3_of_leftBAt (h : AtMgA o Z D r' Zp Np cF x) (L : h.LastLeftBAt) :
    L0.Leads3 o D Zp Np cF (h.toAtMg.mq h.𝔇) h.toAtMg.rc h.free := by
  unfold AtMgA.LastLeftBAt at L
  cases e : L0.l3At o D Zp Np cF with
  | nil => rw [e] at L; exact L.elim
  | cons dB dt => rw [e] at L; exact h.leads3_of_leftB L

end P5J

#print axioms P5J.AtMgA.left_of_leftB
#print axioms P5J.AtMgA.leads3_of_leftB
#print axioms P5J.AtMgA.leads3_of_leftBAt
