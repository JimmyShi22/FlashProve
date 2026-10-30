-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PromiseAt.lean: CONDITIONAL. One statement with its proof; no
definition.

What is here. THE HYPOTHESIS `K4Promise` (Law/Behind.lean (handed in with this file)) AT THE FIRST
CHAIN's THREAD AT THE PUBLIC FILES' OWN TABLE, NUMBERS AND MEANING (`lettersAt`,
Honest/Thread/FirstAt.lean), its twelve other arguments free. K4 is the sub-protocol of the
feed-forward layers' own rounds.

  `k4Promise_at`   **`K4Promise (lettersAt h …).thread k par (K4Fence h.𝔇 E m)`.**

Called. `k4Promise_all` (Law/PromiseAll.lean (handed in with this file)); its four equations on the
thread's fields hold by unfolding.

Kin. `k4Promise_head` (Law/BehindHead.lean) calls this statement at `lettersHead`'s thread.

Not shown here. This file gives no example of its hypotheses together (by binder, beside h:
`k4Promise_at`: hH, H, Sx, Sd, Sn, hlk, st, fO, oRun, fG, gRun). They are: the hypothesis h : AtMgA
(of h alone: the side library AtFullSide proves, with no hypothesis, that h has a member at one
place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth)), and the first eleven hypotheses of the library's `eleven_at_all` at h's own data
h.𝔇 (by name, with the library's statements for ten of them: Law/PromiseAll.lean's head; THAT h
GIVES WHAT THESE STATEMENTS ASK IS NOT SHOWN HERE: Law/ElevenHead.lean shows it, with `LaidK4` for
the group). `K4Fence h.𝔇 E m`, six facts on the state in front that the promise does not hold, is
the hypothesis's parameter Fence: asked of whoever calls `k4_behind` (Law/Behind.lean), not shown
here: at `lettersHead`'s thread and at the one E `P5J.At.E Zp cF LFull`, Law/BehindHead.lean
(`k4Fence_at`) has five of the six wherever the thread stands in front of the member, and
Law/ReadyHead.lean (`k4_heard_head`) the sixth under hH, AtK4, K4OnX and K4OnD. E is a free
parameter. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second hash function, alone,
as `lettersAt`. A LAW, NOT A PART: no file that defines a part of the proof file's description may
import this one: its imports reach Johnson/Goal/. Following import lines, and stopping unopened at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module
whose name begins Cb.Bridge, its imports reach 17 modules under Johnson/Goal/ and 4 under
Johnson/Bridge/, and none of the others; what lies behind the 21 is not counted; 46 of the modules
that it reaches have RecCompile in their names, none of them RecCompile's Honest*, Both or PassH*.
All these come with `eleven_at_all`'s file and with Johnson/P5J/MgAtAll.lean, where AtMgA is
defined. Earlier walks, which opened every module that they reached and read import lines and
nothing else, counted 47 under Johnson/Goal/, 48 with RecCompile in their names and 140 under
ThirdParty/; they are not made anew. No statement or proof of a file under Johnson/Goal/ or
ThirdParty/ was read for this file. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PromiseAll
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD K4NamedW)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Road.K4.More (PS K4Fence)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Link K9.statesOfLink)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT WideData linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The thread's form and promise pass the accepting decision of the sub-protocol of the
feed-forward layers' rounds, at the public files' own table, numbers and meaning.** -/
theorem k4Promise_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X' : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) {E : WideData ProofFile.InstPub} {k m : ℕ} {pl : Place} {par : Par}
    {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
    {layout : Option ByteArray} {n : ℕ} {l : Link S Claim} {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (H : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) (Sd : K4OnD h.𝔇 m par n)
    (Sn : K4NamedW h.𝔇 E k m par told n) (hlk : h.𝔇.lk m = some l)
    (st : ∀ u, StatesAt (K9.statesOfLink l) 2 par "front" u ∧
      StatesAt (K9.statesOfLink l) 2 par "back" u)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) :
    K4Promise
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread k par
      (K4Fence h.𝔇 E m) :=
  k4Promise_all rfl rfl rfl rfl hH H Sx Sd Sn hlk st fO oRun fG gRun

end ProofFile.Honest.K4



#print axioms ProofFile.Honest.K4.k4Promise_at
