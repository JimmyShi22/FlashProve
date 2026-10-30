-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/HeadTops.lean: CONDITIONAL.

What is here. THE THREAD's DEBT `Behind` AT THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4), AT A THREAD OF THE FIRST CHAIN, AT THE PUBLIC FILES' OWN DATA, ANY PROVER AND A
RUN's INPUT (`lettersHead`, Honest/Thread/FirstHead.lean), WITH THE SIXTH FACT OF `K4Fence` PAID OUT
OF THE PROMISE IN FRONT: `k4_behind_head` (Law/BehindHead.lean) called with `k4_heard_head`
(Law/ReadyHead.lean). One statement with its proof: a call.

  `k4_behind_top`   **`Behind` at the member.**

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: this file gives no example (by binder, beside
h: `k4_behind_top`: hH, A, Sx, Sd, Sn, hlk, st, fO, oRun, fG, gRun, hSit, hM, hb, hb₀, hKp, hRd).
They are those of `k4_behind_head` less heard: NOTHING IS ASKED OF WHAT THE LOOKUP HAS HEARD. The
member's step tests no sent value (Law/Hears.lean). THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`,
the format's second hash function, alone. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: its imports reach Johnson/Goal/. Following import lines, and
stopping unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/
and at every module whose name begins Cb.Bridge, its imports reach 57 modules under Johnson/Goal/, 6
under Johnson/Bridge/ and 1 whose name begins Cb.Bridge, and none of the others; what lies behind
these is not counted; 46 of the modules that it reaches have RecCompile in their names, none of them
RecCompile's Honest*, Both or PassH*. An earlier walk, which opened every module that it reached,
counted 152 modules under Johnson/Goal/, 53 whose name holds RecCompile and 140 under ThirdParty/;
another, which stopped unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/ alone, met 2 modules
under ThirdParty/. `Behind` speaks only where the thread stands: that it stands at any run is not
shown. NOT COMPLETENESS.

Kin. The same debt under fewer hypotheses: `k4_behind_all` (Law/ElevenHead.lean: beside h it asks A,
hb₀, hKp and hRd alone). Another kind's like law at its own members, at the same thread:
`k5_owes_all_head_M` (Honest/K5/Law/HeadM.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.BehindHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ReadyHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD K4NamedW)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Link K9.statesOfLink)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`Behind` AT THE MEMBER, WITH NOTHING ASKED OF WHAT THE LOOKUP HAS HEARD.** CONDITIONAL. -/
theorem k4_behind_top {k m : ℕ} {pl : Place} {par : Par}
    {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
    {layout : Option ByteArray} {n : ℕ} {l : Link S Claim} {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) (Sd : K4OnD h.𝔇 m par n)
    (Sn : K4NamedW h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) k m par told n)
    (hlk : h.𝔇.lk m = some l)
    (st : ∀ u, StatesAt (K9.statesOfLink l) 2 par "front" u ∧
      StatesAt (K9.statesOfLink l) 2 par "back" u)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG)
    (hSit : K4Sits (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k par)
    (hM : K4NoMark (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k)
    (hb : k ≤ cF.blocksInOrder.length) (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp pl s s')
    (hRd : ∀ v s s', Rd k v s → K4KeepsM s s' → Rd (k + 1) v s') :
    Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k :=
  k4_behind_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hH A Sx Sd Sn hlk st fO oRun fG gRun
    hSit hM hb hb₀ hKp hRd
    (k4_heard_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A Sx Sd)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_behind_top
