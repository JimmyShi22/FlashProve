-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/BehindHead.lean: CONDITIONAL.

What is here. THE THREAD's DEBT `Behind` (Honest/Thread/Pays.lean) AT THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4), AT A THREAD OF THE FIRST CHAIN, AT THE PUBLIC FILES' OWN DATA,
ANY PROVER AND A RUN's INPUT (`lettersHead`, Honest/Thread/FirstHead.lean): the seat, the promise
and the fence laid together AT ONE par AND ONE E. Statements and proofs: calls.

  `k4Promise_head`   `K4Promise` at that thread: `k4Promise_at` (Law/PromiseAt.lean) by unfolding.
  `k4Fence_at`   **where the thread stands at a state in front of the member, five of `K4Fence`'s
      six hold of that state**, by `k4Fence_head` (Law/FenceHead.lean); the sixth is asked.
  `k4_behind_head`   **`Behind` at the member**, under the hypotheses named below.

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: this file gives no example (by binder, beside
h: `k4Promise_head`: hH, A, Sx, Sd, Sn, hlk, st, fO, oRun, fG, gRun · `k4Fence_at`: hp, hk, h2, hb,
hT, heard · `k4_behind_head`: hH, A, Sx, Sd, Sn, hlk, st, fO, oRun, fG, gRun, hSit, hM, hb, hb₀,
hKp, hRd, heard): the hypothesis h : AtMgA (`foldFacts_thr`, Honest/Thread/ReachFacts.lean, asks no
more; of h alone: the side library AtFullSide proves, with no hypothesis, that h has a member at one
place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth)); the first eleven hypotheses of the library's `eleven_at_all` at h.𝔇 and
`P5J.At.E Zp cF LFull` (by name: Law/PromiseAll.lean's head; Law/ElevenHead.lean shows them under h
and `LaidK4`); `K4Sits` (Law/Sits.lean) and `K4NoMark` (Law/KeepsStep.lean): Law/SitsAt.lean has
both from one equation on the member; that k is a border of the chain (k ≤ cF.blocksInOrder.length); that the
reply is not heard by this member (b₀ ≠ k + 1); and that `K4KeepsM` (Law/KeepsStep.lean) gives the
clause of `keeps` at the member's place and lets the riders beside the reply's pass. ONE FACT ON THE
STATE IN FRONT STAYS A HYPOTHESIS: heard: what the lookup has heard has the public parameters'
shape: Law/ReadyHead.lean has it out of the promise in front (`k4_heard_head`, under hH, A, Sx and
Sd), and Law/HeadTops.lean lays it in here. The member's step tests no sent value (Law/Hears.lean).
`Behind` speaks only where the thread stands: that it stands at any run is not shown. NOT
COMPLETENESS. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second hash function, alone. A LAW,
NOT A PART: no file that defines a part of the proof file's description may import this one: its
imports reach Johnson/Goal/. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 57 modules under Johnson/Goal/, 6 under Johnson/Bridge/ and 1 whose
name begins Cb.Bridge, and none of the others; what lies behind these is not counted; 46 of the
modules that it reaches have RecCompile in their names, none of them RecCompile's Honest*, Both or
PassH*. An earlier walk, which opened every module that it reached and read import lines and nothing
else, counted 152 modules under Johnson/Goal/, 53 whose name holds RecCompile and 140 under
ThirdParty/. They come with the library's laws, with AtMgA and with `foldFacts_thr`. No statement or
proof of a file under Johnson/Goal/ or ThirdParty/ was read for this file.

Kin. `k4_behind_head` calls `k4_behind_thr` (Law/Behind.lean), which has the debt at any thread. The
same debt under fewer hypotheses, above this file: `k4_behind_top` (Law/HeadTops.lean: heard is
had), `k4_behind_all` (Law/ElevenHead.lean: beside h it asks A, hb₀, hKp and hRd alone). Another
kind's like law at its own members, at the same thread: `k5_owes_all_head_M`
(Honest/K5/Law/HeadM.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PromiseAt
import Johnson.Desc.ProofFile.Honest.K4.Law.FenceHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts

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
open ProofFile.Honest.FirstThread (Script WtF lettersHead foldFacts_thr)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The promise passes, at that thread.** -/
theorem k4Promise_head {E : WideData ProofFile.InstPub} {k m : ℕ} {pl : Place} {par : Par}
    {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
    {layout : Option ByteArray} {n : ℕ} {l : Link S Claim} {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) (Sd : K4OnD h.𝔇 m par n)
    (Sn : K4NamedW h.𝔇 E k m par told n) (hlk : h.𝔇.lk m = some l)
    (st : ∀ u, StatesAt (K9.statesOfLink l) 2 par "front" u ∧
      StatesAt (K9.statesOfLink l) 2 par "back" u)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) :
    K4Promise (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k par
      (K4Fence h.𝔇 E m) :=
  k4Promise_at h _ Q _ _ test carryX item n₁ n₂ _ _ _ hH A Sx Sd Sn hlk st fO oRun fG gRun

/-- **Five of the six facts, where the thread stands in front of the member.** -/
theorem k4Fence_at {b m : ℕ} {pl : Place} (hp : P5J.At.ps[b]? = some pl)
    (hk : pl.link = some m) (h2 : 2 ≤ pl.piece) (hb : b ≤ cF.blocksInOrder.length) {k : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E)
    (heard : ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = (P5J.At.X Zp).y.fo) :
    K4Fence h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) m s := by
  have hm : s.failed = none := by
    have hT' := hT
    unfold Thr at hT'
    obtain ⟨-, -, hF, -⟩ := hT'
    have e : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.mp e
  exact k4Fence_head h (foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (a := (mm.st.input.x.pub, s)) ⟨hb, k, mm, E, hT, rfl⟩ hm hp hk h2 heard

/-- **`Behind` AT THE MEMBER, AT THAT THREAD.** CONDITIONAL: on h; the first eleven hypotheses of
the library's `eleven_at_all`; the seat (`K4Sits`, `K4NoMark`); that k is a border of the chain
(k ≤ cF.blocksInOrder.length); that the reply is not heard by this member (b₀ ≠ k + 1); that `K4KeepsM` gives
the place's clause of `keeps` and lets the riders beside the reply's pass; and heard, wherever the
thread stands in front. -/
theorem k4_behind_head {k m : ℕ} {pl : Place} {par : Par}
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
    (hRd : ∀ v s s', Rd k v s → K4KeepsM s s' → Rd (k + 1) v s')
    (heard : ∀ c s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E →
      ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = (P5J.At.X Zp).y.fo) :
    Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k := by
  refine k4_behind_thr hSit hM
    (k4Promise_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hH A Sx Sd Sn hlk st fO oRun fG gRun)
    (fun c s mm E hT => k4Fence_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w A.here A.link
      (by rw [A.piece]; exact Nat.le_succ 2) hb hT (heard c s mm E hT)) ?_ ?_
  · intro s s' K q hq
    have e : q = pl := Option.some.inj (hq.symm.trans A.here)
    rw [e]
    exact hKp s s' K
  · intro v s s' hr K
    refine ⟨fun hle => ?_, hRd v s s' hr.2 K⟩
    rw [K.1.1.out]
    exact hr.1 (by omega)

end ProofFile.Honest.K4




#print axioms ProofFile.Honest.K4.k4Promise_head
#print axioms ProofFile.Honest.K4.k4Fence_at
#print axioms ProofFile.Honest.K4.k4_behind_head
