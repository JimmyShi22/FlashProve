-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokensHead.lean: CONDITIONAL.

What is here. WHEREVER THE FIRST CHAIN's THREAD STANDS IN FRONT OF THE MEMBER OF THE FEED-FORWARD
LAYERS' ROUNDS, THE TOKENS THAT THE VERIFIER's STATE HOLDS PASS `tokensFit`: they are T, each below
the size of the vocabulary. Under h : AtMgA and `LaidK4` alone. Why: the chain's own start lays the
request's words only where the verifier's tests on them accept, and marks the state else; no member
turns the words or takes a mark away (the library's `ReqStays`); the thread's state is reached and
bears no mark. So the hypothesis hTok of `k4_accepted_all` (Law/ElevenHead.lean) and of what calls
it falls. Statements and proofs; the first after the proof text of the library's `req_at_open`
(Johnson/LTPileR/AtGate.lean) and `req_start` (Johnson/LTPileR/ReqSeat.lean).

Not shown here. THAT THE THREAD STANDS AT ANY RUN. THAT h CAN HOLD: the side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). OF h TOGETHER WITH hT,
that the thread stands, NO EXAMPLE IS KNOWN TO US (`LaidK4` asks nothing beyond h: `laid_head`,
Law/SeatedHead.lean, at the library's `atK4_full`). Nothing on what the tokens are worth, nor that
they are the honest side's. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second hash function,
alone. A LAW, NOT A PART: no file that defines a part of the proof file's description may import
this one: its imports reach Johnson/Goal/ (through Honest/Thread/ReachFacts.lean and
Johnson/P5J/VocabAtHead.lean); no statement of a file there is called by name in it, but
`tokens_head` RESTS, through the library's `vocab_at_head`, on statements there. Transitive imports,
by a program's walk over import lines. Opening every module that it reaches: 152 modules under
Johnson/Goal/, 53 whose name holds RecCompile, 140 under ThirdParty/. Stopping unopened at
Johnson/Goal/, Johnson/D/ and ThirdParty/ (so these are floors): 58 under Johnson/Goal/, 46 whose
name holds RecCompile, 2 under ThirdParty/. By both: none under Johnson/D/; none of RecCompile's
Honest*, Both or PassH*. No property is claimed.

  `reqOk_reached`   at a reached state without a mark the verifier's tests on the request's words
      accept. General in the opening.
  `tokensFit_of_reqOk`   these tests hold `tokensFit`, at every group.
  `tokens_head`   **`tokensFit` wherever the thread stands in front of the member.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB
import Johnson.LTPileR.AtGate
import Johnson.P5J.VocabAtHead
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_reach)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- CONDITIONAL: on O, hp, h and hm (this h is the statement's own: that the state is reached). **At
a reached state without a mark the verifier's tests on the request's words accept.** -/
theorem reqOk_reached {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Zq : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zq Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Zq) k a) (hm : a.2.failed = none) :
    a.2.reqOk Zq.p.X.T Zq.p.X.P.h.V = true := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  have q : Meaning.K2.ReqStays (ProofFile.startS Zq a.1) a.2 :=
    Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial
      (fun _ _ _ => trivial) hp k hf
  have h0 := q.2 hm
  have s0 : (ProofFile.startS Zq a.1).reqOk Zq.p.X.T Zq.p.X.P.h.V = true := by
    unfold ProofFile.startS at h0 ⊢
    dsimp only at h0 ⊢
    split
    · rename_i hq
      exact hq
    · rename_i hq
      rw [if_neg hq] at h0
      cases h0
  unfold VerifiableInference.Desc.First.S.reqOk VerifiableInference.Desc.First.S.tokv
    VerifiableInference.Desc.First.S.rowR VerifiableInference.Desc.First.S.rowE
    VerifiableInference.Desc.First.S.reqT at s0 ⊢
  rw [q.1]
  exact s0

/-- **These tests hold `tokensFit`**, at every group. -/
theorem tokensFit_of_reqOk {s : S} {P : Layer.Pub} {g : Nat} (h : s.reqOk P.y.T P.V = true) :
    tokensFit { P with tokv := seatS.tokv s } g = true := by
  unfold VerifiableInference.Desc.First.S.reqOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  have hz : s.tokv.size = P.y.T := by
    unfold VerifiableInference.Desc.First.S.tokv VerifiableInference.Desc.First.S.reqT
    rw [Array.size_map, Array.size_extract, h1]
    omega
  show (g != 0 || (s.tokv.size == P.y.T && s.tokv.all fun t => decide (t < P.V))) = true
  rw [h2, hz, beq_self_eq_true]
  exact Bool.or_true _

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h and `LaidK4`. **`tokensFit` WHEREVER THE THREAD STANDS IN FRONT OF THE
MEMBER.** -/
theorem tokens_head {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E) :
    tokensFit { (parOf x).P with tokv := seatS.tokv s } (parOf x).g = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb : k ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 Lh.member).1
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -⟩ := hT'
  have hm : s.failed = none := by
    have e : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.mp e
  have ok := reqOk_reached O (P5J.flat_ok h.toAtMg) k _ hr hm
  have hV := P5J.vocab_at_head h.toAtMg
  refine tokensFit_of_reqOk ?_
  show s.reqOk x.2.P.y.T x.2.P.V = true
  rw [Lh.P, hV.2.2, ← hV.1]
  exact ok

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.reqOk_reached
#print axioms ProofFile.Honest.K4.tokensFit_of_reqOk
#print axioms ProofFile.Honest.K4.tokens_head
