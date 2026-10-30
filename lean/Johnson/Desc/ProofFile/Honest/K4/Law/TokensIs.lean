-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokensIs.lean: CONDITIONAL.

What is here. WHEREVER THE FIRST CHAIN's THREAD STANDS (`lettersHead`), THE TOKENS THAT THE
VERIFIER's STATE HOLDS ARE THE INSTANCE's: `s.tokv = k4Tokens mm.st.input.x`, under h : AtMgA alone,
at every border of the chain. It is the hypothesis `K4TokensTieAt` (Law/ScriptAt.lean) at tokens :=
`k4Tokens` (Honest/K4/Part.lean), which is what K4's lot lays. Why: at a reached state without a
mark the state's words are the request file's (the library's `req_at_open`,
Johnson/LTPileR/AtGate.lean), and both sides take all words but the last two. With `tokens_head`
(Law/TokensHead.lean): in front of the member of the feed-forward layers' rounds the honest side's
own test `k4TokensFit` accepts these tokens at the member's public data. Statements and proofs.

Not shown here. THAT THE THREAD STANDS AT ANY RUN. THAT h CAN HOLD: the side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). OF h TOGETHER WITH hT,
that the thread stands, NO EXAMPLE IS KNOWN TO US (`LaidK4` asks nothing beyond h: `laid_head`,
Law/SeatedHead.lean, at the library's `atK4_full`; hb: that k is a border of the chain). Nothing
where another function is laid for tokens. `k4TokensFit` is shown where the thread stands, not at
every valid input. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second hash function, alone. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach Johnson/Goal/. Transitive imports, by a program's walk over import lines. Opening
every module that it reaches: 175 modules under Johnson/Goal/, 53 whose name holds RecCompile, 140
under ThirdParty/. Stopping unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/ (so these are
floors): 71 under Johnson/Goal/, 46 whose name holds RecCompile, 2 under ThirdParty/. By both: none
under Johnson/D/; none of RecCompile's Honest*, Both or PassH*. No property is claimed.

  `tokv_head`   **the state's tokens are the instance's.**
  `tokensTie_head`   the same in the letters of `K4TokensTieAt`.
  `tokensFit_k4`   **`k4TokensFit` at the member's public data and the instance's tokens.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ScriptAt
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_reach)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h. **THE STATE's TOKENS ARE THE INSTANCE's**, wherever the thread stands. -/
theorem tokv_head {k : ℕ} (hb : k ≤ cF.blocksInOrder.length) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E) :
    s.tokv = k4Tokens mm.st.input.x := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -⟩ := hT'
  have hm : s.failed = none := by
    have e : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.mp e
  have e : s.req = Verify.words32 mm.st.input.x.pub.request :=
    Meaning.K2.req_at_open O (P5J.flat_ok h.toAtMg) 0 k _ hr hm
  unfold VerifiableInference.Desc.First.S.tokv VerifiableInference.Desc.First.S.reqT k4Tokens
  rw [e]

/-- The same in the letters of `K4TokensTieAt`. -/
theorem tokensTie_head {k : ℕ} (hb : k ≤ cF.blocksInOrder.length) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E) :
    K4TokensTieAt k4Tokens s mm :=
  tokv_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT

/-- CONDITIONAL: on h and `LaidK4`. **`k4TokensFit` AT THE MEMBER's PUBLIC DATA AND THE INSTANCE's
TOKENS**, wherever the thread stands in front of the member. -/
theorem tokensFit_k4 {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E) :
    k4TokensFit (k4PubAt cF k x) (k4Tokens mm.st.input.x) = true := by
  have hb : k ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 Lh.member).1
  rw [← tokv_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT]
  exact tokens_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hT

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokv_head
#print axioms ProofFile.Honest.K4.tokensTie_head
#print axioms ProofFile.Honest.K4.tokensFit_k4
