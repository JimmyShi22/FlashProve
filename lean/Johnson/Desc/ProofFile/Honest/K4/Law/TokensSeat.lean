-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokensSeat.lean: CONDITIONAL.

What is here. The test on the request's tokens (`k4TokensFit`, Honest/K4/Part.lean: the request has
the plan's number of tokens, each below the size of the vocabulary; asked in the first group of
layers alone) holds at the tokens that K4's own half reads (`k4Tokens`: all words of the instance's
request file but the last two), given the verifier's own public test on the request's words.
`reqFine Zp p` is that test as a Bool on an instance's public part: the chain's start (`ProofFile.startS`,
Johnson/Desc/ProofFile/Pub.lean) lays the request's words into its first state and keeps that state
only where `S.reqOk` accepts it. The tokens that this state shows are `k4Tokens`, by unfolding
(`tokens_is`); the first two clauses of `S.reqOk` are the two of `k4TokensFit`
(`k4TokensFit_of_reqOk`); under h and `LaidK4` the T and V of the chain's member are the public
part's (`tokensSeat_member`). So the hypothesis hTk of `k4Seated_member` (Law/SeatedMember.lean)
follows, at tokens := `k4Tokens`, from hVd: at the one input w the request passes the verifier's
test (`hTk_of`). WHOEVER HAS `reqFine` AT w PAYS hVd AT EVERY Vd: Law/TokensSeatMark.lean does, from
«the chain's start bears no mark». Where the thread stands in front of the member, `tokensFit_k4`
(Law/TokensIs.lean) has the test itself. In a later group hTk follows from `LaidK4` and g ≠ 0 alone
(`hTk_later`): in eleven of the twelve groups `k4Seated_member` with `hTk_later` needs no hVd. At a
reached state without a mark the test has accepted (`reqFine_reached`; nothing calls it yet): the
start lays a mark else, and no member of the chain takes a mark off. With `hTk_of`: `K4Seated` at
the thread from half, hLk and hVd (`k4Seated_tokens`).

Not shown here. hVd IS A HYPOTHESIS. WITHOUT IT hTk CAN BE FALSE IN THE FIRST GROUP: at Vd := True
and a request file of another length, or with a token from V on. `reqFine` asks more than hTk needs:
also that the covered range is not empty and ends within T. Tests that can fail, on the ends of
`S.reqOk`, stand in Law/ReqEnds.lean. That the thread stands at any run. That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with `LaidK4`, half, hLk and hVd (`k4Seated_tokens`), or with `LaidK4` and
hq (`tokensSeat_member`), no example is known to us. (h here is the hypothesis on `AtMgA`: a
variable of the file, and a binder of `tokensSeat_member`; in `k4TokensFit_of_reqOk` and
`reqFine_reached` the letter h names another hypothesis.) half and hLk: hypotheses, as in
Law/SeatedMember.lean. It reads only the public request; it says nothing about the model's values at
these tokens. `tokensSeat_member`, `hTk_of`, `hTk_later` and `k4Seated_tokens` stand under h or
`LaidK4`: only for the full-size model and the format's second hash function; the six other names are
general.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/, as those of Law/TokensHead.lean and
Law/SeatedMember.lean do.

  `reqFine`   the verifier's test on the request's words that reads no reply, at an instance.
  `tokens_is`   the tokens of the start's state are `k4Tokens`.
  `k4TokensFit_later`, `k4TokensFit_of_reqOk`   the test from nothing; from `S.reqOk`.
  `reqFine_of_start`   where the start bears no mark, the test has accepted.
  `reqFine_reached`   at a reached state without a mark the test has accepted.
  `tokensSeat_member`   **the test at the member's own public data.**
  `hTk_of`, `hTk_later`   **hTk.**
  `k4Seated_tokens`   **`K4Seated` at tokens := `k4Tokens`.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedMember
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- The verifier's tests on the request's words that read no reply, at an instance's public part:
the test under which the chain's start keeps its first state. -/
def reqFine (Zp : ProofFile.Pub) (p : ProofFile.InstPub) : Bool :=
  (Zp.s₀.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V

/-- The tokens that the start's state shows are the lot's own reader's. -/
theorem tokens_is (Zp : ProofFile.Pub) (xi : ProofFile.Inst) :
    (Zp.s₀.withReq (Verify.words32 xi.pub.request)).tokv = k4Tokens xi := rfl

/-- In a later group the test asks nothing. -/
theorem k4TokensFit_later {Q : K4Pub} (tokv : Array Nat) (hg : Q.g ≠ 0) :
    k4TokensFit Q tokv = true := by
  unfold k4TokensFit
  rw [bne_iff_ne.mpr hg]
  rfl

/-- The verifier's tests on the request's words hold the test on the tokens, at every group. -/
theorem k4TokensFit_of_reqOk {s : S} {Q : K4Pub} (h : s.reqOk Q.P.y.T Q.P.V = true) :
    k4TokensFit Q s.tokv = true := by
  unfold VerifiableInference.Desc.First.S.reqOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  have hz : s.tokv.size = Q.P.y.T := by
    unfold VerifiableInference.Desc.First.S.tokv VerifiableInference.Desc.First.S.reqT
    rw [Array.size_map, Array.size_extract, h1]
    omega
  show (Q.g != 0 || (s.tokv.size == Q.P.y.T && s.tokv.all fun t => decide (t < Q.P.V))) = true
  rw [h2, hz, beq_self_eq_true]
  exact Bool.or_true _

/-- Where the chain's start bears no mark, the test has accepted. -/
theorem reqFine_of_start {Zp : ProofFile.Pub} {p : ProofFile.InstPub}
    (h0 : (ProofFile.startS Zp p).failed = none) : reqFine Zp p = true := by
  unfold ProofFile.startS at h0
  dsimp only at h0
  by_cases hq : (Zp.s₀.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true
  · exact hq
  · rw [if_neg hq] at h0
    cases h0

/-- At a reached state without a mark the test has accepted. General in the opening. After the proof
text of `reqOk_reached` (Law/TokensHead.lean). -/
theorem reqFine_reached {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Zq : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zq Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Zq) k a) (hm : a.2.failed = none) :
    reqFine Zq a.1 = true := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  have q : Meaning.K2.ReqStays (ProofFile.startS Zq a.1) a.2 :=
    Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial
      (fun _ _ _ => trivial) hp k hf
  exact reqFine_of_start (q.2 hm)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, `LaidK4` and hq. **THE TEST ON THE TOKENS AT THE MEMBER's OWN PUBLIC DATA AND
THE LOT's OWN READER**, from the verifier's test on the request's words. -/
theorem tokensSeat_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) (xi : ProofFile.Inst)
    (hq : reqFine Zp xi.pub = true) : k4TokensFit (k4PubAt cF k x) (k4Tokens xi) = true := by
  have hV := P5J.vocab_at_head h.toAtMg
  rw [← tokens_is Zp xi]
  refine k4TokensFit_of_reqOk ?_
  show (Zp.s₀.withReq (Verify.words32 xi.pub.request)).reqOk x.2.P.y.T x.2.P.V = true
  rw [Lh.P, hV.2.2, ← hV.1]
  exact hq

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}

include h in
/-- CONDITIONAL on h, `LaidK4` and hVd. **hTk**, from one clause on Vd. -/
theorem hTk_of (Lh : LaidK4 Zp cF k m g x blk) (hVd : Vd w → reqFine Zp w.x.pub = true) :
    Vd w → k4TokensFit (k4PubAt cF k x) (k4Tokens w.x) = true :=
  fun hv => tokensSeat_member h Lh w.x (hVd hv)

/-- CONDITIONAL on `LaidK4` and hg. **hTk in a later group**, from nothing else, at every reader. -/
theorem hTk_later (Lh : LaidK4 Zp cF k m g x blk) (hg : g ≠ 0) (tokens : ProofFile.Inst → Array Nat) :
    Vd w → k4TokensFit (k4PubAt cF k x) (tokens w.x) = true :=
  fun _ => k4TokensFit_later _ (by
    show x.2.g ≠ 0
    rw [Lh.grp]
    exact hg)

/-- CONDITIONAL on h, `LaidK4`, half, hLk and hVd. **`K4Seated` AT THE THREAD, AT THE LOT's OWN
READER OF THE TOKENS.** -/
theorem k4Seated_tokens (Lh : LaidK4 Zp cF k m g x blk) {cells : Tr → Cells}
    {weights : W₀ → Weights} {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens look (k4PubAt cF k x)))
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) = true)
    (hVd : Vd w → reqFine Zp w.x.pub = true) :
    K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      k4Tokens look (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_member h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh half hLk
    (hTk_of h Vd w Lh hVd)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokens_is
#print axioms ProofFile.Honest.K4.k4TokensFit_later
#print axioms ProofFile.Honest.K4.k4TokensFit_of_reqOk
#print axioms ProofFile.Honest.K4.reqFine_of_start
#print axioms ProofFile.Honest.K4.reqFine_reached
#print axioms ProofFile.Honest.K4.tokensSeat_member
#print axioms ProofFile.Honest.K4.hTk_of
#print axioms ProofFile.Honest.K4.hTk_later
#print axioms ProofFile.Honest.K4.k4Seated_tokens
