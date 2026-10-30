-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/TokOfFine.lean: CONDITIONAL.

What is here. THE LIBRARY's DECODER OF A REQUEST FILE RETURNS (`Meaning.backReq`,
Johnson/Meaning/ReqBytes.lean) WHERE THE VERIFIER's OWN TESTS ON THE REQUEST's WORDS ACCEPT
(`S.reqOk`, Johnson/Desc/First/State.lean, at the first state with the file's words laid and at the
public parameters' numbers: written out here, it is the body of `reqFine`, Law/TokensSeat.lean,
which is not imported) AND THE FILE IS WHOLE WORDS (its size is a multiple of 4). So
`TokensArePrompt k4Tokens` (Law/W/TokPublic.lean, Law/W/TokOfBytes.lean), to which the hypothesis
hTokP of the exchange at the own item of the feed-forward layers' own rounds (sub-protocol K4) comes
down, follows from these two public clauses; and, asked under the thread's parameter Vd of the
thread's own input, they give the binder hTokP of `k4_exchange_tenth` (Law/ExchangeTenth.lean) at
the lot's own reader of the tokens. Why: the decoder asks T + 2 words, each token below V, the two
bounds below T + 1, the first bound below the second, and the reply 0 where the second bound lies
before the window's end; it lays the reply 0 itself; the verifier's tests have T + 2 words, each
token below V and r < e ≤ T. Under the library's hypothesis h the public parameters' T and V are the
reference ones (`T_of`, Johnson/Road/K4/C/JoinPubOf.lean, at `plan_head`; the library's
`P5J.vocab_at_head`).

  `wordsFit_of_reqOk`   the decoder's test on the words, and r < e, from the verifier's tests at the
      reference numbers. General in the state.
  `backReq_of_reqOk`   the decoder returns, at bytes that are whole words.
  `backReq_of_fine`   the same under h, at the public parameters' numbers.
  `tokensPrompt_of_fine`   **`TokensArePrompt k4Tokens xi`.**
  `hTokP_of_fine`   **the binder hTokP, wherever `ThrS` stands.**

Not shown here. hq, hVd: THAT THE VERIFIER's TESTS ACCEPT AT A RUN's INSTANCE, and h4, hW4: THAT ITS
REQUEST FILE IS WHOLE WORDS: hypotheses on public bytes; the second has an owner: the description's
own test on the instance asks it first (`whole_of_okBy`, Law/W/WholeWords.lean; `whole_of_okStart`,
Law/W/WholeAtStart.lean), and the frame's statements over a run take that test's answer as a
hypothesis. h4 CANNOT BE DROPPED FROM `backReq_of_reqOk`: the reader of words (`fileWords`,
OnBytes/Model/Config.lean) reads size / 4 words, so one to three bytes more at a file's end leave
the verifier's tests as they were, and the decoder asks size % 4 = 0 first. h: in the last three
statements the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean); in the first two the
binder h is another: the verifier's test accepts; hs there: the state's request is the file's words.
The side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh, hq and h4 (`backReq_of_fine`, `tokensPrompt_of_fine`) or with Lh,
hVd and hW4 (`hTokP_of_fine`) no example is known to us. Lh (`LaidK4`, Law/SeatedHead.lean): on
public lists and numbers; it is spent for the number of positions alone. THE READER `k4Tokens`
ALONE: that a prover's half is laid over it is a hypothesis of the tops. THAT THE THREAD STANDS AT
ANY RUN. `k4_exchange_own_at` (Law/ExchangeOwnAt.lean) calls `hTokP_of_fine`. No example is written
here, and no test. THE FULL SIZE ALONE, and, but for the first two statements, the format's second
hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with the files that are called. Through `plan_head` and `P5J.vocab_at_head` THE LAST
THREE STATEMENTS REST ON STATEMENTS OF FILES UNDER Johnson/Goal/: `Meaning.P34.pub34_all`
(Law/W/PlanHead.lean's head) and, by the text of Johnson/P5J/VocabAtHead.lean,
`OnBytes.Road.Hd.core_of_scope`, `Meaning.HeadS.sizes_in_scope` and
`Meaning.Emb.emb_public_in_scope`. A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.TokOfBytes
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanHead
import Johnson.Desc.ProofFile.Honest.K4.Law.IndexIs
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Road.K4.C.JoinPubOf
import Johnson.P5J.VocabAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Req)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-! ## 1 The two tests on the words -/

/-- CONDITIONAL: on h. **The decoder's test on the words, and r < e**, from the verifier's tests at
the reference numbers. -/
theorem wordsFit_of_reqOk {s : S} (h : s.reqOk ppref.T ppref.V = true) :
    OnBytes.Flat.WordsFit ppref s.req ∧
      (s.req.getD ppref.T 0).toNat < (s.req.getD (ppref.T + 1) 0).toNat := by
  unfold S.reqOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have eR : s.reqT = ppref.T := by
    unfold S.reqT
    omega
  have h4 : s.rowR < s.rowE ∧ s.rowE ≤ ppref.T := by simpa using h3
  unfold S.rowR S.rowE at h4
  rw [eR] at h4
  have hz : s.tokv.size = ppref.T := by
    unfold S.tokv
    rw [Array.size_map, Array.size_extract]
    omega
  refine ⟨⟨h1, fun t => ?_, by omega, by omega⟩, h4.1⟩
  have ht : t.val < s.tokv.size := by
    rw [hz]
    exact t.isLt
  have k := (Array.all_eq_true.mp h2) t.val ht
  rw [← getD_words s.req s.reqT t.val (by rw [eR]; exact t.isLt) (by omega)]
  show s.tokv.getD t.val 0 < ppref.V
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
  exact of_decide_eq_true k

/-- CONDITIONAL: on hs, h4 and h. **The decoder returns**, at bytes that are whole words. s: any
state whose request's words are the bytes' words. -/
theorem backReq_of_reqOk (b : ByteArray) {s : S} (hs : s.req = Verify.words32 b)
    (h4 : b.size % 4 = 0) (h : s.reqOk ppref.T ppref.V = true) :
    ∃ rq : Req, Meaning.backReq b = some rq := by
  obtain ⟨hW, hlt⟩ := wordsFit_of_reqOk h
  rw [hs] at hW hlt
  unfold Meaning.backReq OnBytes.Flat.unlayB
  dsimp only
  rw [dif_pos ⟨h4, hW⟩, Option.bind_some]
  exact ⟨_, dif_pos ⟨hlt, fun _ => rfl⟩⟩

/-! ## 2 Under h -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh, hq and h4. The decoder returns at an instance's request file. -/
theorem backReq_of_fine (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) (xi : ProofFile.Inst)
    (hq : (Zp.s₀.withReq (Verify.words32 xi.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true)
    (h4 : xi.pub.request.size % 4 = 0) :
    ∃ rq : Req, Meaning.backReq xi.pub.request = some rq := by
  have A := plan_head h Lh
  have e2 : x.2.P.y.T = DF.T := OnBytes.Road.K4.C.T_of A.lay A.sw.p3 A.sized
  rw [Lh.P] at e2
  have eT : Zp.p.X.T = ppref.T := e2
  have eV : Zp.p.X.P.h.V = ppref.V := (P5J.vocab_at_head h.toAtMg).1
  rw [eT, eV] at hq
  exact backReq_of_reqOk xi.pub.request rfl h4 hq

/-- CONDITIONAL: on h, Lh, hq and h4. **THE LOT's OWN READER OF THE TOKENS READS THE PROMPT THAT THE
LIBRARY DECODES**, from two public clauses on the request file. -/
theorem tokensPrompt_of_fine (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) (xi : ProofFile.Inst)
    (hq : (Zp.s₀.withReq (Verify.words32 xi.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true)
    (h4 : xi.pub.request.size % 4 = 0) :
    TokensArePrompt k4Tokens xi := by
  obtain ⟨_, hr⟩ := backReq_of_fine h Lh xi hq h4
  exact tokens_k4 xi hr

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hVd and hW4. **THE BINDER hTokP, WHEREVER `ThrS` STANDS**, at the lot's
own reader of the tokens, from two clauses under Vd. -/
theorem hTokP_of_fine (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hVd : Vd w₁ →
      (Zp.s₀.withReq (Verify.words32 w₁.x.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true)
    (hW4 : Vd w₁ → w₁.x.pub.request.size % 4 = 0) :
    ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      g = 0 → TokensArePrompt k4Tokens mm.st.input.x := by
  intro _ _ mm _ hT _
  obtain ⟨e, hV⟩ := input_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT.1
  rw [e]
  exact tokensPrompt_of_fine h Lh w₁.x (hVd hV) (hW4 hV)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.wordsFit_of_reqOk
#print axioms ProofFile.Honest.K4.W.backReq_of_reqOk
#print axioms ProofFile.Honest.K4.W.backReq_of_fine
#print axioms ProofFile.Honest.K4.W.tokensPrompt_of_fine
#print axioms ProofFile.Honest.K4.W.hTokP_of_fine
