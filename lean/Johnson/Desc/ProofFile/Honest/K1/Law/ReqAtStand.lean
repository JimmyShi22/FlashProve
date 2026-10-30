-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ReqAtStand.lean: AT A STAND OF THE
THREAD UNDER THE LIBRARY's HEAD: THE VERIFIER's STATE's REQUEST's WORDS ARE THE INPUT's INSTANCE's;
SO THE STATE's COVERED POSITIONS AND THE FILLER's HAVE ONE FIELD hOnC, AND THE MAKER OF THE OUTPUT
HEAD's TABLES GIVES ONE ANSWER AT BOTH. Six statements and their proofs. No definition. Public: of
the input the instance's public request alone is named; no witness, no Script's field, no coin is
read: the run's coins stand as a bound letter of the thread's stand.

  coveredAt_cost  where coveredAt returns at a reply y it returns at every entry of the
                  vocabulary, with the same hOnC
  coveredAt_tok   where coveredAt returns at y: y < V
  tables_cost     ReadsQuiet.tables reads of the covered positions the field hOnC alone
  req_at_stand    under h and Thr at lettersHead's thread at b: s.req = Verify.words32
                  m.st.input.x.pub.request
  cov_at_stand    so where s.covered returns c: covOf returns some c' with c'.hOnC = c.hOnC
  tables_at_stand so ReadsQuiet.tables at the filler's cover, its default arm included, is
                  ReadsQuiet.tables at c

WHAT IT IS FOR. The last clause of HeadPlanS
(Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHeadAtS.lean) speaks of the maker's tables at the
filler's cover; the state's record behind the reads (HeadRecord.lean) has the tables at the state's
own cover. This file joins the two covers.

KIN: NOTHING NEW IS SAID OF "EVERY MEMBER's YES KEEPS THE REQUEST's WORDS": IT LIES:
Meaning.K2.flat_req, reach_req, req_start (Johnson/LTPileR/ReqSeat.lean); req_kept_at,
coveredAt_same (Johnson/AtFull/Shape/ReqAtHead.lean); flat_req_head, fold_req_head
(Johnson/Desc/ProofFile/Honest/K13/FrontAtHead.lean); the field reqIs of FoldFacts
(Johnson/Desc/First/FoldFacts.lean), which reach_facts has at the head and
Johnson/Desc/ProofFile/Honest/K11/ClaimAtHead.lean spends at one border. req_at_stand is that field
at the thread's stand. NEAR KIN OF coveredAt_cost: coveredAt_on
(Johnson/Desc/ProofFile/Honest/K11/ClaimOfQuiet.lean: a row): the same form at the
field hOn, at two states with one request: no twin (another field); cov_at_stand's road
(coveredAt_cost, then coveredAt_same) is its road in two steps.
SISTERS OF tables_cost ON THE OTHER ARGUMENT: tables_nine, tables_fields
(Johnson/Desc/ProofFile/Honest/K6/HeardWhole.lean: sealed): which fields of what was heard the maker
reads.

THE PREMISES AT THE STAND ARE FOUR, EACH A FORM THAT STANDS ALREADY. h : P5J.AtMgA: the library's
head (Johnson/P5J/MgAtAll.lean: sealed): A HYPOTHESIS. hb : b ≤ cF.blocksInOrder.length and hT : Thr at
lettersHead's thread: thr_reach's own two, to the letter (a row). hc : S.covered returns: the sealed
function's return, at the filler's two letters G.W.T and G.W.P.h.V. TWO THINGS THAT THE ROAD WANTS
ARE NOT ASKED: "no mark at s", which reqIs asks: head_noMark (a row) has it from hT; "the vocabulary
is not empty": coveredAt_tok has it from hc.

Limits. That Thr holds at any state is not said. hc CAN HOLD ONLY BEHIND THE HEARD REPLY: in front
of it S.covered refuses, and the two last statements say nothing. AT lettersHead ALONE: no letter L.
That the quiet block's plan has the filler's T and V is not said here. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BookFacts
import Johnson.AtFull.Shape.ReqAtHead
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 Two lemmas on public functions -/

/-- **WHICH POSITIONS HAVE A COST DOES NOT HANG ON THE REPLY**: where coveredAt
(Johnson/Desc/First/State.lean) returns at a reply y, it returns at every entry y' of the
vocabulary, with the same field hOnC. -/
theorem coveredAt_cost {T V y y' : ℕ} {s : S} {c : Head.Covered}
    (h : s.coveredAt T V y = .ok c) (hy' : y' < V) :
    ∃ c', s.coveredAt T V y' = .ok c' ∧ c'.hOnC = c.hOnC := by
  unfold S.coveredAt at h ⊢
  dsimp only at h ⊢
  rw [show decide (y' < V) = true from decide_eq_true hy']
  revert h
  generalize decide (y < V) = b1
  generalize (s.req.size == T + 2) = b2
  generalize (((s.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = b3
  generalize (decide ((s.req.getD T 0).toNat ≥ (s.req.getD (T + 1) 0).toNat) ||
    decide ((s.req.getD (T + 1) 0).toNat > T)) = b4
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> intro h <;>
    first
      | (exfalso
         revert h
         simp
         done)
      | (refine ⟨_, rfl, ?_⟩
         have h' := Except.ok.inj h
         rw [← h'])

/-- Where coveredAt returns, the reply is an entry of the vocabulary. -/
theorem coveredAt_tok {T V y : ℕ} {s : S} {c : Head.Covered} (h : s.coveredAt T V y = .ok c) :
    y < V := by
  by_contra hn
  unfold S.coveredAt at h
  dsimp only at h
  rw [show decide (y < V) = false from decide_eq_false hn] at h
  simp at h

/-- **OF THE COVERED POSITIONS THE MAKER OF THE HEAD's TABLES READS hOnC ALONE.** -/
theorem tables_cost (hS : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) {c c' : Head.Covered}
    (e : c'.hOnC = c.hOnC) (x : Head.Heard) :
    ReadsQuiet.tables hS L hp c' x = ReadsQuiet.tables hS L hp c x := by
  have hw : ∀ z, Head.costWeights c' z = Head.costWeights c z := fun z => by
    unfold Head.costWeights
    rw [e]
  unfold ReadsQuiet.tables
  simp only [hw]

/-! ## 2 At a stand of the thread, under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT A STAND OF THE THREAD THE STATE's REQUEST's WORDS ARE THE INPUT's INSTANCE's.** Three
calls: thr_reach (Johnson/Desc/ProofFile/Honest/Thread/ReachFacts.lean), head_noMark and the field
reqIs of reach_facts (Johnson/Desc/ProofFile/Honest/Thread/BookFacts.lean). -/
theorem req_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.req = Verify.words32 m.st.input.x.pub.request :=
  (reach_facts h).reqIs b (m.st.input.x.pub, s)
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)

/-- **SO WHERE THE STATE's COVERED POSITIONS RETURN, THE FILLER's DO, WITH THE SAME hOnC.** The
state's: S.covered: coveredAt at the heard reply. The filler's: covOf (Johnson/HonestTrace/
U3Rows.lean): coveredAt at the stand-in 0, at any first state with the instance's request's words
laid in. -/
theorem cov_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) {c : Head.Covered}
    (hc : s.covered G.W.T G.W.P.h.V = .ok c) :
    ∃ c', OnBytes.HonestTrace.U3.covOf Zq G m.st.input.x = .ok c' ∧ c'.hOnC = c.hOnC := by
  have e := req_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  unfold S.covered at hc
  cases hy : s.replyTok? with
  | none =>
    rw [hy] at hc
    cases hc
  | some y =>
    rw [hy] at hc
    obtain ⟨c', h1, h2⟩ := coveredAt_cost (y' := 0) hc
      (Nat.lt_of_le_of_lt (Nat.zero_le y) (coveredAt_tok hc))
    refine ⟨c', ?_, h2⟩
    unfold OnBytes.HonestTrace.U3.covOf
    rw [Johnson.AtFull.Shape.coveredAt_same (s := s)
      (show (Zq.s₀.withReq (Verify.words32 m.st.input.x.pub.request)).req = s.req from e.symm)]
    exact h1

/-- **AND THE MAKER OF THE HEAD's TABLES GIVES ONE ANSWER AT BOTH**, the filler's default arm
included: it is not met. -/
theorem tables_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) {c : Head.Covered}
    (hc : s.covered G.W.T G.W.P.h.V = .ok c) (hS : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2)
    (y : Head.Heard) :
    ReadsQuiet.tables hS L hp
        ((OnBytes.HonestTrace.U3.covOf Zq G m.st.input.x).toOption.getD default) y =
      ReadsQuiet.tables hS L hp c y := by
  obtain ⟨c', h1, h2⟩ :=
    cov_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT Zq G hc
  rw [h1]
  exact tables_cost hS L hp h2 y

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.coveredAt_cost
#print axioms ProofFile.Honest.FirstThread.coveredAt_tok
#print axioms ProofFile.Honest.FirstThread.tables_cost
#print axioms ProofFile.Honest.FirstThread.req_at_stand
#print axioms ProofFile.Honest.FirstThread.cov_at_stand
#print axioms ProofFile.Honest.FirstThread.tables_at_stand
