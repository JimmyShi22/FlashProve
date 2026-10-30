-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLOwedAtStand.lean

It states no goal. No property of the protocol is claimed.

The three that the tie of the words at the
first chain's closing proximity test asks beside itself (hH, hV, hw, h0 of `wordsTied_L`,
not beneath this file; h1 of `carryRows_of_book`, ClosingWordsBook.lean), AT A STAND of the library's
own thread in front of member 354: at the stand's coins k, the stand's input and every list of
challenges, at the thread's own chain number.

  `first_thread_chain_is_zero`   the thread's chain number is 0
  `valid_at_stand`               at a stand the input meets the letter Vd
  `switch_lot_returns_at_closing_stand`   THE STATEMENT

By what. `switch_lot_returns_at_closing_place` (LotLOwedAtHead.lean); `head_valid`, `sits_head`
(Honest/Thread/FirstHead.lean); the text of `Thr` (Honest/Thread/Thr.lean).

Hypotheses. h: the head. hB: Bk is the maker's book. hG, hf: pl is the finish at the blank ground. hok:
the closing's public test at pl. hpub: the inputs that the thread calls valid pass the filling's
public test. hT: the stand.

Limits.
- hok and hpub are premises: neither is shown here at any segments, layout or filling.
- Of the stand only its last clause is read: the input is valid. The book lends at every run's coins.
- hd is free: the challenges in front of the finish, `heardL (frontOf m)`, are one case; that the
  Script's lot reads just these is not shown here.
- WITH EVERY CITATION OF AtFullSide/K14/SwitchesLend.lean GOES ITS SENTENCE: «handed something» is not
  «handed its own coins, once».
- Full size, the format's second hash function alone.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `valid_at_stand` and `switch_lot_returns_at_closing_stand` bear
this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hB, hG, hf and hok speak of the public files, the book, the ground, the finish and the
  closing's public test: they name no coin. hpub is bound over every input that meets Vd and reads
  its instance: it names no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- In both k, s, m and E are the theorem's own binders. The letters s, m and E (the verifier's state,
  the state of the prover's side, the available tables) stand under hT : `Thr … b k s m E` (in the
  second at border 354): a premise of the first kind: it names k; by its text, at fixed s, m and E
  it can hold at some values of the coins and fail at others.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no
  premise in front that names a coin; the invariant reads them.
- `first_thread_chain_is_zero` names no coin: it bears none.
- What lifts the bar: for s, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (lettersHead Script WtF head_valid)
open ProofFile.Honest.K2.Law (SwitchCoins)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The first thread's chain number is 0.** -/
theorem first_thread_chain_is_zero :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain = 0 := rfl

/-- At a stand the input meets the letter Vd. -/
theorem valid_at_stand {b : ℕ} {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    Vd m.st.input := by
  unfold Thr at hT
  obtain ⟨-, -, -, -, -, -, hV⟩ := hT
  exact ((head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _).1 hV).2

/-- **AT A STAND IN FRONT OF THE CLOSING TEST**: no message of the finish's sending with a main row goes
unsampled; the sending has messages 0 and 1; the frame hands the switch's part coins off the stand's
coins at the thread's chain number; and at them the lot's rows return at the stand's input, at every
list of challenges. -/
theorem switch_lot_returns_at_closing_stand
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub)
    (hok : K2.closingOk K2.freshTable (segs.take pl.link) pl = true)
    (hpub : ∀ v, Vd v → K2.publicOk D lay pl (segs.take pl.link) v.x = true)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E) :
    K2.NoWord (K2.switchSent pl.sizes pl.others) ∧ 0 < (K2.switchSent pl.sizes pl.others).size ∧
      1 < (K2.switchSent pl.sizes pl.others).size ∧
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries,
        K2.handed (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain pl k =
            some c ∧
          ∀ hd : List Fmt.Drawn, ∃ V : ℕ → Johnson.Prover.Send.Rows,
            K2.switchRowsLaid D readers (K2.lotClosingAt lay segs) pl c m.st.input hd = .ok V := by
  obtain ⟨hn, h0, h1, hall⟩ :=
    switch_lot_returns_at_closing_place h.toAtMg hB hG hf D readers lay segs hok
  have hv := hpub _ (valid_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)
  obtain ⟨c, -, hH, -⟩ := hall k m.st.input hv []
  refine ⟨hn, h0, h1, c, hH, fun hd => ?_⟩
  obtain ⟨c', V, hH', hV⟩ := hall k m.st.input hv hd
  obtain rfl : c' = c := Option.some.inj (hH'.symm.trans hH)
  exact ⟨V, hV⟩

end

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.first_thread_chain_is_zero
#print axioms ProofFile.Honest.K12.AtProof.valid_at_stand
#print axioms ProofFile.Honest.K12.AtProof.switch_lot_returns_at_closing_stand
