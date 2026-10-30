-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLOwedReady.lean

It states no goal. No property of the protocol is claimed.

THE PREMISE hready of
`closingTestOldOpenings_at_joinedScript` (LotLTableHold.lean), in its own form, general in the Script: at
EACH stand of the library's own thread in front of member 354 the frame hands the switch's part coins
at the chain number 0, and at them the switch's rows are laid at the stand's input and any front
stretch of the challenges heard. One theorem: a call.

  `switch_lot_ready_at_every_closing_stand`

By what. `switch_lot_returns_at_closing_stand` (LotLOwedAtStand.lean).

Hypotheses. h, hB, hG, hf, hok, hpub: as there.

Limits. Those of LotLOwedAtStand.lean. At the lot's own closing `lotClosingAt lay segs` alone. So where
these hold the switch's table (`K2.switchTableAt`) is not the table without a word at a stand: by
`table_of_rows` (K2/Law/RowsTie.lean), not called here. Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `switch_lot_ready_at_every_closing_stand` bears this label; the
rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hB, hG, hf and hok speak of the public files, the book, the ground, the finish and the
  closing's public test: they name no coin. hpub is bound over every input that meets Vd and reads
  its instance: it names no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- A run's coins k are bound inside the end. Beside k it binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `Thr … 354 k st m
  E`: a premise of the first kind: it names k; by its text, at fixed st, m and E it can hold at some
  values of the coins and fail at others.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no
  premise in front that names a coin; the invariant reads them.
- What lifts the bar: for st, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K2.Law (SwitchCoins)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At each stand in front of the closing test the switch's lot is ready.** n: how many of the
challenges heard the lot reads. -/
theorem switch_lot_ready_at_every_closing_stand
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub)
    (hok : K2.closingOk K2.freshTable (segs.take pl.link) pl = true)
    (hpub : ∀ v, Vd v → K2.publicOk D lay pl (segs.take pl.link) v.x = true) (n : ℕ) :
    ∀ k st m E, Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st m E →
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries, K2.handed 0 pl k = some c ∧
        ∃ V : ℕ → Johnson.Prover.Send.Rows,
          K2.switchRowsLaid D readers (K2.lotClosingAt lay segs) pl c m.st.input
            (m.st.heard.take n) = .ok V := by
  intro k st m E hT
  obtain ⟨-, -, -, c, hH, hall⟩ := switch_lot_returns_at_closing_stand h H Q test carryX item n₁ n₂
    b₀ Vd Rd Kp w hB hG hf D readers lay segs hok hpub hT
  exact ⟨c, hH, hall _⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.switch_lot_ready_at_every_closing_stand
