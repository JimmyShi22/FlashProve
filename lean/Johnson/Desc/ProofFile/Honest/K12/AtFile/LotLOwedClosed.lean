-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLOwedClosed.lean

It states no goal. No property of the protocol is claimed.

The two tops of LotLOwedAtHead.lean and
LotLOwedAtStand.lean WITH THE CLOSING's PUBLIC TEST PAID: at the plan's own segments
(`K2.segmentsOf Zp G`), under the head at the format's second hash function. Of the premises of the two tops hok
is gone; the filling's public test at the instance stays.

  `closing_test_passes_at_finish`   `closingOk` says yes at the finish, at the segments in front of it
  `switch_lot_returns_at_closing_place_with_closing_paid`   the three at the real closing place
  `switch_lot_returns_at_closing_stand_with_closing_paid`   the three at a stand in front of member 354

By what. `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean: 25 closed
facts by Lean's kernel beneath it) at the opening that the head holds (`LaidAt.opened`), whose ground
is the blank one (`IM.Open.blank`, Johnson/IMR/SeatOpen.lean).

Hypotheses. h: the head. hB: Bk is the maker's book. hG, hf: pl is the finish at the blank ground. At
the place: the filling's public test at the input's public instance. At the stand: hpub, the inputs
that the thread calls valid pass that test; hT, the stand.

Limits.
- hpub is a premise: shown here at no layout and no filling; D, readers and lay are letters.
- All limits of the two files beneath stand, the sentence on AtFullSide/K14/SwitchesLend.lean among
  them: «handed something» is not «handed its own coins, once».
- Full size, the format's second hash function alone.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `switch_lot_returns_at_closing_stand_with_closing_paid` bears this
label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hB, hG and hf speak of the public files, the book, the ground and the finish: they name no
  coin. hpub is bound over every input that meets Vd and reads its instance: it names no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- There k, s, m and E are the theorem's own binders. The letters s, m and E (the verifier's state,
  the state of the prover's side, the available tables) stand under hT : `Thr … 354 k s m E`: a
  premise of the first kind: it names k; by its text, at fixed s, m and E it can hold at some values
  of the coins and fail at others.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no
  premise in front that names a coin; the invariant reads them.
- `closing_test_passes_at_finish` names no coin.
  `switch_lot_returns_at_closing_place_with_closing_paid` binds k and w by "for all" and ties no
  letter; its inner premise `K2.publicOk … w.x = true` reads the input's instance. They bear none.
- What lifts the bar: for s, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedAtStand
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

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

/-- **The closing's public test says yes at the finish**, at the plan's segments in front of it. -/
theorem closing_test_passes_at_finish (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) :
    K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take pl.link) pl = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact K2.Law.closing_at_head h O pl (List.mem_of_find?_eq_some hf)

/-- **THE THREE AT THE REAL CLOSING PLACE, THE CLOSING's TEST PAID.** -/
theorem switch_lot_returns_at_closing_place_with_closing_paid {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF)
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) :
    K2.NoWord (K2.switchSent pl.sizes pl.others) ∧ 0 < (K2.switchSent pl.sizes pl.others).size ∧
      1 < (K2.switchSent pl.sizes pl.others).size ∧
      ∀ (k : Coins Bk) (w : Local W₀ Rc Xi Tr),
        K2.publicOk D lay pl ((K2.segmentsOf Zp G).take pl.link) w.x = true →
          ∀ hd : List Fmt.Drawn,
            ∃ (c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries)
              (V : ℕ → Johnson.Prover.Send.Rows), K2.handed 0 pl k = some c ∧
                K2.switchRowsLaid D readers (K2.lotClosingAt lay (K2.segmentsOf Zp G)) pl c w hd =
                  .ok V :=
  switch_lot_returns_at_closing_place h hB hG hf D readers lay (K2.segmentsOf Zp G)
    (closing_test_passes_at_finish h hG hf)

/-- **THE THREE AT A STAND IN FRONT OF THE CLOSING TEST, THE CLOSING's TEST PAID.** -/
theorem switch_lot_returns_at_closing_stand_with_closing_paid
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
    (hpub : ∀ v, Vd v → K2.publicOk D lay pl ((K2.segmentsOf Zp G).take pl.link) v.x = true)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E) :
    K2.NoWord (K2.switchSent pl.sizes pl.others) ∧ 0 < (K2.switchSent pl.sizes pl.others).size ∧
      1 < (K2.switchSent pl.sizes pl.others).size ∧
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries,
        K2.handed (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain pl k =
            some c ∧
          ∀ hd : List Fmt.Drawn, ∃ V : ℕ → Johnson.Prover.Send.Rows,
            K2.switchRowsLaid D readers (K2.lotClosingAt lay (K2.segmentsOf Zp G)) pl c m.st.input
              hd = .ok V :=
  switch_lot_returns_at_closing_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hB hG hf D readers
    lay (K2.segmentsOf Zp G) (closing_test_passes_at_finish h.toAtMg hG hf) hpub hT

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closing_test_passes_at_finish
#print axioms ProofFile.Honest.K12.AtProof.switch_lot_returns_at_closing_place_with_closing_paid
#print axioms ProofFile.Honest.K12.AtProof.switch_lot_returns_at_closing_stand_with_closing_paid
