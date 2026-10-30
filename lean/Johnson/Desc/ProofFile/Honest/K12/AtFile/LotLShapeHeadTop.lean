-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeHeadTop.lean

It states no goal. No property of the protocol is claimed.

acceptedS_stands_L's PREMISE hShape
(not beneath this file), TO THE LETTER, UNDER THE HEAD ALONE: at every stand of the thread with Said in front
of the first chain's closing proximity test (member 354), at the record that enterFinish returns, the two public tests
on the shape (frontFiveB, frontPlainB) say yes. Calls.

  closingStateLaid_at_reach          the form ClosingStateLaid at every reached, unmarked state at which the promise's
                                     test on the members says yes
  closingRecordLaid_at_every_stand   hlaid of closingShapeTests_at_stand, with no premise left but the head
  closingShapeTests_under_the_head   hShape

By what. closingGroupLaid_at_reach (LotLShapeAtReach.lean: what the last code switch lays, under the head, at a raw
reach) · closingRecordLaid_at_stand, closingShapeTests_of_state_form (LotLShapeHeadStand.lean).

IMPORTS OF Johnson.Top.H0.*: none by name (through LotLShapeAtReach.lean: Johnson.Top.H0.Tw.K2C.FinFront, named in
LotLShapeFinish.lean's head; through LotLShapeBoolsKinds.lean: see its head).

Hypotheses. h: the head. hG, hf: the plan's finish at the blank ground.

Limits.
- THAT A STAND IS REACHED IS NOT SAID: where the thread stands nowhere at 354 the statement says nothing.
- Two public tests on a shape pass: nothing on values, nothing on what a prover sends.
- Closed lines by Lean's kernel lie beneath. Full size, the format's second hash function alone.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingRecordLaid_at_every_stand` and
`closingShapeTests_under_the_head` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hG and hf speak of the public files, the ground and the finish: they name no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- A run's coins k are bound inside the end of each. Beside k it binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `ThrS … 354 k st m
  E`: a premise of the first kind: it names k; by its text, at fixed st, m and E it can hold at some
  values of the coins and fail at others. The record R under `enterFinish st = .ok R` names no coin.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, Said) stand under no
  premise in front that names a coin; the invariant reads them.
- `closingStateLaid_at_reach` speaks of a reach, which names no coin: it bears none.
- What lifts the bar: for st, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeHeadStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S membersHeld)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K.Member (codesFull)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12 (frontFiveB frontPlainB)
open ProofFile.Honest.K12.AtProof (finishAt parL)
open ProofFile.Honest.Sh (testSh thinSh)
open P5J (AtMg AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The form at every reached, unmarked state at which the promise's test on the members says yes.** -/
theorem closingStateLaid_at_reach (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) (p : ProofFile.InstPub) (s : S)
    (reached : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s)) (unmarked : s.failed = none)
    (members : membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true) : ClosingStateLaid s :=
  closingGroupLaid_at_reach h reached unmarked members

/-- **hlaid of closingShapeTests_at_stand, under the head alone.** -/
theorem closingRecordLaid_at_every_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ k st m E R,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R → ClosingRecordLaid R :=
  closingRecordLaid_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (closingStateLaid_at_reach h.toAtMg)

/-- **acceptedS_stands_L's premise hShape, under the head alone.** -/
theorem closingShapeTests_under_the_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {pl : K2.SwitchPlace}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hf : finishAt Zp G = some pl) :
    ∀ k st m E R,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      frontFiveB (H2U.p12OfMade Zp.made) codesFull (testSh R) = true ∧
        frontPlainB (H2U.p12OfMade Zp.made) (parL pl) (thinSh R) = true :=
  closingShapeTests_of_state_form h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hG hf
    (closingStateLaid_at_reach h.toAtMg)

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.closingStateLaid_at_reach
#print axioms ProofFile.Honest.K12.LotL.closingRecordLaid_at_every_stand
#print axioms ProofFile.Honest.K12.LotL.closingShapeTests_under_the_head
