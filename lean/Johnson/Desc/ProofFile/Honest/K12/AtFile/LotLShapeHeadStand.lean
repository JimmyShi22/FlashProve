-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeHeadStand.lean

It states no goal. No property of the protocol is claimed.

THE JOIN AT THE STAND: from "the state in front of
the first chain's closing proximity test bears what the last code switch lays" (a form on the state, at terms of the
written shape and codes, with the number of open rows under ∃) to ClosingRecordLaid (LotLShapeBoolsStand.lean) at the
record that enterFinish returns, at every stand of the thread at 354: the premise hlaid of
closingShapeTests_at_stand; and so acceptedS_stands_L's premise hShape.

  ClosingStateLaid                  THE FORM on a state of the first chain
  closingRecordLaid_of_state        form · the promise's test on the open rows · enterFinish returns R ⟹
                                    ClosingRecordLaid R
  closingRecordLaid_at_stand        at every stand, from the form at every reached, unmarked state at which the
                                    promise's test on the members says yes
  closingShapeTests_of_state_form   hShape from that one premise

By what. closingGroupLaid_written (LotLShapeHeadRecords.lean) · closingRows_on_shape (LotLShapeBoolsKinds.lean: the
kinds, from rowsHeld: so the number under ∃ is 657) ·
enterFinish_ok (Johnson/Desc/K12/SeatLaws.lean) · thr_reach (Honest/Thread/ReachFacts.lean) · head_len
(Honest/Thread/SteppedYes.lean) · codes_two (Honest/K12/AsksAtHead.lean) · closingShapeTests_at_stand.

IMPORTS OF Johnson.Top.H0.*: none by name (one comes in through LotLShapeBoolsKinds.lean: see its head).

Hypotheses. h: the head. atReach: THE FORM AT EVERY REACHED STATE: a premise here: its payer is the law
closingGroupLaid_at_reach (LotLShapeAtReach.lean).

Limits.
- atReach is shown here of no state. That a stand is reached is not said.
- Full size, the format's second hash function alone.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingRecordLaid_at_stand` and `closingShapeTests_of_state_form`
bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hG and hf speak of the public files, the ground and the finish: they name no coin. atReach is
  bound over every reached state: a reach names no coin.
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
- `closingRecordLaid_of_state` names no coin: it bears none.
- What lifts the bar: for st, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeHeadRecords
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeBoolsStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeBoolsKinds
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open OnBytes (TreeShape TreeLay)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S FinOwn rowsHeld membersHeld)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Ground.Sh (stSh bookSh coreSh freshOrc)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (codesFull2)
open H2K.Member (codesFull)
open ProofFile.Honest.FirstThread (lettersHead Script WtF thr_reach head_len)
open ProofFile.Honest.K12 (frontFiveB frontPlainB)
open ProofFile.Honest.K12.AtProof (finishAt parL)
open ProofFile.Honest.Sh (testSh thinSh)
open P5J (AtMg AtMgA CellsM TS)

/-- **The form: the state bears what the last code switch lays.** The chain stands at its finish; the finish's own
record names message 186 as the mask and group 25; the codes are the written ones; 77 roots are counted; and the shape shows the closing group, the
carrier, the mask and their tree, at terms of the written shape and codes. How many open rows of the generator's kind
the group has, and the tree's shape, stand under ∃. -/
def ClosingStateLaid (s : S) : Prop :=
  ∃ (n : ℕ) (o : FinOwn) (lay : TreeLay) (τ : TreeShape),
    treesOfFinish shapeFull codesFull2 = some lay ∧ lay.shapes = #[τ] ∧
    s.here = .fin o ∧ o.mask = some 186 ∧ o.fr.group = 25 ∧ s.st.codes = codesFull2 ∧
    s.roots = 77 ∧
    ClosingGroupLaid ⟨stSh s.st, bookSh s.book, s.roots⟩ 25 185 186 76
      ⟨0, 0, [185], [false], .plain :: List.replicate n .generator, false⟩
      ⟨H2K12.shL, true, 1, [(.main, 8388607)], [25],
        OnBytes.Slice.freshLedger codesFull2 H2K12.shL, false⟩
      (freshOrc (maskNoticeOfShape shapeFull)) ⟨τ, 76, .own 76, [185, 186], true, 0⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **From the form on the state to the form on the record.** -/
theorem closingRecordLaid_of_state (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {s : S}
    (laid : ClosingStateLaid s) (held : rowsHeld (P5J.At.N Zp cF) H2K12.O354 s = true)
    {R : T12} (enters : enterFinish s = .ok R) :
    ClosingRecordLaid R := by
  obtain ⟨n, o, lay, τ, hlay, hτ, hhere, hmask, hgroup, codes, hroots, hl⟩ := laid
  obtain ⟨o', ho', -, -, e⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s R enters
  obtain rfl : o = o' := by
    have t := hhere.symm.trans ho'
    injection t
  have hk := ((closingRows_on_shape h held).2 _ hl.groupIs).1
  have hk' : OnBytes.RowKind.plain :: List.replicate n OnBytes.RowKind.generator =
      .plain :: List.replicate 657 .generator := hk
  have hn : n = 657 := by
    have t := congrArg List.length hk'
    rw [List.length_cons, List.length_cons, List.length_replicate, List.length_replicate] at t
    omega
  subst e
  exact ⟨hgroup, rfl, hmask, codes.trans ProofFile.Honest.K12.Light.codes_two.symm, hroots,
    _, _, _, _, _, _, _, closingGroupLaid_written hn hlay hτ hl⟩

/-- **At every stand of the thread in front of the closing test**: hlaid of closingShapeTests_at_stand. -/
theorem closingRecordLaid_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (atReach : ∀ (p : ProofFile.InstPub) (s : S), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s) →
      s.failed = none → membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true → ClosingStateLaid s) :
    ∀ k st m E R,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R → ClosingRecordLaid R := by
  intro k st m E R hTS he
  have hT := hTS.1
  have hlen : 354 ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    decide
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  have h' := hT
  unfold Thr at h'
  obtain ⟨-, -, hF, -, -, -, -⟩ := h'
  obtain ⟨hf, -, hc⟩ := hF
  have hfail : st.failed = none :=
    Option.isNone_iff_eq_none.1 (show st.failed.isNone = true from hf)
  rcases hc with hc | ⟨hb, -, -, -⟩
  · exact absurd hfail hc
  simp only [Bool.and_eq_true] at hb
  have hmem : membersHeld (P5J.At.N Zp cF) H2K12.O354 st = true := hb.1.1.1.2
  have hheld : rowsHeld (P5J.At.N Zp cF) H2K12.O354 st = true := hb.1.1.1.1.2
  exact closingRecordLaid_of_state h.toAtMg (atReach _ _ hr hfail hmem) hheld he

/-- **acceptedS_stands_L's premise hShape, from the form at every reached state.** -/
theorem closingShapeTests_of_state_form (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {pl : K2.SwitchPlace}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hf : finishAt Zp G = some pl)
    (atReach : ∀ (p : ProofFile.InstPub) (s : S), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s) →
      s.failed = none → membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true → ClosingStateLaid s) :
    ∀ k st m E R,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      frontFiveB (H2U.p12OfMade Zp.made) codesFull (testSh R) = true ∧
        frontPlainB (H2U.p12OfMade Zp.made) (parL pl) (thinSh R) = true :=
  closingShapeTests_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hG hf
    (closingRecordLaid_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said atReach)

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.ClosingStateLaid
#print axioms ProofFile.Honest.K12.LotL.closingRecordLaid_of_state
#print axioms ProofFile.Honest.K12.LotL.closingRecordLaid_at_stand
#print axioms ProofFile.Honest.K12.LotL.closingShapeTests_of_state_form
