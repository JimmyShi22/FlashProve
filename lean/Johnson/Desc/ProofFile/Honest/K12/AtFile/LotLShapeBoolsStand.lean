-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeBoolsStand.lean

It states no goal. No property of the protocol is claimed.

`acceptedS_stands_L`'s PREMISE hShape
(not beneath this file), TO THE LETTER, FROM ONE PREMISE ON THE RECORD AT A STAND: what the last
code switch has laid is the written local shape. No closed shape of the whole record is asked.

  `ClosingRecordLaid`     THE FORM OF THE PREMISE, on the record R on entry to the closing test: the group
                          under test is 25 · nothing passes · the mask is message 186 · the codes are the
                          written ones · 77 roots · and `ClosingGroupLaid` (LotLShapeLaidForm.lean) at
                          25, 185, 186, 76 and the four written records, at some value of the seven
                          fields that the tests do not read
  `five_of_laid`, `plain_of_laid`   the two tests at a shape that meets the form
  `firstShapeTest_of_closingRecordLaid`   the first at the record
  `shapeTests_of_closingRecordLaid`   both at the record
  `closingShapeTests_at_stand`        hShape

By what. `core_is_localCore` (LotLShapeBoolsLaid.lean); `closingShape_passes_five`,
`closingShape_passes_plain` (LotLShapeBoolsClosed.lean: Lean's kernel, by `kernel_rfl`); `p12_at_head`
(Johnson/AtFull/Shape/TestNumbersAtHead.lean); `places_head`, `finishW` (AtFullSide/K12/FitsAtHeadL.lean).

Hypotheses of the last. h: the head. hG, hf: the plan's finish at the blank ground.
hlaid: AT EACH STAND of the thread with Said, at the record that `enterFinish`
returns: `ClosingRecordLaid`.

Limits.
- hlaid IS A PREMISE ON EVERY STAND: shown here of none. One stand at which it fails makes it false.
- That a stand is reached is not said.
- Full size, the format's second hash function alone.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingShapeTests_at_stand` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hG and hf speak of the public files, the ground and the finish: they name no coin.
- hlaid is itself bound over all coins and every stand: by itself it picks among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- A run's coins k are bound inside the end. Beside k it binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `ThrS … 354 k st m
  E`: a premise of the first kind: it names k; by its text, at fixed st, m and E it can hold at some
  values of the coins and fail at others. The record R under `enterFinish st = .ok R` names no coin.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, Said) stand under no
  premise in front that names a coin; the invariant reads them.
- The other theorems of this file name no coin: they bear none.
- What lifts the bar: for st, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeBoolsClosed
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.AtFull.Shape.TestNumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Ground.Sh (CoreSh GrpSh OrcSh TreeSh SrcSh coreSh)
open H2K.Member (piLFull codesFull)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12 (frontFiveB frontPlainB)
open ProofFile.Honest.K12.AtProof (finishAt finishW places_head parL)
open ProofFile.Honest.Sh (testSh thinSh)
open P5J (AtMgA CellsM TS)

/-- **The form of the premise: the record on entry to the closing test bears the written local
shape.** -/
structure ClosingRecordLaid (R : T12) : Prop where
  groupUnderTest : R.g = 25
  nothingPasses : R.pass = .nothing
  maskIsThere : R.mask = some 186
  codesAreWritten : R.st.codes = codesFull
  rootsCounted : R.roots = 77
  laid : ∃ (carrierLedger maskLedger : Option OnBytes.Ledger) (carrierSpent : Bool) (maskRows : ℕ)
    (maskPad : List (OnBytes.Part × ℕ)) (maskGroups : List ℕ) (source : SrcSh),
    ClosingGroupLaid (coreSh ⟨R.st, R.book, R.roots⟩) 25 185 186 76 closingGroup
      (carrierMessage carrierLedger carrierSpent)
      (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)

section
variable {c : CoreSh} {carrierLedger maskLedger : Option OnBytes.Ledger} {carrierSpent : Bool}
  {maskRows : ℕ} {maskPad : List (OnBytes.Part × ℕ)} {maskGroups : List ℕ} {source : SrcSh}

/-- The first test at a shape that meets the form. -/
theorem five_of_laid (hc : c.st.codes = codesFull) (hr : c.roots = 77)
    (hl : ClosingGroupLaid c 25 185 186 76 closingGroup (carrierMessage carrierLedger carrierSpent)
      (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)) :
    frontFiveB piLFull codesFull ⟨c, 25, .nothing, some 186⟩ = true := by
  have e := core_is_localCore hl
  rw [hc, hr] at e
  have t := closingShape_passes_five
    (fun i => c.st.oracles.getD i (carrierMessage carrierLedger carrierSpent))
    (fun i => c.st.groups.getD i closingGroup) (fun i => c.book.trees.getD i (closingTree source))
    (fun i => c.book.place.getD i (0, 0)) carrierLedger maskLedger
    carrierSpent maskRows maskPad maskGroups source
  rw [← e] at t
  exact t

/-- The second test at a shape that meets the form, at the written finish. -/
theorem plain_of_laid (hc : c.st.codes = codesFull) (hr : c.roots = 77)
    (hl : ClosingGroupLaid c 25 185 186 76 closingGroup (carrierMessage carrierLedger carrierSpent)
      (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source))
    {p : K2.SwitchPlace} (hp : finishW = some p) :
    frontPlainB piLFull (parL p) ⟨c, 25, .nothing, some 186⟩ = true := by
  have e := core_is_localCore hl
  rw [hc, hr] at e
  have t := closingShape_passes_plain
    (fun i => c.st.oracles.getD i (carrierMessage carrierLedger carrierSpent))
    (fun i => c.st.groups.getD i closingGroup) (fun i => c.book.trees.getD i (closingTree source))
    (fun i => c.book.place.getD i (0, 0)) carrierLedger maskLedger carrierSpent maskRows maskPad
    maskGroups source
  rw [← e, hp] at t
  exact t

end

/-- **The first test at a record that bears the written local shape**: the one sentence on the shape
that `StandLeft.five` (K12/AtFile/LAcceptedOpens.lean; not imported) asks. -/
theorem firstShapeTest_of_closingRecordLaid {R : T12} (h : ClosingRecordLaid R) :
    frontFiveB piLFull codesFull (testSh R) = true := by
  obtain ⟨hg, hn, hm, hc, hr, _, _, _, _, _, _, _, hl⟩ := h
  show frontFiveB piLFull codesFull
    ⟨coreSh ⟨R.st, R.book, R.roots⟩, R.g, ProofFile.Honest.Sh.passSh R.pass, R.mask⟩ = true
  rw [hg, hn, hm]
  exact five_of_laid hc hr hl

/-- **Both tests at a record that bears the written local shape.** -/
theorem shapeTests_of_closingRecordLaid {R : T12} (h : ClosingRecordLaid R) {p : K2.SwitchPlace}
    (hp : finishW = some p) :
    frontFiveB piLFull codesFull (testSh R) = true ∧
      frontPlainB piLFull (parL p) (thinSh R) = true := by
  refine ⟨firstShapeTest_of_closingRecordLaid h, ?_⟩
  obtain ⟨hg, hn, hm, hc, hr, _, _, _, _, _, _, _, hl⟩ := h
  · show frontPlainB piLFull (parL p)
      ⟨coreSh ⟨R.st, R.book, R.roots⟩, R.g, ProofFile.Honest.Sh.thinPass R.pass, R.mask⟩ = true
    rw [hg, hn, hm]
    exact plain_of_laid hc hr hl hp

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`acceptedS_stands_L`'s premise hShape**, from hlaid. -/
theorem closingShapeTests_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {pl : K2.SwitchPlace}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hf : finishAt Zp G = some pl)
    (hlaid : ∀ k st m E R,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R → ClosingRecordLaid R) :
    ∀ k st m E R,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      frontFiveB (H2U.p12OfMade Zp.made) codesFull (testSh R) = true ∧
        frontPlainB (H2U.p12OfMade Zp.made) (parL pl) (thinSh R) = true := by
  intro k st m E R hT he
  have hp : finishW = some pl := by
    rw [← hf]
    unfold finishAt finishW
    rw [places_head h.toAtMg hG]
  rw [Johnson.AtFull.Shape.p12_at_head h.toAtMg]
  exact shapeTests_of_closingRecordLaid (hlaid k st m E R hT he) hp

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.ClosingRecordLaid
#print axioms ProofFile.Honest.K12.LotL.five_of_laid
#print axioms ProofFile.Honest.K12.LotL.plain_of_laid
#print axioms ProofFile.Honest.K12.LotL.firstShapeTest_of_closingRecordLaid
#print axioms ProofFile.Honest.K12.LotL.shapeTests_of_closingRecordLaid
#print axioms ProofFile.Honest.K12.LotL.closingShapeTests_at_stand
