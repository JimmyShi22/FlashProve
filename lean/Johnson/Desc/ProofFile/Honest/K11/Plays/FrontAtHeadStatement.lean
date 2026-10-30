-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FrontAtHeadStatement.lean: AT THE FIRST CHAIN's THREAD AT
THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), FROM THE PAIR OF THE THREAD AND
"EVERY WORD SHOWN IS BELOW THE PRIME" (`ThrS … SaidOk`) AT BORDER 346: THE STATE STANDS IN THE
HEAD's LINK, WITH WHAT THE HEAD HEARD LAID; FIVE OF THE TWELVE CLAUSES OF "THE STATE IS READY" WITH
IT; THE MASK ROW's SENTENCE WITH NO FRAME BESIDE IT; AND THE PUBLIC TEST BEHIND THE MEMBER's STEP:
STATEMENTS ALONE: four definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one
of the library's goals: they are lemmas' statements.

Why. As in LedgerAtHeadStatement.lean of this folder: payers, at this thread, of premises of the
kind's laws that go from the thread in front to the state. Here the road is the library's facts at
reached states: so the pair is asked, not the thread alone.

  `HereAtHead`      s.here = .head a and a.x = some hx, for some a, hx
  `HalfReadyAtHead`   so, with LedgerAtHead.lean's two: no mark · here · a.opened = true · a.x =
                      some hx · the ledger's three sizes (five clauses of `MergeReady`,
                      AcceptedStatement.lean, word for word; "here" and "a.x" among them), and
                      beside: the ledger has the kind's number of slots · every slot from its next
                      free number on is free
  `MaskAtHeadPlain`   `MaskAtAtHead` (MaskAtHeadStatement.lean of this folder) WITHOUT ITS TWO
                      LETTERS Fr AND A MEMBER OF ITS STRINGS: the library's law beneath speaks of a
                      statement with such a member beside it and does not read it; every frame's
                      strings have a member
  `PubTestAtHead`     THE FIELD pubTest OF `K11SeatedS` (ShareSStatement.lean of this folder), IN
                      THAT FIELD's OWN TEXT, at this thread, Said := SaidOk, b := 346, and the group
                      of segment 24 of the head's own numbers

Limits. THE FULL SIZE ALONE; the head is a premise, at the earlier hash. Of "the state is ready"
seven clauses are not had here: that nothing waits · that a claim is laid · that it fits the layout
· that the slot of the claim's value is filled · that the end value's slot is there · that it is
free (had here but for the count of slots) · the count of slots. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.LedgerAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskAtHeadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.PscRun (Sized FreeAbove)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT Mem xAt)
open VerifiableInference.Desc.First (HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (MaskAt mergeStates)
open VerifiableInference.Desc.K9 (formsIn Readers)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement that the state stands in the head's link. The letters of the thread: those of
`thrS_rchAt`. Not proved here; a lemma's statement, none of the library's goals. -/
def HereAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    ∃ (a : HeadOwn) (hx : OnBytes.Model.Head.Heard), s.here = .head a ∧ a.x = some hx

/-- The statement on the clauses gathered. Not proved here; a lemma's statement, none of the
library's goals. -/
def HalfReadyAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    s.failed = none ∧
      ∃ (a : HeadOwn) (hx : OnBytes.Model.Head.Heard), s.here = .head a ∧ a.opened = true ∧
        a.x = some hx ∧ Sized a.F ∧ a.F.ns = (_root_.K11.parOf Zp Bs.G₀).nMsg ∧ FreeAbove a.F

/-- The statement on the mask row, with no frame beside it. Not proved here; a lemma's statement,
none of the library's goals. -/
def MaskAtHeadPlain : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (xM : Mem),
    xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E →
    MaskAt (h.𝔇.N.group 24) xM 0 s

/-- The statement on the public test behind. Not proved here; a lemma's statement, none of the
library's goals. -/
def PubTestAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr),
    ∀ blk k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
        E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[346]? = some blk →
      formsIn (Readers.ofStates (mergeStates "the merge")) (h.𝔇.N.group 24) 8 "the merge" s' = true

end ProofFile.Honest.K11
