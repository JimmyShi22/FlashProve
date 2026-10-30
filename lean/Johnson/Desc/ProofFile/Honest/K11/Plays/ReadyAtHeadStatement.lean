-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ReadyAtHeadStatement.lean: AT THE FIRST CHAIN's THREAD AT
THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), FROM THE PAIR `ThrS … SaidOk` AT
BORDER 346: "THE STATE IS READY" (`MergeReady`, AcceptedStatement.lean of this folder) COMES DOWN TO
THREE OF ITS TWELVE CLAUSES: that the claim fits the layout · that the slot of the claim's value is
filled · the count of slots: STATEMENTS ALONE: two definitions of propositions. NOTHING IS PROVED IN
THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

  `SevenReadyAtHead`    seven clauses word for word: no mark · the head's link · it is open ·
                        nothing waits · a claim is laid · what the head heard is laid · the ledger's
                        three sizes; and beside: the ledger has the kind's number of slots · every
                        slot from its next free number on is free
  `ReadyOfThreeAtHead`  where the three clauses that are left hold of whatever own part, claim and
                        hearing the state holds: `MergeReady`: the two clauses on the end value's
                        slot follow from the count, the number of slots and "free above"

Limits. THE THREE ARE A PREMISE. THE FULL SIZE ALONE; the head is a premise, at the earlier hash.
That the pair holds at any stand is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open OnBytes.PscRun (Sized Filled FreeAbove)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (HeadOwn)
open Johnson.Desc.First.ForkMerge (claimFits)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the seven. Not proved here; a lemma's statement, none of the library's goals.
-/
def SevenReadyAtHead : Prop :=
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
      ∃ (a : HeadOwn) (claim : WsClaim) (hx : OnBytes.Model.Head.Heard), s.here = .head a ∧
        a.opened = true ∧ s.noneWaits = true ∧ a.claim = some claim ∧ a.x = some hx ∧ Sized a.F ∧
        a.F.ns = (_root_.K11.parOf Zp Bs.G₀).nMsg ∧ FreeAbove a.F

/-- The statement from the three. Not proved here; a lemma's statement, none of the library's goals.
-/
def ReadyOfThreeAtHead : Prop :=
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
    (∀ (a : HeadOwn) (claim : WsClaim) (hx : OnBytes.Model.Head.Heard), s.here = .head a →
      a.claim = some claim → a.x = some hx →
      claimFits (_root_.K11.parOf Zp Bs.G₀).lay claim = true ∧ Filled a.F hx.sV ∧
        a.F.next + 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 3 =
          (_root_.K11.parOf Zp Bs.G₀).nMsg) →
    MergeReady (_root_.K11.parOf Zp Bs.G₀) s

end ProofFile.Honest.K11
