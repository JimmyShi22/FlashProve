-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ReadyOfCountStatement.lean: AT THE FIRST CHAIN's THREAD AT
THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), FROM THE PAIR `ThrS … SaidOk` AT
BORDER 346: "THE STATE IS READY" (`MergeReady`, AcceptedStatement.lean of this folder) COMES DOWN TO
ONE OF ITS TWELVE CLAUSES: THE COUNT OF SLOTS: A STATEMENT ALONE: a definition of a proposition.
NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: it is a lemma's statement.

  `ReadyOfCountAtHead` where the ledger's next free number and 2 lk + 3 more are the kind's number
                       of slots, at whatever own part the state holds: `MergeReady`

Limits. THE COUNT IS A PREMISE. THE FULL SIZE ALONE; the head is a premise, at the earlier hash.
That the pair holds at any stand is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyAtHeadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (HeadOwn)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def ReadyOfCountAtHead : Prop :=
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
    (∀ a : HeadOwn, s.here = .head a →
      a.F.next + 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 3 = (_root_.K11.parOf Zp Bs.G₀).nMsg) →
    MergeReady (_root_.K11.parOf Zp Bs.G₀) s

end ProofFile.Honest.K11
