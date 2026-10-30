-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LedgerAtHeadStatement.lean: IN FRONT OF THE MERGE's MEMBER,
AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean): NO
MARK; THE TABLE's TWO PUBLIC TESTS ON THE LEDGER, THE SECOND AT THE KIND's OWN NUMBER OF SLOTS; SO
THREE OF THE TWELVE CLAUSES OF "THE STATE IS READY", AND TWO FACTS TOWARD TWO MORE: STATEMENTS
ALONE: two definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the
library's goals: they are lemmas' statements.

Why. `MergeReady` (AcceptedStatement.lean of this folder) is a premise of the kind's law on its
member's yes, from the thread in front to the state. The frame asks such a premise's payer at this
thread, in a file of its own, where one of its roads gives it. This is the road of the public items
that are open at the border.

  `LedgerAtHead`      where the thread holds at border 346: s.failed = none · ledgerB s = true ·
                      freeAboveB (K11.parOf Zp Bs.G₀).nMsg s = true (the two tests:
                      Johnson/Desc/First/FillKeeper.lean)
  `OpenedAtHead`      so, where s stands in the head's link with the own part a: a.opened = true ·
                      the ledger has its three sizes (with "no mark": three clauses of `MergeReady`,
                      word for word) · it has the kind's number of slots · every slot from its next
                      free number on is free (no clauses of it: toward "the end value's slot is
                      there" and "is free", which want the count of slots too)

Limits. THE FULL SIZE ALONE; the head is a premise, at the earlier hash. That s stands in the head's
link is a premise of the second. Of "the state is ready" nine clauses are not had here. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.K11.Returns.OfFormStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.PscRun (Sized FreeAbove)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (HeadOwn ledgerB freeAboveB)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the mark and the two tests. The letters of the thread: those of `head_ledger`.
Not proved here; a lemma's statement, none of the library's goals. -/
def LedgerAtHead : Prop :=
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
    Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 k s m E →
    s.failed = none ∧ ledgerB s = true ∧ freeAboveB (_root_.K11.parOf Zp Bs.G₀).nMsg s = true

/-- The statement on the four clauses. Not proved here; a lemma's statement, none of the library's
goals. -/
def OpenedAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (k : Coins Bk) (s : TS)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (Bs : ProofFile.PureBase) (a : HeadOwn),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 k s m E →
    s.here = .head a →
    a.opened = true ∧ Sized a.F ∧ a.F.ns = (_root_.K11.parOf Zp Bs.G₀).nMsg ∧ FreeAbove a.F

end ProofFile.Honest.K11
