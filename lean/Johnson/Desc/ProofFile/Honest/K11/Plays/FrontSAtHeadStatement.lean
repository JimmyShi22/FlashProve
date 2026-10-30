-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FrontSAtHeadStatement.lean: THE FIELD front OF `K11SeatedS`
(ShareSStatement.lean of this folder), BUT FOR ITS LAST CLAUSE, AT THE FIRST CHAIN's THREAD AT THE
LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean), FROM THE PAIR `ThrS … SaidOk` AT
BORDER 346 ALONE: STATEMENTS ALONE: three definitions of propositions. NOTHING IS PROVED IN THIS
FILE, and none is one of the library's goals: they are an end's form and two lemmas' statements.

  `FrontSeven`     the field's seven clauses that speak of the state and the layout: the head's link
                   · a claim · what the head heard · the open segment's part is read (`segAt?`) ·
                   the masked sumcheck's promise in front (`LedgerReady`) at the merge's start form
                   and shape · the slot of the claim's value is filled · the claim's unit is there,
                   the claim passes `verify-on-bytes`'s test on its sizes, the unit is in order and
                   lies within the weights' rows
  `FrontOfReady`   general in the kind's numbers P and the state: where "the state is ready"
                   (`MergeReady`, AcceptedStatement.lean of this folder), every slot from the
                   ledger's next free number on is free, and the layout comes out of the library's
                   `wsLayOf`: the seven
  `FrontSAtHead`   the seven at the thread, from the pair and what the maker's base returns

Limits. THE FIELD's LAST CLAUSE IS NOT HERE: that the prover's letter claims, at what it has heard,
is the list of just that claim. THAT THE PAIR HOLDS AT ANY STAND IS NOT SAID: whoever stands at 346
has passed the verifier's own tests at the 346 sub-protocols in front, and several clauses hold
because these tests have passed. THE FULL SIZE ALONE at the last; the head is a premise, at the
earlier hash: no example of it is shown here; the library's `head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean) has one under four premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareSStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (oneE)
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsShape wsLayOf wsClaimShape wsForkStart)
open OnBytes.PscRun (FreeAbove)
open OnBytes.Road (UnitOK)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Part.MaskedSum (LedgerReady)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The seven clauses. A definition: an end's form. -/
def FrontSeven (P : HeadMergeP) (s : S) : Prop :=
  ∃ a claim x0 b9, s.here = .head a ∧ a.claim = some claim ∧ a.x = some x0 ∧
    segAt? s = some b9 ∧
    LedgerReady (wsForkStart #[x0.sV] #[oneE]) (headMergeShape P.lay.lk) a.F ∧
    OnBytes.PscRun.Filled a.F x0.sV ∧
    ∃ un, P.lay.U[claim.ui]? = some un ∧ wsClaimShape P.lay claim = .ok () ∧
      UnitOK P.lay.lk un ∧ un.off + un.rows ≤ P.lay.m0

/-- The statement from "ready". Not proved here; a lemma's statement, none of the library's goals.
-/
def FrontOfReady : Prop :=
  ∀ (P : HeadMergeP) (s : S) (sh : WsShape) (p3 : Bool) (lkW : ℕ),
    wsLayOf sh p3 lkW = .ok P.lay → MergeReady P s →
    (∀ a, s.here = .head a → FreeAbove a.F) → FrontSeven P s

/-- The statement at the thread. Not proved here; a lemma's statement, none of the library's goals.
-/
def FrontSAtHead : Prop :=
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
    FrontSeven (_root_.K11.parOf Zp Bs.G₀) s

end ProofFile.Honest.K11
