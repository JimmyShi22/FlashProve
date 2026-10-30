-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/PlaysAtHeadStatement.lean: THE FRAME's DEBT `Plays`
(Honest/Thread/Pays.lean), AND SO `PlaysS` (Honest/Thread/PaysS.lean), AT THE MERGE's MEMBER, NUMBER
346, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`,
Honest/Thread/FirstHead.lean): FROM ONE PREMISE ON THE PROVER: that its half at the merge's place is
the kind's: A STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it
is none of the library's goals: it is a lemma's statement.

  `PlaysAtHead`  the head · what the maker's base returns · the premise of `AcceptedSAtHead`
                 (AcceptedAtHeadStatement.lean of this folder) on the prover: `Plays` at 346, and
                 `PlaysS` at 346 at every letter Said: the half's play and the laying of the columns
                 return, and the new trees are the functions' tables

Limits. THE PREMISE ON THE PROVER IS NOT SHOWN OF ANY PROVER. The debt's own premises stay (that the
thread's sentence holds at 346; that the challenges fit; that the half does not stop; that the steps
are made). THE FULL SIZE ALONE; the head is a premise, at the earlier hash: no example of it is
shown here; the library's `head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one under
four premises. ONE MEMBER OF ONE CHAIN: nothing on a whole run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedAtHeadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def PlaysAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (Bs : ProofFile.PureBase)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (H.first.find? fun g => g.place == IM.k11Place) =
      some (headMergeHalf claims weights (_root_.K11.parOf Zp Bs.G₀)) →
    Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 ∧
      ∀ Said, PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 346

end ProofFile.Honest.K11
