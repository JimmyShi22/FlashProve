-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/OpenAt346Statement.lean: THE ITEM .forms 24 4 "weights" IS
OPEN AT BORDER 346 OF THE FIRST CHAIN's TABLE OF JOINTS AT THE LIBRARY's OWN WRITTEN LISTS, AND SHUT
AT 347: the merge's member closes it: STATEMENTS ALONE: two definitions of propositions. NOTHING IS
PROVED IN THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

  `WeightsOpenAt346`    at the frame's open sets (`fwdOpen`, Honest/Thread/Thr.lean) over its
                        forward rows (`FirstRows.rows`, Honest/Thread/FirstRows.lean) at
                        `P5J.At.links` and `P5J.At.ps` (Johnson/P5J/LettersAt.lean): the item is a
                        member at 346; AS A CONTROL: it is none at 347
  `WeightsOpenAtHead`   so it is a member of what the first chain's thread at the head has open at
                        346: the first premise of `ClaimTrueAtHead` (ClaimTrueStatement.lean of this
                        folder), in its own words

Limits. A CLOSED FACT ON WRITTEN LISTS: it says which items a table names as open: NOTHING ON
WHETHER THE ITEM's SENTENCE HOLDS ANYWHERE. The full size alone: the lists are the library's own at
25 segments. The head stands among the second's letters and is not spent. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The statement on the written lists. Not proved here; a lemma's statement, none of the library's
goals. -/
def WeightsOpenAt346 : Prop :=
  Item.forms 24 4 "weights" ∈
      fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 346 ∧
    Item.forms 24 4 "weights" ∉
      fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 347

/-- The statement at the thread. Not proved here; a lemma's statement, none of the library's goals.
-/
def WeightsOpenAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr),
    Item.forms 24 4 "weights" ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 346

end ProofFile.Honest.K11
