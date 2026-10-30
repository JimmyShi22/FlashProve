-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/RowRidesStatement.lean: THE ITEMS "row m c" OF THE FIRST
CHAIN's THREAD AT THE LIBRARY's HEAD RIDE PAST EVERY MEMBER WHOSE CLAUSE OF "keeps" LEAVES THE
STATEMENT AND THE BOOK; AND SO PAST THE MERGE's MEMBER, NUMBER 346: STATEMENTS ALONE: three
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals:
they are lemmas' statements.

  `RowRidesAt`       general in the member's number b, the segment m and the class c: where "keeps b
                     s s'" gives s'.st = s.st and s'.book = s.book: the frame's `RidesPastAt`
                     (Honest/Thread/Shares.lean) at b at the item .row m c
  `K11KeepsLeaves`   the kind's own clause `K11Keeps` (Johnson/Desc/K11/Returns/KeepsStatement.lean)
                     leaves both: no thread
  `K11RowsRide`      where the thread's "keeps" at 346 gives `K11Keeps P`: `RidesPastAt` at 346 at
                     every .row m c

Why. At the composed meaning the sentence "row m c" reads of the verifier's state the statement and
the book alone, and of the oracles' strings nothing (`rowSays`, `classRows`,
Johnson/Desc/First/Close/Law/FillRow.lean; `wordsAtFirst`, FillRowFirst.lean beside it). By the
frame's authors' evaluation of the written tables five such items are open across 346: row 24 at the
classes carried, position and the three samples.

Limits. THE PREMISE ON "keeps" STAYS: that the thread's "keeps" at 346 gives `K11Keeps P` holds
where the letter Kp is laid so: it is not laid so. WHICH ITEMS ARE OPEN ACROSS 346 IS NOT SAID
HERE. NOTHING HERE SHOWS THAT A ROW's SENTENCE HOLDS AT ANY STATE. THE LIBRARY HAS THE LIKE ACROSS
THE MERGE's ACCEPTING STEP, BOTH WAYS, FROM THAT STEP's YES (`row_back`,
Johnson/Top/H0/MergeLaw/RidesRows.lean): here the yes is not at hand: the clause is. THE FIRST HALF
OF `K11KeepsLeaves` (the statement) IS ALSO A LEMMA OF THE FRAME's AUTHORS (k11Keeps_st, in a file
of theirs that is in no issue yet): the same statement, the same proof: here the book is added. The
head is a premise here, at the earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.K11.Returns.KeepsStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The general statement. Not proved here; a lemma's statement, none of the library's goals. -/
def RowRidesAt : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (b m : Nat)
    (c : RowClass),
    (∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st ∧ s'.book = s.book) →
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.row m c)

/-- The statement on the kind's clause. Not proved here; a lemma's statement, none of the library's
goals. -/
def K11KeepsLeaves : Prop :=
  ∀ (P : HeadMergeP) (s s' : S), K11Keeps P s s' → s'.st = s.st ∧ s'.book = s.book

/-- The statement at 346. Not proved here; a lemma's statement, none of the library's goals. -/
def K11RowsRide : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (P : HeadMergeP),
    (∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11Keeps P s s') →
    ∀ (m : Nat) (c : RowClass),
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346
        (Item.row m c)

end ProofFile.Honest.K11
