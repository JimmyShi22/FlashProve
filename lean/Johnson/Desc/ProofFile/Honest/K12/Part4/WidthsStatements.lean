--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/WidthsStatements.lean: THE PROXIMITY TEST OF THE LAST CHAIN
(the kind K12, at the place W of the proof file): THE WIDTHS OF THE THREE TREES THAT IT TAKES OVER
FROM THE TWO EARLIER CHAINS. Statements: definitions alone. The proofs:
Honest/K12/Part4/Widths.lean.

WHAT IT IS NOT.
  * Nothing is proved here: every statement is a definition of type Prop.
  * A WIDTH IS A PUBLIC NUMBER: how many words a column of a tree's table has. Nothing is said of
  what
    the tables hold, nor that they are the tables which the test's job reads (the clause "taken" of
    that place's stand is another debt).
  * Not the structure WidthsAt itself (Honest/K12/AtFile/WTable.lean, another house's file, which
  has
    not yet been through Lean): its three fields are WRITTEN OUT here, so that this file does not
    stand over that one. Whoever holds that file closes the structure with the three.
  * The first chain's two widths are stated at a thread whose tables at the members 2 and 356 are
    the shared sending's own texts (OwnTrees at treeTbl): THAT IS A PREMISE HERE. At the first
    chain's Script (firstScriptAt, AtFullSide/K1/FirstScript.lean)
    that file's laws pay it (ownTrees_first_two, ownTrees_first_w, k1Seated_first): the join is not
    in this file.
  * The shared chain's width is stated at the table tableShared
    another house's file, in no sealed tree). That a shared thread's table is that term is its
    letters' matter.
  * Under the library's hypothesis on the proof file's description: the full size alone.
  * No run is named; nothing on completeness, on soundness or on what a proof hides.

WORDS. A tree is an oracle message's Merkle tree; its table is what lies beneath the root; the
table's words are the number of words of one column. "own n" is a chain's own tree number n, from 0,
in the order of sending. The last chain's test opens three older trees: own 1 and own 82 of the
first chain and own 1 of the shared chain (takenLast, Honest/K12/AtFile/OpensLines.lean), at the
declared widths 3, 12 and 36 (wideLast, Honest/K12/AtFile/WTreesSentBeforeTest.lean). What a member tells: the
oracle messages that its block declares, in order.

WHAT IT IS.
  ToldWidthsOfTheTakenTrees       CLOSED FACTS on the written list of what the first chain's members
                                  tell: no tree is told in front of member 2, and 82 in front of
                                  member 356; member 2's second tree has 3 words, member 356's first
                                  has 12
  OwnTreeOfASendingHasItsToldWidth   GENERAL, no description named: where a thread's table at a
                                  member's trees is the shared sending's own text at a job, the
                                  member's block declares the job's plan's oracle messages, and the
                                  book's count at the job's address is the part's: the table of the
                                  member's tree number j has the words that the block tells for it,
                                  at ALL coins, inputs and challenges
  FirstChainsTakenTreesHaveTheirWidths   so, under the head, at the first chain's thread: own 1 has
                                  3 words and own 82 has 12
  SharedChainsTakenTreeHasItsWidth   under the head, at the written book: own 1 of tableShared has
                                  36 words
  WidthsOfTheThreeTakenTrees      the three together: the fields masks, own, omega of WidthsAt,
                                  written out

WHY "AT ALL COINS". The text of a sending's tree is total: where the book has not the part's coins
it is the table of no word. So the width is the declared one only where the book covers the part:
that is what the premise on the book's count is for. It is a public test.

THE PREMISES, AND WHOSE EACH IS.
  h            the library's hypothesis (P5J.AtMgA).
  the member, its oracle messages, the book's count (twice)   three fields of the shared sending's
               record K1Seated (Honest/K1/Seated.lean: member, shape, hasCoins): K1's.
  OwnTrees (twice)   the thread's table is the job's own text: whoever writes the Script.
  the book     bookWhole at the written description returns Bk: the maker's.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seated
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.BookLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open P5J (AtMgA CellsM TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnTrees)
open ProofFile.Honest.K1 (SendJob PlaceIn treeTbl dueR)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared)

/-! ## 1 Closed facts -/

/-- **What the written list tells of the two trees that the last chain takes from the first.** -/
def ToldWidthsOfTheTakenTrees : Prop :=
  treesTold toldFull 2 = 0 ∧ treesTold toldFull 356 = 82 ∧
    ((toldFull[2]?).bind (·[1]?)).map (·.words) = some 3 ∧
    ((toldFull[356]?).bind (·[0]?)).map (·.words) = some 12

/-! ## 2 General: a sending's own tree -/

/-- **The table of a sending's tree has the words that the member's block tells for it**, at all
coins, inputs and challenges. No description is named. -/
def OwnTreeOfASendingHasItsToldWidth : Prop :=
  ∀ (Bk : ProverCoinCounts) (S Cl V Wl Xt Pb W X : Type) (T : Thread Bk S Cl V Wl Xt Pb) (member trees : Nat)
    (wit : Wl → W) (job : SendJob W X) (own₀ : X) (off : Nat → Nat) (block : Block S Cl),
    OwnTrees T member trees (treeTbl 0 wit job own₀) off →
    T.bs[member]? = some block →
    block.oracles = VerifiableInference.Desc.K1.oracles job.P →
    dueAt (Bk.rowsOf 0) ⟨job.P.place, 0⟩ = dueR job.P job.ride →
    ∀ (j : Nat), j < trees → ∀ told, block.oracles.flatten[j]? = some told →
    ∀ k v hd, (T.table (.own (treesTo T.bs member + j)) k v hd).2.words = told.words

/-! ## 3 At the proof file -/

/-- **The first chain's two**: under the head, at a first chain's thread whose tables at the members
2 and 356 are the shared sending's own texts. -/
def FirstChainsTakenTreesHaveTheirWidths : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (wit : Local W₀ Rc Inst Tr → PlaceIn Inst) (opening lastSending : SendJob (PlaceIn Inst) X)
    (own₀ : X) (offOpening offLast : Nat → Nat) (blockOpening blockLast : Block TS Cl),
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[2]? =
      some blockOpening →
    blockOpening.oracles = VerifiableInference.Desc.K1.oracles opening.P →
    dueAt (Bk.rowsOf 0) ⟨opening.P.place, 0⟩ = dueR opening.P opening.ride →
    OwnTrees (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2
      opening.P.trees.length (treeTbl 0 wit opening own₀) offOpening →
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[356]? =
      some blockLast →
    blockLast.oracles = VerifiableInference.Desc.K1.oracles lastSending.P →
    dueAt (Bk.rowsOf 0) ⟨lastSending.P.place, 0⟩ = dueR lastSending.P lastSending.ride →
    OwnTrees (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 356
      lastSending.P.trees.length (treeTbl 0 wit lastSending own₀) offLast →
    (∀ k v hd, ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
      (.own 1) k v hd).2.words = 3) ∧
    ∀ k v hd, ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
      (.own 82) k v hd).2.words = 12

/-- **The shared chain's one**: under the head, at the book that the maker's routine returns at the
written description. -/
def SharedChainsTakenTreeHasItsWidth : Prop :=
  ∀ (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl), P5J.AtMg o Z D r Zp Np cF →
    ∀ (Bk : ProverCoinCounts) (W₀ Rc X₀ : Type) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (testOnU testOnOmega : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀),
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk →
    ∀ (k : Coins Bk) v hd,
      (tableShared (VerifiableInference.Desc.K1.qAt Zp Np) weights rand testOnU testOnOmega own₀
        (.own 1) k v hd).2.words = 36

/-- **THE THREE TOGETHER**: the fields masks, own and omega of WidthsAt, written out, at the first
chain's thread's table and at tableShared. -/
def WidthsOfTheThreeTakenTrees : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (wit : Local W₀ Rc Inst Tr → PlaceIn Inst) (opening lastSending : SendJob (PlaceIn Inst) X)
    (own₀ : X) (offOpening offLast : Nat → Nat) (blockOpening blockLast : Block TS Cl)
    (Ws Rs Xs : Type) (weights : Ws → Weights) (rand : Rs → TableRand)
    (testOnU testOnOmega : TestJob (Common Ws Rs TableKey) Xs) (ownShared : Xs),
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[2]? =
      some blockOpening →
    blockOpening.oracles = VerifiableInference.Desc.K1.oracles opening.P →
    dueAt (Bk.rowsOf 0) ⟨opening.P.place, 0⟩ = dueR opening.P opening.ride →
    OwnTrees (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2
      opening.P.trees.length (treeTbl 0 wit opening own₀) offOpening →
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[356]? =
      some blockLast →
    blockLast.oracles = VerifiableInference.Desc.K1.oracles lastSending.P →
    dueAt (Bk.rowsOf 0) ⟨lastSending.P.place, 0⟩ = dueR lastSending.P lastSending.ride →
    OwnTrees (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 356
      lastSending.P.trees.length (treeTbl 0 wit lastSending own₀) offLast →
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk →
    (∀ k v hd, ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
      (.own 1) k v hd).2.words = 3) ∧
    (∀ k v hd, ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
      (.own 82) k v hd).2.words = 12) ∧
    ∀ (k : Coins Bk) v hd,
      (tableShared (VerifiableInference.Desc.K1.qAt Zp Np) weights rand testOnU testOnOmega
        ownShared (.own 1) k v hd).2.words = 36

end ProofFile.Honest.K12.Part4
