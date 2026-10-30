-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/BookFacts.lean: two public facts on the verifier's book of
trees along the first chain at the full size. No two oracle messages have one place in the book
(`PlacesApart`, Johnson/Desc/First/Close/Law/FillRow.lean), and a tree's own number is its place in
the book. Both hold at every state without a mark of failure that the chain's own steps reach. So
they hold where the invariant holds (`lettersHead`, FirstHead.lean), and after an accepting step
from such a state. They speak of no coin and no witness. Both are fields of the library's facts on
reached states (`FoldFacts`: `bookFits`, `bookInOrder`), read through the library's own lemmas on
its tests. No definition.

  1  `reach_facts`   the library's facts, at "reached by the chain's own steps"
  2  `reach_placesApart`, `reach_treeNumber`   the two facts at a reached state
  3  `head_placesApart`, `head_treeNumber`   where the invariant holds
  4  `head_placesApart_next`, `head_treeNumber_next`   after a sub-protocol's step from a state at
     which the invariant holds, if the state after it has no mark of failure

Called: `foldFacts_raw`, `thr_reach` (ReachFacts.lean), `stepYes_of_stepped` (SteppedYes.lean); the
library's `bookFitsB_iff` (Johnson/Desc/Sound/BookTestsLaw.lean), `places_inj`
(Johnson/Desc/Book/BookFits.lean), `numbers_of_book0` (Johnson/Desc/K12/Door/DoorGives.lean). The
first tree's number at the head's data is 0 (`foldD_ft`, Johnson/P5J/FoldAt.lean).

Limits.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * First chain only.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `head_reach_next`, `head_placesApart_next`,
    `head_treeNumber_next`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.First.Close.Law.FillRow
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.Book.BookFits
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- The library's facts on reached states, at "reached by the chain's own steps". -/
theorem reach_facts :
    FoldFacts (fun b (a : ProofFile.InstPub × TS) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (fun a => a)
      (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull) P5J.At.reqW P5J.At.links
      P5J.At.ps :=
  foldFacts_raw h.toAtMg _ _ (fun _ _ hr => hr) (P5J.laid_at_head h.toAtMg)
    (P5J.startB_at_head h.toAtMg) (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))

include h in
/-- No two oracle messages have one place in the book, at a reached state without a mark. -/
theorem reach_placesApart {b : Nat} {a : ProofFile.InstPub × TS}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (h0 : a.2.failed = none) :
    VerifiableInference.Desc.First.PlacesApart a.2 := by
  have e : VerifiableInference.Desc.Sound.bookFitsB a.2.book = true :=
    (reach_facts h).bookFits b a hR h0
  intro o o' q ho ho'
  exact VerifiableInference.Desc.Book.places_inj
    ((VerifiableInference.Desc.Sound.bookFitsB_iff a.2.book).1 e) ho ho'

include h in
/-- A tree's own number is its place in the book, at a reached state without a mark. -/
theorem reach_treeNumber {b : Nat} {a : ProofFile.InstPub × TS}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (h0 : a.2.failed = none) :
    ∀ (z : Nat) (T : OnBytes.Tree), a.2.book.trees[z]? = some T → T.number = z := by
  have e : VerifiableInference.Desc.K12.Door.bookInOrderB 0 a.2.book a.2.roots = true :=
    (reach_facts h).bookInOrder b a hR h0
  exact VerifiableInference.Desc.K12.Door.numbers_of_book0 e

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Where the invariant holds, the state has no mark of failure. -/
theorem head_noMark {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.failed = none := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  exact Option.isNone_iff_eq_none.1 hF.1

/-- **No two oracle messages have one place in the book**, where the invariant holds. -/
theorem head_placesApart {b : Nat} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    VerifiableInference.Desc.First.PlacesApart s :=
  reach_placesApart h (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)

/-- **A tree's own number is its place in the book**, where the invariant holds. -/
theorem head_treeNumber {b : Nat} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ∀ (z : Nat) (T : OnBytes.Tree), s.book.trees[z]? = some T → T.number = z :=
  reach_treeNumber h (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)

/-- The state after a sub-protocol's step is reached. -/
theorem head_reach_next {b : Nat} {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (b + 1) (m.st.input.x.pub, s') :=
  Reach.succ
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1) hT) hblk
    (stepYes_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread hd hS)

/-- **`PlacesApart` after a sub-protocol's step.** -/
theorem head_placesApart_next {b : Nat} {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') (h0 : s'.failed = none) :
    VerifiableInference.Desc.First.PlacesApart s' :=
  reach_placesApart h
    (head_reach_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hd hS) h0

/-- **A tree's own number is its place in the book, after a sub-protocol's step.** -/
theorem head_treeNumber_next {b : Nat} {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') (h0 : s'.failed = none) :
    ∀ (z : Nat) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z :=
  reach_treeNumber h
    (head_reach_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hd hS) h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.reach_facts
#print axioms ProofFile.Honest.FirstThread.reach_placesApart
#print axioms ProofFile.Honest.FirstThread.reach_treeNumber
#print axioms ProofFile.Honest.FirstThread.head_noMark
#print axioms ProofFile.Honest.FirstThread.head_placesApart
#print axioms ProofFile.Honest.FirstThread.head_treeNumber
#print axioms ProofFile.Honest.FirstThread.head_reach_next
#print axioms ProofFile.Honest.FirstThread.head_placesApart_next
#print axioms ProofFile.Honest.FirstThread.head_treeNumber_next
