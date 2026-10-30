-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/BookFitsAt.lean: the library's condition `BookFits` on the
verifier's list of commitment trees ("every message stands in its tree's list of parts at its own
part number", Johnson/Desc/Book/BookFits.lean), at a reached state of the first chain, where the
invariant at `lettersHead` holds, and after a sub-protocol's step. No definition.

Honest/Thread/BookFacts.lean shows `PlacesApart` by way of `BookFits` and does not state `BookFits`
itself.

  1  `reach_bookFits`   at a reached state without a mark of failure. The field `bookFits` of the
     library's facts on reached states (`reach_facts`, Honest/Thread/BookFacts.lean) and the
     library's `bookFitsB_iff` (Johnson/Desc/Sound/BookTestsLaw.lean)
  2  `head_bookFits`   where the invariant holds at a border of the chain (`hb`: at most the length
     of the flat list)
  3  `head_bookFits_next`   after a sub-protocol's step, with the binders of
     `head_placesApart_next` (Honest/Thread/BookFacts.lean). Among them is `drawsFit`: the
     challenges fit the sub-protocol's rounds
  4  `reach_bookFits_front`, `head_bookFits_next_front`   the same at a border up to 353, without
     the hypothesis "no mark of failure". A call of the library's `Meaning.K2.bookFits_reached`
     (Johnson/IMR/AtReach.lean), which speaks of the chain's first 353 sub-protocols
     (`Meaning.K2.front_len`, Johnson/IMR/FinPin.lean)

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (Honest/Thread/FirstAt.lean says which that is).
  * In entry 3, that the state after the step has no mark of failure is a hypothesis (`h0`). Entry 4
    has no such hypothesis and does not reach the last five sub-protocols.
  * Entries 1, 3 and 4 ask more than the fact needs. The library's `Meaning.K2.atFirstFits_all`
    (Johnson/IMR/AtReach.lean) has the test `bookFitsB` of the book at every reached state, at every
    border, without "no mark of failure" and without the bound 353. Its two hypotheses follow from
    `AtMgA`: `h.laid.opened`, and `P5J.flat_ok` (Johnson/P5J/FoldJ1.lean). So `h0` and the bound are
    limits of the road that this file takes, not of the fact. This is read off the types; no lemma
    of this file states it.
  * Nothing here shows that a state is reached, or that the invariant holds, at any run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BookFacts
import Johnson.IMR.AtReach
import Johnson.IMR.FinPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- `BookFits` at a reached state without a mark. -/
theorem reach_bookFits {b : Nat} {a : ProofFile.InstPub × TS}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (h0 : a.2.failed = none) :
    VerifiableInference.Desc.Book.BookFits a.2.book := by
  have e : VerifiableInference.Desc.Sound.bookFitsB a.2.book = true :=
    (reach_facts h).bookFits b a hR h0
  exact (VerifiableInference.Desc.Sound.bookFitsB_iff a.2.book).1 e

include h in
/-- `BookFits` at a state reached at a border up to 353. -/
theorem reach_bookFits_front {b : Nat} {a : ProofFile.InstPub × TS}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a) (hb : b ≤ 353) :
    VerifiableInference.Desc.Book.BookFits a.2.book := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.bookFits_reached O (z := a.1) (s := a.2) hR
    (by rw [Meaning.K2.front_len h.scope h.reads O]; exact hb)

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- `BookFits` where the invariant holds at a border of the chain (`hb`). -/
theorem head_bookFits {b : Nat} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    VerifiableInference.Desc.Book.BookFits s.book :=
  reach_bookFits h (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)

/-- `BookFits` after a sub-protocol's step, to a state without a mark. -/
theorem head_bookFits_next {b : Nat} {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') (h0 : s'.failed = none) :
    VerifiableInference.Desc.Book.BookFits s'.book :=
  reach_bookFits h
    (head_reach_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hd hS) h0

/-- `BookFits` after the step of one of the chain's first 353 sub-protocols. -/
theorem head_bookFits_next_front {b : Nat} (hb : b < 353) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    VerifiableInference.Desc.Book.BookFits s'.book :=
  reach_bookFits_front h
    (head_reach_next h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hd hS) hb

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.reach_bookFits
#print axioms ProofFile.Honest.FirstThread.reach_bookFits_front
#print axioms ProofFile.Honest.FirstThread.head_bookFits_next_front
#print axioms ProofFile.Honest.FirstThread.head_bookFits
#print axioms ProofFile.Honest.FirstThread.head_bookFits_next
