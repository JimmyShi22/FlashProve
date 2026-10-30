-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ReaderAt.lean: what the library's reader of a segment's mask
row returns, at a message with one mask row. It holds two definitions of hypotheses, three lemmas,
and a made-up example at which the first hypothesis holds and one at which it fails.

Several sub-protocols' lemmas read the mask row off the thread's witness by
`(dataQ own a (seatTab cs arr ms v)).mask ν` (Johnson/Desc/Sound/FormsQ.lean,
Johnson/Desc/Sound/BordersFill.lean). That expression goes through six functions of the library.
Each of them branches on the verifier's state or on the plan: `maskOracle` chooses the message,
`seatAt` its seat, `seatTab` the member of `ms` at that seat, `numOf` the message's number in the
witness, `tabQ` splits the entry's index into a row and a place, and `Wit.tab` asks `padB` whether
the place belongs to the sample's pad. `ReaderFacts` lists, in that order, the one outcome of each
branch under which the expression is `v.msg n true 0 ν`.

With it, the hypothesis `ReaderReads` of Law/Rule/TiesFall.lean follows from one equation on the
Script's function `msg` (Honest/Thread/First.lean).

  1  `ReaderFacts`, `ReaderAt`   the six facts, about a frame, a book and a statement; the same at
     an open segment's part
  2  `reader_facts`, `reader_at`   under them the reader returns the witness's message `n`
  3  `readerReads_one`   `ReaderReads` for the first chain's thread
  4  `ReaderToy`   a made-up frame, book and statement: the facts hold up to entry 7 and fail up to
     entry 8, where the pad's place is

Limits.
  * One mask row only (`rowBits = 0`). With more mask rows the library's index of an entry and the
    format's number of it agree only if the number of rows is a power of two; that case is not
    treated here.
  * Nothing here shows `ReaderAt` at a state of the protocol.
  * Nothing here shows the equation `hQ` for any Script.
  * The example is made up; it is no state of the protocol.
  * No statement about distributions is made.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Wit padB)
open VerifiableInference.Desc.K9 (segAt? seatAt)
open VerifiableInference.Desc.K9L (dataOf maskOracle)
open VerifiableInference.Desc.Sound (MsgT Mem seatOf numOf seatTab memTab tabQ dataQ)

/-! ## 1 The six facts -/

/-- The facts that the reader of a segment's mask row uses. `f`, `book`, `st`: the frame, the book
of trees and the statement of the verifier's state. `own`: the seats that may be read. `n`: the
number, in the witness, of the message that holds the mask row. `free`: up to which entry. This
defines a hypothesis; the definition claims nothing. -/
def ReaderFacts (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (own : List (ℕ × ℕ))
    (f : OnBytes.ReqFrame) (book : OnBytes.TreeBook) (st : OnBytes.Statement) (n free : ℕ) : Prop :=
  ∃ (o : ℕ) (x : ℕ × ℕ) (y : Mem),
    maskOracle f = some o ∧
    seatAt own book o = some x ∧
    ms.find? (fun z => decide (seatOf z = x)) = some y ∧
    numOf arr y = n ∧
    st.rowBits o .mask = 0 ∧
    ∀ ν, ν < free → padB cs (y.1.l.get y.2).1 true 0 ν = false

/-- The same at an open segment's part `a`. This defines a hypothesis; the definition claims
nothing. -/
def ReaderAt (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (own : List (ℕ × ℕ))
    (a : VerifiableInference.Desc.K9.Part) (n free : ℕ) : Prop :=
  ReaderFacts cs arr ms own a.L.check.frame a.d.book a.d.st n free

/-! ## 2 What the reader returns -/

theorem reader_facts {Cells Tok : Type} {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem}
    {own : List (ℕ × ℕ)} {f : OnBytes.ReqFrame} {book : OnBytes.TreeBook} {st : OnBytes.Statement}
    {n free : ℕ} (h : ReaderFacts cs arr ms own f book st n free) (Rr : OnBytes.ReqRows)
    (v : Wit Cells Tok MsgT) {ν : ℕ} (hν : ν < free) :
    (dataOf Rr f st (tabQ own st book (seatTab cs arr ms v))).mask ν = v.msg n true 0 ν := by
  obtain ⟨o, x, y, h1, h2, h3, h4, h5, h6⟩ := h
  show (match maskOracle f with
    | some o => tabQ own st book (seatTab cs arr ms v) o .mask ν
    | none => 0) = _
  rw [h1]
  show tabQ own st book (seatTab cs arr ms v) o .mask ν = _
  unfold tabQ
  rw [h2, h5]
  show seatTab cs arr ms v x true (ν % 2 ^ 0) (ν / 2 ^ 0) = _
  rw [pow_zero, Nat.mod_one, Nat.div_one]
  unfold seatTab
  rw [h3]
  show (if padB cs (y.1.l.get y.2).1 true 0 ν = true then _ else v.msg (numOf arr y) true 0 ν) = _
  rw [h6 ν hν, h4]
  rfl

theorem reader_at {Cells Tok : Type} {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem}
    {own : List (ℕ × ℕ)} {a : VerifiableInference.Desc.K9.Part} {n free : ℕ}
    (h : ReaderAt cs arr ms own a n free) (v : Wit Cells Tok MsgT) {ν : ℕ} (hν : ν < free) :
    (dataQ own a (seatTab cs arr ms v)).mask ν = v.msg n true 0 ν :=
  reader_facts h a.L.check.rows v hν

/-! ## 3 The hypothesis on the reader, from one equation on the Script -/

/-- `L`: the first chain's parameters. `val`: the conversion into the reader's field. `rowOf`,
`ownC`: the sender's function for a mask entry, and the sender's own coins in a run's coins. -/
theorem readerReads_one {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
    (L : FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    {At : Coins Bk → VerifiableInference.Desc.First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}
    {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem} {own : List (ℕ × ℕ)} {n free : ℕ}
    {d : Due} {rowOf : Cs d → ℕ → OnBytes.E} {ownC : Coins Bk → Cs d}
    {val : OnBytes.E → OnBytes.Slice.GE}
    (hA : ∀ k s m En, At k s m En → ∀ a, segAt? s = some a → ReaderAt cs arr ms own a n free)
    (hQ : ∀ k w h ν, ν < free → L.Q.msg n k w h true 0 ν = val (rowOf (ownC k) ν)) :
    ReaderReads L.thread At segAt?
      (fun a _ _ (v : Wit Cells Tok MsgT) ν => (dataQ own a (seatTab cs arr ms v)).mask ν) val
      (fun k _ _ ν => rowOf (ownC k) ν) (· < free) := by
  intro k s m En hAt a ha ds ν hν
  exact (reader_at (hA k s m En hAt a ha) (L.Q.wit k m.st.input (m.st.heard ++ ds)) hν).trans
    (hQ k _ _ ν hν)

/-! ## 4 A made-up example -/

namespace ReaderToy

def cs : OnBytes.Codes := { mask := #[⟨3, 8, 1⟩] }
def sh : OnBytes.OracleShape := { maskRows := 1, maskCode := 0, answers := 1 }
def fr : OnBytes.ReqFrame :=
  { shape := { code := 0, maskCode := 0
               link := [{ plain := 0
                          messages := [{ shape := sh, leafClass := 0, moment := 0, life := 0 }] }]
               atStart := [], answers := 1, last := [], choice := default }
    groups := #[], next := .laterOrClose, link := 0, own := #[5] }
def bk : OnBytes.TreeBook := { place := #[(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (2, 1)] }
def st : OnBytes.Statement := { oracles := (Array.replicate 5 default).push { shape := sh } }
def mem : Mem := ⟨⟨[(sh, 0)], fun _ => (2, 1)⟩, ⟨0, by decide⟩⟩
def arr : ℕ → ℕ → ℕ := fun j t => 10 * j + t

/-- The facts hold up to entry 7. -/
theorem holds : ReaderFacts cs arr [mem] [(2, 1)] fr bk st 21 7 :=
  ⟨5, (2, 1), mem, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- They fail up to entry 8: entry 7 is the pad's place. -/
theorem fails : ¬ ReaderFacts cs arr [mem] [(2, 1)] fr bk st 21 8 := by
  rintro ⟨o, x, y, h1, h2, h3, -, -, h6⟩
  have e1 : maskOracle fr = some 5 := rfl
  rw [e1] at h1
  cases h1
  have e2 : seatAt [(2, 1)] bk 5 = some (2, 1) := rfl
  rw [e2] at h2
  cases h2
  have e3 : [mem].find? (fun z => decide (seatOf z = (2, 1))) = some mem := rfl
  rw [e3] at h3
  cases h3
  exact absurd (h6 7 (by decide)) (by decide)

end ReaderToy

end ProofFile.Honest

#print axioms ProofFile.Honest.reader_facts
#print axioms ProofFile.Honest.reader_at
#print axioms ProofFile.Honest.readerReads_one
#print axioms ProofFile.Honest.ReaderToy.holds
#print axioms ProofFile.Honest.ReaderToy.fails
