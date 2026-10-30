-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/LayoutRead/Pieces.lean: THE LAYOUT FILE's READER (OnBytes.Plan.layoutRead,
OnBytes/Plan/ReqFrame.lean) CUT AT LINE ENDS: general laws, at every text: nothing is evaluated
here.

Why. Lean's kernel bears that reader's own routines on a written list of bytes, at a cost that grows
with the bytes (measured on pieces of 25, 100 and 400 lines: that they return, and two counts); it
does not bear the whole file out of
one String literal. With these laws the reader's value at a text that is a row of pieces, each
ending in a line feed, is had from one closed fact a piece.

Main names. A piece: a list of bytes. rev2 x: a reader's two lists, each turned round: the file's
order.
  `linesLoop_done`: the lines that are done are only handed on: linesLoop t cur done is done, turned
    round, in front of linesLoop t cur [].
  `linesLoop_cut`: behind a line feed the loop stands at an empty line.
  **`linesOf_append`**: linesOf ((a ++ [10]) ++ b) = linesOf (a ++ [10]) ++ linesOf b.
  **`gatherLines_append`**: gatherLines (l₁ ++ l₂) out = (gatherLines l₁ out).bind (gatherLines l₂).
  **`gatherLines_onto`**: what is gathered already is only handed on: gatherLines l out is
    gatherLines l {} laid in front of out.
  `PieceIs p v`: THE CLOSED FACT OF ONE PIECE: p ends in a line feed, and the reader's routines at p
    alone return v, in the file's order. `pieceB`, `pieceIs_of_test`: the same as a test with code.
  **`gather_pieces`**, **`layoutRead_pieces`**: where each piece has its fact, the reader at the
    pieces in a row returns the values in a row.
Limits. No piece is shown to have its fact here. That a given file's bytes are such a row of pieces
is a premise (hb). Nothing on what the lines mean. Nothing on soundness.

-/
import OnBytes.Plan.ReqFrame
import Ladder.FilesReadLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.LayoutRead
open OnBytes.Plan

/-- The lines that are done are only handed on. -/
theorem linesLoop_done : ∀ (t cur : List UInt8) (done : List (List UInt8)),
    linesLoop t cur done = done.reverse ++ linesLoop t cur []
  | [], [], done => by simp [linesLoop]
  | [], c :: cur, done => by simp [linesLoop]
  | c :: l, cur, done => by
    by_cases h : (c == 10) = true
    · simp only [linesLoop, h, if_true]
      rw [linesLoop_done l [] (cur.reverse :: done), linesLoop_done l [] [cur.reverse]]
      simp
    · simp only [linesLoop, h, if_false, Bool.false_eq_true]
      exact linesLoop_done l (c :: cur) done

/-- Behind a line feed the loop stands at an empty line, with some lines done, whatever follows. -/
theorem linesLoop_cut : ∀ (a cur : List UInt8) (done : List (List UInt8)),
    ∃ D, ∀ b, linesLoop (a ++ 10 :: b) cur done = linesLoop b [] D
  | [], cur, done => ⟨cur.reverse :: done, fun b => by simp [linesLoop]⟩
  | c :: a, cur, done => by
    by_cases h : (c == 10) = true
    · obtain ⟨D, hD⟩ := linesLoop_cut a [] (cur.reverse :: done)
      exact ⟨D, fun b => by
        rw [List.cons_append]
        simp only [linesLoop, h, if_true]
        exact hD b⟩
    · obtain ⟨D, hD⟩ := linesLoop_cut a (c :: cur) done
      exact ⟨D, fun b => by
        rw [List.cons_append]
        simp only [linesLoop, h, if_false, Bool.false_eq_true]
        exact hD b⟩

/-- **The lines of a text behind a line feed are the lines in front, then the lines behind.** -/
theorem linesOf_append (a b : List UInt8) :
    linesOf ((a ++ [10]) ++ b) = linesOf (a ++ [10]) ++ linesOf b := by
  obtain ⟨D, hD⟩ := linesLoop_cut a [] []
  have e1 : linesOf ((a ++ [10]) ++ b) = linesLoop b [] D := by
    unfold linesOf
    rw [List.append_assoc, List.singleton_append]
    exact hD b
  have e2 : linesOf (a ++ [10]) = D.reverse := by
    unfold linesOf
    rw [hD []]
    simp [linesLoop]
  rw [e1, e2, linesLoop_done b [] D]
  rfl

/-- **The gathering of two rows of lines is the gathering of the first, then of the second.** -/
theorem gatherLines_append : ∀ (l₁ l₂ : List (List UInt8)) (out : LayoutLines),
    gatherLines (l₁ ++ l₂) out = (gatherLines l₁ out).bind (gatherLines l₂)
  | [], l₂, out => by simp [gatherLines]
  | line :: rest, l₂, out => by
    rw [List.cons_append]
    -- the second row's gathering stands as a letter while the first is opened
    generalize hf : gatherLines l₂ = f
    unfold gatherLines
    split
    · subst hf
      exact gatherLines_append rest l₂ out
    · split
      · subst hf
        exact gatherLines_append rest l₂ _
      · subst hf
        exact gatherLines_append rest l₂ _
      · rfl

/-- x laid in front of out: both lists stand the last line first. -/
def onto (out x : LayoutLines) : LayoutLines := ⟨x.groups ++ out.groups, x.blocks ++ out.blocks⟩

/-- **What is gathered already is only handed on.** -/
theorem gatherLines_onto : ∀ (l : List (List UInt8)) (out : LayoutLines),
    gatherLines l out = (gatherLines l {}).map (onto out)
  | [], out => by simp [gatherLines, onto]
  | line :: rest, out => by
    unfold gatherLines
    split
    · exact gatherLines_onto rest out
    · split
      · rename_i b _
        rw [gatherLines_onto rest { out with blocks := b :: out.blocks },
          gatherLines_onto rest
            { ({} : LayoutLines) with blocks := b :: ({} : LayoutLines).blocks },
          Option.map_map]
        congr 1
        funext x
        simp [onto]
      · rename_i g _
        rw [gatherLines_onto rest { out with groups := g :: out.groups },
          gatherLines_onto rest
            { ({} : LayoutLines) with groups := g :: ({} : LayoutLines).groups },
          Option.map_map]
        congr 1
        funext x
        simp [onto]
      · rfl

/-- A reader's two lists, each turned round: the file's order. -/
def rev2 (x : LayoutLines) : LayoutLines := ⟨x.groups.reverse, x.blocks.reverse⟩

/-- **The closed fact of one piece**: it ends in a line feed, and the reader's routines at it alone
return v, in the file's order. -/
def PieceIs (p : List UInt8) (v : LayoutLines) : Prop :=
  (∃ a, p = a ++ [10]) ∧ (gatherLines (linesOf p) {}).map rev2 = some v

/-- The closed fact of one piece as a test with code. -/
def pieceB (p : List UInt8) (v : LayoutLines) : Bool :=
  (p.getLast? == some 10) && decide ((gatherLines (linesOf p) {}).map rev2 = some v)

/-- The test's yes gives the fact. -/
theorem pieceIs_of_test {p : List UInt8} {v : LayoutLines} (h : pieceB p v = true) :
    PieceIs p v := by
  unfold pieceB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨a, ha⟩ := List.getLast?_eq_some_iff.1 h.1
  exact ⟨⟨a, ha⟩, h.2⟩

/-- The values in a row. -/
def rowOf (vs : List LayoutLines) : LayoutLines :=
  ⟨vs.flatMap (·.groups), vs.flatMap (·.blocks)⟩

/-- **Where each piece has its fact, the routines at the pieces in a row return the values in a
row.** -/
theorem gather_pieces : ∀ (ps : List (List UInt8)) (vs : List LayoutLines),
    List.Forall₂ PieceIs ps vs →
      (gatherLines (linesOf ps.flatten) {}).map rev2 = some (rowOf vs)
  | [], [], _ => by simp [linesOf, linesLoop, gatherLines, rev2, rowOf]
  | p :: ps, v :: vs, h => by
    cases h with
    | cons hp hps =>
      obtain ⟨⟨a, rfl⟩, hv⟩ := hp
      have ih := gather_pieces ps vs hps
      rw [List.flatten_cons, linesOf_append, gatherLines_append]
      cases h1 : gatherLines (linesOf (a ++ [10])) {} with
      | none => rw [h1] at hv; cases hv
      | some x =>
        rw [h1] at hv
        have ex : rev2 x = v := Option.some.inj hv
        rw [Option.bind_some, gatherLines_onto (linesOf ps.flatten) x]
        cases h2 : gatherLines (linesOf ps.flatten) {} with
        | none => rw [h2] at ih; cases ih
        | some y =>
          rw [h2] at ih
          have ey : rev2 y = rowOf vs := Option.some.inj ih
          subst ex
          simp only [Option.map_some]
          congr 1
          have e1 : y.groups.reverse = (rowOf vs).groups := congrArg (·.groups) ey
          have e2 : y.blocks.reverse = (rowOf vs).blocks := congrArg (·.blocks) ey
          simp only [rev2, onto, rowOf, List.reverse_append, List.flatMap_cons] at e1 e2 ⊢
          rw [e1, e2]

/-- **The layout file's reader at a file whose bytes are such a row of pieces.** -/
theorem layoutRead_pieces {b : ByteArray} {ps : List (List UInt8)} {vs : List LayoutLines}
    (hb : b.data.toList = ps.flatten) (h : List.Forall₂ PieceIs ps vs) :
    layoutRead b = some (rowOf vs) := by
  unfold layoutRead
  rw [VerifierAndGoals.Read.toList_eq, hb]
  exact gather_pieces ps vs h

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.linesLoop_done
#print axioms Johnson.AtFull.LayoutRead.linesLoop_cut
#print axioms Johnson.AtFull.LayoutRead.linesOf_append
#print axioms Johnson.AtFull.LayoutRead.gatherLines_append
#print axioms Johnson.AtFull.LayoutRead.gatherLines_onto
#print axioms Johnson.AtFull.LayoutRead.pieceIs_of_test
#print axioms Johnson.AtFull.LayoutRead.gather_pieces
#print axioms Johnson.AtFull.LayoutRead.layoutRead_pieces
