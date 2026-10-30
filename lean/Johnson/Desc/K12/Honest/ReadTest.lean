-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadTest.lean: `ReadAsks` (Johnson/Desc/K12/Honest/ReadWhole.lean) as a test
with code, so that its clauses can be checked together at a value by an evaluation. The only
evaluations lie in Johnson/Desc/ProofFile/Honest/K12/ToyReads.lean (not in the library yet).
`ReadAsks` is the hypothesis under which ReadWhole.lean proves that the reading of the old rows in a
code switch of a proximity test (`Tw.L9.readOld`, Johnson/Top/H0/Tw/L9/Switch.lean; below: the
reading) accepts. The test `readAsksB` returns a `Bool`; where it returns "true", `ReadAsks` holds
and the reading accepts. General: at every input i of a switch (`SwIn`, Switch.lean) and every list
of positions pos (`Positions`, OnBytes/Iop/Ground.lean). Definitions with code, statements and
proofs. It depends on no frame for an honest side: it uses nothing of
Johnson/Desc/ProofFile/Honest/Frame.lean.

In the list: the book (`TreeBook`, OnBytes/Iop/Ground.lean) holds the trees sent so far (`trees`)
and for each oracle message its place (`place`): the index of its tree in `trees`, and its index
among that tree's parts. A tree's place is its index in `trees`. A tree's own list is `Blk.ownList`
(same file): the positions at which the tree is opened under pos. The dealt columns are `i.opened`:
the list of columns (`Col`) from which the reading takes. The statement is `i.st` (`Statement`, same
file). The old rows are `i.old` (`SingleRows`, OnBytes/Iop/Fold.lean); a member is an oracle message
in `i.old.layout.members`.

  `read_yes_test`: where `readAsksB i pos` is "true", `readOld i pos` accepts and leaves no column:
    it returns some book, the empty list of columns and some array of symbols
  `readAsks_of`: where `readAsksB i pos` is "true", there is an array places at which
    `ReadAsks i pos places` holds, with `treeOf i.book` for the trees and `csOf`, at the book, pos,
    `treesAt places` and the dealt columns, for each tree's columns
  `readAsksB i pos`: a definition: the test. It looks up the place of every oracle message that must
    be opened (`singleRowsOracles i.old`, OnBytes/Iop/Fold.lean) and is "false" if one has none (the
    field `placed`). Else it is the conjunction of the other fields of `ReadAsks`, in their order,
    each as a `Bool`, at `treeOf` and `csOf`; `kept`, `main` and `mask` are `memberB` at every
    member. Where `main`, `mask` and `fresh` say "if the statement has this oracle message", the
    test is "false" if it has not
  `memberB i w`: a definition: the test's clauses on member number w: `kept` has no "true" at w; the
    statement has the oracle message; `fitB` at `mainFirst`, `mainRows` and 2 ^ `k`, and at
    `maskFirst`, `maskRows` and 2 ^ `h`
  `treeAsksB`: a definition: `TreeAsks` (Johnson/Desc/K12/Honest/ReadTrees.lean) at the tree
    `treeOf B0 t`, as a test; `treeAsks_of`: its "true" gives `TreeAsks` there
  `fitB first rows cap`: a definition: a test that rows have a first row and fit a table, or are
    none: rows is 0, or first is some f with f + rows ≤ cap; `fit_of`: its "true" gives this as a
    proposition
  `treeOf B t`: a definition: the tree at place t of the book B; the default tree if there is none
  `chunks B pos ts l`, `csOf B pos ts l t`: definitions: the columns l cut tree after tree, each
    tree of ts taking as many as its own list has; what is left after the last tree is dropped.
    `csOf` is what `chunks` cuts for t, and the empty list if t is not in ts

By what. `read_yes_test` takes `ReadAsks` from `readAsks_of` and calls `read_yes_trees`
(Johnson/Desc/K12/Honest/ReadWhole.lean). `readAsks_of` unfolds the test and splits its conjunction;
`treeAsks_of` gives the field `tree`, and `fit_of` the fields `main` and `mask`.

Limits. A "true" at a value is an evaluation by Lean's evaluator, outside the kernel. This file
evaluates the test at no value: no file of the library evaluates `readAsksB` or states `ReadAsks` at
written values. Outside this file `readAsks_of`, `read_yes_test`, `treeAsksB` and `treeAsks_of` are
called
nowhere; Johnson/Desc/K12/Honest/Shape/ReadShape.lean uses `treeOf`, `fitB` and `fit_of`, and
Johnson/Desc/K12/Honest/Shape/ReadFirst.lean uses `treeOf`. Only the direction from the test's
"true" to `ReadAsks` and to the reading's acceptance is proved; no converse is stated.
`read_yes_test` does not say which book and which symbols the reading returns. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc
open Tw.L9 (Col SwIn readOld)

/-- The tree at place t of the book: index t of `B.trees`; the default tree if there is none. -/
def treeOf (B : TreeBook) (t : Nat) : Tree := (B.trees[t]?).getD default

/-- The columns cut tree after tree: each tree of the list takes as many as its own list has. -/
def chunks (B : TreeBook) (pos : Positions) : List Nat → List Col → List (Nat × List Col)
  | [], _ => []
  | t :: ts, l =>
    (t, l.take (Blk.ownList (treeOf B t) pos).size) ::
      chunks B pos ts (l.drop (Blk.ownList (treeOf B t) pos).size)

/-- What `chunks` cuts for the tree at place t; the empty list if t is not in ts. -/
def csOf (B : TreeBook) (pos : Positions) (ts : List Nat) (l : List Col) (t : Nat) : List Col :=
  ((chunks B pos ts l).lookup t).getD []

/-- `TreeAsks` at the tree `treeOf B0 t`, as a test. -/
def treeAsksB (S : Statement) (F : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (cs : List Col) : Bool :=
  (B0.trees[t]?).isSome && shareOk S (treeOf B0 t) &&
  (!(treeOf B0 t).oneList || (treeOf B0 t).lists == 0) &&
  decide ((treeOf B0 t).shape.logN ≤ pos.logN) &&
  decide (cs.length = (Blk.ownList (treeOf B0 t) pos).size) &&
  Own.colsStand ((treeOf B0 t).number - F)
    ((treeOf B0 t).shape.mainWidth + (treeOf B0 t).shape.maskWidth) cs
    (Blk.ownList (treeOf B0 t) pos).toList

theorem treeAsks_of {S : Statement} {F : Nat} {pos : Positions} {B0 : TreeBook} {t : Nat}
    {cs : List Col} (h : treeAsksB S F pos B0 t cs = true) :
    TreeAsks S F pos B0 t (treeOf B0 t) cs := by
  simp only [treeAsksB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 a1
  exact ⟨by unfold treeOf; rw [hT]; rfl, a2, a3, a4, a5, a6⟩

/-- A test: rows is 0, or first is some f with f + rows ≤ cap. -/
def fitB (first : Option Nat) (rows cap : Nat) : Bool :=
  rows == 0 || match first with
    | some f => decide (f + rows ≤ cap)
    | none => false

theorem fit_of {first : Option Nat} {rows cap : Nat} (h : fitB first rows cap = true) :
    rows = 0 ∨ ∃ f, first = some f ∧ f + rows ≤ cap := by
  unfold fitB at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact .inl (beq_iff_eq.1 h)
  · cases first with
    | none => cases h
    | some f => exact .inr ⟨f, rfl, of_decide_eq_true h⟩

/-- The test's clauses on member number w of the old rows' layout. -/
def memberB (i : SwIn) (w : Nat) : Bool :=
  !i.old.layout.kept.getD w false &&
  match i.st.oracles[i.old.layout.members.getD w 0]? with
  | some x =>
    fitB (i.old.layout.mainFirst.getD w none) x.shape.mainRows (2 ^ i.old.layout.k) &&
      fitB (i.old.layout.maskFirst.getD w none) x.shape.maskRows (2 ^ i.old.layout.h)
  | none => false

/-- The test: "false" if an oracle message that must be opened has no place in the book; else the
other fields of `ReadAsks`, in their order, as one `Bool`. -/
def readAsksB (i : SwIn) (pos : Positions) : Bool :=
  match (singleRowsOracles i.old).mapM fun o => i.book.place[o]? with
  | some places =>
    ((treesAt places).all fun t =>
      ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all (singleRowsOracles i.old).contains) &&
    ((treesAt places).all fun t => treeAsksB i.st i.firstTree pos i.book t
      (csOf i.book pos (treesAt places) i.opened t)) &&
    decide (i.opened = (treesAt places).flatMap (csOf i.book pos (treesAt places) i.opened)) &&
    ((singleRowsOracles i.old).toList.all fun o => (i.st.oracles[o]?).isSome) &&
    (pos.all.toList.all fun x => decide (x ∈ pos.draws.toList)) &&
    Own.shapeFits i.old && decide (i.old.masks = 2) && decide (i.old.keptRows = 0) &&
    ((List.range i.old.layout.members.size).all (memberB i)) &&
    (match i.st.oracles[i.old.fresh]? with
      | some x => decide (x.shape.maskRows = 2 ^ i.old.layout.h)
      | none => false)
  | none => false

/-- **The test's "true" gives `ReadAsks`**, at `treeOf` and `csOf`. -/
theorem readAsks_of {i : SwIn} {pos : Positions} (h : readAsksB i pos = true) :
    ∃ places, ReadAsks i pos places (treeOf i.book)
      (csOf i.book pos (treesAt places) i.opened) := by
  unfold readAsksB at h
  cases hp : (singleRowsOracles i.old).mapM fun o => i.book.place[o]? with
  | none => simp [hp] at h
  | some places =>
    simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := h
    have hm : ∀ w, w < i.old.layout.members.size → memberB i w = true := fun w hw =>
      List.all_eq_true.1 a9 w (List.mem_range.2 hw)
    have hget : ∀ w (hw : w < i.old.layout.members.size),
        i.old.layout.members.getD w 0 = i.old.layout.members[w] := fun w hw => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
      rfl
    refine ⟨places, hp, a1, fun t ht => treeAsks_of (List.all_eq_true.1 a2 t ht), a3,
      fun o ho => Option.isSome_iff_exists.1 (List.all_eq_true.1 a4 o ho),
      fun x hx => of_decide_eq_true (List.all_eq_true.1 a5 x hx), a6, a7, a8, fun w hw => ?_,
      fun w hw x hx => ?_, fun w hw x hx => ?_, fun x hx => ?_⟩
    · have k := hm w hw
      unfold memberB at k
      rw [Bool.and_eq_true] at k
      simpa using k.1
    · have k := hm w hw
      unfold memberB at k
      rw [hget w hw, hx, Bool.and_eq_true, Bool.and_eq_true] at k
      exact fit_of k.2.1
    · have k := hm w hw
      unfold memberB at k
      rw [hget w hw, hx, Bool.and_eq_true, Bool.and_eq_true] at k
      exact fit_of k.2.2
    · rw [hx] at a10
      exact of_decide_eq_true a10

/-- **The test's "true" gives that the reading accepts** and leaves no column. -/
theorem read_yes_test {i : SwIn} {pos : Positions} (h : readAsksB i pos = true) :
    ∃ B y, readOld i pos = .ok (B, [], y) := by
  obtain ⟨places, A⟩ := readAsks_of h
  obtain ⟨y, hy⟩ := read_yes_trees i pos places _ _ A
  exact ⟨_, y, hy⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.treeAsks_of
#print axioms ProofFile.Honest.K12.fit_of
#print axioms ProofFile.Honest.K12.readAsks_of
#print axioms ProofFile.Honest.K12.read_yes_test
#print axioms ProofFile.Honest.K12.treeOf
#print axioms ProofFile.Honest.K12.chunks
#print axioms ProofFile.Honest.K12.csOf
#print axioms ProofFile.Honest.K12.treeAsksB
#print axioms ProofFile.Honest.K12.fitB
#print axioms ProofFile.Honest.K12.memberB
#print axioms ProofFile.Honest.K12.readAsksB
