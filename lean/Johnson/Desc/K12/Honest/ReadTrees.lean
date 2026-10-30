-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadTrees.lean: of the reading of the old rows in a code switch, at a list
of trees: the loop that opens the trees accepts. A code switch of a proximity test reads the symbols
of its old rows (the carried rows, the field `old` of `SwIn`) out of dealt columns (`Tw.L9.readOld`,
Johnson/Top/H0/Tw/L9/Switch.lean). At a test's first code switch the rows' oracle messages can be in
several trees, of several depths (a small made-up place of that kind:
Johnson/Desc/ProofFile/Honest/K12/ToyCame.lean). `readOld` opens these trees one after the other, by
a loop over `Tw.L9.openOne` (Switch.lean). This file says under which clauses that loop accepts,
whatever words the columns hold. Definitions, statements and proofs; general in the statement, the
book, the positions and the list of trees. The file does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean): the only file that it imports is Switch.lean.

In the list: S is the statement (`Statement`, OnBytes/Iop/Ground.lean), which holds the oracle
messages, each under a number. A book (`TreeBook`, Ground.lean) holds the trees; t is the place of a
tree in the book. A tree T (`Tree`, Ground.lean) has a depth `shape.logN` (its length is 2 to that
power), a number, its parts (the numbers of the oracle messages in it), the field `oneList` (by
Ground.lean: it holds an oracle message without a sample, so it is opened at one list only) and the
count `lists` (at how many lists it has been opened). pos (`Positions`, Ground.lean) is a list of
positions with a range (`logN`). The tree's own list under the positions is `Blk.ownList T pos`
(Ground.lean): the list at which T is opened. A dealt column (`Col`, Switch.lean) is a key, a
position and a list of words. The loop's state is a book, the dealt columns that are left, and what
has been set aside for the trees opened so far (an array of `Own.Opened`,
Johnson/Desc/Own/Symbols.lean). Bc is the book in the loop's state. F and B0 are what `openOne` is
given next to the state: in `readOld`, the number of the chain's first tree and the book before the
loop.

  `open_all`: the loop. The trees' places are pairwise different · `TreeAsks` at each · at each, Bc
    has the tree of B0 ⟹ the loop over the trees accepts, takes just the trees' dealt columns off
    the front, counts one list more at each tree, and sets aside `laidBy` for each, in order. That
    is: the fold of `openOne S F pos B0` over a list ts of places, from the state (Bc, the columns
    `cs t` of each t in ts, in order, and then rest, acc), returns `.ok` of (`bump Bc ts`, rest, acc
    and then `laidBy pos t (TT t) (cs t)` for each t in ts, in order). At every rest and acc
  `open_one`: one turn of the loop. Under `TreeAsks S F pos B0 t T cs`, and where Bc has T at place
    t: `openOne S F pos B0 t` at the state (Bc, cs and then rest, acc) returns `.ok` of Bc with one
    list more counted at place t, rest, and acc with `laidBy pos t T cs` appended
  `TreeAsks S F pos B0 t T cs`: a definition: what the loop asks of one tree, a structure of
    propositions. It is in the book: T is the tree at place t of B0 (`there`); `shareOk S T` passes
    (`share`); where it may be opened only once (`T.oneList`), it has not been opened (`once`); it
    is not longer than the positions' range (`short`); `Dealt F pos T cs` (`dealt`)
  `Dealt F pos T cs`: a definition: cs is one tree's dealt columns: as many as the tree's own list
    under the positions, each with the tree's key (`T.number - F`), at the list's position, of the
    tree's width (`T.shape.mainWidth + T.shape.maskWidth` words). The test on key, position and
    width is `Own.colsStand` (Johnson/Desc/Own/Shapes.lean)
  `shareOk S T`: a definition: the reading's test on what shares a leaf, at one tree. It takes the
    parts of T that are in S and are sampled (`shape.answers` is not 0). Their lists of groups must
    all be the same, and where `T.oneList` is set that list has at most one group. Where there is no
    such part the test passes
  `bump B ts`: a definition: the book B with one list more counted at the tree at each place in ts
  `laidBy pos t T cs`: a definition: what the loop sets aside for one tree: its place t, its own
    list under the positions, and the words of each column of cs

By what. The proofs unfold `openOne` and call no lemma of another file of this library. In
`open_one`, that the test on what shares a leaf in the text of `openOne` is `shareOk` holds by
unfolding. `open_all` goes by recursion on ts and calls `open_one` at the first place; since the
places are pairwise different, the count at that place leaves the book's trees at the later places
as they are, so the third hypothesis holds again.

Hypotheses of `open_all`. `ts.Nodup`: no place is in ts twice. `TreeAsks S F pos B0 t (TT t) (cs t)`
at every t in ts. `Bc.trees[t]? = B0.trees[t]?` at every t in ts: at these places the book in the
state has the trees of B0.

Limits. Of the reading only the loop over the trees. The look-up of the messages' places in the book
and the test that their trees hold no other message, which come before the loop in `readOld`, are
not in this file. That each message's symbols are found in what was set aside, and that they fit the
layout, is not in this file (Johnson/Desc/K12/Honest/ReadSymbols.lean,
Johnson/Desc/K12/Honest/ReadRows.lean). No statement of this file names `readOld`: the two theorems
are on `openOne` and on its fold; `read_yes_trees` (Johnson/Desc/K12/Honest/ReadWhole.lean) calls
`open_all` at the fold as `readOld` has it. `TreeAsks` is a hypothesis: this file proves it at no S,
F, pos, B0, t, T and cs. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Top.H0.Tw.L9.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc
open Tw.L9 (Col openOne)

/-- The reading's test on what shares a leaf, at one tree. -/
def shareOk (S : Statement) (tree : Tree) : Bool :=
  match tree.parts.toList.filterMap fun o =>
      (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups with
  | [] => true
  | a :: l => l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1))

/-- One tree's dealt columns. F is the number of the chain's first tree. -/
def Dealt (F : Nat) (pos : Positions) (T : Tree) (cs : List Col) : Prop :=
  cs.length = (Blk.ownList T pos).size ∧
    Own.colsStand (T.number - F) (T.shape.mainWidth + T.shape.maskWidth) cs
      (Blk.ownList T pos).toList = true

/-- The book with one list more counted at each tree of the list. -/
def bump (B : TreeBook) : List Nat → TreeBook
  | [] => B
  | t :: ts => bump { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } } ts

/-- What the loop sets aside for one tree. -/
def laidBy (pos : Positions) (t : Nat) (T : Tree) (cs : List Col) : Own.Opened :=
  (t, Blk.ownList T pos, (cs.map fun y => y.2.2.toArray).toArray)

/-- What the loop asks of one tree. -/
structure TreeAsks (S : Statement) (F : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat) (T : Tree)
    (cs : List Col) : Prop where
  there : B0.trees[t]? = some T
  share : shareOk S T = true
  once : (!T.oneList || T.lists == 0) = true
  short : T.shape.logN ≤ pos.logN
  dealt : Dealt F pos T cs

/-- One turn of the loop. Bc is the book in the loop's state; at this tree's place it has the same
tree as B0, the book before the loop. -/
theorem open_one (S : Statement) (F : Nat) (pos : Positions) (B0 Bc : TreeBook) (t : Nat) (T : Tree)
    (cs rest : List Col) (acc : Array Own.Opened) (A : TreeAsks S F pos B0 t T cs)
    (hc : Bc.trees[t]? = some T) :
    openOne S F pos B0 t (Bc, cs ++ rest, acc) =
      .ok ({ Bc with trees := Bc.trees.modify t fun x => { x with lists := x.lists + 1 } }, rest,
        acc.push (laidBy pos t T cs)) := by
  have htake : (cs ++ rest).take (Blk.ownList T pos).size = cs := by
    rw [← A.dealt.1, List.take_left']
    rfl
  have hdrop : (cs ++ rest).drop (Blk.ownList T pos).size = rest := by
    rw [← A.dealt.1, List.drop_left']
    rfl
  unfold openOne
  simp only [hc, A.there, A.once, decide_eq_true A.short, htake, hdrop, A.dealt.1, A.dealt.2,
    Bool.not_true, Bool.false_eq_true, if_false, beq_self_eq_true, Bool.and_self, if_true]
  show (if (!shareOk S T) = true then _ else _) = _
  rw [A.share]
  rfl

/-- **The loop over the trees.** -/
theorem open_all (S : Statement) (F : Nat) (pos : Positions) (B0 : TreeBook) (TT : Nat → Tree)
    (cs : Nat → List Col) : ∀ (ts : List Nat) (Bc : TreeBook) (rest : List Col)
    (acc : Array Own.Opened), ts.Nodup → (∀ t ∈ ts, TreeAsks S F pos B0 t (TT t) (cs t)) →
    (∀ t ∈ ts, Bc.trees[t]? = B0.trees[t]?) →
    ts.foldlM (fun s t => openOne S F pos B0 t s) (Bc, ts.flatMap cs ++ rest, acc) =
      .ok (bump Bc ts, rest, acc ++ (ts.map fun t => laidBy pos t (TT t) (cs t)).toArray)
  | [], Bc, rest, acc, _, _, _ => by
    simp [bump]
    rfl
  | t :: ts, Bc, rest, acc, hn, hA, hB => by
    have A := hA t (List.mem_cons_self ..)
    have hc : Bc.trees[t]? = some (TT t) := (hB t (List.mem_cons_self ..)).trans A.there
    rw [List.foldlM_cons, List.flatMap_cons, List.append_assoc,
      open_one S F pos B0 Bc t (TT t) (cs t) _ acc A hc]
    show ts.foldlM _ _ = _
    rw [open_all S F pos B0 TT cs ts _ rest _ (List.nodup_cons.1 hn).2
      (fun u hu => hA u (List.mem_cons_of_mem _ hu)) fun u hu => by
        have hne : t ≠ u := fun e => (List.nodup_cons.1 hn).1 (e ▸ hu)
        show (Bc.trees.modify t _)[u]? = _
        rw [Array.getElem?_modify, if_neg hne]
        exact hB u (List.mem_cons_of_mem _ hu)]
    simp [bump]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.open_one
#print axioms ProofFile.Honest.K12.open_all
#print axioms ProofFile.Honest.K12.shareOk
#print axioms ProofFile.Honest.K12.Dealt
#print axioms ProofFile.Honest.K12.bump
#print axioms ProofFile.Honest.K12.laidBy
#print axioms ProofFile.Honest.K12.TreeAsks
