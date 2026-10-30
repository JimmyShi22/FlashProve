-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SentTables.lean: the tables in the messages of a proximity test's
rounds, in the order of sending, and their columns. `testAll` (Test.lean in this folder; below: the
term) lists in its field `tr` (`BOut`, Johnson/Prover/Link/BodyAll.lean), for each round, a family
of columns: a function from a position to the column there, a list of words (`UInt64`). The message
of round i (`msgAt`, Parts.lean) has a table where `depthAt` (Test.lean) gives a depth, computed
from the list of stages and the job's field `fresh`: such a round is said to send a tree, and is
called a sending round. Its table is built from the family that the term lists at that round.
Here: the table of a sending round stands, in the list of all tables sent, at the number of sending
rounds in front of it; and its columns, as a view shows them, are the term's.
General: at every job J (`TestJob`, Test.lean: what a caller supplies for its test), input w, front
fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), coins C (`TestCoins`,
Test.lean) and sampled challenges D. Definitions and theorems.

  `sent_table`: under the two hypotheses below: in the list of the tables of the messages of the
    rounds 0 to N - 1, in order, each wrapped in `some`, the element number `sentBefore J r`,
    counted from 0, is `tableOf a` (TableCol.lean) of `treeAt` at r
  `col_treeAt`: for every number a, round r and position x: `Table.col` (the frame,
    Johnson/Desc/ProofFile/Honest/Frame.lean) of `tableOf a` of `treeAt` at r gives, at x, the
    column of `treeAt` at r and x. No hypothesis
  `treeAt`: a definition: the family number r of the term's `tr`; beyond the list, the family whose
    columns are all empty
  `sentBefore`: how many rounds in front of a round send a tree: public. A definition; its
    arguments are the job and a round's number r only: the number of i < r at which `depthAt J i`
    gives a depth
  `msgAt_tables`: the tables of the message of round i: none where `depthAt J i` is `none`; where
    it is `some a`, the one table `tableOf a` of `treeAt` at i
  `GoodCol`: a definition, of a family: at every position the column has the length of the column at
    position 0, and every word of it is the written form (`ofF`) of an element of the base field
    (`CanonW`, TableCol.lean)
  `good_stages`, `good_test`, `good_treeAt`: every family in the `tr` of `stagesAll`
    (Johnson/Desc/K12/Honest/Stages.lean), every family in the term's `tr`, and `treeAt` at every
    round are `GoodCol`
  `good_nil`, `good_aCol`, `good_freshCol`: so are the family of empty columns, `aCol` (Stages.lean:
    the written column of the tree that a switch sends) and `freshCol` (Test.lean: the column, as
    words, of a tree that holds a fresh table and nothing else)
  `flat_at`, `flat_length`: lemmas on lists. Each number i gives at most one element: `g i a` where
    `f i` is `some a`. In the list of these elements for i < N, in order, the element of a number
    r < N that gives one has as its index the count of the i < r that give one; that count is the
    length of the list for i < r

By what. `col_treeAt` is `col_tableOf` (TableCol.lean) at the two halves of `good_treeAt`.
`good_stages` goes by recursion on the list of stages and unfolds `stagesAll`: each family there is
the empty one or an `aCol`. `good_test` unfolds `testAll`: no family at an empty list of stages;
else the empty family, then those of `stagesAll`, the first of them replaced by a `freshCol` where
`J.fresh` is `none`. `good_aCol` and `good_freshCol` call `length_aCol`, `canonW_aCol` and
`canonW_freshCol` (TableCol.lean) and `length_freshCol` (FreshCols.lean). `msgAt_tables` holds by
unfolding. `sent_table` rewrites by `msgAt_tables` and is `flat_at` at `depthAt J`.

Hypotheses of `sent_table`. hr: r < N. h: `depthAt J r` is `some a`: round r sends a tree.

Limits. Whether a round sends a tree is read from `depthAt`, its family from the term: that the two
agree on the rounds is not stated here. Where `depthAt` gives a depth and the term lists the empty
family, or none, the table has width 0 (the widths: `width_treeAt`, FitsAll.lean). The list in
`sent_table` is written out in the statement: that a play of the frame collects this list is not
stated here. Nothing on what a description's rounds declare to open, on a decision, on completeness,
on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.TableCol

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- At every position the column has the length of the column at position 0, and every word of it is
the written form of an element of the base field (`CanonW`, TableCol.lean). -/
def GoodCol (col : ℕ → List UInt64) : Prop :=
  ∀ x, (col x).length = (col 0).length ∧ CanonW (col x)

theorem good_nil : GoodCol fun _ => [] := fun _ => ⟨rfl, fun _ h => by cases h⟩

theorem good_aCol (last : Bool) (next : Fmt.M1.Stage) (Q : PS) : GoodCol (aCol last next Q) :=
  fun x => ⟨length_aCol last next Q x, canonW_aCol last next Q x⟩

theorem good_freshCol (s : Sg) (P : PS) : GoodCol (freshCol s P) :=
  fun x => ⟨by rw [length_freshCol, length_freshCol], canonW_freshCol s P x⟩

/-- Every family in the field `tr` of `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) is
`GoodCol`, at all arguments. -/
theorem good_stages (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), ∀ col ∈ (stagesAll p K rest j cur l o t P trees D).tr, GoodCol col
  | [], j, cur, _, o, t, P, _, D, col, h => by
    have h' : col ∈ [fun _ => ([] : List UInt64), fun _ => []] := h
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h'
    rw [h']
    exact good_nil
  | next :: rest, j, cur, l, o, t, P, trees, D, col, h => by
    simp only [stagesAll, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with (⟨_, _, rfl⟩ | rfl | rfl) | h
    · exact good_nil
    · exact good_aCol _ _ _
    · exact good_nil
    · exact good_stages p K rest (j + 1) next _ _ _ _ _ D col h

/-- Every family in the field `tr` of `testAll` is `GoodCol`. -/
theorem good_test (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    ∀ col ∈ (testAll J w fr C D).tr, GoodCol col := by
  unfold testAll
  split
  · exact fun _ h => by cases h
  · intro col h
    rcases List.mem_cons.1 h with rfl | h
    · exact good_nil
    · split at h
      · rcases List.mem_or_eq_of_mem_set h with h | rfl
        · exact good_stages _ _ _ _ _ _ _ _ _ _ _ col h
        · exact good_freshCol _ _
      · exact good_stages _ _ _ _ _ _ _ _ _ _ _ col h

/-- The family number r in the field `tr` of `testAll`; beyond the list, the family whose columns
are all empty. -/
def treeAt (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) (r : ℕ) :
    ℕ → List UInt64 := (testAll J w fr C D).tr.getD r fun _ => []

theorem good_treeAt (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (r : ℕ) : GoodCol (treeAt J w fr C D r) := by
  unfold treeAt
  rw [List.getD_eq_getElem?_getD]
  cases h : (testAll J w fr C D).tr[r]? with
  | none => exact good_nil
  | some col => exact good_test J w fr C D col (List.mem_of_getElem? h)

/-- The tables of the message of round i: none where `depthAt J i` is `none`; where it is `some a`,
the one table `tableOf a` of `treeAt` at i. -/
theorem msgAt_tables (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) : (msgAt J w fr C D i).tables =
      (depthAt J i).toList.map fun a => tableOf a (treeAt J w fr C D i) := rfl

/-- **The table's column is the column that `testAll` lists.** At every number a, round r and
position x. -/
theorem col_treeAt (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a r x : ℕ) : (tableOf a (treeAt J w fr C D r)).col x = treeAt J w fr C D r x :=
  col_tableOf a _ x (good_treeAt J w fr C D r x).1 (good_treeAt J w fr C D r x).2

/-- The number of rounds i < r at which `depthAt J i` gives a depth. -/
def sentBefore (J : TestJob W X) (r : ℕ) : ℕ :=
  ((List.range r).filter fun i => (depthAt J i).isSome).length

section Flat
variable {α β : Type}

theorem flat_length (f : ℕ → Option α) (g : ℕ → α → β) : ∀ r : ℕ,
    ((List.range r).flatMap fun i => (f i).toList.map (g i)).length =
      ((List.range r).filter fun i => (f i).isSome).length
  | 0 => rfl
  | r + 1 => by
    rw [List.range_succ, List.flatMap_append, List.filter_append, List.length_append,
      List.length_append, flat_length f g r]
    cases h : f r <;> simp [h]

/-- Each number i gives at most one element: `g i a` where `f i` is `some a`. In the list of these
for i < N, in order, the element of r has as its index the count of the i < r that give one. -/
theorem flat_at (f : ℕ → Option α) (g : ℕ → α → β) (N r : ℕ) (a : α) (hr : r < N)
    (h : f r = some a) :
    ((List.range N).flatMap fun i => (f i).toList.map (g i))[((List.range r).filter fun i =>
      (f i).isSome).length]? = some (g r a) := by
  obtain ⟨q, rfl⟩ : ∃ q, N = r + (1 + q) := ⟨N - r - 1, by omega⟩
  rw [List.range_add, List.flatMap_append, ← flat_length f g r,
    List.getElem?_append_right (le_refl _), Nat.sub_self, Nat.add_comm 1 q, List.range_succ_eq_map,
    List.map_cons, List.flatMap_cons, Nat.add_zero, h]
  rfl

end Flat

/-- **Where the table of a round that sends a tree is in the list of all tables sent**: at the index
`sentBefore J r`. The list: the tables of the messages of the rounds below N, in order, each wrapped
in `some`. -/
theorem sent_table (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (N r a : ℕ) (hr : r < N) (h : depthAt J r = some a) :
    ((List.range N).flatMap fun i => (msgAt J w fr C D i).tables.map some)[sentBefore J r]? =
      some (some (tableOf a (treeAt J w fr C D r))) := by
  have e : (fun i => (msgAt J w fr C D i).tables.map some) = fun i =>
      (depthAt J i).toList.map fun a => some (tableOf a (treeAt J w fr C D i)) := by
    funext i
    rw [msgAt_tables, List.map_map]
    rfl
  rw [e]
  exact flat_at (depthAt J) (fun i a => some (tableOf a (treeAt J w fr C D i))) N r a hr h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.good_nil
#print axioms ProofFile.Honest.K12.good_aCol
#print axioms ProofFile.Honest.K12.good_freshCol
#print axioms ProofFile.Honest.K12.good_stages
#print axioms ProofFile.Honest.K12.good_test
#print axioms ProofFile.Honest.K12.good_treeAt
#print axioms ProofFile.Honest.K12.msgAt_tables
#print axioms ProofFile.Honest.K12.col_treeAt
#print axioms ProofFile.Honest.K12.flat_length
#print axioms ProofFile.Honest.K12.flat_at
#print axioms ProofFile.Honest.K12.sent_table
#print axioms ProofFile.Honest.K12.GoodCol
#print axioms ProofFile.Honest.K12.treeAt
#print axioms ProofFile.Honest.K12.sentBefore
