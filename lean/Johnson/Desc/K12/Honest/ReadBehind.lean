-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadBehind.lean: `ReadAsks` before a code switch's sending gives `ReadAsks`
after it. `ReadAsks` (Johnson/Desc/K12/Honest/ReadWhole.lean) is the hypothesis under which that
file proves that the reading of the old rows in a code switch of a proximity test (`Tw.L9.readOld`,
Johnson/Top/H0/Tw/L9/Switch.lean) accepts. A code switch first sends its new oracle messages, then
reads the old rows: at a statement and a book that have grown (in Lean: the field `read` of `Did`,
Johnson/Desc/K12/Law/SwDid.lean). Of the statement and the book, `ReadAsks` reads only the old rows'
oracle messages and their trees, and the sending leaves these as they were. Theorems with their
proofs; no definition. General in the two inputs of the reading, the positions, and the switch's
data, target and messages sent. `readAsks_behind` is called in Johnson/Desc/K12/Honest/ReadSwIn.lean
and Johnson/Desc/K12/Honest/Shape/ReadFirst.lean. It does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list and below: i and i' are inputs of the reading (`SwIn`, Switch.lean). Of their fields,
`st` is the statement (`Statement`, OnBytes/Iop/Ground.lean), `book` the book (`TreeBook`, same
file: the trees sent so far, and for each oracle message its place: its tree and its part of that
tree), `firstTree` the number of the chain's first tree, `opened` the dealt columns, and `old` the
old rows (`SingleRows`, OnBytes/Iop/Fold.lean). The messages asked for are `singleRowsOracles i.old`
(Fold.lean); their trees are those at the indexes `treesAt places` (ReadWhole.lean) of `book.trees`.

  `readAsks_behind`: `ReadAsks` at i gives `ReadAsks` at i', at the same `pos`, `places`, `TT` and
    `cs`, where i' has the statement and the book after a switch's sending (`Taken.stA`,
    `bookSentP`, SwDid.lean) and the rows, first tree and dealt columns of i
  `ReadAsks.of_same`: `ReadAsks` goes from i to i' where the two have the same rows, first tree and
    dealt columns, the books have the same entry of `place` at each message asked for and the same
    entry of `trees` at each index in `treesAt places`, and the statements have the same entry of
    `oracles` at each message asked for
  `treesSent_old`, `partsLaid_old`, `bookSentP_tree`, `bookSentP_place`: the book after a sending
    has the old trees and places as they were. `treesSent` (OnBytes/Slice/BlkSendRun.lean) leaves
    the entry at each index below `trees.size`, `partsLaid` (same file) at each index below `base`;
    so `bookSentP` has the tree of `Bk` at each index below `Bk.trees.size` and the place of `Bk` at
    each index below `Bk.place.size`
  `stA_old`: the statement after a switch's sending and admitting (`Taken.stA`) has the oracle
    message of S at each index below `S.oracles.size`
  `mapM_same`: two functions into `Option` that agree at each element of a list have the same `mapM`
    along it
  `foldl_modify_old`: a fold of `Array.modify` at indexes from `base` on leaves the entry at each
    index below `base`
  `lt_of_some`: where `a[k]?` is `some x`, k is below `a.size`

By what. `readAsks_behind` is `ReadAsks.of_same` at `bookSentP_place`, `bookSentP_tree` and
`stA_old`. That the indexes are below the old sizes follows from the fields `placed`, `tree` and
`oracle` of `ReadAsks` by `lt_of_some` and `OnBytes.Slice.array_mapM_inv`
(OnBytes/Slice/BlkOpenN.lean). `ReadAsks.of_same` goes field by field, with `mapM_same` at `placed`;
that the indexes read are among the messages asked for follows from the fields `masks`, `whole` and
`tree`. The others unfold `treesSent`, `partsLaid` and `stSent` (BlkSendRun.lean), `admitted`
(OnBytes/Slice/BlkCalls.lean), `Taken.stA` and `bookSentP`, with general lemmas on arrays.

Hypotheses. Of `readAsks_behind`: `ReadAsks` at i; `i'.old = i.old`; `i'.firstTree = i.firstTree`;
`i'.opened = i.opened`; `i'.st = D.stA T others i.st`;
`i'.book = bookSentP F roots i.st i.book sent D.lay`. D, T, `others`, `sent`, F and `roots` are free
parameters.

Limits. `ReadAsks` before the sending is a hypothesis; this file gives no value that meets it. That
the reading accepts is not stated here: that is `read_yes_trees` (ReadWhole.lean), which this file
does not call. That a switch's reading gets an input of the form of i' is not shown here. `sent` is
not tied to `sentOf T others` (OnBytes/Slice/BlkCsRun.lean), the messages that `Taken.stA` adds.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadWhole
import Johnson.Desc.K12.Law.SwDid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice
open VerifiableInference.Desc
open H2K.Sw
open Tw.L9 (SwIn)

theorem mapM_same {α β : Type} (f g : α → Option β) : ∀ l : List α, (∀ a ∈ l, f a = g a) →
    l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_same f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **`ReadAsks` depends on the statement and the book only at the messages asked for and at their
trees.** The two inputs have the same `old`, `firstTree` and `opened`. -/
theorem ReadAsks.of_same {i i' : SwIn} {pos : Positions} {places : Array (Nat × Nat)}
    {TT : Nat → Tree} {cs : Nat → List Tw.L9.Col} (A : ReadAsks i pos places TT cs)
    (hold : i'.old = i.old) (hF : i'.firstTree = i.firstTree) (hop : i'.opened = i.opened)
    (hpl : ∀ o ∈ (singleRowsOracles i.old).toList, i'.book.place[o]? = i.book.place[o]?)
    (htr : ∀ t ∈ treesAt places, i'.book.trees[t]? = i.book.trees[t]?)
    (hor : ∀ o ∈ (singleRowsOracles i.old).toList, i'.st.oracles[o]? = i.st.oracles[o]?) :
    ReadAsks i' pos places TT cs := by
  have hids : singleRowsOracles i.old = i.old.layout.members.push i.old.fresh := by
    unfold singleRowsOracles
    rw [A.masks]
    rfl
  have hmem : ∀ w (hw : w < i.old.layout.members.size),
      i.old.layout.members[w] ∈ (singleRowsOracles i.old).toList := fun w hw => by
    rw [hids]
    simp
  have hfr : i.old.fresh ∈ (singleRowsOracles i.old).toList := by
    rw [hids]
    simp
  have hparts : ∀ t ∈ treesAt places, ∀ o ∈ (TT t).parts.toList,
      o ∈ (singleRowsOracles i.old).toList := fun t ht o ho => by
    have k := List.all_eq_true.1 A.whole t ht
    rw [(A.tree t ht).there] at k
    have k2 := Array.all_eq_true_iff_forall_mem.1 k o (Array.mem_toList_iff.1 ho)
    exact Array.mem_toList_iff.2 (Array.contains_iff_mem.1 k2)
  refine ⟨?_, ?_, fun t ht => ?_, by rw [hop]; exact A.opened, fun o ho => ?_, A.listed,
    by rw [hold]; exact A.shape, by rw [hold]; exact A.masks, by rw [hold]; exact A.noKept,
    by rw [hold]; exact A.kept, ?_, ?_, ?_⟩
  · rw [hold, ← A.placed, Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList,
      mapM_same _ _ _ hpl]
  · rw [hold]
    refine List.all_eq_true.2 fun t ht => ?_
    rw [htr t ht]
    exact List.all_eq_true.1 A.whole t ht
  · have T := A.tree t ht
    refine ⟨(htr t ht).trans T.there, ?_, T.once, T.short, by rw [hF]; exact T.dealt⟩
    rw [← T.share]
    unfold shareOk
    rw [List.filterMap_congr fun o ho => by rw [hor o (hparts t ht o ho)]]
  · rw [hold] at ho
    rw [hor o ho]
    exact A.oracle o ho
  · rw [hold]
    intro w hw x hx
    rw [hor _ (hmem w hw)] at hx
    exact A.main w hw x hx
  · rw [hold]
    intro w hw x hx
    rw [hor _ (hmem w hw)] at hx
    exact A.mask w hw x hx
  · rw [hold]
    intro x hx
    rw [hor _ hfr] at hx
    exact A.fresh x hx

theorem treesSent_old (F : Nat) : ∀ (l : List TreeShape) (roots : Nat) (trees : Array Tree)
    (t : Nat), t < trees.size → (treesSent F l roots trees)[t]? = trees[t]?
  | [], _, _, _, _ => rfl
  | s :: l, roots, trees, t, h => by
    rw [treesSent, treesSent_old F l _ _ t (by rw [Array.size_push]; omega),
      Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

theorem foldl_modify_old {α : Type} (base t : Nat) (ht : t < base) (idx : Nat → Nat)
    (f : Nat → α → α) : ∀ (l : List Nat) (a : Array α),
    (l.foldl (fun a i => a.modify (base + idx i) (f i)) a)[t]? = a[t]?
  | [], _ => rfl
  | i :: l, a => by
    rw [List.foldl_cons, foldl_modify_old base t ht idx f l, Array.getElem?_modify,
      if_neg (by omega)]

theorem partsLaid_old (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) (t : Nat) (ht : t < base) :
    (partsLaid sent lay n0 base trees)[t]? = trees[t]? :=
  foldl_modify_old base t ht (fun i => lay.tree.getD i 0) _ _ _

theorem bookSentP_tree (F roots : Nat) (S : Statement) (Bk : TreeBook) (sent : Array OracleNotice)
    (lay : TreeLay) (t : Nat) (ht : t < Bk.trees.size) :
    (bookSentP F roots S Bk sent lay).trees[t]? = Bk.trees[t]? := by
  show (partsLaid sent lay S.oracles.size Bk.trees.size _)[t]? = _
  rw [partsLaid_old _ _ _ _ _ t ht, treesSent_old F _ _ _ t ht]

theorem bookSentP_place (F roots : Nat) (S : Statement) (Bk : TreeBook) (sent : Array OracleNotice)
    (lay : TreeLay) (o : Nat) (ho : o < Bk.place.size) :
    (bookSentP F roots S Bk sent lay).place[o]? = Bk.place[o]? :=
  Array.getElem?_append_left ho

theorem stA_old (D : Taken) (T : SwitchTarget) (others : Array OracleNotice) (S : Statement)
    (o : Nat) (ho : o < S.oracles.size) : (D.stA T others S).oracles[o]? = S.oracles[o]? := by
  show ((S.oracles ++ _).modify S.oracles.size _)[o]? = _
  rw [Array.getElem?_modify, if_neg (by omega), Array.getElem?_append_left ho]

theorem lt_of_some {α : Type} {a : Array α} {k : Nat} {x : α} (h : a[k]? = some x) :
    k < a.size := by
  by_cases c : k < a.size
  · exact c
  · rw [Array.getElem?_eq_none (by omega)] at h
    cases h

/-- **From before a switch's sending to after it.** `ReadAsks` at i gives `ReadAsks` at i', whose
statement is `D.stA T others i.st` and whose book is `bookSentP F roots i.st i.book sent D.lay`. -/
theorem readAsks_behind {i i' : SwIn} {pos : Positions} {places : Array (Nat × Nat)}
    {TT : Nat → Tree} {cs : Nat → List Tw.L9.Col} (A : ReadAsks i pos places TT cs) (D : Taken)
    (T : SwitchTarget) (others sent : Array OracleNotice) (F roots : Nat)
    (hold : i'.old = i.old) (hF : i'.firstTree = i.firstTree) (hop : i'.opened = i.opened)
    (hst : i'.st = D.stA T others i.st)
    (hbk : i'.book = bookSentP F roots i.st i.book sent D.lay) :
    ReadAsks i' pos places TT cs := by
  obtain ⟨z1, z2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ A.placed
  refine A.of_same hold hF hop (fun o ho => ?_) (fun t ht => ?_) fun o ho => ?_
  · obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 ho)
    have e := z2 k hk
    have e2 : places[k]? = some (places[k]'(by rw [z1]; exact hk)) := Array.getElem?_eq_getElem _
    rw [e2] at e
    rw [hbk]
    exact bookSentP_place _ _ _ _ _ _ _ (lt_of_some e)
  · rw [hbk]
    exact bookSentP_tree _ _ _ _ _ _ _ (lt_of_some (A.tree t ht).there)
  · obtain ⟨x, hx⟩ := A.oracle o ho
    rw [hst]
    exact stA_old _ _ _ _ _ (lt_of_some hx)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.mapM_same
#print axioms ProofFile.Honest.K12.ReadAsks.of_same
#print axioms ProofFile.Honest.K12.treesSent_old
#print axioms ProofFile.Honest.K12.foldl_modify_old
#print axioms ProofFile.Honest.K12.partsLaid_old
#print axioms ProofFile.Honest.K12.bookSentP_tree
#print axioms ProofFile.Honest.K12.bookSentP_place
#print axioms ProofFile.Honest.K12.stA_old
#print axioms ProofFile.Honest.K12.lt_of_some
#print axioms ProofFile.Honest.K12.readAsks_behind
