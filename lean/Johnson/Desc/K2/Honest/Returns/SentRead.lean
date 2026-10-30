-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SentRead.lean: WHAT THE LAW ON THE READING OF THE OLD ROWS ASKS
(`ReadFits`, Returns/Read.lean) IS CARRIED FROM ONE INPUT OF THE STEP TO ANOTHER IN WHICH EVERY
OLDER MESSAGE, PLACE AND TREE STANDS AS IT WAS; AND THE SENDING THAT THE CODE SWITCH CALLS LEAVES
THEM SO. Statements and proofs.

WHY. The law on a segment's first place (`LinkFits`, Returns/Link.lean) asks `ReadFits` at what the
sending hands on: at the statement and the book BEHIND the sending. The reading opens OLD messages'
trees alone. So it is enough to ask `ReadFits` at the statement and the book IN FRONT.

  `Older`           the relation between two inputs i, i': the same carried rows, first tree and
                    columns; every message, place and tree of i stands in i' as it was
  `leafOk_same`, `allOpen_older`   the test on what shares a leaf; the premises tree by tree
  `Older.sameIds`, `.samePlaces`, `.sameTrees`, `.sameShape`   the opened messages, their places,
                    their trees and their shapes are one
  `ReadFits.older`   THE CARRYING: `Older i i'` and `ReadFits i pos` give `ReadFits i' pos`
  `inFront`         the step's input with the statement and the book in front of the sending
  `older_sent`      the sending leaves them so: `Older` from `inFront` to what the sending hands on:
                    the older trees by the library's `treesSent_old`, `partsLaid_old`
                    (OnBytes/Slice/BlkSentSeat.lean)
  `readFits_sent`   SO: `ReadFits` in front gives `ReadFits` at what the sending hands on

Limits. `ReadFits` reads of its input the carried rows, the statement, the book, the first tree and
the columns: `inFront`'s other fields are idle. That `ReadFits` holds in front is shown nowhere
here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.Read
import Johnson.Desc.K2.Honest.Returns.SendsMore
import OnBytes.Slice.BlkSentSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open _root_.Tw.K2 (SwIn Par9 Front Col leafOk leafGroups)
open VerifiableInference.Desc.First.K2 (behindArgs)
open VerifiableInference.Desc.LinkJoin (ColFits keptCount)

/-- The same carried rows, first tree and columns; every message, place and tree of i stands in i'
as it was. -/
structure Older (i i' : SwIn) : Prop where
  old : i'.old = i.old
  firstTree : i'.firstTree = i.firstTree
  opened : i'.opened = i.opened
  msgs : ∀ o, o < i.st.oracles.size → i'.st.oracles[o]? = i.st.oracles[o]?
  places : ∀ o, o < i.book.place.size → i'.book.place[o]? = i.book.place[o]?
  trees : ∀ t, t < i.book.trees.size → i'.book.trees[t]? = i.book.trees[t]?

theorem leafOk_same {S S' : Statement} {tree : Tree}
    (h : ∀ q ∈ tree.parts.toList, S'.oracles[q]? = S.oracles[q]?) :
    leafOk S' tree = leafOk S tree := by
  unfold leafOk leafGroups
  rw [List.filterMap_congr fun q hq => by rw [h q hq]]

theorem allOpen_older {S S' : Statement} (ft : Nat) (pos : Positions) {B B' : TreeBook}
    (hm : ∀ o, o < S.oracles.size → S'.oracles[o]? = S.oracles[o]?)
    (ht : ∀ t, t < B.trees.size → B'.trees[t]? = B.trees[t]?) :
    ∀ (ts : List Nat) (c : List OpenedColumn),
      (∀ t ∈ ts, ∀ tree, B.trees[t]? = some tree → ∀ q ∈ tree.parts.toList, q < S.oracles.size) →
      AllOpen S ft pos B ts c → AllOpen S' ft pos B' ts c
  | [], _, _, _ => trivial
  | t :: ts, c, hp, hA => by
    obtain ⟨tree, h1, h2, h3, h4, h5, h6, h7⟩ := hA
    have hlt : t < B.trees.size := (Array.getElem?_eq_some_iff.1 h1).1
    have eo : ownAt pos B' t = ownAt pos B t := by
      unfold ownAt
      rw [ht t hlt]
    refine ⟨tree, (ht t hlt).trans h1, ?_, h3, h4, ?_, ?_, ?_⟩
    · rw [leafOk_same fun q hq => hm q (hp t List.mem_cons_self tree h1 q hq)]
      exact h2
    · rw [eo]
      exact h5
    · rw [eo]
      exact h6
    · rw [eo]
      exact allOpen_older ft pos hm ht ts _ (fun t' h' => hp t' (List.mem_cons_of_mem _ h')) h7

variable {i i' : SwIn}

theorem Older.sameIds (h : Older i i') : idsOf i' = idsOf i := by
  unfold idsOf
  rw [h.old]

theorem Older.samePlaces (h : Older i i') (hp : ∀ o ∈ (idsOf i).toList, o < i.book.place.size) :
    placesOf i' = placesOf i := by
  unfold placesOf
  rw [h.sameIds]
  refine Array.map_congr_left fun o ho => ?_
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    h.places o (hp o (Array.mem_toList_iff.2 ho))]

theorem Older.sameTrees (h : Older i i') (hp : ∀ o ∈ (idsOf i).toList, o < i.book.place.size) :
    treesOf i' = treesOf i := by
  unfold treesOf
  rw [h.samePlaces hp]

theorem Older.sameShape (h : Older i i') (o : Nat) (ho : o < i.st.oracles.size) :
    shapeAt i' o = shapeAt i o := by
  unfold shapeAt
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, h.msgs o ho]

/-- **The carrying.** -/
theorem ReadFits.older (h : Older i i') {pos : Positions} (F : ReadFits i pos) :
    ReadFits i' pos := by
  have hids : idsOf i = i.old.layout.members.push i.old.fresh := by
    unfold idsOf singleRowsOracles
    rw [F.masks]
    rfl
  have hfresh : i.old.fresh < i.st.oracles.size :=
    F.stated _ (by rw [hids]; simp)
  have hmem : ∀ w, i.old.layout.members.getD w 0 < i.st.oracles.size := fun w => by
    by_cases hw : w < i.old.layout.members.size
    · refine F.stated _ ?_
      rw [hids, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
      simp
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hfresh
  have lt_of : ∀ {α : Type} (a b : Array α) (o : Nat), o < b.size → a[o]? = b[o]? → o < a.size :=
    fun a b o ho e => by
      rw [Array.getElem?_eq_getElem ho] at e
      exact (Array.getElem?_eq_some_iff.1 e).1
  refine
    { masks := by rw [h.old]; exact F.masks
      challenges := by rw [h.old]; exact F.challenges
      maskVars := by rw [h.old]; exact F.maskVars
      keptSize := by rw [h.old]; exact F.keptSize
      mainSize := by rw [h.old]; exact F.mainSize
      maskSize := by rw [h.old]; exact F.maskSize
      placed := fun o ho => by
        rw [h.sameIds] at ho
        exact lt_of _ _ o (F.placed o ho) (h.places o (F.placed o ho))
      stated := fun o ho => by
        rw [h.sameIds] at ho
        exact lt_of _ _ o (F.stated o ho) (h.msgs o (F.stated o ho))
      own := fun t ht tree he q hq => by
        rw [h.sameTrees F.placed] at ht
        obtain ⟨tr, h0⟩ := allOpen_tree _ _ _ _ _ _ t ht F.opens
        rw [h.trees t (Array.getElem?_eq_some_iff.1 h0).1] at he
        rw [h.sameIds]
        exact F.own t ht tree he q hq
      opens := by
        rw [h.sameTrees F.placed, h.firstTree, h.opened]
        exact allOpen_older _ _ h.msgs h.trees _ _
          (fun t ht tree he q hq => F.stated q (F.own t ht tree he q hq)) F.opens
      fits := ?_
      keptRows := ?_
      fresh := by rw [h.old, h.sameShape _ hfresh]; exact F.fresh }
  · rw [h.old]
    intro w hw
    have e : i.old.layout.members[w] = i.old.layout.members.getD w 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
      rfl
    rw [h.sameShape _ (e ▸ hmem w)]
    exact F.fits w hw
  · rw [h.old]
    have e : (fun w => (shapeAt i' (i.old.layout.members.getD w 0)).mainRows) =
        fun w => (shapeAt i (i.old.layout.members.getD w 0)).mainRows :=
      funext fun w => by rw [h.sameShape _ (hmem w)]
    rw [e]
    exact F.keptRows

/-- The step's input with the statement and the book in front of the sending. -/
def inFront (P : Par9) (x : Front) (B : TreeBook) (y : _root_.Tw.K2.Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) : SwIn :=
  { behindArgs P x y rL cols with st := x.st, book := B }

/-- **The sending leaves every older message, place and tree as it was.** -/
theorem older_sent (P : Par9) (x : Front) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView)
    (cols : List OpenedColumn) (Q : K1.Par) :
    Older (inFront P x B (sentAt Q x.st B roots rS rL) rL cols)
      (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) :=
  { old := rfl, firstTree := rfl, opened := rfl
    msgs := fun o ho => sentAt_old Q x.st B roots rS rL o ho
    places := fun o ho => by
      show (sentAt Q x.st B roots rS rL).book.place[o]? = B.place[o]?
      rw [sentAt_book]
      exact Array.getElem?_append_left ho
    trees := fun t ht => by
      show (sentAt Q x.st B roots rS rL).book.trees[t]? = B.trees[t]?
      rw [sentAt_book]
      exact (Slice.partsLaid_old _ _ _ _ _ t ht).trans (Slice.treesSent_old _ _ _ _ t ht) }

/-- **What the reading asks in front holds at what the sending hands on.** -/
theorem readFits_sent (P : Par9) (x : Front) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView)
    (cols : List OpenedColumn) (Q : K1.Par) {pos : Positions}
    (F : ReadFits (inFront P x B (sentAt Q x.st B roots rS rL) rL cols) pos) :
    ReadFits (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) pos :=
  F.older (older_sent P x B roots rS rL cols Q)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.allOpen_older
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ReadFits.older
#print axioms VerifiableInference.Desc.K2.Honest.Returns.older_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.readFits_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.leafOk_same
#print axioms VerifiableInference.Desc.K2.Honest.Returns.Older.sameIds
#print axioms VerifiableInference.Desc.K2.Honest.Returns.Older.samePlaces
#print axioms VerifiableInference.Desc.K2.Honest.Returns.Older.sameTrees
#print axioms VerifiableInference.Desc.K2.Honest.Returns.Older.sameShape
