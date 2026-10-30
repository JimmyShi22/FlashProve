-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ViewOrder.lean: the opened columns of a chain's view in OnBytes/Maker/Whole.lean stand
in the order, and under the keys, in which the strict reader lists them.

A decision sees a chain as a view: the rounds' items and draws, and a list of opened columns, each
under a key and a place. The strict reader lists, round by round, first the stored tables' columns
and then the trees' (`Fmt.openedX`, Fmt/Rules8X.lean). The reduction of a whole file makes that list
from the drawn positions: it first says what they ask for (`wantsOf`), then looks each column up
(`colOf`) and lays it under its key (`viewOf`). This file shows that the two lists are equal, given,
round by round, what ties the round's data to the round as read (`RoundFits`).

The look-up is a letter here (`col`), so that nothing is asked of transcripts or tables.

Main definitions.
  `tagOf`: an opened column under its key and place.
  `treeWants`: what a round's draws ask of one tree.
  `RoundFits a dep key first col d r`: of the round's data d and the round r as read. The first
    openings of r are the stored tables' of d, one for each, each at the list of its part of the
    draws; the others are the trees' of d, one for each, each at the list of the draws, cut to the
    depth that `dep` says of the tree; the tree's key is the reader's: the number in the opening's
    shape less `first`; each opening has as many columns as places; and `col` finds each listed
    column at its place.
Main theorems.
  `opened_of_fits`: the two lists are equal, for rounds that fit.
  `viewOf_opened`: the same in the letters of `viewOf` and `colOf`.
  `viewX_less`: `Fmt.viewX` of a chain whose last round opens nothing, without that round
    (`lessLast`).

What is not claimed. That any round fits. Nothing on what a chain proves.


-/
import OnBytes.Maker.Whole
import Run.PageIsViewProofs

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- An opened column under its key and place: a stored table's under its item's key, a tree's under
the key that `key` gives to its number. -/
def tagOf (key : ℕ → ℕ) : Want → List UInt64 → ℕ × ℕ × List UInt64
  | .table item x, c => (Fmt.storedKey item, x, c)
  | .tree j x, c => (key j, x, c)

/-- What drawn positions ask of the tree with the number j. -/
def treeWants (dep : ℕ → Option ℕ) (poss : List ℕ) (j : ℕ) : List Want :=
  match dep j with
  | none => []
  | some b => (Fmt.listOf (poss.map (· % 2 ^ b))).map fun x => Want.tree j x

theorem treeWants_some {dep : ℕ → Option ℕ} {j b : ℕ} (h : dep j = some b) (poss : List ℕ) :
    treeWants dep poss j = (Fmt.listOf (poss.map (· % 2 ^ b))).map fun x => Want.tree j x := by
  unfold treeWants
  rw [h]

/-- One round's wants, then the others'. -/
theorem wantsOf_cons (a : ℕ) (dep : ℕ → Option ℕ) (d : RDT) (ds : List RDT) (R : Fmt.Drawn)
    (Rs : List Fmt.Drawn) :
    wantsOf a dep (d :: ds) (R :: Rs) =
      (d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ a))).map fun x => Want.table s.item x) ++
      d.opens.flatMap (treeWants dep R.poss) ++ wantsOf a dep ds Rs := rfl

/-- Pairs with a list, and with as much of it as the first list is long. -/
theorem zip_take_length {α β : Type} : ∀ (l : List α) (m : List β),
    l.zip (m.take l.length) = l.zip m
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
    rw [List.length_cons, List.take_succ_cons, List.zip_cons_cons, List.zip_cons_cons,
      zip_take_length l m]

/-- What ties a round's data to the round as read. -/
structure RoundFits (a : ℕ) (dep : ℕ → Option ℕ) (key : ℕ → ℕ) (first : ℕ)
    (col : Want → Option (List UInt64)) (d : RDT) (r : Fmt.RoundOut) : Prop where
  /-- the stored tables' openings come first, one for each table -/
  stored : List.Forall₂ (fun (t : Fmt.Stored) (z : Fmt.Shape × List ℕ × Fmt.OpenOut) =>
      z.2.1 = Fmt.listOf ((Fmt.partOf t r.drawn.poss).map (· % 2 ^ a)) ∧
      z.2.2.cols.length = z.2.1.length ∧
      ∀ x c, (x, c) ∈ z.2.1.zip z.2.2.cols → col (.table t.item x) = some c)
    d.stored (r.opens.take d.stored.length)
  /-- then the trees', one for each tree that the round opens -/
  trees : List.Forall₂ (fun (j : ℕ) (z : Fmt.Shape × List ℕ × Fmt.OpenOut) =>
      dep j = some z.1.a ∧ z.2.1 = Fmt.listOf (r.drawn.poss.map (· % 2 ^ z.1.a)) ∧
      z.2.2.cols.length = z.2.1.length ∧ key j = z.1.tree - first ∧
      ∀ x c, (x, c) ∈ z.2.1.zip z.2.2.cols → col (.tree j x) = some c)
    d.opens (r.opens.drop d.stored.length)

/-- One round's stored tables. -/
theorem stored_part (g : Want → Option (ℕ × ℕ × List UInt64)) (a : ℕ) (poss : List ℕ) :
    ∀ {ts : List Fmt.Stored} {zs : List (Fmt.Shape × List ℕ × Fmt.OpenOut)},
    List.Forall₂ (fun (t : Fmt.Stored) (z : Fmt.Shape × List ℕ × Fmt.OpenOut) =>
      z.2.1 = Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ a)) ∧
      z.2.2.cols.length = z.2.1.length ∧
      ∀ x c, (x, c) ∈ z.2.1.zip z.2.2.cols →
        g (.table t.item x) = some (Fmt.storedKey t.item, x, c)) ts zs →
    (ts.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ a))).map fun x =>
          Want.table s.item x).filterMap g =
      (ts.zip zs).flatMap fun y =>
        (y.2.2.1.zip y.2.2.2.cols).map fun p => (Fmt.storedKey y.1.item, p.1, p.2)
  | _, _, .nil => rfl
  | t :: ts, z :: zs, .cons h r => by
    rw [List.flatMap_cons, List.filterMap_append, stored_part g a poss r, List.zip_cons_cons,
      List.flatMap_cons]
    congr 1
    rw [← h.1, List.filterMap_map]
    exact filterMap_zip_of _ (fun x c => (Fmt.storedKey t.item, x, c)) z.2.1 z.2.2.cols h.2.1
      fun x c hm => h.2.2 x c hm

/-- One round's trees. -/
theorem trees_part (g : Want → Option (ℕ × ℕ × List UInt64)) (dep : ℕ → Option ℕ) (key : ℕ → ℕ)
    (first : ℕ) (poss : List ℕ) :
    ∀ {js : List ℕ} {zs : List (Fmt.Shape × List ℕ × Fmt.OpenOut)},
    List.Forall₂ (fun (j : ℕ) (z : Fmt.Shape × List ℕ × Fmt.OpenOut) =>
      dep j = some z.1.a ∧ z.2.1 = Fmt.listOf (poss.map (· % 2 ^ z.1.a)) ∧
      z.2.2.cols.length = z.2.1.length ∧ key j = z.1.tree - first ∧
      ∀ x c, (x, c) ∈ z.2.1.zip z.2.2.cols → g (.tree j x) = some (key j, x, c)) js zs →
    (js.flatMap (treeWants dep poss)).filterMap g =
      zs.flatMap fun z => (z.2.1.zip z.2.2.cols).map fun p => (z.1.tree - first, p.1, p.2)
  | _, _, .nil => rfl
  | j :: js, z :: zs, .cons h r => by
    rw [List.flatMap_cons, List.filterMap_append, trees_part g dep key first poss r,
      List.flatMap_cons]
    congr 1
    rw [treeWants_some h.1, ← h.2.1, List.filterMap_map, ← h.2.2.2.1]
    exact filterMap_zip_of _ (fun x c => (key j, x, c)) z.2.1 z.2.2.cols h.2.2.1
      fun x c hm => h.2.2.2.2 x c hm

/-- **The opened columns, in the reader's order and under the reader's keys.** -/
theorem opened_of_fits (a : ℕ) (dep : ℕ → Option ℕ) (key : ℕ → ℕ) (first : ℕ)
    (col : Want → Option (List UInt64)) :
    ∀ {ds : List RDT} {ros : List Fmt.RoundOut},
    List.Forall₂ (RoundFits a dep key first col) ds ros →
    (wantsOf a dep ds (ros.map (·.drawn))).filterMap (fun w => (col w).map (tagOf key w)) =
      ((ds.map (·.stored)).zip ros).flatMap fun u => Fmt.openedX first u.1 u.2
  | _, _, .nil => rfl
  | d :: ds, r :: ros, .cons h t => by
    rw [List.map_cons, wantsOf_cons, List.filterMap_append, List.filterMap_append,
      opened_of_fits a dep key first col t, List.map_cons, List.zip_cons_cons, List.flatMap_cons]
    congr 1
    show _ = ((d.stored.zip r.opens).flatMap fun y =>
        (y.2.2.1.zip y.2.2.2.cols).map fun p => (Fmt.storedKey y.1.item, p.1, p.2)) ++
      (r.opens.drop d.stored.length).flatMap fun z =>
        (z.2.1.zip z.2.2.cols).map fun p => (z.1.tree - first, p.1, p.2)
    congr 1
    · rw [← zip_take_length d.stored r.opens]
      exact stored_part _ a r.drawn.poss (h.stored.imp fun t z hz =>
        ⟨hz.1, hz.2.1, fun x c hm => by rw [hz.2.2 x c hm]; rfl⟩)
    · exact trees_part _ dep key first r.drawn.poss (h.trees.imp fun j z hz =>
        ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, fun x c hm => by rw [hz.2.2.2.2 x c hm]; rfl⟩)

section
variable (C : CK) (D : WholeD) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁))
  (τ₂ : Iop.Tr (uLT C D.ds₂)) (τ₃ : Iop.Tr (uLT C D.ds₃))

/-- The list of opened columns of `viewOf`, with `tagOf`. -/
theorem viewOf_tag (rs : List RV) (key : ℕ → ℕ) (ws : List Want) :
    (viewOf C D y τ₁ τ₂ τ₃ rs key ws).opened =
      ws.filterMap fun w => (colOf C D y τ₁ τ₂ τ₃ w).map (tagOf key w) := by
  show (ws.filterMap fun w => (colOf C D y τ₁ τ₂ τ₃ w).map _) = _
  refine congrArg (fun f => ws.filterMap f) (funext fun w => ?_)
  cases w <;> rfl

/-- **The opened columns of a chain's view** are the reader's, for rounds that fit. -/
theorem viewOf_opened (rs : List RV) (key : ℕ → ℕ) (first : ℕ) {ds : List RDT}
    {ros : List Fmt.RoundOut}
    (h : List.Forall₂ (RoundFits D.a D.depth key first (colOf C D y τ₁ τ₂ τ₃)) ds ros) :
    (viewOf C D y τ₁ τ₂ τ₃ rs key (wantsOf D.a D.depth ds (ros.map (·.drawn)))).opened =
      ((ds.map (·.stored)).zip ros).flatMap fun u => Fmt.openedX first u.1 u.2 :=
  (viewOf_tag C D y τ₁ τ₂ τ₃ rs key _).trans (opened_of_fits D.a D.depth key first _ h)

end

/-- A view without its last round. The opened columns stay. -/
def lessLast (v : View) : View := ⟨v.rounds.dropLast, v.opened⟩

/-- **The strict reader's view of a chain whose last round opens nothing, without that round**: its
rounds are those before the last, and its opened columns are theirs. -/
theorem viewX_less (S : Fmt.SpecX) (o : Fmt.ChainOut) (ros : List Fmt.RoundOut)
    (last : Fmt.RoundOut) (tss : List (List Fmt.Stored)) (tl : List Fmt.Stored)
    (ho : o.rounds.toList = ros ++ [last]) (hS : S.stored = tss ++ [tl])
    (hl : tss.length = ros.length) (hop : last.opens = []) :
    lessLast (Fmt.viewX S o) =
      ⟨ros.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩,
        (tss.zip ros).flatMap fun u => Fmt.openedX S.base.firstTree u.1 u.2⟩ := by
  have e : Fmt.openedX S.base.firstTree tl last = [] := by
    unfold Fmt.openedX Fmt.openedOf
    simp [hop]
  show (⟨(o.rounds.toList.map fun r => (⟨Fmt.noRoots r.vals, r.drawn⟩ : RV)).dropLast,
      (S.stored.zip o.rounds.toList).flatMap fun u => Fmt.openedX S.base.firstTree u.1 u.2⟩ :
      View) = _
  rw [ho, hS, List.map_append, List.map_singleton, List.dropLast_concat, List.zip_append hl,
    List.flatMap_append]
  show (⟨_, _ ++ (Fmt.openedX S.base.firstTree tl last ++ [])⟩ : View) = _
  rw [e, List.append_nil, List.append_nil]

end OnBytes.Maker
