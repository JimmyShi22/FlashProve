-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK2Cols.lean: the code switch (kind K2) reads the old rows at the drawn
positions out of opened columns (readOld, Johnson/Top/H0/Tw/K2/Switch.lean). This file shows that whether that reading
succeeds, and the sizes of what it returns, do not depend on the words in the columns. Five definitions with code; the
rest are theorems.

Words. A column is a key, a position and a list of words; its shape is its key, its position and the number of its words
(colShape, Honest/K10/WipeFold.lean). The wiped copy of a statement is the statement with every row's target set to zero
(wipeSt, Honest/K10/StAtZero.lean); singleRowsWithZeroTarget (Honest/K10/WipeS.lean) does the same to the carried rows. Two outcomes are
alike under a function w (AlikeE w, Wipe/Alike.lean) if both fail with the same message, or both succeed with values
that are equal after w is applied. A row's target is its right side; the plan's SwitchTarget (the letters T and
G.target) is another thing: the codes and shapes of the group to which a switch leads.

What is proved. readOld_rel: take two lists of columns with the same shapes, two statements with the same wiped copy,
and the carried rows with and without their target. Then readOld fails with the same message on both sides, or returns
on both; in that case the two books of trees are equal, the columns left have the same shapes, and the two arrays of
symbols have the same size. The steps:
  colsStand_same   the test on the opened columns reads only their shapes
  openOne_st, openOne_cols, openAll_rel   the opening of one tree, and of all trees in turn
  columnOf_shape   cutting a leaf's words into symbols gives as many symbols as the message's shape has rows, whatever
                 the words are
  symbolsAt_rel    what a message holds at the positions: present on both sides or on neither, with the same sizes
  layFrom_size, layRows_size, layMember_rel, layMembers_rel, rowsAt_rel, rowsFrom_rel, rowsSymbols_rel   laying symbols
                 into tables and folding them: every test there is on a size

By what. Each function is unfolded and followed branch by branch. Two values are compared after applying a function that
drops the words: shO (an opened tree), sh3 (the state of the loop that opens trees), shC (a column of symbols), shT (the
three tables), shY (what readOld returns). Section 1 holds general lemmas that carry such a comparison through an
if-then-else, a bind, a fold and a mapM.

Limits. Nothing is said about the symbols' values: at two lists of columns they can differ. The theorems hold for all
arguments, whether or not a run can reach them. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.ProofFile.Honest.K10.BatWipe
import Johnson.Desc.ProofFile.Honest.K10.WipeS
import Johnson.Top.H0.Tw.K2.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E F Statement Oracle TreeBook Positions Column SingleRows GroupLayout zeroE singleRowsOracles listOfT)
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Own (Opened colsStand whereOpened symbolsAt layFrom layRows Tables layMember layMembers
  rowsAt shapeFits rowsFrom rowsSymbols)
open Tw.K2 (SwIn openOne readOld)

/-! ## 1 General laws -/

/-- If `g p = g' p'` and `g q = g' q'`, then g and g' agree on two if-then-else terms with the same condition. -/
theorem swIte {α β : Type} {c : Prop} [Decidable c] (g g' : α → β) {p q p' q' : α} (hp : g p = g' p')
    (hq : g q = g' q') : g (if c then p else q) = g' (if c then p' else q') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact hp
  · rw [if_neg h, if_neg h]
    exact hq

/-- The same for two Boolean conditions that are equal. -/
theorem swBite {α β : Type} (g g' : α → β) {b b' : Bool} {p q p' q' : α} (hb : b = b') (hp : g p = g' p')
    (hq : g q = g' q') : g (if b = true then p else q) = g' (if b' = true then p' else q') := by
  subst hb
  exact swIte g g' hp hq

/-- Two if-then-else terms with the same condition are alike (`AlikeE`, Wipe/Alike.lean) if their branches are. -/
theorem alikeIte {α β : Type} {w : α → β} {c : Prop} [Decidable c] {p q p' q' : Except String α}
    (hp : AlikeE w p p') (hq : AlikeE w q q') : AlikeE w (if c then p else q) (if c then p' else q') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact hp
  · rw [if_neg h, if_neg h]
    exact hq

/-- The same for two Boolean conditions that are equal. -/
theorem alikeBite {α β : Type} {w : α → β} {b b' : Bool} {p q p' q' : Except String α} (hb : b = b')
    (hp : AlikeE w p p') (hq : AlikeE w q q') :
    AlikeE w (if b = true then p else q) (if b' = true then p' else q') := by
  subst hb
  exact alikeIte hp hq

/-- If two options are equal after mapping φ, both are `none`, or both are `some` with values equal under φ. -/
theorem omapSplit {α β : Type} {φ : α → β} {o o' : Option α} (h : o.map φ = o'.map φ) :
    (o = none ∧ o' = none) ∨ ∃ a a', o = some a ∧ o' = some a' ∧ φ a = φ a' := by
  cases o with
  | none =>
    cases o' with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some a' => cases h
  | some a =>
    cases o' with
    | none => cases h
    | some a' => exact Or.inr ⟨a, a', rfl, rfl, Option.some.inj h⟩

/-- Two `Option.bind`s are equal under ψ if their first parts are equal under φ and their continuations send values
equal under φ to results equal under ψ. -/
theorem obindRel {β γ δ ε : Type} (φ : β → δ) (ψ : γ → ε) {p p' : Option β} {k k' : β → Option γ}
    (hp : p.map φ = p'.map φ) (h : ∀ b b', φ b = φ b' → (k b).map ψ = (k' b').map ψ) :
    (p.bind k).map ψ = (p'.bind k').map ψ := by
  rcases omapSplit hp with ⟨h1, h2⟩ | ⟨b, b', h1, h2, hb⟩
  · subst h1 h2
    rfl
  · subst h1 h2
    exact h b b' hb

/-- Two `Option.map`s are equal under ψ if the options are equal under φ and the two mapped functions send values equal
under φ to values equal under ψ. -/
theorem omapRel {α β γ δ : Type} (φ : α → γ) (ψ : β → δ) {o o' : Option α} {g g' : α → β}
    (ho : o.map φ = o'.map φ) (h : ∀ a a', φ a = φ a' → ψ (g a) = ψ (g' a')) :
    (o.map g).map ψ = (o'.map g').map ψ := by
  rcases omapSplit ho with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    rfl
  · subst h1 h2
    exact congrArg some (h a a' ha)

/-- `List.mapM` with two functions whose results are equal under φ at every entry gives lists equal under φ. -/
theorem swMapL {α β γ : Type} (φ : β → γ) (f f' : α → Option β) (h : ∀ a, (f a).map φ = (f' a).map φ) :
    ∀ l : List α, (l.mapM f).map (List.map φ) = (l.mapM f').map (List.map φ)
  | [] => by rw [List.mapM_nil, List.mapM_nil]
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    refine bind_rel φ (List.map φ) (h a) fun b b' hb => ?_
    refine bind_rel (List.map φ) (List.map φ) (swMapL φ f f' h l) fun t t' ht => ?_
    show some ((b :: t).map φ) = some ((b' :: t').map φ)
    rw [List.map_cons, List.map_cons, hb, ht]

/-- The same with the resulting lists turned into arrays. -/
theorem swMapM {α β γ : Type} (φ : β → γ) (f f' : α → Option β) (h : ∀ a, (f a).map φ = (f' a).map φ)
    (l : List α) :
    ((l.mapM f).map List.toArray).map (fun A => A.map φ) = ((l.mapM f').map List.toArray).map fun A => A.map φ := by
  refine omapRel (List.map φ) (fun A : Array β => A.map φ) (swMapL φ f f' h l) fun t t' ht => ?_
  show t.toArray.map φ = t'.toArray.map φ
  rw [List.map_toArray, List.map_toArray, ht]

/-- The same for `Array.mapM`. -/
theorem swMapA {α β γ : Type} (φ : β → γ) (f f' : α → Option β) (h : ∀ a, (f a).map φ = (f' a).map φ)
    (A : Array α) : (A.mapM f).map (fun B => B.map φ) = (A.mapM f').map fun B => B.map φ := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  exact swMapM φ f f' h A.toList

/-- `List.foldlM` in `Except`: from start values equal under φ, with steps that keep this, the two results are alike
under φ. -/
theorem alikeFold {α β γ : Type} (φ : β → γ) (f f' : β → α → Except String β)
    (h : ∀ b b' a, φ b = φ b' → AlikeE φ (f b a) (f' b' a)) :
    ∀ (l : List α) (b b' : β), φ b = φ b' → AlikeE φ (l.foldlM f b) (l.foldlM f' b')
  | [], _, _, hb => AlikeE.ok hb
  | a :: l, b, b', hb => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact AlikeE.bind' (h b b' a hb) fun c c' hc => alikeFold φ f f' h l c c' hc

/-- Reading index i of two arrays of equal size gives equal results if, under φ, both mapped functions always give the
same constant c. -/
theorem atConst {α β γ : Type} {a a' : Array α} (h : a.size = a'.size) (φ : β → γ) {f f' : α → β} {c : γ}
    (hf : ∀ x, φ (f x) = c) (hf' : ∀ x, φ (f' x) = c) (i : Nat) :
    ((a[i]?).map f).map φ = ((a'[i]?).map f').map φ := by
  by_cases hi : i < a.size
  · have hi' : i < a'.size := h ▸ hi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi']
    show some (φ (f a[i])) = some (φ (f' a'[i]))
    rw [hf, hf']
  · have e1 : a[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hi)
    have e2 : a'[i]? = none := Array.getElem?_eq_none (h ▸ Nat.le_of_not_lt hi)
    exact (congrArg (fun o => (o.map f).map φ) e1).trans (congrArg (fun o => (o.map f').map φ) e2).symm

/-- Reading entry i of entry w of two arrays of arrays that are equal under φ gives results equal under φ. -/
theorem at2Rel {α β : Type} {φ : α → β} {A A' : Array (Array α)}
    (h : A.map (fun a => a.map φ) = A'.map fun a => a.map φ) (w i : Nat) :
    ((A[w]?).bind (·[i]?)).map φ = ((A'[w]?).bind (·[i]?)).map φ := by
  have k : ∀ B : Array (Array α),
      ((B[w]?).bind (·[i]?)).map φ = ((B.map fun a => a.map φ)[w]?).bind (·[i]?) := fun B => by
    rw [Array.getElem?_map]
    cases B[w]? with
    | none => rfl
    | some a =>
      show (a[i]?).map φ = (a.map φ)[i]?
      rw [Array.getElem?_map]
  rw [k A, k A', h]

/-! ## 2 The opened columns stand as asked -/

/-- `colsStand` can be computed from the columns' shapes (key, position, width) alone. -/
theorem colsStand_shape (key W : Nat) : ∀ (cols : List OpenedColumn) (xs : List Nat),
    colsStand key W cols xs =
      ((cols.map colShape).zip xs).all fun p => p.1.1 == key && p.1.2.1 == p.2 && p.1.2.2 == W
  | [], _ => by simp [colsStand]
  | _ :: _, [] => by simp [colsStand]
  | c :: cols, x :: xs => by
    have ih := colsStand_shape key W cols xs
    unfold VerifiableInference.Desc.Own.colsStand at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih, colShape]

/-- **`colsStand` gives the same answer on two lists of columns with the same shapes.** -/
theorem colsStand_same (key W : Nat) {got got' : List OpenedColumn} (h : got.map colShape = got'.map colShape)
    (xs : List Nat) : colsStand key W got xs = colsStand key W got' xs := by
  rw [colsStand_shape, colsStand_shape, h]

/-- The first n columns of two lists with the same shapes have the same shapes. -/
theorem takeShape {l l' : List OpenedColumn} (h : l.map colShape = l'.map colShape) (n : Nat) :
    (l.take n).map colShape = (l'.take n).map colShape := by
  rw [List.map_take, List.map_take, h]

/-- Two lists of columns with the same shapes have the same length. -/
theorem shapeLen {l l' : List OpenedColumn} (h : l.map colShape = l'.map colShape) : l.length = l'.length := by
  have e := congrArg List.length h
  rw [List.length_map, List.length_map] at e
  exact e

/-! ## 3 The opening of trees -/

/-- What is compared of an opened tree: its index in the book, the positions at which it was opened, and how many
columns were taken. The columns' words are dropped. -/
def shO (x : Opened) : Nat × Array Nat × Nat := (x.1, x.2.1, x.2.2.size)

/-- What is compared of the state of the loop that opens trees: the book, the shapes of the columns not yet taken, and
the opened trees under `shO`. -/
def sh3 (s : TreeBook × List OpenedColumn × Array Opened) :
    TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) :=
  (s.1, s.2.1.map colShape, s.2.2.map shO)

/-- The list of groups that `openOne` reads of a sampled message is the same at a statement and at its wiped copy. -/
theorem told_wipe (S : Statement) (o : Nat) :
    (((wipeSt S).oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups) =
      (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups := by
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? with
  | none => rfl
  | some x => rfl

/-- `openOne` is the same function at a statement and at its wiped copy. -/
theorem openOne_st (S : Statement) : openOne (wipeSt S) = openOne S := by
  funext ft pos B0 t s
  unfold Tw.K2.openOne
  simp only [told_wipe]

/-- Two entries for an opened tree that are built from lists of columns of equal length are equal under `shO`. -/
theorem shO_took (t : Nat) (xs : Array Nat) {got got' : List OpenedColumn} (h : got.length = got'.length) :
    shO (t, xs, (got.map fun y => y.2.2.toArray).toArray) =
      shO (t, xs, (got'.map fun y => y.2.2.toArray).toArray) := by
  show (t, xs, ((got.map fun y => y.2.2.toArray).toArray).size) =
    (t, xs, ((got'.map fun y => y.2.2.toArray).toArray).size)
  rw [List.size_toArray, List.size_toArray, List.length_map, List.length_map, h]

/-- The loop state that `openOne` returns on success is equal under `sh3` on both sides if the states it started from
are. -/
theorem sh3_step (B1 : TreeBook) {left left' : List OpenedColumn} {cols cols' : Array Opened}
    (hl : left.map colShape = left'.map colShape) (hc : cols.map shO = cols'.map shO) (n t : Nat)
    (xs : Array Nat) :
    sh3 (B1, left.drop n, cols.push (t, xs, ((left.take n).map fun y => y.2.2.toArray).toArray)) =
      sh3 (B1, left'.drop n, cols'.push (t, xs, ((left'.take n).map fun y => y.2.2.toArray).toArray)) := by
  show (B1, (left.drop n).map colShape,
      (cols.push (t, xs, ((left.take n).map fun y => y.2.2.toArray).toArray)).map shO) =
    (B1, (left'.drop n).map colShape,
      (cols'.push (t, xs, ((left'.take n).map fun y => y.2.2.toArray).toArray)).map shO)
  rw [List.map_drop, List.map_drop, hl, Array.map_push, Array.map_push, hc,
    shO_took t xs (shapeLen (takeShape hl n))]

/-- **`openOne` on two loop states equal under `sh3`** fails with the same message, or returns states equal under `sh3`.
-/
theorem openOne_cols (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    {s s' : TreeBook × List OpenedColumn × Array Opened} (h : sh3 s = sh3 s') :
    AlikeE sh3 (openOne S ft pos B0 t s) (openOne S ft pos B0 t s') := by
  obtain ⟨B, left, cols⟩ := s
  obtain ⟨B', left', cols'⟩ := s'
  have hB : B = B' :=
    (congrArg (fun z : TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) => z.1) h :)
  have hl : left.map colShape = left'.map colShape :=
    (congrArg (fun z : TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) => z.2.1) h :)
  have hc : cols.map shO = cols'.map shO :=
    (congrArg (fun z : TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) => z.2.2) h :)
  subst hB
  unfold Tw.K2.openOne
  dsimp only
  cases B.trees[t]? with
  | none => exact AlikeE.error _
  | some tree =>
    cases B0.trees[t]? with
    | none => exact AlikeE.error _
    | some tree0 =>
      dsimp only
      refine alikeIte (AlikeE.error _) ?_
      refine alikeIte (AlikeE.error _) ?_
      refine alikeIte (AlikeE.error _) ?_
      refine alikeBite ?_ (AlikeE.ok (sh3_step _ hl hc _ _ _)) (AlikeE.error _)
      rw [shapeLen (takeShape hl _), colsStand_same _ _ (takeShape hl _)]

/-- **The whole loop that opens trees**, at two statements with the same wiped copy and two start states equal under
`sh3`, fails with the same message, or ends in states equal under `sh3`. -/
theorem openAll_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (ft : Nat) (pos : Positions) (B0 : TreeBook)
    (l : List Nat) {s s' : TreeBook × List OpenedColumn × Array Opened} (h : sh3 s = sh3 s') :
    AlikeE sh3 (l.foldlM (fun s t => openOne S ft pos B0 t s) s)
      (l.foldlM (fun s t => openOne S' ft pos B0 t s) s') := by
  have e : openOne S = openOne S' := by rw [← openOne_st S, ← openOne_st S', hS]
  rw [e]
  exact alikeFold sh3 _ _ (fun b b' t hb => openOne_cols S' ft pos B0 t hb) l s s' h

/-! ## 4 What a message holds at the positions -/

/-- What is compared of a column of symbols: the number of main symbols and the number of mask symbols. -/
def shC (c : Column) : Nat × Nat := (c.main.size, c.mask.size)

/-- **`Blk.columnOf` returns as many main and mask symbols as the message's shape has rows, whatever words it is
given.** -/
theorem columnOf_shape (x : Oracle) (a b : Nat) (c : Array F) :
    shC (OnBytes.Blk.columnOf x a b c) = (x.shape.mainRows, x.shape.maskRows) := by
  simp [shC, OnBytes.Blk.columnOf]

/-- Searching the opened trees by index and then applying `shO` is the same as applying `shO` first and then searching.
-/
theorem find_shO (t : Nat) : ∀ l : List Opened,
    (l.find? fun x => x.1 == t).map shO = (l.map shO).find? fun z => z.1 == t
  | [] => rfl
  | a :: l => by
    have ih := find_shO t l
    have e : ((shO a).1 == t) = (a.1 == t) := rfl
    rw [List.map_cons, List.find?_cons, List.find?_cons, e]
    cases a.1 == t with
    | false => exact ih
    | true => rfl

/-- **`symbolsAt`**, at statements with the same wiped copy and opened trees equal under `shO`, returns nothing at both,
or columns of the same sizes. -/
theorem symbolsAt_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') (B : TreeBook) (pos : Positions)
    {cols cols' : List Opened} (hc : cols.map shO = cols'.map shO) (o : Nat) (p : Nat × Nat) :
    (symbolsAt S B pos cols o p).map (fun A => A.map shC) =
      (symbolsAt S' B pos cols' o p).map fun A => A.map shC := by
  have hx : (S.oracles[o]?).map (·.shape) = (S'.oracles[o]?).map (·.shape) := by
    rw [← shape_at_wipe S o, ← shape_at_wipe S' o, hS]
  have hm : (cols.find? fun x => x.1 == p.1).map shO = (cols'.find? fun x => x.1 == p.1).map shO := by
    rw [find_shO, find_shO, hc]
  unfold VerifiableInference.Desc.Own.symbolsAt
  cases B.trees[p.1]? with
  | none => rfl
  | some tree =>
    rcases omapSplit hx with ⟨h1, h2⟩ | ⟨x, x', h1, h2, hs⟩
    · rw [h1, h2]
    · rcases omapSplit hm with ⟨h3, h4⟩ | ⟨m, m', h3, h4, hmm⟩
      · rw [h1, h2, h3, h4]
      · rw [h1, h2, h3, h4]
        have hl : m.2.1 = m'.2.1 := (congrArg (fun z : Nat × Array Nat × Nat => z.2.1) hmm :)
        have hz : m.2.2.size = m'.2.2.size := (congrArg (fun z : Nat × Array Nat × Nat => z.2.2) hmm :)
        have hs' : x.shape = x'.shape := hs
        dsimp only
        refine swMapM shC _ _ (fun i => ?_) _
        rw [hl]
        refine obindRel id shC rfl fun here here' hh => ?_
        have hh' : here = here' := hh
        subst hh'
        exact atConst hz shC (c := (x.shape.mainRows, x.shape.maskRows)) (fun c => columnOf_shape x _ _ c)
          (fun c => by rw [columnOf_shape, hs']) here

/-! ## 5 The laying of symbols into tables -/

/-- `layFrom` does not change the table's size. -/
theorem layFrom_size : ∀ (l : List E) (table : Array E) (f : Nat), (layFrom table f l).size = table.size
  | [], _, _ => rfl
  | e :: es, table, f => by
    show (layFrom (table.setIfInBounds f e) (f + 1) es).size = table.size
    rw [layFrom_size es, Array.size_setIfInBounds]

/-- Whether `layRows` succeeds, and the size of its result, depend only on the sizes of the table and of the column. -/
theorem layRows_size {table table' : Array E} (ht : table.size = table'.size) (first : Option Nat)
    {col col' : Array E} (hc : col.size = col'.size) :
    (layRows table first col).map Array.size = (layRows table' first col').map Array.size := by
  obtain ⟨l⟩ := col
  obtain ⟨l'⟩ := col'
  have hl : l.length = l'.length := hc
  cases l with
  | nil =>
    cases l' with
    | nil => exact congrArg some ht
    | cons a' t' => exact absurd hl (by simp)
  | cons a t =>
    cases l' with
    | nil => exact absurd hl (by simp)
    | cons a' t' =>
      cases first with
      | none => rfl
      | some f =>
        show (if f + (a :: t).length ≤ table.size then some (layFrom table f (a :: t)) else none).map Array.size =
          (if f + (a' :: t').length ≤ table'.size then some (layFrom table' f (a' :: t')) else none).map
            Array.size
        rw [hl, ht]
        refine swIte (Option.map Array.size) (Option.map Array.size) ?_ rfl
        show some (layFrom table f (a :: t)).size = some (layFrom table' f (a' :: t')).size
        rw [layFrom_size, layFrom_size, ht]

/-- What is compared of the three tables: their sizes. -/
def shT (t : Tables) : Nat × Nat × Nat := (t.main.size, t.mask.size, t.kept.size)

/-- `layMember` on columns and tables of the same sizes returns nothing at both, or tables of the same sizes. -/
theorem layMember_rel (L : GroupLayout) (w : Nat) {col col' : Column} (hc : shC col = shC col') {t t' : Tables}
    (ht : shT t = shT t') : (layMember L w col t).map shT = (layMember L w col' t').map shT := by
  have c1 : col.main.size = col'.main.size := (congrArg (fun z : Nat × Nat => z.1) hc :)
  have c2 : col.mask.size = col'.mask.size := (congrArg (fun z : Nat × Nat => z.2) hc :)
  have t1 : t.main.size = t'.main.size := (congrArg (fun z : Nat × Nat × Nat => z.1) ht :)
  have t2 : t.mask.size = t'.mask.size := (congrArg (fun z : Nat × Nat × Nat => z.2.1) ht :)
  have t3 : t.kept.size = t'.kept.size := (congrArg (fun z : Nat × Nat × Nat => z.2.2) ht :)
  unfold VerifiableInference.Desc.Own.layMember
  refine obindRel Array.size shT (layRows_size t2 _ c2) fun m m' hm => ?_
  have hm' : m.size = m'.size := hm
  refine swIte (Option.map shT) (Option.map shT) ?_ ?_
  · show some (t.main.size, m.size, (t.kept ++ col.main).size) =
      some (t'.main.size, m'.size, (t'.kept ++ col'.main).size)
    rw [Array.size_append, Array.size_append, t1, hm', t3, c1]
  · refine omapRel Array.size shT (layRows_size t1 _ c1) fun a a' ha => ?_
    have ha' : a.size = a'.size := ha
    show (a.size, m.size, t.kept.size) = (a'.size, m'.size, t'.kept.size)
    rw [ha', hm', t3]

/-- The same for `layMembers`, which lays in all listed members. -/
theorem layMembers_rel (L : GroupLayout) {opened opened' : Array (Array Column)}
    (hO : opened.map (fun A => A.map shC) = opened'.map fun A => A.map shC) (i : Nat) :
    ∀ (ws : List Nat) (t t' : Tables), shT t = shT t' →
      (layMembers L opened i ws t).map shT = (layMembers L opened' i ws t').map shT
  | [], _, _, ht => congrArg some ht
  | w :: ws, t, t', ht => by
    show (((opened[w]?).bind (·[i]?)).bind fun col =>
        (layMember L w col t).bind (layMembers L opened i ws)).map shT =
      (((opened'[w]?).bind (·[i]?)).bind fun col =>
        (layMember L w col t').bind (layMembers L opened' i ws)).map shT
    refine obindRel shC shT (at2Rel hO w i) fun col col' hc => ?_
    refine obindRel shT shT (layMember_rel L w hc ht) fun u u' hu => ?_
    exact layMembers_rel L hO i ws u u' hu

/-- The symbols gathered at one position, before the fresh mask's symbol is added, are equally many on both sides. -/
theorem y2Size {y y' k k' : Array E} (hy : y.size = y'.size) (hk : k.size = k'.size) (a a' b b' : E) (c : Prop)
    [Decidable c] :
    (if c then (y.push a ++ k).push b else y.push a ++ k).size =
      (if c then (y'.push a' ++ k').push b' else y'.push a' ++ k').size := by
  refine swIte Array.size Array.size ?_ ?_
  · simp only [Array.size_push, Array.size_append, hy, hk]
  · simp only [Array.size_push, Array.size_append, hy, hk]

/-- Pushing one element onto two arrays of equal size gives arrays of equal size. -/
theorem pushSize {A A' : Array E} (h : A.size = A'.size) (v v' : E) :
    (some (A.push v)).map Array.size = (some (A'.push v')).map Array.size := by
  show some (A.push v).size = some (A'.push v').size
  rw [Array.size_push, Array.size_push, h]

/-- **`rowsAt`**, on columns of the same sizes and arrays of equal size, returns nothing at both, or arrays of equal
size. -/
theorem rowsAt_rel (s : SingleRows) {opened opened' : Array (Array Column)}
    (hO : opened.map (fun A => A.map shC) = opened'.map fun A => A.map shC) {y y' : Array E}
    (hy : y.size = y'.size) (i : Nat) :
    (rowsAt s opened y i).map Array.size = (rowsAt s opened' y' i).map Array.size := by
  unfold VerifiableInference.Desc.Own.rowsAt
  dsimp only
  refine obindRel shT Array.size (layMembers_rel s.layout hO i _ _ _ rfl) fun t t' ht => ?_
  have t3 : t.kept.size = t'.kept.size := (congrArg (fun z : Nat × Nat × Nat => z.2.2) ht :)
  refine swBite (Option.map Array.size) (Option.map Array.size) (by rw [t3]) rfl ?_
  refine swIte (Option.map Array.size) (Option.map Array.size) ?_ ?_
  · refine obindRel shC Array.size (at2Rel hO _ i) fun fr fr' hf => ?_
    have f2 : fr.mask.size = fr'.mask.size := (congrArg (fun z : Nat × Nat => z.2) hf :)
    refine swBite (Option.map Array.size) (Option.map Array.size) (by rw [f2]) rfl ?_
    exact pushSize (y2Size hy t3 _ _ _ _ _) _ _
  · exact congrArg some (y2Size hy t3 _ _ _ _ _)

/-- The same for `rowsFrom`, which runs `rowsAt` over a list of positions. -/
theorem rowsFrom_rel (s : SingleRows) {opened opened' : Array (Array Column)}
    (hO : opened.map (fun A => A.map shC) = opened'.map fun A => A.map shC) :
    ∀ (is : List Nat) (y y' : Array E), y.size = y'.size →
      (rowsFrom s opened is y).map Array.size = (rowsFrom s opened' is y').map Array.size
  | [], _, _, hy => congrArg some hy
  | i :: is, y, y', hy => by
    show ((rowsAt s opened y i).bind (rowsFrom s opened is)).map Array.size =
      ((rowsAt s opened' y' i).bind (rowsFrom s opened' is)).map Array.size
    exact obindRel Array.size Array.size (rowsAt_rel s hO hy i) fun z z' hz => rowsFrom_rel s hO is z z' hz

/-- `rowsAt` does not read the carried rows' target. -/
theorem rowsAt_old (s : SingleRows) (opened : Array (Array Column)) (y : Array E) (i : Nat) :
    rowsAt (singleRowsWithZeroTarget s) opened y i = rowsAt s opened y i := by
  unfold VerifiableInference.Desc.Own.rowsAt
  rfl

/-- Nor does `rowsFrom`. -/
theorem rowsFrom_old (s : SingleRows) (opened : Array (Array Column)) :
    ∀ (is : List Nat) (y : Array E), rowsFrom (singleRowsWithZeroTarget s) opened is y = rowsFrom s opened is y
  | [], _ => rfl
  | i :: is, y => by
    show (rowsAt (singleRowsWithZeroTarget s) opened y i).bind (rowsFrom (singleRowsWithZeroTarget s) opened is) =
      (rowsAt s opened y i).bind (rowsFrom s opened is)
    rw [rowsAt_old, funext (rowsFrom_old s opened is)]

/-- **`rowsSymbols`**, on columns of the same sizes, with or without the carried rows' target, returns nothing at both,
or arrays of equal size. -/
theorem rowsSymbols_rel (s : SingleRows) {opened opened' : Array (Array Column)}
    (hO : opened.map (fun A => A.map shC) = opened'.map fun A => A.map shC) (n : Nat) :
    (rowsSymbols (singleRowsWithZeroTarget s) opened n).map Array.size = (rowsSymbols s opened' n).map Array.size := by
  have e : shapeFits (singleRowsWithZeroTarget s) = shapeFits s := by
    unfold VerifiableInference.Desc.Own.shapeFits
    rfl
  unfold VerifiableInference.Desc.Own.rowsSymbols
  rw [e, rowsFrom_old]
  exact swIte (Option.map Array.size) (Option.map Array.size) (rowsFrom_rel s hO _ _ _ rfl) rfl

/-! ## 6 The reading of the old rows -/

/-- What is compared of `readOld`'s result: the book, the shapes of the columns left, and the number of symbols. -/
def shY (z : TreeBook × List OpenedColumn × Array E) : TreeBook × List (Nat × Nat × Nat) × Nat :=
  (z.1, z.2.1.map colShape, z.2.2.size)

/-- `singleRowsOracles` does not read the carried rows' target. -/
theorem singleRowsOracles_old (s : SingleRows) : singleRowsOracles (singleRowsWithZeroTarget s) = singleRowsOracles s := by
  unfold OnBytes.singleRowsOracles
  rfl

/-- **`readOld`** fails with the same message on both sides, or returns the same book, columns left of the same shapes,
and equally many symbols. -/
theorem readOld_rel (i : SwIn) (pos : Positions) {S' : Statement} {c' : List OpenedColumn} (hS : wipeSt S' = wipeSt i.st)
    (hc : SameShape c' i.opened) :
    AlikeE shY (readOld { i with st := S', opened := c', old := singleRowsWithZeroTarget i.old } pos) (readOld i pos) := by
  obtain ⟨st, book, ft, opened, old, T, grp, ids, entry, settled, drawn, itemsLeft⟩ := i
  have hS' : wipeSt S' = wipeSt st := hS
  have hc' : c'.map colShape = opened.map colShape := hc
  unfold Tw.K2.readOld
  dsimp only
  rw [singleRowsOracles_old]
  cases ((singleRowsOracles old).mapM fun o => book.place[o]?) with
  | none => exact AlikeE.error _
  | some places =>
    dsimp only
    refine alikeIte (AlikeE.error _) ?_
    have h0 : sh3 (book, c', #[]) = sh3 (book, opened, #[]) := by
      show (book, c'.map colShape, (#[] : Array Opened).map shO) =
        (book, opened.map colShape, (#[] : Array Opened).map shO)
      rw [hc']
    rcases (openAll_rel hS' ft pos book (listOfT (places.map (·.1)).toList) h0).split with
      ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
    · rw [h1, h2]
      exact AlikeE.error e
    · rw [h1, h2]
      obtain ⟨B', left', cols'⟩ := a
      obtain ⟨B, left, cols⟩ := a'
      have hB : B' = B :=
        (congrArg (fun z : TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) => z.1) ha :)
      have hl : left'.map colShape = left.map colShape :=
        (congrArg (fun z : TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) => z.2.1) ha :)
      have hk : cols'.map shO = cols.map shO :=
        (congrArg (fun z : TreeBook × List (Nat × Nat × Nat) × Array (Nat × Array Nat × Nat) => z.2.2) ha :)
      have hk' : cols'.toList.map shO = cols.toList.map shO := by
        rw [← Array.toList_map, ← Array.toList_map, hk]
      dsimp only
      rcases omapSplit (swMapA (fun A : Array Column => A.map shC)
          (fun y => symbolsAt S' book pos cols'.toList y.1 y.2) (fun y => symbolsAt st book pos cols.toList y.1 y.2)
          (fun y => symbolsAt_rel hS' book pos hk' y.1 y.2) ((singleRowsOracles old).zip places)) with
        ⟨h3, h4⟩ | ⟨O', O, h3, h4, hO⟩
      · rw [h3, h4]
        exact AlikeE.error _
      · rw [h3, h4]
        dsimp only
        rcases omapSplit (rowsSymbols_rel old hO pos.all.size) with ⟨h5, h6⟩ | ⟨y', y, h5, h6, hy⟩
        · rw [h5, h6]
          exact AlikeE.error _
        · rw [h5, h6]
          refine AlikeE.ok ?_
          have hy' : y'.size = y.size := hy
          show (B', left'.map colShape, y'.size) = (B, left.map colShape, y.size)
          rw [hB, hl, hy']

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.swIte
#print axioms ProofFile.Honest.K10.swBite
#print axioms ProofFile.Honest.K10.alikeIte
#print axioms ProofFile.Honest.K10.alikeBite
#print axioms ProofFile.Honest.K10.omapSplit
#print axioms ProofFile.Honest.K10.obindRel
#print axioms ProofFile.Honest.K10.omapRel
#print axioms ProofFile.Honest.K10.swMapL
#print axioms ProofFile.Honest.K10.swMapM
#print axioms ProofFile.Honest.K10.swMapA
#print axioms ProofFile.Honest.K10.alikeFold
#print axioms ProofFile.Honest.K10.atConst
#print axioms ProofFile.Honest.K10.at2Rel
#print axioms ProofFile.Honest.K10.colsStand_shape
#print axioms ProofFile.Honest.K10.colsStand_same
#print axioms ProofFile.Honest.K10.takeShape
#print axioms ProofFile.Honest.K10.shapeLen
#print axioms ProofFile.Honest.K10.shO
#print axioms ProofFile.Honest.K10.sh3
#print axioms ProofFile.Honest.K10.told_wipe
#print axioms ProofFile.Honest.K10.openOne_st
#print axioms ProofFile.Honest.K10.shO_took
#print axioms ProofFile.Honest.K10.sh3_step
#print axioms ProofFile.Honest.K10.openOne_cols
#print axioms ProofFile.Honest.K10.openAll_rel
#print axioms ProofFile.Honest.K10.shC
#print axioms ProofFile.Honest.K10.columnOf_shape
#print axioms ProofFile.Honest.K10.find_shO
#print axioms ProofFile.Honest.K10.symbolsAt_rel
#print axioms ProofFile.Honest.K10.layFrom_size
#print axioms ProofFile.Honest.K10.layRows_size
#print axioms ProofFile.Honest.K10.shT
#print axioms ProofFile.Honest.K10.layMember_rel
#print axioms ProofFile.Honest.K10.layMembers_rel
#print axioms ProofFile.Honest.K10.y2Size
#print axioms ProofFile.Honest.K10.pushSize
#print axioms ProofFile.Honest.K10.rowsAt_rel
#print axioms ProofFile.Honest.K10.rowsFrom_rel
#print axioms ProofFile.Honest.K10.rowsAt_old
#print axioms ProofFile.Honest.K10.rowsFrom_old
#print axioms ProofFile.Honest.K10.rowsSymbols_rel
#print axioms ProofFile.Honest.K10.shY
#print axioms ProofFile.Honest.K10.singleRowsOracles_old
#print axioms ProofFile.Honest.K10.readOld_rel
