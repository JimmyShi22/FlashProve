-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ColsFit.lean: THE COLUMNS' SHARE OF "THE TREES OPEN ONE AFTER THE
OTHER" (`AllOpen`, Returns/ReadOpen.lean) AND "NO COLUMN IS LEFT" (`leftAfter ... = []`) FOLLOWS
FROM THE TEST ON COLUMNS THAT `Block.step` RUNS IN FRONT OF EVERY DECISION (Johnson/Desc/Block.lean:
the view's next columns are, in key, position and width, those that the rounds read) AND FROM HOW IT
LAYS THEM INTO GROUPS, WHERE THE PLAN's LIST OF READ TREES IS TIED TO THE BOOK's OPENED TREES, TREE
FOR TREE. Three definitions: a premise by name, along two lists, and a reading of `flat`; statements
with their proofs.

WHAT IS PAID AND WHAT IS NOT. `AllOpen` says seven things of each opened tree. FOUR ARE ON THE
VERIFIER's STATE ALONE AND STAY PREMISES HERE, inside `TreeTied`: the tree is in the book · `leafOk`
· a tree of one list has not been opened before · its depth is within the positions' range. TWO ARE
ON THE COLUMNS AND ARE PAID: the next columns are as many as the tree's list; each has the tree's
key, the list's position, the tree's width. The seventh is the like for the trees behind it.
`TreeTied` holds three equations more: THE TIE: the tree's number, depth and width are those of the
plan's entry.

  `TreeTied`, `AllTied`   THE PREMISE, tree by tree: the four facts on the state and the three
                    equations; along two lists of one length
  `flatAt`, `flat_is`   `flat` (Johnson/Top/H0/Tw/K2C/Kind.lean) at a list of read trees
  `ownAt_list`      the list at which a tree of the book is opened is the list by which `groupsOf`
                    reads it, where every draw lies below the positions' range
  `colsStand_of`    columns of one key whose positions and widths are a list's stand as asked
  `cols_open`       THE LAW, general in the two lists
  `map_flat`, `groups_are`   a tool; what `groupsOf` lists at the kind's two rounds
  `reads_give`      AT THE KIND's OWN ROUNDS, at the groups as `Block.step` lays them: `AllOpen` and
                    "no column is left"

Limits. THAT THE PLAN's LIST IS TIED TO THE BOOK's TREES AT ANY STATE IS NOT SHOWN: `TreeTied` has
no payer here. Where the two lists differ in length the premise `AllTied` is false and the law is
idle. THAT EVERY DRAW LIES BELOW THE POSITIONS' RANGE IS A PREMISE OF BOTH TOPS: at the kind's
rounds `range_give` (Returns/ItemsFit.lean) has it at the plan's range. Nothing on what the columns
hold. That a run's columns pass `Block.step`'s test is the frame's law (`fits_played`,
Johnson/Desc/ProofFile/Honest/Law/Cut.lean), not called here. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.ReadOpen
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (regroup groupsOf)
open VerifiableInference.Desc.First.K2 (P2 rounds flat)
open VerifiableInference.Desc.Own (colsStand)
open _root_.Tw.K2 (Col leafOk)

/-- **THE PREMISE, tree by tree.** t: a tree's place in the book. r: an entry of the plan's list of
read trees: number in the chain, depth, width. -/
def TreeTied (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (r : Nat × Nat × Nat) : Prop :=
  ∃ tree, B0.trees[t]? = some tree ∧ leafOk S tree = true ∧
    (tree.oneList = true → tree.lists = 0) ∧ tree.shape.logN ≤ pos.logN ∧
    tree.number - firstTree = r.1 ∧ tree.shape.logN = r.2.1 ∧
    tree.shape.mainWidth + tree.shape.maskWidth = r.2.2

/-- The premise along two lists: as many trees as entries, each tied to its entry. -/
def AllTied (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    List Nat → List (Nat × Nat × Nat) → Prop
  | [], [] => True
  | t :: ts, r :: rd => TreeTied S firstTree pos B0 t r ∧ AllTied S firstTree pos B0 ts rd
  | _, _ => False

/-- `flat` at a list of read trees. -/
def flatAt (rd : List (Nat × Nat × Nat)) (gs : List (List (Nat × List UInt64))) : List OpenedColumn :=
  (rd.zip gs).flatMap fun x => x.2.map fun c => (x.1.1, c.1, c.2)

theorem flat_is (p : P2) (gs : List (List (Nat × List UInt64))) : flat p gs = flatAt p.read gs :=
  rfl

/-- The list at which a tree of the book is opened, as `groupsOf` lists it. -/
theorem ownAt_list (logN : Nat) (poss : List Nat) (hin : ∀ q ∈ poss, q < 2 ^ logN)
    (B0 : TreeBook) (t : Nat) (tree : Tree) (h : B0.trees[t]? = some tree) :
    (ownAt (Positions.ofDraws logN poss) B0 t).toList =
      Fmt.listOf (poss.map (· % 2 ^ tree.shape.logN)) := by
  rw [← ownAt_eq h]
  unfold Blk.ownList Positions.ofDraws
  by_cases e : tree.shape.logN = logN
  · have hid : poss.map (· % 2 ^ tree.shape.logN) = poss := by
      rw [e]
      exact (List.map_congr_left fun q hq => Nat.mod_eq_of_lt (hin q hq)).trans (List.map_id' _)
    rw [if_pos (by simpa using e), hid, ← listOfT_eq]
  · rw [if_neg (by simpa using e), ← listOfT_eq]
    simp

/-- Columns of one key whose positions and widths are a list's stand as asked. -/
theorem colsStand_of (key W : Nat) : ∀ (A : List OpenedColumn) (xs : List Nat), (∀ a ∈ A, a.1 = key) →
    A.map (fun a => (a.2.1, a.2.2.length)) = xs.map (fun x => (x, W)) →
    colsStand key W A xs = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | a :: A, x :: xs, hk, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    have ih := colsStand_of key W A xs (fun b hb => hk b (List.mem_cons_of_mem _ hb)) h.2
    unfold colsStand at ih ⊢
    rw [List.zip_cons_cons, List.all_cons, ih, hk a List.mem_cons_self, h.1.1, h.1.2]
    simp

/-- **THE LAW.** ts: the book's opened trees. rd: the plan's read trees. cols: columns whose
positions and widths are, group by group, those that `groupsOf` lists. -/
theorem cols_open (S : Statement) (firstTree logN : Nat) (poss : List Nat)
    (hin : ∀ q ∈ poss, q < 2 ^ logN) (B0 : TreeBook) :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)) (cols : List OpenedColumn),
      AllTied S firstTree (Positions.ofDraws logN poss) B0 ts rd →
      cols.map (fun c => (c.2.1, c.2.2.length)) =
        (rd.map fun r => (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x => (x, r.2.2)).flatMap
          id →
      AllOpen S firstTree (Positions.ofDraws logN poss) B0 ts
          (flatAt rd (regroup (rd.map fun r => (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length)
            cols)) ∧
        leftAfter (Positions.ofDraws logN poss) B0 ts
          (flatAt rd (regroup (rd.map fun r => (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length)
            cols)) = []
  | [], [], _, _, _ => ⟨trivial, rfl⟩
  | [], _ :: _, _, hT, _ => hT.elim
  | _ :: _, [], _, hT, _ => hT.elim
  | t :: ts, r :: rd, cols, hT, hc => by
    obtain ⟨⟨tree, h0, hl, ho, hr, e1, e2, e3⟩, hT'⟩ := hT
    have hown := ownAt_list logN poss hin B0 t tree h0
    rw [e2] at hown
    have hsize : (ownAt (Positions.ofDraws logN poss) B0 t).size =
        (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length := by
      rw [← Array.length_toList, hown]
    rw [List.map_cons, List.flatMap_cons] at hc
    have hX : ((Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x => (x, r.2.2)).length =
        (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length := List.length_map _
    have htake : (cols.take (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length).map
        (fun c => (c.2.1, c.2.2.length)) =
        (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x => (x, r.2.2) := by
      rw [List.map_take, hc]
      exact List.take_left' hX
    have hdrop : (cols.drop (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length).map
        (fun c => (c.2.1, c.2.2.length)) =
        (rd.map fun r => (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map
          fun x => (x, r.2.2)).flatMap id := by
      rw [List.map_drop, hc]
      exact List.drop_left' hX
    obtain ⟨ihA, ihL⟩ := cols_open S firstTree logN poss hin B0 ts rd _ hT' hdrop
    have hflat : flatAt (r :: rd) (regroup ((r :: rd).map fun r =>
        (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length) cols) =
        ((cols.take (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length).map
          fun c => (r.1, c.2.1, c.2.2)) ++
        flatAt rd (regroup (rd.map fun r => (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length)
          (cols.drop (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length)) := by
      unfold flatAt
      rw [List.map_cons]
      show ((r, (cols.take _).map fun c => (c.2.1, c.2.2)) :: List.zip rd _).flatMap _ = _
      rw [List.flatMap_cons, List.map_map]
      rfl
    have hlenA : ((cols.take (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).length).map
        fun c => ((r.1, c.2.1, c.2.2) : OpenedColumn)).length =
        (ownAt (Positions.ofDraws logN poss) B0 t).size := by
      have := congrArg List.length htake
      rw [List.length_map, List.length_map] at this
      rw [List.length_map, this, hsize]
    rw [hflat]
    refine ⟨⟨tree, h0, hl, ho, hr, ?_, ?_, ?_⟩, ?_⟩
    · rw [List.length_append, hlenA]
      exact Nat.le_add_right _ _
    · rw [List.take_left' hlenA, hown, e1, e3]
      refine colsStand_of _ _ _ _ (fun a ha => ?_) ?_
      · obtain ⟨c, _, rfl⟩ := List.mem_map.1 ha
        rfl
      · rw [List.map_map]
        exact htake
    · rw [List.drop_left' hlenA]
      exact ihA
    · show leftAfter _ B0 ts (List.drop _ _) = []
      rw [List.drop_left' hlenA]
      exact ihL

/-- A map over lists laid in a row. -/
theorem map_flat {α β γ : Type} (g : β → γ) (f : α → List β) : ∀ l : List α,
    ((l.map f).flatMap id).map g = (l.map fun a => (f a).map g).flatMap id
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append,
      map_flat g f l]
    rfl

/-- What `groupsOf` lists at the kind's two rounds. -/
theorem groups_are (p : P2) (ft : Nat) (d₁ d₂ : Fmt.Drawn) :
    groupsOf ft (rounds p) [d₁, d₂] = p.read.map fun r =>
      (Fmt.listOf (d₂.poss.map (· % 2 ^ r.2.1))).map
        fun x => (p.firstTree + r.1 - ft, x, r.2.2) := by
  simp [rounds, groupsOf, List.map_map, Function.comp_def]

/-- **At the kind's own rounds, at the groups as `Block.step` lays them.** hc: `Block.step`'s test
on the columns. -/
theorem reads_give (S : Statement) (p : P2) (ft logN : Nat) (d₁ d₂ : Fmt.Drawn)
    (hin : ∀ q ∈ d₂.poss, q < 2 ^ logN) (B0 : TreeBook) (ts : List Nat) (cols : List OpenedColumn)
    (hT : AllTied S p.firstTree (Positions.ofDraws logN d₂.poss) B0 ts p.read)
    (hc : cols.map (fun c => (c.1, c.2.1, c.2.2.length)) =
      (groupsOf ft (rounds p) [d₁, d₂]).flatMap id) :
    AllOpen S p.firstTree (Positions.ofDraws logN d₂.poss) B0 ts
        (flat p (regroup ((groupsOf ft (rounds p) [d₁, d₂]).map (·.length)) cols)) ∧
      leftAfter (Positions.ofDraws logN d₂.poss) B0 ts
        (flat p (regroup ((groupsOf ft (rounds p) [d₁, d₂]).map (·.length)) cols)) = [] := by
  rw [groups_are] at hc ⊢
  have hc' : cols.map (fun c => (c.2.1, c.2.2.length)) =
      (p.read.map fun r => (Fmt.listOf (d₂.poss.map (· % 2 ^ r.2.1))).map
        fun x => (x, r.2.2)).flatMap id := by
    have := congrArg (List.map fun y : Nat × Nat × Nat => y.2) hc
    rw [List.map_map, map_flat] at this
    refine this.trans (congrArg (fun l => List.flatMap id l) (List.map_congr_left fun r _ => ?_))
    rw [List.map_map]
    rfl
  have hlen : (p.read.map fun r => (Fmt.listOf (d₂.poss.map (· % 2 ^ r.2.1))).map
      fun x => (p.firstTree + r.1 - ft, x, r.2.2)).map (·.length) =
      p.read.map fun r => (Fmt.listOf (d₂.poss.map (· % 2 ^ r.2.1))).length := by
    rw [List.map_map]
    exact List.map_congr_left fun r _ => List.length_map _
  rw [hlen, flat_is]
  exact cols_open S p.firstTree logN d₂.poss hin B0 ts p.read cols hT hc'

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.flat_is
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ownAt_list
#print axioms VerifiableInference.Desc.K2.Honest.Returns.colsStand_of
#print axioms VerifiableInference.Desc.K2.Honest.Returns.cols_open
#print axioms VerifiableInference.Desc.K2.Honest.Returns.map_flat
#print axioms VerifiableInference.Desc.K2.Honest.Returns.groups_are
#print axioms VerifiableInference.Desc.K2.Honest.Returns.reads_give
