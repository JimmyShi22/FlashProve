-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/LongCols.lean: the code switch: WHAT THE TEXT HEARS AT A DRAWN
POSITION HANGS ON THE COLUMNS AT THAT POSITION ALONE. Second part: from the columns shown to each
message's column at a position.

orc: a family of oracles: to a tree's key and a position, the words of the tree's column there. If
every column that the step is shown is orc's (ColsOf), then what the text cuts out for a message at
the drawn position q is a function of orc, the book, the statement and q.
  ColsOf       every column shown holds orc's words at its own key and position
  GoodOpened   an opened tree, as the text's openOne records it: it was opened at its own list, and
               its column number j holds orc's words at the tree's key and the list's position
               number j
  push_good, openOne_good, open_good  the text's openOne, and the loop over the trees, record such
               entries alone
  colOne       THE COLUMN OF ONE MESSAGE AT ONE POSITION, off orc
  symbolsAt_one  what symbolsAt holds at position number i is colOne at the i-th listed position
LIMITS. orc is a letter. ColsOf is a premise of push_good, openOne_good and open_good; symbolsAt_one
takes what these give (every opened tree is GoodOpened) as its premise. That the columns shown are
some oracles' is not shown. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Desc.Own.ShapesMean
import OnBytes.Slice.BlkProxMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Own (Opened symbolsAt whereOpened colsStand colsStand_iff)

/-- Every column shown is orc's. -/
def ColsOf (orc : Nat → Nat → List UInt64) (cols : List _root_.Tw.K2.Col) : Prop :=
  ∀ c ∈ cols, c.2.2 = orc c.1 c.2.1

/-- An opened tree's record holds orc's columns at the tree's own list. -/
def GoodOpened (B0 : TreeBook) (ft : Nat) (pos : Positions) (orc : Nat → Nat → List UInt64)
    (m : Opened) : Prop :=
  ∃ tree0, B0.trees[m.1]? = some tree0 ∧ m.2.1 = Blk.ownList tree0 pos ∧
    ∀ (j : Nat) (c : Array F), m.2.2[j]? = some c →
      ∃ x, m.2.1[j]? = some x ∧ c = (orc (tree0.number - ft) x).toArray

theorem push_good {ft : Nat} {pos : Positions} {B0 : TreeBook} {t : Nat}
    {orc : Nat → Nat → List UInt64} {cols : List _root_.Tw.K2.Col} {acc : Array Opened}
    {tree0 : OnBytes.Tree} {W : Nat} (h2 : B0.trees[t]? = some tree0)
    (hok : ((cols.take (Blk.ownList tree0 pos).size).length == (Blk.ownList tree0 pos).size &&
      colsStand (tree0.number - ft) W (cols.take (Blk.ownList tree0 pos).size)
        (Blk.ownList tree0 pos).toList) = true)
    (hc : ColsOf orc cols) (hg : ∀ m ∈ acc.toList, GoodOpened B0 ft pos orc m) :
    ColsOf orc (cols.drop (Blk.ownList tree0 pos).size) ∧
      ∀ m ∈ (acc.push (t, Blk.ownList tree0 pos,
        ((cols.take (Blk.ownList tree0 pos).size).map fun y => y.2.2.toArray).toArray)).toList,
        GoodOpened B0 ft pos orc m := by
  rw [Bool.and_eq_true] at hok
  obtain ⟨hlen, hst⟩ := hok
  have hlen' : (cols.take (Blk.ownList tree0 pos).size).length =
      (Blk.ownList tree0 pos).size := by simpa using hlen
  refine ⟨fun c hcm => hc c (List.mem_of_mem_drop hcm), fun m hm => ?_⟩
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · exact hg m hm
  · refine ⟨tree0, h2, rfl, fun j c hj => ?_⟩
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hj
    obtain ⟨col, hcol, rfl⟩ := hj
    have hjl : j < (Blk.ownList tree0 pos).size := by
      rw [← hlen']
      exact (List.getElem?_eq_some_iff.1 hcol).1
    refine ⟨(Blk.ownList tree0 pos)[j], Array.getElem?_eq_getElem hjl, ?_⟩
    obtain ⟨e1, e2, -⟩ := (colsStand_iff _ _ _ _).1 hst j col (Blk.ownList tree0 pos)[j] hcol
      (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hjl])
    rw [hc col (List.mem_of_mem_take (List.mem_of_getElem? hcol)), e1, e2]

theorem openOne_good {S : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook} {t : Nat}
    {orc : Nat → Nat → List UInt64}
    {s s' : TreeBook × List _root_.Tw.K2.Col × Array Opened}
    (h : _root_.Tw.K2.openOne S ft pos B0 t s = .ok s') (hc : ColsOf orc s.2.1)
    (hg : ∀ m ∈ s.2.2.toList, GoodOpened B0 ft pos orc m) :
    ColsOf orc s'.2.1 ∧ ∀ m ∈ s'.2.2.toList, GoodOpened B0 ft pos orc m := by
  unfold _root_.Tw.K2.openOne at h
  simp only at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals (cases h; exact push_good (by assumption) (by assumption) hc hg)

theorem open_good {S : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook}
    {orc : Nat → Nat → List UInt64} : ∀ (ts : List Nat)
    (s s' : TreeBook × List _root_.Tw.K2.Col × Array Opened),
    ts.foldlM (fun s t => _root_.Tw.K2.openOne S ft pos B0 t s) s = .ok s' → ColsOf orc s.2.1 →
    (∀ m ∈ s.2.2.toList, GoodOpened B0 ft pos orc m) →
    ∀ m ∈ s'.2.2.toList, GoodOpened B0 ft pos orc m
  | [], s, s', h, _, hg => by
    cases h
    exact hg
  | t :: ts, s, s', h, hc, hg => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := bindOk h
    obtain ⟨a, b⟩ := openOne_good h1 hc hg
    exact open_good ts s1 s' h2 a b

/-- **The column of one message at one position, off the oracles.** -/
def colOne (S : Statement) (B : TreeBook) (ft logN : Nat) (orc : Nat → Nat → List UInt64) (o : Nat)
    (p : Nat × Nat) (q : Nat) : Option Column :=
  match B.trees[p.1]?, S.oracles[o]? with
  | some tree, some x =>
    some (Blk.columnOf x ((tree.shape.mainSymbols.extract 0 p.2).foldl (· + ·) 0)
      (tree.shape.mainWidth + (tree.shape.maskSymbols.extract 0 p.2).foldl (· + ·) 0)
      (orc (tree.number - ft)
        (if tree.shape.logN == logN then q else q % 2 ^ tree.shape.logN)).toArray)
  | _, _ => none

/-- **What symbolsAt holds at position number i.** -/
theorem symbolsAt_one {S : Statement} {B : TreeBook} {ft : Nat} {pos : Positions}
    {orc : Nat → Nat → List UInt64} {cols : List Opened} {o : Nat} {p : Nat × Nat}
    {out : Array Column} (h : symbolsAt S B pos cols o p = some out)
    (hg : ∀ m ∈ cols, GoodOpened B ft pos orc m) (i : Nat) (hi : i < pos.all.size) :
    out[i]? = colOne S B ft pos.logN orc o p (pos.all.getD i 0) := by
  unfold symbolsAt at h
  split at h
  · rename_i tree x mine h1 h2 h3
    dsimp only at h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨k1, k2⟩ := OnBytes.Slice.list_mapM_inv _ _ _ hl
    have hil : i < l.length := by
      rw [k1]
      simpa using hi
    have k3 := k2 i (by simpa using hi)
    rw [List.getElem_range, List.getElem?_eq_getElem hil] at k3
    obtain ⟨here, hw, k4⟩ := Option.bind_eq_some_iff.1 k3
    obtain ⟨c, hcq, k5⟩ := Option.map_eq_some_iff.1 k4
    obtain ⟨tree0, g1, g2, g3⟩ := hg mine (List.mem_of_find?_eq_some h3)
    have hm1 : mine.1 = p.1 := by simpa using List.find?_some h3
    rw [hm1, h1] at g1
    obtain rfl := Option.some.inj g1
    obtain ⟨xj, hx, rfl⟩ := g3 here c hcq
    have hxj : xj = if (tree.shape.logN == pos.logN) = true then pos.all.getD i 0
        else pos.all.getD i 0 % 2 ^ tree.shape.logN := by
      unfold whereOpened at hw
      by_cases hs : (tree.shape.logN == pos.logN) = true
      · rw [if_pos hs] at hw ⊢
        obtain rfl := Option.some.inj hw
        rw [g2] at hx
        unfold Blk.ownList at hx
        rw [if_pos hs] at hx
        rw [Array.getD_eq_getD_getElem?, hx]
        rfl
      · rw [if_neg hs] at hw ⊢
        obtain ⟨-, e⟩ := OnBytes.Slice.ProxRun.idxOf_some _ _ _ hw
        rw [Array.getD_eq_getD_getElem?, hx] at e
        exact e
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hil, ← k5]
    unfold colOne
    rw [h1, h2, hxj]
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.open_good
#print axioms VerifiableInference.Desc.First.K2.symbolsAt_one
