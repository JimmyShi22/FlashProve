-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/BookAt15.lean: IN FRONT OF
THE KEY FILE's FIRST PROXIMITY TEST THE BOOK's TREE OF THE LOOKUPS' OWN MESSAGE HAS THE SHAPE THAT
THE DESCRIPTION TELLS: OFF THE HISTORY. At a state of the first chain that was reached at border 15
(two lookups): the book places message 1 where the planner's layouts say; the tree there has the
layout's shape; the description tells of the tree of that number; and what it tells fits that shape
(ShapeIs, Johnson/Desc/K12/Coin/FramesTie.lean). So SeatIs holds of every member that is tied to
that place, at every numbering that gives the place its number.

Main names:
  toldK1 P: what a sending of the kind K1 tells of its trees, in a row.
  toldK1_at | toldK1_length | toldK1_shape: its entry number τ, written out; it tells of as many
    trees as the layout has shapes; ShapeIs of the layout's shape and what is told.
  seatIs_of_shape: SeatIs of a member that is tied to a place whose tree fits what is told, with
    the numbering a letter.
  book_15_of: the sentence above, where the description tells what the two sendings tell.
  book_15: the sentence above. seatIs_15: SeatIs at that place.

That the description tells, at (the first sending's trees) + τ, what the second sending tells of its
tree τ: a sibling file's oracleAt_own (Johnson/RunOne/Law/KeyToldFirst.lean).

Kin: the like for the linear claim's chain's sendings (told_at, told_shape,
Johnson/Desc/K12/Coin/ToldOfLay.lean), whose list differs in how a tenant's groups are read.
Words: "the description" is the key file's IOP as written in Lean (Key.descriptionFromSource X N P); "the planner's
layout" is what layTrees, the routine that places a prover's message's oracle messages in trees,
returns; a "block" is a sub-protocol.
Premise of book_15 and seatIs_15: two lookups; no other premise on the plan. book_15_of has, beside,
what the sibling file pays.
Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.BookAt2
import Johnson.Desc.K12.Coin.ToldOfLay
import Johnson.RunOne.Law.KeyToldFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.BookAt15
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.LayTreesLaws
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K1 (Par)
open VerifiableInference.Desc.K12.Coin (ShapeIs SeatIs tenantOf zipIdx_range)
open VerifiableInference.Desc.Key (FirstState Claim Source lookupsOf)
open _root_.Desc.K14.Law.Fence (seatsB laidSeats seatsB_iff)
open Johnson.RunOne.Sound (FK fk_first_flat fk_idx_at fk_msg_at)
open Johnson.RunOne.Law.FrontSteps (sent_par messageOf_first)
open Johnson.RunOne.Law.BookStays (book_back)
open Johnson.RunOne.Law.BookAt2 (seats_two)
open LPFD (Hist₁)

/-- What a sending of the kind K1 tells of its trees, in a row. -/
def toldK1 (P : Par) : List VerifiableInference.Desc.Oracle :=
  (VerifiableInference.Desc.K1.oracles P).flatMap id

/-- **The entry number τ of what is told.** -/
theorem toldK1_at (P : Par) (lay : TreeLay) (h : Own.treesMade P.codes P.sent = some lay) (τ : ℕ)
    (T : TreeShape) (hT : lay.shapes[τ]? = some T) :
    (toldK1 P)[τ]? = some
      { logLength := T.logN, words := T.mainWidth + T.maskWidth
        tenants := (inTree lay.tree τ P.sent.size).map (tenantOf P.sent P.groups) } := by
  have hl : layTrees P.codes P.sent = some lay := by rw [← Own.treesMade_eq]; exact h
  have hsz := layTrees_treeSize P.codes P.sent lay hl
  unfold toldK1 VerifiableInference.Desc.K1.oracles VerifiableInference.Desc.K1.Par.trees
  rw [h]
  simp only [List.flatMap_cons, List.flatMap_nil, id, List.append_nil, Option.map_some,
    Option.getD_some]
  rw [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, hT]
  simp only [Option.map_some, Nat.zero_add]
  congr 2
  rw [zipIdx_range _ default, List.filter_map, List.map_map, Array.length_toList]
  unfold inTree
  have hf : (List.range P.sent.size).filter
        ((fun x : OracleNotice × ℕ => lay.tree[x.2]? == some τ) ∘
          fun i => (P.sent.toList.getD i default, i)) =
      (List.range P.sent.size).filter fun i => lay.tree.getD i 0 == τ := by
    refine List.filter_congr fun i hi => ?_
    have hi' : i < lay.tree.size := by rw [hsz]; exact List.mem_range.1 hi
    show (lay.tree[i]? == some τ) = (lay.tree.getD i 0 == τ)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
    simp
  rw [hf]
  refine List.map_congr_left fun i _ => ?_
  have e : P.sent.toList.getD i default = P.sent.getD i default := by
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  show _ = tenantOf P.sent P.groups i
  simp only [Function.comp, e]
  rfl

/-- It tells of as many trees as the layout has shapes. -/
theorem toldK1_length (P : Par) (lay : TreeLay) (h : Own.treesMade P.codes P.sent = some lay) :
    (toldK1 P).length = lay.shapes.size := by
  unfold toldK1 VerifiableInference.Desc.K1.oracles VerifiableInference.Desc.K1.Par.trees
  rw [h]
  simp

/-- **Of each tree something is told, and it fits the layout's shape.** -/
theorem toldK1_shape (P : Par) (lay : TreeLay) (h : Own.treesMade P.codes P.sent = some lay)
    (τ : ℕ) (T : TreeShape) (hT : lay.shapes[τ]? = some T) :
    ∃ o, (toldK1 P)[τ]? = some o ∧ ShapeIs T o := by
  have hl : layTrees P.codes P.sent = some lay := by rw [← Own.treesMade_eq]; exact h
  obtain ⟨a, b⟩ := layTrees_symbols P.codes P.sent lay hl τ T hT
  refine ⟨_, toldK1_at P lay h τ T hT, ?_, ?_, rfl⟩
  · rw [a, List.map_map]
    rfl
  · rw [b, List.map_map]
    rfl

/-- SeatIs of a member that is tied to a place of the book whose tree fits what is told, at every
numbering that gives the place the number j₀. -/
theorem seatIs_of_shape (no : ℕ → ℕ) (book : TreeBook) (m : H2K.First.Seat1) (z u j₀ : ℕ)
    (T : Tree) (o : VerifiableInference.Desc.Oracle) (hT : book.trees[z]? = some T)
    (hS : ShapeIs T.shape o) (hno : no z = j₀) (hmt : m.t = z) (hmp : m.part = u)
    (hts : m.tsh = T.shape) : SeatIs no book m j₀ u o :=
  ⟨by rw [hmt]; exact hno, by rw [hmt, hT, hts]; rfl, hmp, by rw [hts]; exact hS.main,
    by rw [hts]; exact hS.mask, by rw [hts]; exact hS.log⟩

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The sentence, where the description tells what the two sendings tell.** PI, PB: the two
sendings' parameters. -/
theorem book_15_of (PI PB : Par) (hcI : PI.codes = X.Y.k.oneTime.codes)
    (hsI : PI.sent = #[X.Y.k.oneTime.indexMasks]) (hcB : PB.codes = X.Y.k.oneTime.codes)
    (hsB : PB.sent = Wf.messageOf X.Y.k.oneTime.ranges)
    (hO : ∀ τ, τ < (toldK1 PB).length →
      (VerifiableInference.Desc.Key.descriptionFromSource X N P).oracleAt ((toldK1 PI).length + τ) =
        (toldK1 PB)[τ]?)
    (D : WholeD) (hn : (lookupsOf X.Y.k.oneTime).length = 2) (a)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 15 a) :
    ∃ layI layB T o, layTrees X.Y.k.oneTime.codes #[X.Y.k.oneTime.indexMasks] = some layI ∧
      layTrees X.Y.k.oneTime.codes (Wf.messageOf X.Y.k.oneTime.ranges) = some layB ∧
      (show FirstState from a.2).d.book.place[1]? =
        some (layI.shapes.size + layB.tree.getD 0 0, layB.part.getD 0 0) ∧
      (show FirstState from a.2).d.book.trees[layI.shapes.size + layB.tree.getD 0 0]? = some T ∧
      T.shape = layB.shapes.getD (layB.tree.getD 0 0) default ∧
      (VerifiableInference.Desc.Key.descriptionFromSource X N P).oracleAt
        (layI.shapes.size + layB.tree.getD 0 0) = some o ∧
      ShapeIs T.shape o := by
  obtain ⟨a0, h0, -, eb⟩ := book_back D 13 (by rw [hn]) a h
  obtain ⟨layI, layB, hlI, hlB, hs⟩ := seats_two D a0 h0
  rw [seatsB_iff] at hs
  obtain ⟨lm, hlm⟩ := messageOf_first X.Y.k.oneTime.ranges
  have hpos : 0 < (Wf.messageOf X.Y.k.oneTime.ranges).size := by
    rw [← Array.length_toList, hlm]
    exact Nat.succ_pos _
  obtain ⟨hp, ht⟩ := hs (1 + 0, (layI.shapes.size + layB.tree.getD 0 0, layB.part.getD 0 0),
    layB.shapes.getD (layB.tree.getD 0 0) default)
    (List.mem_map.2 ⟨0, List.mem_range.2 hpos, rfl⟩)
  obtain ⟨T, hT, hTs⟩ := Option.map_eq_some_iff.1 ht
  have hmI : Own.treesMade PI.codes PI.sent = some layI := by
    rw [Own.treesMade_eq, hcI, hsI]
    exact hlI
  have hmB : Own.treesMade PB.codes PB.sent = some layB := by
    rw [Own.treesMade_eq, hcB, hsB]
    exact hlB
  have hτ : layB.tree.getD 0 0 < layB.shapes.size :=
    (Own.treesMade_gives hmB).2.1 0 (by rw [hsB]; exact hpos)
  have hsh : layB.shapes[layB.tree.getD 0 0]? = some T.shape := by
    rw [hTs, Array.getElem?_eq_getElem hτ, Array.getElem_eq_getD default]
  obtain ⟨o, ho, hS⟩ := toldK1_shape PB layB hmB _ _ hsh
  refine ⟨layI, layB, T, o, hlI, hlB, by rw [eb]; exact hp, by rw [eb]; exact hT, hTs, ?_, hS⟩
  rw [← toldK1_length PI layI hmI, hO _ (by rw [toldK1_length PB layB hmB]; exact hτ)]
  exact ho

open Johnson.RunOne.KeySendGood (parIdx parMsg) in
open Johnson.RunOne.Law.KeyToldFirst (par_facts oracleAt_own) in
/-- **IN FRONT OF THE FIRST PROXIMITY TEST THE BOOK's TREE OF THE LOOKUPS' OWN MESSAGE HAS THE SHAPE
THAT THE DESCRIPTION TELLS.** -/
theorem book_15 (D : WholeD) (hn : (lookupsOf X.Y.k.oneTime).length = 2) (a)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 15 a) :
    ∃ layI layB T o, layTrees X.Y.k.oneTime.codes #[X.Y.k.oneTime.indexMasks] = some layI ∧
      layTrees X.Y.k.oneTime.codes (Wf.messageOf X.Y.k.oneTime.ranges) = some layB ∧
      (show FirstState from a.2).d.book.place[1]? =
        some (layI.shapes.size + layB.tree.getD 0 0, layB.part.getD 0 0) ∧
      (show FirstState from a.2).d.book.trees[layI.shapes.size + layB.tree.getD 0 0]? = some T ∧
      T.shape = layB.shapes.getD (layB.tree.getD 0 0) default ∧
      (VerifiableInference.Desc.Key.descriptionFromSource X N P).oracleAt
        (layI.shapes.size + layB.tree.getD 0 0) = some o ∧
      ShapeIs T.shape o :=
  book_15_of (parIdx X) (parMsg X) (par_facts X).1 (par_facts X).2.1 (par_facts X).2.2.1
    (par_facts X).2.2.2 (fun τ hτ => oracleAt_own X N P τ hτ) D hn a h

/-- **SeatIs at that place**, of every member that is tied to it, at every numbering that gives the
place the number j₀. -/
theorem seatIs_15 (D : WholeD) (hn : (lookupsOf X.Y.k.oneTime).length = 2) (a)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 15 a) :
    ∃ z u T o, (show FirstState from a.2).d.book.place[1]? = some (z, u) ∧
      (show FirstState from a.2).d.book.trees[z]? = some T ∧
      (VerifiableInference.Desc.Key.descriptionFromSource X N P).oracleAt z = some o ∧
      ∀ (no : ℕ → ℕ) (m : H2K.First.Seat1) (j₀ : ℕ), no z = j₀ → m.t = z → m.part = u →
        m.tsh = T.shape → SeatIs no (show FirstState from a.2).d.book m j₀ u o := by
  obtain ⟨layI, layB, T, o, -, -, hp, hT, -, ho, hS⟩ := book_15 (N := N) (P := P) D hn a h
  exact ⟨_, _, T, o, hp, hT, ho, fun no m j₀ hno hmt hmp hts =>
    seatIs_of_shape no _ m _ _ j₀ T o hT hS hno hmt hmp hts⟩

end Johnson.RunOne.Law.BookAt15

#print axioms Johnson.RunOne.Law.BookAt15.toldK1_at
#print axioms Johnson.RunOne.Law.BookAt15.toldK1_length
#print axioms Johnson.RunOne.Law.BookAt15.toldK1_shape
#print axioms Johnson.RunOne.Law.BookAt15.seatIs_of_shape
#print axioms Johnson.RunOne.Law.BookAt15.book_15_of
#print axioms Johnson.RunOne.Law.BookAt15.book_15
#print axioms Johnson.RunOne.Law.BookAt15.seatIs_15
