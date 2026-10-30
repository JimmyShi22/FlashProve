-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeatsCarried.lean: **THE SHARED CHAIN's RECORD CARRIES WHERE EACH MESSAGE WAS LAID: A THIRD BOOL BESIDE "shape k".** Definitions with code; statements and proofs, in the blocks' own
decide-form.

What for. The tie of the two frames (Johnson/Desc/K12/Coin/FramesTie.lean: hM | hZ) leaves two facts on the book at the two proximity tests: a member's place is (a place whose tree has the
file's number, the tenant), and the tree there has the shape that the description tells. What ONE sending's laid trees are (part, symbols, shape) is a law on the planner's layout, on the plan alone: that
law is not this file's. Here: that the record CARRIES the layout from the sending to the tests.
  seatsB l B       for each (message's number, (place of its tree in the book, its part), the tree's shape) of the list l: the book places the message so, and the tree there has that shape. KIN: K12's
                   Part1P (Law/FirstRead.lean:511), of which this is the book's half, as a test with code.
  laidSeats n0 base sent lay   the list for one sending: n0: the first message's number; base: the book's count of trees in front.
  seatsB_keeps     BookKeeps (the library's: each place; each tree's shape, number, parts) keeps it.    bookKeeps_recv   a receiving has BookKeeps.
  seatsB_new       **a receiving lays it**: seatsB (laidSeats bk.place.size bk.trees.size sent lay) at the book behind, where the layout names its own trees.
  seatX P sentU layU layO k d   THE BOOL: borders 0 … 2: the book is empty · 3 … 5: it has just o_u's sending's places and trees, laid so · 6 … 12: both sendings' are laid so (at the chain's last border 12 too) · behind: nothing.
  seatX_first · seatX_front · seatX_k14 · seatX_onGu · seatX_onGomega · seatX_end   EVERY BLOCK HANDS IT ON.
  seatX_place      what the tests, and the last chain's start, spend: at the borders 6 … 12: the i-th message of either sending, its place and its tree's shape.
  seatsB_moved     A CONTROL: a book that places the message elsewhere fails.
Limits. layU | layO: the planner's layouts at the PLAN's codes (layTrees P.codes …): premises. WHICH NUMBERS THE GROUP's MEMBERS BEAR is not here. At the chain's own record St. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookAtK14
import Johnson.Desc.Sound.FenceK14Named
import Johnson.Desc.K12.Coin.SamplesThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Sound (Received recvBook recvBook_place_new recvBook_place_old
  partsLaid_count treesSent_count)

/-- A message's number; the place of its tree in the book and its part; the tree's shape. -/
abbrev Laid : Type := ℕ × (ℕ × ℕ) × TreeShape

/-- The book places each listed message so, and the tree there has that shape. -/
def seatsB (l : List Laid) (B : TreeBook) : Bool :=
  l.all fun e => B.place[e.1]? == some e.2.1 && (B.trees[e.2.1.1]?).map (·.shape) == some e.2.2

theorem seatsB_iff (l : List Laid) (B : TreeBook) : seatsB l B = true ↔
    ∀ e ∈ l, B.place[e.1]? = some e.2.1 ∧ (B.trees[e.2.1.1]?).map (·.shape) = some e.2.2 := by
  unfold seatsB
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem seatsB_append (l l' : List Laid) (B : TreeBook) :
    seatsB (l ++ l') B = (seatsB l B && seatsB l' B) := by
  unfold seatsB
  rw [List.all_append]

/-- The list for one sending. -/
def laidSeats (n0 base : ℕ) (sent : Array OracleNotice) (lay : TreeLay) : List Laid :=
  (List.range sent.size).map fun i =>
    (n0 + i, (base + lay.tree.getD i 0, lay.part.getD i 0),
      lay.shapes.getD (lay.tree.getD i 0) default)

/-- What keeps each place and each tree's shape keeps it. -/
theorem seatsB_keeps (l : List Laid) (B B' : TreeBook) (hk : BookKeeps B B')
    (h : seatsB l B = true) : seatsB l B' = true := by
  rw [seatsB_iff] at h ⊢
  intro e he
  obtain ⟨h1, h2⟩ := h e he
  refine ⟨hk.place _ _ h1, ?_⟩
  obtain ⟨T, hT, e2⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨T', hT', e3, _⟩ := hk.tree _ T hT
  rw [hT']
  show some T'.shape = _
  rw [e3, e2]

/-- A receiving keeps what lay in the book. -/
theorem bookKeeps_recv (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) : BookKeeps bk (recvBook ft bk sent lay n0 roots) := by
  refine ⟨fun o p h => ?_, fun t T h => ?_⟩
  · rw [recvBook_place_old ft bk sent lay n0 roots o (Array.getElem?_eq_some_iff.1 h).1]
    exact h
  · have ht : t < bk.trees.size := (Array.getElem?_eq_some_iff.1 h).1
    refine ⟨T, ?_, rfl, rfl, rfl⟩
    show (partsLaid sent lay n0 bk.trees.size (treesSent ft _ roots bk.trees))[t]? = some T
    rw [partsLaid_old _ _ _ _ _ t ht, treesSent_old _ _ _ _ t ht]
    exact h

/-- The τ-th of the appended trees has the τ-th shape. -/
theorem treesSent_new_shape (first : ℕ) : ∀ (l : List TreeShape) (r : ℕ) (A : Array Tree) (τ : ℕ),
    τ < l.length → ((treesSent first l r A)[A.size + τ]?).map (·.shape) = l[τ]?
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | s :: l, r, A, 0, _ => by
    show ((treesSent first l (r + 1) (A.push _))[A.size + 0]?).map (·.shape) = _
    rw [treesSent_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
    rfl
  | s :: l, r, A, τ + 1, h => by
    have ih := treesSent_new_shape first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ (Nat.lt_of_succ_lt_succ h)
    rw [Array.size_push] at ih
    have e1 : A.size + (τ + 1) = A.size + 1 + τ := by omega
    show ((treesSent first l (r + 1) (A.push _))[A.size + (τ + 1)]?).map (·.shape) = _
    rw [e1, ih]
    rfl

/-- **A receiving lays it.** -/
theorem seatsB_new (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) (hl : ∀ i, i < sent.size → lay.tree.getD i 0 < lay.shapes.size) :
    seatsB (laidSeats bk.place.size bk.trees.size sent lay) (recvBook ft bk sent lay n0 roots) =
      true := by
  rw [seatsB_iff]
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
  have hi' : i < sent.size := List.mem_range.1 hi
  refine ⟨recvBook_place_new ft bk sent lay n0 roots i hi', ?_⟩
  have hτ := hl i hi'
  have h1 : ((recvBook ft bk sent lay n0 roots).trees[bk.trees.size + lay.tree.getD i 0]?).map
      (fun x => (x.shape, x.number)) =
      ((treesSent ft lay.shapes.toList roots bk.trees)[bk.trees.size + lay.tree.getD i 0]?).map
        fun x => (x.shape, x.number) := partsLaid_public _ _ _ _ _ _
  have h2 := congrArg (Option.map Prod.fst) h1
  rw [Option.map_map, Option.map_map] at h2
  show ((recvBook ft bk sent lay n0 roots).trees[bk.trees.size + lay.tree.getD i 0]?).map
    (·.shape) = some (lay.shapes.getD (lay.tree.getD i 0) default)
  refine (h2.trans (treesSent_new_shape ft _ roots bk.trees _
    (by rw [Array.length_toList]; exact hτ))).trans ?_
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem hτ, Array.getElem_eq_getD default]

/-- The book's two counts behind a receiving. -/
theorem recvBook_counts (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) : (recvBook ft bk sent lay n0 roots).place.size = bk.place.size + sent.size ∧
      (recvBook ft bk sent lay n0 roots).trees.size = bk.trees.size + lay.shapes.size := by
  constructor
  · show (bk.place ++ _).size = _
    simp
  · show (partsLaid sent lay n0 bk.trees.size
      (treesSent ft lay.shapes.toList roots bk.trees)).size = _
    rw [partsLaid_count, treesSent_count, Array.length_toList]

/-! ## The Bool -/

/-- **THE THIRD BOOL BESIDE "shape k".** sentU, layU: o_u's sending's messages and their layout; layO: o_omega's sending's layout. -/
def seatX (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ) (d : St) : Bool :=
  if k ≤ 2 then d.book.place.size == 0 && d.book.trees.size == 0
  else if k ≤ 5 then
    d.book.place.size == sentU.size && d.book.trees.size == layU.shapes.size &&
      seatsB (laidSeats 0 0 sentU layU) d.book
  else if k ≤ 12 then
    seatsB (laidSeats 0 0 sentU layU ++ laidSeats sentU.size layU.shapes.size (withOmega P.S) layO) d.book
  else true

theorem seatX_first (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (codes : Codes)
    (key : TableKey) : seatX P sentU layU layO 0 (first codes key) = true := rfl

/-- A block that leaves the book hands it on inside a stretch of borders with one clause. -/
theorem seatX_same (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ) (d d' : St)
    (hb : d'.book = d.book) (hk : k + 1 ≤ 2 ∨ (2 < k ∧ k + 1 ≤ 5) ∨ 5 < k)
    (h : seatX P sentU layU layO k d = true) : seatX P sentU layU layO (k + 1) d' = true := by
  unfold seatX at h ⊢
  rw [hb]
  rcases hk with h1 | ⟨h1, h2⟩ | h1
  · rw [if_pos (by omega)] at h
    rw [if_pos h1]
    exact h
  · rw [if_neg (by omega), if_pos (by omega)] at h
    rw [if_neg (by omega), if_pos h2]
    exact h
  · rw [if_neg (by omega), if_neg (by omega)] at h
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h3 : k + 1 ≤ 12
    · rw [if_pos (by omega)] at h
      rw [if_pos h3]
      exact h
    · rw [if_neg h3]

theorem seatX_front (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (frontBlock c).decide d rs gs = .ok d') (hX : seatX P sentU layU layO 0 d = true) :
    seatX P sentU layU layO 1 d' = true :=
  seatX_same P sentU layU layO 0 d d' (by rw [bookStep_front c d d' rs gs h]) (.inl (by omega)) hX

/-- **K14's eight blocks hand it on.** i: the block's place in blocks P, from 0. -/
theorem seatX_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (sentU : Array OracleNotice)
    (hU : withU P.S = some sentU) (layU layO : TreeLay)
    (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (i : ℕ) (b : Block St Unit) (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hX : seatX P sentU layU layO (i + 1) d = true) :
    seatX P sentU layU layO (i + 2) d' = true := by
  obtain ⟨sentU', hU', e2, e5⟩ := blocks_two P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl : sentU' = sentU := Option.some.inj (hU'.symm.trans hU)
  have own : (b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8) → d'.book = d.book := fun hq =>
    (own_leave P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h).1
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · obtain rfl : b1 = b := by simpa using hb
    exact seatX_same P sentU' layU layO 1 d d' (own (.inl rfl)) (.inl (by omega)) hX
  · obtain rfl : b2 = b := by simpa using hb
    rw [e2] at h
    obtain ⟨_, _, _, rb, _⟩ := sendAt_received_plan P _ (parK1 P 2 "o_u and the first mask" sentU') _
      _ _ (behindU_book P.par) layU (by rw [parK1_sent]; exact hlU) d d' rs gs h
    rw [parK1_sent] at rb
    unfold seatX at hX ⊢
    rw [if_pos (by omega)] at hX
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [Bool.and_eq_true, beq_iff_eq] at hX ⊢
    obtain ⟨p0, t0⟩ := hX
    obtain ⟨c1, c2⟩ := recvBook_counts (parK1 P 2 "o_u and the first mask" sentU').gp.firstTree d.book
      sentU' layU d.st.oracles.size d.roots
    have hn := seatsB_new (parK1 P 2 "o_u and the first mask" sentU').gp.firstTree d.book sentU' layU
      d.st.oracles.size d.roots fun j hj => OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlU hj
    rw [p0, t0] at hn
    rw [rb]
    exact ⟨⟨by rw [c1, p0, Nat.zero_add], by rw [c2, t0, Nat.zero_add]⟩, hn⟩
  · obtain rfl : b3 = b := by simpa using hb
    exact seatX_same P sentU' layU layO 3 d d' (own (.inr (.inl rfl))) (.inr (.inl ⟨by omega, by omega⟩)) hX
  · obtain rfl : b4 = b := by simpa using hb
    exact seatX_same P sentU' layU layO 4 d d' (own (.inr (.inr (.inl rfl))))
      (.inr (.inl ⟨by omega, by omega⟩)) hX
  · obtain rfl : b5 = b := by simpa using hb
    rw [e5] at h
    obtain ⟨_, _, _, rb, _⟩ := sendAt_received_plan P _ (parK1 P 5 "o_omega and o_sp" (withOmega P.S))
      _ _ _ (behindOmega_book P.par) layO (by rw [parK1_sent]; exact hlO) d d' rs gs h
    rw [parK1_sent] at rb
    unfold seatX at hX ⊢
    rw [if_neg (by omega), if_pos (by omega)] at hX
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp only [Bool.and_eq_true, beq_iff_eq] at hX
    obtain ⟨⟨p0, t0⟩, hs⟩ := hX
    have hn := seatsB_new (parK1 P 5 "o_omega and o_sp" (withOmega P.S)).gp.firstTree d.book
      (withOmega P.S) layO d.st.oracles.size d.roots
      fun j hj => OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO hj
    rw [p0, t0] at hn
    rw [rb, seatsB_append, Bool.and_eq_true]
    exact ⟨seatsB_keeps _ _ _ (bookKeeps_recv _ _ _ _ _ _) hs, hn⟩
  · obtain rfl : b6 = b := by simpa using hb
    exact seatX_same P sentU' layU layO 6 d d' (own (.inr (.inr (.inr (.inl rfl))))) (.inr (.inr (by omega))) hX
  · obtain rfl : b7 = b := by simpa using hb
    exact seatX_same P sentU' layU layO 7 d d' (own (.inr (.inr (.inr (.inr (.inl rfl))))))
      (.inr (.inr (by omega))) hX
  · obtain rfl : b8 = b := by simpa using hb
    exact seatX_same P sentU' layU layO 8 d d' (own (.inr (.inr (.inr (.inr (.inr rfl))))))
      (.inr (.inr (by omega))) hX
  · simp at hb

/-- A block that keeps what lay in the book hands it on behind the second sending. -/
theorem seatX_keeps (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ) (d d' : St)
    (hk : 5 < k) (hb : BookKeeps d.book d'.book) (h : seatX P sentU layU layO k d = true) :
    seatX P sentU layU layO (k + 1) d' = true := by
  unfold seatX at h ⊢
  rw [if_neg (by omega), if_neg (by omega)] at h
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases h3 : k + 1 ≤ 12
  · rw [if_pos (by omega)] at h
    rw [if_pos h3]
    exact seatsB_keeps _ _ _ hb h
  · rw [if_neg h3]

theorem seatX_onGu (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') (hX : seatX P sentU layU layO 9 d = true) : seatX P sentU layU layO 10 d' = true :=
  seatX_keeps P sentU layU layO 9 d d' (by omega)
    (VerifiableInference.Desc.K12.Coin.onGu_leaves p he ha d d' rs gs h).2.2.2.2 hX

theorem seatX_onGomega (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') (hX : seatX P sentU layU layO 10 d = true) :
    seatX P sentU layU layO 11 d' = true :=
  seatX_keeps P sentU layU layO 10 d d' (by omega)
    (VerifiableInference.Desc.K12.Coin.onGomega_leaves p he ha d d' rs gs h).2.2.2.2 hX

/-- Past the chain's end, at one record. -/
theorem seatX_end (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (h : seatX P sentU layU layO 11 d = true) : seatX P sentU layU layO 12 d = true :=
  seatX_same P sentU layU layO 11 d d rfl (.inr (.inr (by omega))) h

/-- **What the tests spend.** -/
theorem seatX_place (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ) (d : St)
    (hk : 5 < k ∧ k ≤ 12) (h : seatX P sentU layU layO k d = true) :
    (∀ i, i < sentU.size →
      d.book.place[i]? = some (layU.tree.getD i 0, layU.part.getD i 0) ∧
        (d.book.trees[layU.tree.getD i 0]?).map (·.shape) =
          some (layU.shapes.getD (layU.tree.getD i 0) default)) ∧
    ∀ i, i < (withOmega P.S).size →
      d.book.place[sentU.size + i]? =
          some (layU.shapes.size + layO.tree.getD i 0, layO.part.getD i 0) ∧
        (d.book.trees[layU.shapes.size + layO.tree.getD i 0]?).map (·.shape) =
          some (layO.shapes.getD (layO.tree.getD i 0) default) := by
  unfold seatX at h
  rw [if_neg (by omega), if_neg (by omega), if_pos hk.2, seatsB_iff] at h
  constructor
  · intro i hi
    have := h (0 + i, (0 + layU.tree.getD i 0, layU.part.getD i 0),
      layU.shapes.getD (layU.tree.getD i 0) default)
      (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
    simpa using this
  · intro i hi
    exact h (sentU.size + i, (layU.shapes.size + layO.tree.getD i 0, layO.part.getD i 0),
      layO.shapes.getD (layO.tree.getD i 0) default)
      (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

/-- A control: a book that places the message elsewhere fails. -/
theorem seatsB_moved (e : Laid) (l : List Laid) (B : TreeBook) (q : ℕ × ℕ)
    (hq : B.place[e.1]? = some q) (hne : q ≠ e.2.1) : seatsB (e :: l) B = false := by
  cases h : seatsB (e :: l) B with
  | false => rfl
  | true =>
    have h1 := ((seatsB_iff _ _).1 h e List.mem_cons_self).1
    rw [hq] at h1
    exact absurd (Option.some.inj h1) hne

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.seatsB_new
#print axioms Desc.K14.Law.Fence.seatX_k14
#print axioms Desc.K14.Law.Fence.seatX_onGu
#print axioms Desc.K14.Law.Fence.seatX_onGomega
#print axioms Desc.K14.Law.Fence.seatX_place
#print axioms Desc.K14.Law.Fence.seatsB_moved
