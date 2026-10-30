-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/OwnReached.lean: `ReadFits.own` (Returns/Read.lean: a tree that holds
an opened message holds opened messages alone) AT A STATE THAT IS REACHED IN FRONT OF A SWITCH, IN
THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC PART: AT THE SWITCHES INTO THE GROUPS 2 TO 23 AND AT
THE OUTPUT HEAD's: 23 OF THE KIND's 25 PLACES. NOT at the switch into group 1, which opens segment
0's messages, NOR behind the last segment, which opens segment 24's. Statements with their proofs:
calls and sums.

  `mem_shift`, `mem_ids` sums: a range of numbers shifted; the opened messages, as
                    Returns/SeatsWalk.lean has them, are three stretches of numbers
  `mates_opened` THE CORE, from the fold's returns: 1 ≤ l < 24: in the book at any cut k from 14 (l
                    + 1) + 2 up to the front's length, a message that has the tree of one of the
                    messages that the carried rows at 14 (l + 1) + 2 name is itself named by them
  `tree_of_opened` a tree among the opened messages' trees is the tree of one of them, by the book's
                    list of places
  `link_own_reached`, `head_own_reached` `ReadFits.own`, in its own letters, at `inFront P9 (frontAt
                    s L Q) s.book y rL cols`, 1 ≤ m < 23, and at `inFront P9 (headFrontOf s a T)
                    s.book y rL cols`: for all P9, y, rL, cols

THE ROAD. The opened messages are the closed segment's three sendings, whole: the switch's (the
carrying message, the kept copies, the own messages of moment 0, the fresh mask) and the two later
ones' (`members_behind_laid`, `fresh_behind_laid`: Returns/SeatsWalk.lean; `counts_link`:
Returns/SendCounts.lean). The book is cut in front of and behind each (`cut_kept`, `cut_mates`:
Returns/CutsKept.lean): so a message of one of their trees lies in the same stretch. Every part of a
tree is placed where it stands (`partsPlaced_reached`, `own_of_places`: Returns/PartsPlaced.lean).

By, beside these, the library's: `open_has` (Johnson/IMR/WalkGivesAt.lean) · `open_recAll`
(Johnson/IMR/ListsEnds.lean), `rows_of_pub`, `laid_at` (Johnson/IMR/FrontPin.lean): two masks ·
`front_len` (Johnson/IMR/FinPin.lean) · `fold_cut` (Johnson/IMR/GroupRest.lean), `fold_back`
(Johnson/IMR/FoldTools.lean) · `listOfT_eq` (OnBytes/Chain/Draws.lean), `listOf_mem`
(Fmt/Rules6Laws.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean) ·
`front_nums_head` (Johnson/IMR/HeadFront.lean): the head's own frame's carried rows are the walk's
at 338. This folder's: `link_book_reached` (Returns/MembersReached.lean), `head_book_reached`
(Returns/ArmsFree.lean): the opened messages have places · `placeQ` (Returns/PinReached.lean).

Limits. TWO OF THE 25 PLACES ARE LEFT. "Reached" is: over the list of the wrapped sub-protocols.
`here` and the frame's group's look-up are premises at the head. THE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.PartsPlaced
import Johnson.Desc.K2.Honest.Returns.CutsKept
import Johnson.Desc.K2.Honest.Returns.SeatsWalk
import Johnson.Desc.K2.Honest.Returns.SendCounts
import Johnson.Desc.K2.Honest.Returns.MembersReached
import Johnson.Desc.K2.Honest.Returns.ArmsFree
import Johnson.Desc.K2.Honest.Returns.PinReached
import Johnson.IMR.HeadFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf frontAt_of)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (open_has open_recAll rows_of_pub laid_at front_len fold_cut fold_back frontOf
  msgsAt front_nums_head)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

/-- A range of numbers, shifted. -/
theorem mem_shift (n a q : Nat) :
    q ∈ ((Array.range n).map (· + a)).toList ↔ a ≤ q ∧ q < a + n := by
  simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨q - a, by omega, by omega⟩

/-- The opened messages are three stretches of numbers. -/
theorem mem_ids (n₀ K m0 c₃ m1 c₅ m2 q : Nat) :
    q ∈ ((#[n₀] ++ (Array.range K).map (· + (n₀ + 1)) ++
        ((Array.range m0).map (· + (n₀ + (1 + K))) ++ (Array.range m1).map (· + c₃) ++
          (Array.range m2).map (· + c₅))).push (n₀ + (1 + K) + m0)).toList ↔
      (n₀ ≤ q ∧ q < n₀ + (1 + K + (m0 + 1))) ∨ (c₃ ≤ q ∧ q < c₃ + m1) ∨
        (c₅ ≤ q ∧ q < c₅ + m2) := by
  rw [Array.toList_push, List.mem_append, Array.toList_append, List.mem_append,
    Array.toList_append, List.mem_append, Array.toList_append, List.mem_append,
    Array.toList_append, List.mem_append, mem_shift, mem_shift, mem_shift, mem_shift,
    List.mem_singleton, List.mem_singleton]
  omega

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **A message of an opened message's tree is opened.** -/
theorem mates_opened (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₂ Rk : List Fmt.RoundView}
    {C C₂ Ck : List VerifiableInference.Desc.OpenedColumn} {t₂ t : S} {k : Nat}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hk₂ : 14 * (l + 1) + 2 ≤ k) (hk : k ≤ (frontOf c).length)
    (f : foldBlocks 0 (c.blocksInOrder.take (k)) (ProofFile.startS Z p) R C = .ok (t, Rk, Ck))
    {o q τ j j' : Nat} (ho : o ∈ (singleRowsOracles t₂.check.frame.rows).toList)
    (po : t.book.place[o]? = some (τ, j)) (pq : t.book.place[q]? = some (τ, j')) :
    q ∈ (singleRowsOracles t₂.check.frame.rows).toList := by
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, hmem⟩ :=
    members_behind_laid hS hR O h1 h24 f₂
  have hfresh := fresh_behind_laid hS hR O h1 h24 g₀ f₂
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 14 * l + 3) 13
    (by rw [show 14 * l + 3 + 13 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 14 * l + 6) 10
    (by rw [show 14 * l + 6 + 10 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨t₆, R₆, C₆, g₆⟩ := fold_cut (k := 14 * l + 8) 8
    (by rw [show 14 * l + 8 + 8 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨c1, c4, c6⟩ := counts_link hS hR O h1 h24 g₀ g₁ g₃ g₄ g₅ g₆
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega) (Nat.le_trans hk₂ hk) f₂).walk
      (by rw [(laid_at hS hR O (by omega : l + 1 < 25) f₂).2]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, hfresh, mem_ids] at ho ⊢
  have K₀ := cut_kept O (by omega : 14 * l + 2 ≤ k) hk g₀ f
  have K₁ := cut_kept O (by omega : 14 * l + 3 ≤ k) hk g₁ f
  have K₃ := cut_kept O (by omega : 14 * l + 5 ≤ k) hk g₃ f
  have K₄ := cut_kept O (by omega : 14 * l + 6 ≤ k) hk g₄ f
  have K₅ := cut_kept O (by omega : 14 * l + 7 ≤ k) hk g₅ f
  have K₆ := cut_kept O (by omega : 14 * l + 8 ≤ k) hk g₆ f
  rw [open_has O (by omega) g₀] at K₀
  rw [open_has O (by omega) g₁, c1] at K₁
  rw [open_has O (by omega) g₃] at K₃
  rw [open_has O (by omega) g₄, c4] at K₄
  rw [open_has O (by omega) g₅] at K₅
  rw [open_has O (by omega) g₆, c6] at K₆
  rcases ho with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl (cut_mates K₀ K₁ po pq a b)
  · exact Or.inr (Or.inl (cut_mates K₃ K₄ po pq a b))
  · exact Or.inr (Or.inr (cut_mates K₅ K₆ po pq a b))

/-- A tree among the opened ones' trees is the tree of an opened message. -/
theorem tree_of_opened {i : _root_.Tw.K2.SwIn} {τ : Nat} (h : τ ∈ treesOf i) :
    ∃ o ∈ (idsOf i).toList, (i.book.place.getD o (0, 0)).1 = τ := by
  unfold treesOf at h
  rw [listOfT_eq, Fmt.listOf_mem] at h
  unfold placesOf at h
  simp only [Array.toList_map, List.mem_map] at h
  obtain ⟨_, ⟨o, ho, rfl⟩, e⟩ := h
  exact ⟨o, ho, e⟩

/-- **`ReadFits.own` at the switch into a group from the second on.** -/
theorem link_own_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h1 : 1 ≤ m)
    (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ t ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      (inFront P9 (frontAt s L Q) s.book y rL cols).book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList,
        q ∈ (idsOf (inFront P9 (frontAt s L Q) s.book y rL cols)).toList := by
  have hlen : 14 * (m + 1) + 2 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  refine own_of_places (i := (inFront P9 (frontAt s L Q) s.book y rL cols)) (r := s.roots)
    (partsPlaced_reached O (reach_raw hr) hlen) fun q τ k pq hτ => ?_
  obtain ⟨o, ho, e⟩ := tree_of_opened hτ
  have hlt := (link_book_reached hS hR O h23 hr L Q P9 y rL cols).1 o ho
  have hlt' : o < s.book.place.size := hlt
  have po : s.book.place[o]? = some (τ, (s.book.place.getD o (0, 0)).2) := by
    have e' : (s.book.place.getD o (0, 0)).1 = τ := e
    rw [← e', Array.getElem?_eq_getElem hlt']
    simp [Array.getD, hlt']
  exact mates_opened hS hR O h1 (by omega) f₂ (Nat.le_refl _) hlen f₂ ho po pq

/-- **`ReadFits.own` at the output head's switch.** -/
theorem head_own_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) {G : ReqGroup}
    (group : s.check.frame.groups[s.check.frame.link]? = some G) (T : SwitchTarget) (P9 : Par9)
    (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    ∀ t ∈ treesOf (inFront P9 (headFrontOf s a T) s.book y rL cols), ∀ tree,
      (inFront P9 (headFrontOf s a T) s.book y rL cols).book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList,
        q ∈ (idsOf (inFront P9 (headFrontOf s a T) s.book y rL cols)).toList := by
  have hlen : 339 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f⟩ := (reach_raw hr).fold
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f
  have hrows : a.fr.rows = tm.check.frame.rows :=
    (front_nums_head hS hR O fm f (q := placeQ .head) rfl
      (frontAt_of (Or.inr (Or.inl ⟨rfl, a, G, here, group, rfl⟩)))).2.2.1
  refine own_of_places (i := (inFront P9 (headFrontOf s a T) s.book y rL cols)) (r := s.roots)
    (partsPlaced_reached O (reach_raw hr) hlen) fun q τ k pq hτ => ?_
  obtain ⟨o, ho, e⟩ := tree_of_opened hτ
  have hlt := (head_book_reached hS hR O hr here T P9 y rL cols).1 o ho
  have hlt' : o < s.book.place.size := hlt
  have po : s.book.place[o]? = some (τ, (s.book.place.getD o (0, 0)).2) := by
    have e' : (s.book.place.getD o (0, 0)).1 = τ := e
    rw [← e', Array.getElem?_eq_getElem hlt']
    simp [Array.getD, hlt']
  have ho' : o ∈ (singleRowsOracles tm.check.frame.rows).toList := by
    rw [← hrows]
    exact ho
  show q ∈ (singleRowsOracles a.fr.rows).toList
  rw [hrows]
  exact mates_opened hS hR O (l := 23) (by omega) (by omega) fm (by omega) hlen f ho' po pq

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.mem_shift
#print axioms VerifiableInference.Desc.K2.Honest.Returns.mem_ids
#print axioms VerifiableInference.Desc.K2.Honest.Returns.mates_opened
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tree_of_opened
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_own_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_own_reached
