-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/UnopenedLinks.lean: "A TREE THAT THE SWITCH OPENS HAS BEEN OPENED AT
NO LIST" AT A REACHED STATE, AT 23 OF THE KIND's 25 PLACES (the switches into the groups 2 to 23;
the output head's): MORE THAN `AllOpen`'s clause "a tree of one list has not been opened"
(Returns/ReadOpen.lean) asks. In the goals' scope, UNDER THE PLAN's OWN TEST, THE WRITTEN CUT OF THE
FIRST CHAIN AND THE WRITTEN SHAPE: three premises that the heads `P5J.AtMg` | `P5J.AtMgA` pay. NOT
the switch into group 1, NOT the place behind the last segment. Statements with their proofs: calls,
sums and ONE CLOSED TEST BY LEAN's KERNEL WITH ITS CONTROL.

  `opened_unopened` THE CORE, from the fold's returns: l + 1 < 24 · the count at 14 (l + 1) + 2 is
                    n₀ · the count at the far cut is n₀ and what the segment's three sendings add ⊢
                    in the book at the far cut the tree of a message that the carried rows at 14 (l
                    + 2) + 2 name has `lists` = 0
  `seg_totals`, `seg_totals_can_fail`, `seg_total` THE CLOSED HALF, at the written shape: for k = 1
                    … 23 the library's closed count `n0At (k + 1)` is `n0At k` and what segment k's
                    three sendings add; a control: with one more it is false at k = 1; the test's
                    yes as an equation
  `link_unopened_reached`, `head_unopened_reached` THE TOPS: 1 ≤ m < 23, at `inFront P9 (frontAt s L
                    Q) s.book y rL cols` | at 339, at `inFront P9 (headFrontOf s a T) s.book y rL
                    cols`: every tree among `treesOf` that stands in the book has `lists` = 0

By, this folder's: `unopened_seg` (Returns/Unopened.lean) · `counts_rise` (Returns/BookSame.lean) ·
`members_behind_laid`, `fresh_behind_laid` (Returns/SeatsWalk.lean) · `mem_ids`, `tree_of_opened`
(Returns/OwnReached.lean) · `cut_kept` (Returns/CutsKept.lean) · `link_book_reached`
(Returns/MembersReached.lean), `head_book_reached` (Returns/ArmsFree.lean), `placeQ`
(Returns/PinReached.lean). The library's: `n0_at_link_paid`, `n0_at_head_paid`
(Johnson/IMR/ToldPaid.lean): the counts at the switches' cuts, closed · `plan_of`
(Johnson/P1K2R/FoldSidePaid.lean) · `n0At` (Johnson/Top/H0/K2Hears/PlaceNums.lean), `shW`
(Johnson/Top/H0/K2Hands/FrontsFull.lean) · `open_has` (Johnson/IMR/WalkGivesAt.lean) · `open_recAll`
(Johnson/IMR/ListsEnds.lean), `rows_of_pub`, `laid_at` (Johnson/IMR/FrontPin.lean) ·
`front_nums_head` (Johnson/IMR/HeadFront.lean), `frontAt_of` (Johnson/Top/H0/Tw/K2C/HeldAtYes.lean)
· `fold_cut` (Johnson/IMR/GroupRest.lean), `fold_back` (Johnson/IMR/FoldTools.lean), `front_len`
(Johnson/IMR/FinPin.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean).
`opened_unopened`'s first lines are `mates_opened`'s (Returns/OwnReached.lean).

Limits. DEVICES: `decide +kernel` twice, under a raised recursion limit: the closed test and its
control. The control shows that the test can say no at one changed number, no more. THE FULL SIZE
ALONE. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. At the head `here` and the group's look-up are premises. This
file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.Unopened
import Johnson.Desc.K2.Honest.Returns.OwnReached
import Johnson.IMR.ToldPaid
import Johnson.P1K2R.FoldSidePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf frontAt_of n0At)
open VerifiableInference.Desc.First.K2Hands (shW)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (open_has open_recAll rows_of_pub laid_at front_len fold_cut fold_back frontOf
  front_nums_head msgsAt)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **The tree of an opened message has been opened at no list.** -/
theorem opened_unopened (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat}
    (h24 : l + 1 < 24) {p : ProofFile.InstPub} {R R₂ RE : List Fmt.RoundView}
    {C C₂ CE : List VerifiableInference.Desc.OpenedColumn} {t₂ s : S} {d n₀ : Nat} (hd : 8 ≤ d)
    (hk : 14 * (l + 1) + 8 + d ≤ (frontOf c).length)
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1 + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 8 + d)) (ProofFile.startS Z p) R C = .ok (s, RE, CE))
    (h0 : ∀ t R' C', foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C =
      .ok (t, R', C') → t.st.oracles.size = n₀)
    (hc : s.st.oracles.size = n₀ +
      (1 + (First.K2.targetAt Z.first.shape (l + 1)).kept.size +
        (msgsAt Z.first.shape (l + 1) 0 + 1)) +
      msgsAt Z.first.shape (l + 1) 1 + msgsAt Z.first.shape (l + 1) 2)
    {o τ j : Nat} {tree : Tree} (ho : o ∈ (singleRowsOracles t₂.check.frame.rows).toList)
    (po : s.book.place[o]? = some (τ, j)) (ht : s.book.trees[τ]? = some tree) :
    tree.lists = 0 := by
  have h1 : 1 ≤ l + 1 := by omega
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, hmem⟩ :=
    members_behind_laid hS hR O h1 h24 f₂
  have hfresh := fresh_behind_laid hS hR O h1 h24 g₀ f₂
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega) (by omega) f₂).walk
      (by rw [(laid_at hS hR O (by omega : l + 1 + 1 < 25) f₂).2]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, hfresh, mem_ids] at ho
  have u3 := counts_rise O (by omega : 14 * (l + 1) + 2 ≤ 14 * (l + 1) + 5) (by omega) g₀ g₃
  have u5 := counts_rise O (by omega : 14 * (l + 1) + 2 ≤ 14 * (l + 1) + 7) (by omega) g₀ g₅
  have hge : t₀.st.oracles.size ≤ o := by
    rcases ho with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ <;> omega
  have K₀ := cut_kept O (by omega : 14 * (l + 1) + 2 ≤ 14 * (l + 1) + 8 + d) hk g₀ f
  rw [open_has O (by omega) g₀] at K₀
  have hτ : t₀.book.trees.size ≤ τ := by
    have k := K₀.2.2 o τ j po
    rcases Nat.lt_or_ge τ t₀.book.trees.size with lt | ge
    · have lo : o < t₀.st.oracles.size := k.2 lt
      omega
    · exact ge
  refine unopened_seg hS hR O h24 hk g₀ f ?_ τ tree hτ ht
  rw [h0 t₀ R₀ C₀ g₀]
  exact hc

/-! ## The closed half -/

set_option maxRecDepth 1000000 in
/-- **At the written shape: what a segment's three sendings add is what the closed counts say.** -/
theorem seg_totals : ((List.range' 1 23).all fun k => decide (n0At (k + 1) = n0At k +
      (1 + (First.K2.targetAt shW k).kept.size + (msgsAt shW k 0 + 1)) +
      msgsAt shW k 1 + msgsAt shW k 2)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one message more the equation is false at segment 1. -/
theorem seg_totals_can_fail : n0At 2 ≠ n0At 1 +
      (1 + (First.K2.targetAt shW 1).kept.size + (msgsAt shW 1 0 + 1)) +
      msgsAt shW 1 1 + msgsAt shW 1 2 + 1 := by
  decide +kernel

theorem seg_total {k : Nat} (h1 : 1 ≤ k) (h24 : k < 24) : n0At (k + 1) = n0At k +
      (1 + (First.K2.targetAt shW k).kept.size + (msgsAt shW k 0 + 1)) +
      msgsAt shW k 1 + msgsAt shW k 2 :=
  of_decide_eq_true (List.all_eq_true.1 seg_totals k (by rw [List.mem_range'_1]; omega))

/-! ## At a reached state -/

/-- **At the switches into the groups 2 to 23.** -/
theorem link_unopened_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    {m : Nat} (h1 : 1 ≤ m) (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ τ ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      s.book.trees[τ]? = some tree → tree.lists = 0 := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  have hlen : 14 * (l + 1) + 8 + 8 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  have f : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 8 + 8)) (ProofFile.startS Z z) rs cl =
      .ok (s, [], []) := by
    rw [show 14 * (l + 1) + 8 + 8 = 14 * (l + 1 + 1) + 2 by omega]
    exact f₂
  have hp : ∀ k, ∀ b ∈ c.blocksInOrder.take k, b.planOk = true :=
    fun k b hb => P1K2.plan_of O hpl b (List.mem_of_mem_take hb)
  intro τ hτ tree ht
  obtain ⟨o, ho, e⟩ := tree_of_opened hτ
  have hlt := (link_book_reached hS hR O h23 hr L Q P9 y rL cols).1 o ho
  have hlt' : o < s.book.place.size := hlt
  have po : s.book.place[o]? = some (τ, (s.book.place.getD o (0, 0)).2) := by
    have e' : (s.book.place.getD o (0, 0)).1 = τ := e
    rw [← e', Array.getElem?_eq_getElem hlt']
    simp [Array.getD, hlt']
  refine opened_unopened hS hR O (by omega : l + 1 < 24) (n₀ := n0At (l + 1)) (Nat.le_refl 8)
    hlen f₂ f (fun t R' C' g => Meaning.Carry.n0_at_link_paid hS hR O hcut (by omega) (by omega)
      (hp _) z rs cl (t, R', C') g) ?_ ho po ht
  rw [hsh, ← seg_total (by omega : 1 ≤ l + 1) (by omega)]
  exact Meaning.Carry.n0_at_link_paid hS hR O hcut (by omega) (by omega) (hp _) z rs cl
    (s, [], []) f₂

/-- **At the output head's switch.** -/
theorem head_unopened_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) {G : ReqGroup}
    (group : s.check.frame.groups[s.check.frame.link]? = some G) (T : SwitchTarget) (P9 : Par9)
    (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    ∀ τ ∈ treesOf (inFront P9 (headFrontOf s a T) s.book y rL cols), ∀ tree,
      s.book.trees[τ]? = some tree → tree.lists = 0 := by
  have hlen : 14 * (22 + 1) + 8 + 9 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f⟩ := (reach_raw hr).fold
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f
  have hrows : a.fr.rows = tm.check.frame.rows :=
    (front_nums_head hS hR O fm f (q := placeQ .head) rfl
      (frontAt_of (Or.inr (Or.inl ⟨rfl, a, G, here, group, rfl⟩)))).2.2.1
  have hp : ∀ k, ∀ b ∈ c.blocksInOrder.take k, b.planOk = true :=
    fun k b hb => P1K2.plan_of O hpl b (List.mem_of_mem_take hb)
  intro τ hτ tree ht
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
  refine opened_unopened hS hR O (l := 22) (by omega) (n₀ := n0At 23) (d := 9) (by omega)
    hlen fm f (fun t R' C' g => Meaning.Carry.n0_at_link_paid hS hR O hcut (l := 23) (by omega)
      (by omega) (hp _) z rs cl (t, R', C') g) ?_ ho' po ht
  rw [hsh, ← seg_total (k := 23) (by omega) (by omega)]
  exact Meaning.Carry.n0_at_head_paid hS hR O hcut (hp _) z rs cl (s, [], []) f

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.opened_unopened
#print axioms VerifiableInference.Desc.K2.Honest.Returns.seg_totals
#print axioms VerifiableInference.Desc.K2.Honest.Returns.seg_totals_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.seg_total
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_unopened_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_unopened_reached
