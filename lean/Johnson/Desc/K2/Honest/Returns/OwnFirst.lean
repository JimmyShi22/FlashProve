-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/OwnFirst.lean: `ReadFits.own` (Returns/Read.lean) AT THE SWITCH INTO
GROUP 1, WHICH OPENS THE FIRST SEGMENT's MESSAGES: AT A STATE THAT IS REACHED AT THE NUMBER 16, IN
THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC PART. With Returns/OwnReached.lean and
Returns/OwnFinish.lean: ALL 25 OF THE KIND's PLACES. Statements with their proofs: calls and sums.

  `mem_ids0` sums: the first segment's opened messages are three stretches of numbers, the first
                    from 0
  `counts_zero` how many messages the first segment's two later sendings add (`counts_link`,
                    Returns/SendCounts.lean, begins at segment 1)
  `mates_opened0` THE CORE, from the fold's returns: in the book at any cut k from 16 up to the
                    front's length, a message that has the tree of one of the messages that the
                    carried rows at 16 name is itself named by them
  `link_own_first` `ReadFits.own`, in its own letters, at `inFront P9 (frontAt s L Q) s.book y rL
                    cols`: for all L, Q, P9, y, rL, cols
  `link_own_all` the same at every m < 23: with `link_own_reached` (Returns/OwnReached.lean)

THE ROAD. The two later sendings: as at the other segments: each is just what lies between two cuts
of the walk (Returns/CutsKept.lean). THE FIRST SENDING CARRIES MORE THAN IS OPENED: behind the own
messages of moment 0 and the fresh mask ride the shape's messages "at the start". They stand in
other trees: in every later book the sending's messages stand where `layTrees` lays them
(`first_places`, Returns/FirstSending.lean); two messages of one tree have one class of leaves
(`layTrees_class`, Returns/TreeClass.lean); a rider's class is above the others' (`first_class`,
Returns/FirstSending.lean, under the shape's own public test, which holds at a reached state).

By, beside these, this folder's: `closing_behind_laid` (Returns/SeatsWalk.lean) · `step_count`
(Returns/SendCounts.lean) · `mem_shift`, `tree_of_opened` (Returns/OwnReached.lean) · `cut_kept`,
`cut_mates` (Returns/CutsKept.lean) · `partsPlaced_reached`, `own_of_places`
(Returns/PartsPlaced.lean) · `link_book_reached` (Returns/MembersReached.lean). The library's:
`flags_zero_named` (Johnson/IMR/FlagsZeroNamed.lean) · `mask_zero_named`
(Johnson/IMR/MaskZeroNamed.lean) · `tail_rows` (Johnson/IMR/GroupTail.lean) · `closeFrame_reads`
(Johnson/Desc/First/Link/Law/CloseReads.lean) · `entry_at_zero` (Johnson/IMR/FrameEntry.lean),
`walk_a`, `walk_b` (Johnson/IMR/FrameAt.lean), `atMoment_of` (Johnson/IMR/FlagsAt.lean) ·
`laid_is_start` (Johnson/IMR/GroupAt.lean) · `open_has` (Johnson/IMR/WalkGivesAt.lean) ·
`open_recAll` (Johnson/IMR/ListsEnds.lean), `rows_of_pub`, `laid_at` (Johnson/IMR/FrontPin.lean) ·
`reqOk_shape` (OnBytes/Params/Fit/TreesSized.lean) · `Open.first` (Johnson/IMR/SeatOpen.lean) ·
`front_len` (Johnson/IMR/FinPin.lean) · `fold_cut` (Johnson/IMR/GroupRest.lean), `fold_back`
(Johnson/IMR/FoldTools.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean).

Limits. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN
MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.OwnReached
import Johnson.Desc.K2.Honest.Returns.TreeClass
import Johnson.Desc.K2.Honest.Returns.FirstSending
import Johnson.IMR.MaskZeroNamed
import OnBytes.Params.Fit.TreesSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (closeFrame_reads)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (laterF flags_zero_named mask_zero_named tail_rows entry_at_zero walk_a walk_b
  atMoment_of laid_is_start open_has open_recAll rows_of_pub laid_at front_len fold_cut fold_back
  frontOf msgsAt)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

/-- The first segment's opened messages are three stretches of numbers. -/
theorem mem_ids0 (m0 c₃ m1 c₅ m2 q : Nat) :
    q ∈ (((Array.range m0).map (· + 0) ++ (Array.range m1).map (· + c₃) ++
        (Array.range m2).map (· + c₅)).push m0).toList ↔
      q < m0 + 1 ∨ (c₃ ≤ q ∧ q < c₃ + m1) ∨ (c₅ ≤ q ∧ q < c₅ + m2) := by
  rw [Array.toList_push, List.mem_append, Array.toList_append, List.mem_append,
    Array.toList_append, List.mem_append, mem_shift, mem_shift, mem_shift, List.mem_singleton]
  omega

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **The first segment's two later sendings.** -/
theorem counts_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₁ R₃ R₄ R₅ R₆ : List Fmt.RoundView}
    {C C₁ C₃ C₄ C₅ C₆ : List VerifiableInference.Desc.OpenedColumn} {t₁ t₃ t₄ t₅ t₆ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₄ : foldBlocks 0 (c.blocksInOrder.take (6)) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅))
    (f₆ : foldBlocks 0 (c.blocksInOrder.take (8)) (ProofFile.startS Z p) R C = .ok (t₆, R₆, C₆)) :
    t₄.st.oracles.size = t₃.st.oracles.size + msgsAt Z.first.shape 0 1 ∧
      t₆.st.oracles.size = t₅.st.oracles.size + msgsAt Z.first.shape 0 2 := by
  have h24 : 0 < 24 := by omega
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 2) f₁
  have e0s := laid_is_start hS hR O f₀
  have Rr := open_recAll hS hR O (Nat.le_refl 2) (by rw [front_len hS hR O]; omega) f₀
  obtain ⟨f, a1, a2, mo, lk, hg, -, sh, -, -⟩ := entry_at_zero hS hR O f₁
  have s1 : f.shape = Z.first.shape := by
    rw [sh, ← e0s]
    exact Rr.walk.shape
  obtain ⟨b1, -⟩ := walk_a hS hR O h24 f₁ a1 a2 2 (by omega) t₃ R₃ C₃ f₃
  obtain ⟨b2, -⟩ := walk_b hS hR O h24 f₁ f₃ hg a1 a2 1 (by omega) t₅ R₅ C₅ f₅
  refine ⟨?_, ?_⟩
  · rw [step_count hS hR O h24 (j := 3) (Or.inl rfl) f₃ f₄ b1.link, mo, atMoment_of s1 lk]
    rfl
  · rw [step_count hS hR O h24 (j := 5) (Or.inr rfl) f₅ f₆ b2.link]
    have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    rw [m2, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk]
    rfl

/-- **A message of an opened message's tree is opened: the first segment's.** -/
theorem mates_opened0 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₂ Rk : List Fmt.RoundView} {C C₂ Ck : List VerifiableInference.Desc.OpenedColumn}
    {t₂ t : S} {k : Nat}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (16)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hk₂ : 16 ≤ k) (hk : k ≤ (frontOf c).length)
    (f : foldBlocks 0 (c.blocksInOrder.take (k)) (ProofFile.startS Z p) R C = .ok (t, Rk, Ck))
    {o q τ j j' : Nat} (ho : o ∈ (singleRowsOracles t₂.check.frame.rows).toList)
    (po : t.book.place[o]? = some (τ, j)) (pq : t.book.place[q]? = some (τ, j')) :
    q ∈ (singleRowsOracles t₂.check.frame.rows).toList := by
  have h24 : 0 < 24 := by omega
  -- the opened messages as numbers
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 9) 7 f₂
  obtain ⟨L, G, hL, -, -, hG, hmem, -⟩ := tail_rows hS hR O h24 fu f₂
  obtain ⟨t₃, t₅, R₃, R₅, C₃, C₅, L', G', g₃, g₅, hL', -, hG', em, -, eo, -⟩ :=
    flags_zero_named hS hR O (n := 1) (by omega) fu
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain ⟨w, Rw, Cw, Lw, Q, rs, x, fw, hLw, -, hx, hf, -⟩ := closing_behind_laid hS hR O h24 f₂
  obtain ⟨_, mk, -, -, hm, hfr⟩ := closeFrame_reads hx
  obtain ⟨Lm, hLm, -, hmask⟩ := mask_zero_named hS hR O (n := 9) (by omega) fw
  obtain rfl : Lw = Lm := Option.some.inj (hLw.symm.trans hLm)
  have hfresh : t₂.check.frame.rows.fresh = msgsAt Z.first.shape 0 0 := by
    rw [hf, hfr]
    exact Option.some.inj (hm.symm.trans hmask)
  have Rr := open_recAll hS hR O (by omega : 2 ≤ 16) (Nat.le_trans hk₂ hk) f₂
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub Rr.walk
      (by rw [(laid_at hS hR O (by omega : 1 < 25) f₂).2]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, em, eo, hfresh, mem_ids0] at ho ⊢
  -- the cuts
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 3) 13 f₂
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 6) 10 f₂
  obtain ⟨t₆, R₆, C₆, g₆⟩ := fold_cut (k := 8) 8 f₂
  obtain ⟨c4, c6⟩ := counts_zero hS hR O g₁ g₃ g₄ g₅ g₆
  have K₁ := cut_kept O (by omega : 3 ≤ k) hk g₁ f
  have K₃ := cut_kept O (by omega : 5 ≤ k) hk g₃ f
  have K₄ := cut_kept O (by omega : 6 ≤ k) hk g₄ f
  have K₅ := cut_kept O (by omega : 7 ≤ k) hk g₅ f
  have K₆ := cut_kept O (by omega : 8 ≤ k) hk g₆ f
  obtain ⟨c1, ly, hly, hpl⟩ := first_places hS hR O (by omega : 3 ≤ k) hk g₁ f
  rw [open_has O (by omega) g₁, c1] at K₁
  rw [open_has O (by omega) g₃] at K₃
  rw [open_has O (by omega) g₄, c4] at K₄
  rw [open_has O (by omega) g₅] at K₅
  rw [open_has O (by omega) g₆, c6] at K₆
  rcases ho with a | ⟨a, b⟩ | ⟨a, b⟩
  · -- the first sending: the riders stand in other trees
    refine Or.inl ?_
    have e0 : msgsAt Z.first.shape 0 0 = ((K1.frame₀ Bs.G₀.first).atMoment 0).length := by
      unfold msgsAt
      rw [O.first, atMoment_of (f := K1.frame₀ Z.first) rfl rfl 0]
      rfl
    have hsz : ((K1.frame₀ Bs.G₀.first).atMoment 0).length + 1 ≤
        (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size := by
      rw [first_sent]
      simp
    have ho' : o < (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size := by omega
    have hq' : q < (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size :=
      (K₁.2.2 q τ j' pq).2 ((K₁.2.2 o τ j po).1 ho')
    have eo' : ly.tree.getD o 0 = τ :=
      congrArg Prod.fst (Option.some.inj ((hpl o ho').symm.trans po))
    have eq' : ly.tree.getD q 0 = τ :=
      congrArg Prod.fst (Option.some.inj ((hpl q hq').symm.trans pq))
    have ecl := layTrees_class _ _ ly hly ho' hq' (eo'.trans eq'.symm)
    have hok : reqShapeOk Bs.G₀.first.shape = true := by
      rw [O.first]
      exact OnBytes.Params.reqOk_shape Rr.ok
    rcases Nat.lt_or_ge q (msgsAt Z.first.shape 0 0 + 1) with lt | ge
    · exact lt
    · have := first_class (K1.gpOf Z) hok (i := o) (j := q) (by omega) (by omega) hq'
      omega
  · exact Or.inr (Or.inl (cut_mates K₃ K₄ po pq a b))
  · exact Or.inr (Or.inr (cut_mates K₅ K₆ po pq a b))

/-- **`ReadFits.own` at the switch into group 1.** -/
theorem link_own_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (0 + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ t ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      (inFront P9 (frontAt s L Q) s.book y rL cols).book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList,
        q ∈ (idsOf (inFront P9 (frontAt s L Q) s.book y rL cols)).toList := by
  have hlen : 16 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  refine own_of_places (i := (inFront P9 (frontAt s L Q) s.book y rL cols)) (r := s.roots)
    (partsPlaced_reached O (reach_raw hr) hlen) fun q τ k pq hτ => ?_
  obtain ⟨o, ho, e⟩ := tree_of_opened hτ
  have hlt := (link_book_reached hS hR O (by omega : 0 < 23) hr L Q P9 y rL cols).1 o ho
  have hlt' : o < s.book.place.size := hlt
  have po : s.book.place[o]? = some (τ, (s.book.place.getD o (0, 0)).2) := by
    have e' : (s.book.place.getD o (0, 0)).1 = τ := e
    rw [← e', Array.getElem?_eq_getElem hlt']
    simp [Array.getD, hlt']
  exact mates_opened0 hS hR O f₂ (Nat.le_refl _) hlen f₂ ho po pq

/-- **`ReadFits.own` at every switch into a later group.** -/
theorem link_own_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ t ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      (inFront P9 (frontAt s L Q) s.book y rL cols).book.trees[t]? = some tree →
      ∀ q ∈ tree.parts.toList,
        q ∈ (idsOf (inFront P9 (frontAt s L Q) s.book y rL cols)).toList := by
  rcases Nat.eq_zero_or_pos m with rfl | h1
  · exact link_own_first hS hR O hr L Q P9 y rL cols
  · exact link_own_reached hS hR O h1 h23 hr L Q P9 y rL cols

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.mem_ids0
#print axioms VerifiableInference.Desc.K2.Honest.Returns.counts_zero
#print axioms VerifiableInference.Desc.K2.Honest.Returns.mates_opened0
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_own_first
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_own_all
