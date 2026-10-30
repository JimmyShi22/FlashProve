-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/UnopenedFirst.lean: AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH
INTO GROUP 1 NO TREE OF THE BOOK HAS BEEN OPENED AT ANY LIST; so, with Returns/UnopenedLinks.lean,
"a tree that the switch opens has been opened at no list" AT EVERY SWITCH INTO A LATER GROUP, IN ONE
STATEMENT. In the goals' scope, UNDER THE PLAN's OWN TEST, THE WRITTEN CUT OF THE FIRST CHAIN AND
THE WRITTEN SHAPE. Statements with their proofs: calls, sums and ONE CLOSED TEST BY LEAN's KERNEL
WITH ITS CONTROL.

  `first_step_stays` AT THE SEAT, over the first segment's opening (the cuts 2 and 3): `treesStay`
                    (Returns/TreesStay.lean)
  `unopened_first` THE CORE, from the fold's returns: the count of oracle messages at a cut from 8
                    up to the front's length is what the first segment's three sendings add ⊢
                    `newZero 0` of the book there
  `first_total`, `first_total_can_fail` THE CLOSED HALF, at the written shape: the library's closed
                    count `n0At 1` is what these three sendings add; a control: with one more it is
                    false
  `link_unopened_first`, `link_unopened_all` THE TOPS: at the number 16 | at every m < 23, at
                    `inFront P9 (frontAt s L Q) s.book y rL cols`: every tree among `treesOf` that
                    stands in the book has `lists` = 0

By, this folder's: `first_stays`, `treesStay_same`, `treesStay_trans` (Returns/TreesStay.lean) ·
`newZero_stays`, `commit_step_stays` (Returns/Unopened.lean) · `book_same_between`, `counts_rise`
(Returns/BookSame.lean) · `link_unopened_reached` (Returns/UnopenedLinks.lean) · `first_places`,
`first_sent` (Returns/FirstSending.lean) · `counts_zero` (Returns/OwnFirst.lean). The library's:
`k1_first_sits`, `Joined.yes` (Johnson/IMR/FirstSeats.lean), `hear_at_flat`
(Johnson/IMR/FlatIx.lean), `flatIx_scope` (Johnson/IMR/FlatScope.lean) · `laid_is_start`
(Johnson/IMR/GroupAt.lean), `start_empty` (Johnson/IMR/BookSeat.lean) · `framesOf_core`
(Johnson/Goal/Meaning/CoreSeated.lean) · `atMoment_of` (Johnson/IMR/FlagsAt.lean), `msgsAt`
(Johnson/IMR/OwnSize.lean), `Open.first` (Johnson/IMR/SeatOpen.lean) · `n0_at_link_paid`
(Johnson/IMR/ToldPaid.lean), `plan_of` (Johnson/P1K2R/FoldSidePaid.lean), `n0At`
(Johnson/Top/H0/K2Hears/PlaceNums.lean), `shW` (Johnson/Top/H0/K2Hands/FrontsFull.lean) · `fold_cut`
(Johnson/IMR/GroupRest.lean), `fold_next` (Johnson/IMR/FoldTools.lean), `front_len`
(Johnson/IMR/FinPin.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean).
`first_step_stays`' descent to the text's yes is `first_places`', which is the library's
`entry_at_zero`'s (Johnson/IMR/FrameEntry.lean): typed a third time.

Limits. DEVICES: `decide +kernel` twice, under a raised recursion limit: the closed test and its
control. The control shows that the test can say no at one changed number, no more. THE FULL SIZE
ALONE. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. Nothing at the output head's switch (Returns/UnopenedLinks.lean
has it) nor behind the last segment. This file's imports are heavy. Nothing on any property.




-/
import Johnson.Desc.K2.Honest.Returns.UnopenedLinks
import Johnson.Desc.K2.Honest.Returns.OwnFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (n0At)
open VerifiableInference.Desc.First.K2Hands (shW)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (laid_is_start start_empty framesOf_core fold_cut fold_next front_len frontOf
  msgsAt atMoment_of)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At the seat: the first segment's opening leaves the elder trees and lays unopened ones.** -/
theorem first_step_stays (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn}
    {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    treesStay (coreS t₀) (coreS t₁) := by
  obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
  have i0 : c.blocksInOrder[2]? = some b := by
    have q := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
      (by omega : 14 * 0 + 0 + 2 = 2)] at q
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs' gs' = .ok m := y1
  exact treesStay_trans (first_stays _ _ y')
    ((framesOf_core treesStay_same hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3)

/-- **No tree has been opened, as long as nothing more is sent.** -/
theorem unopened_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R RE : List Fmt.RoundView} {C CE : List VerifiableInference.Desc.OpenedColumn} {s : S}
    {d : Nat} (hk : 8 + d ≤ (frontOf c).length)
    (f : foldBlocks 0 (c.blocksInOrder.take (8 + d)) (ProofFile.startS Z p) R C = .ok (s, RE, CE))
    (hc : s.st.oracles.size =
      (msgsAt Z.first.shape 0 0 + 1 + Z.first.shape.atStart.length) + msgsAt Z.first.shape 0 1 +
      msgsAt Z.first.shape 0 2) :
    newZero 0 s.book := by
  obtain ⟨t6, R6, C6, g6⟩ := fold_cut (k := 8) d f
  obtain ⟨t₅, R₅, C₅, g₅⟩ := fold_cut (k := 7) 1 g6
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 6) 1 g₅
  obtain ⟨t₃, R₃, C₃, g₃⟩ := fold_cut (k := 5) 1 g₄
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 3) 2 g₃
  obtain ⟨t₀, R₀, C₀, g₀⟩ := fold_cut (k := 2) 1 g₁
  obtain ⟨c4, c6⟩ := counts_zero hS hR O g₁ g₃ g₄ g₅ g6
  have c1 := (first_places hS hR O (Nat.le_refl 3) (by omega) g₁ g₁).1
  have e0 : msgsAt Z.first.shape 0 0 = ((K1.frame₀ Bs.G₀.first).atMoment 0).length := by
    unfold msgsAt
    rw [O.first, atMoment_of (f := K1.frame₀ Z.first) rfl rfl 0]
    rfl
  have hs : (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size =
      msgsAt Z.first.shape 0 0 + 1 + Z.first.shape.atStart.length := by
    rw [first_sent, e0, O.first]
    simp
    omega
  have u13 := counts_rise O (by omega : 3 ≤ 5) (by omega) g₁ g₃
  have u45 := counts_rise O (by omega : 6 ≤ 7) (by omega) g₄ g₅
  have u6s := counts_rise O (by omega : 8 ≤ 8 + d) hk g6 f
  have e13 : t₃.book = t₁.book := book_same_between O (by omega) (by omega) g₁ g₃ (by omega)
  have e45 : t₅.book = t₄.book := book_same_between O (by omega) (by omega) g₄ g₅ (by omega)
  have e6s : s.book = t6.book := book_same_between O (by omega) hk g6 f (by omega)
  have z0 : newZero 0 t₀.book := by
    intro j t _ ht
    rw [laid_is_start hS hR O g₀, (start_empty O.pub p).1] at ht
    cases ht
  have z1 : newZero 0 t₁.book :=
    newZero_stays (a := coreS t₀) (b := coreS t₁) z0 (first_step_stays hS hR O g₀ g₁)
  have z3 : newZero 0 t₃.book := by rw [e13]; exact z1
  have z4 : newZero 0 t₄.book :=
    newZero_stays (a := coreS t₃) (b := coreS t₄) z3
      (commit_step_stays hS hR O (l := 0) (by omega) (j := 3) (Or.inl rfl) g₃ g₄)
  have z5 : newZero 0 t₅.book := by rw [e45]; exact z4
  have z6 : newZero 0 t6.book :=
    newZero_stays (a := coreS t₅) (b := coreS t6) z5
      (commit_step_stays hS hR O (l := 0) (by omega) (j := 5) (Or.inr rfl) g₅ g6)
  rw [e6s]
  exact z6

/-! ## The closed half -/

set_option maxRecDepth 1000000 in
/-- **At the written shape: what the first segment's three sendings add.** -/
theorem first_total : n0At 1 =
      (msgsAt shW 0 0 + 1 + shW.atStart.length) + msgsAt shW 0 1 +
      msgsAt shW 0 2 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one message more the equation is false. -/
theorem first_total_can_fail : n0At 1 ≠
      (msgsAt shW 0 0 + 1 + shW.atStart.length) + msgsAt shW 0 1 +
      msgsAt shW 0 2 + 1 := by
  decide +kernel

/-! ## At a reached state -/

/-- **At the switch into group 1.** -/
theorem link_unopened_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (0 + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ τ ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      s.book.trees[τ]? = some tree → tree.lists = 0 := by
  have hlen : 8 + 8 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  intro τ _ tree ht
  refine unopened_first hS hR O (d := 8) hlen f₂ ?_ τ tree (Nat.zero_le _) ht
  rw [hsh, ← first_total]
  exact Meaning.Carry.n0_at_link_paid hS hR O hcut (l := 1) (by omega) (by omega)
    (fun b hb => P1K2.plan_of O hpl b (List.mem_of_mem_take hb)) z rs cl (s, [], []) f₂

/-- **At every switch into a later group.** -/
theorem link_unopened_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ τ ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      s.book.trees[τ]? = some tree → tree.lists = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | h1
  · exact link_unopened_first hS hR O hpl hcut hsh hr L Q P9 y rL cols
  · exact link_unopened_reached hS hR O hpl hcut hsh h1 h23 hr L Q P9 y rL cols

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_step_stays
#print axioms VerifiableInference.Desc.K2.Honest.Returns.unopened_first
#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_total
#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_total_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_unopened_first
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_unopened_all
