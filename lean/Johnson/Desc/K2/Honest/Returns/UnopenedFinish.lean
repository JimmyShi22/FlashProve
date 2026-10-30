-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/UnopenedFinish.lean: "A TREE THAT THE SWITCH OPENS HAS BEEN OPENED AT
NO LIST" BEHIND THE LAST SEGMENT (the number 353), AT A REACHED STATE: with
Returns/UnopenedLinks.lean and Returns/UnopenedFirst.lean: AT ALL 25 OF THE KIND's PLACES. In the
goals' scope, UNDER THE PLAN's OWN TEST, THE WRITTEN CUT OF THE FIRST CHAIN AND THE WRITTEN SHAPE.
What Returns/Unopened.lean and Returns/UnopenedLinks.lean have at the segments 1 to 23, at the
output head's segment. Statements with their proofs: calls, sums and ONE CLOSED TEST BY LEAN's
KERNEL WITH ITS CONTROL.

  `h2_zero`, `head_step_zero` the output head's switch leaves what it lays itself opened at no list:
                    of its sub-protocol's yes; AT THE SEAT (the cuts 339 and 340)
  `commit_step_stays24` AT THE SEAT, over hearing sub-protocol number 4 or 6 of that segment:
                    `treesStay`
  `unopened_last` THE CORE, from the fold's return at 353: the count of oracle messages there is the
                    count at 339 and what the segment's three sendings add ⊢ `newZero` at the number
                    of trees at 339, of the book at 353
  `last_total`, `last_total_can_fail` THE CLOSED HALF, at the written shape: `n0At 25` is `n0At 24`
                    and what these three sendings add; a control: with one more it is false
  `fin_unopened_reached` THE TOP: at 353, behind the quiet front's yes, at `inFront P9 (finFrontOf t
                    a Q) t.book y rL cols`: every tree among `treesOf` that stands in the book has
                    `lists` = 0

By, this folder's: `yes_fresh` (Returns/SwitchFresh.lean) · `commit_stays`, `treesStay_same`,
`treesStay_trans` (Returns/TreesStay.lean) · `newZero_stays` (Returns/Unopened.lean) ·
`book_same_between`, `counts_rise` (Returns/BookSame.lean) · `counts_head`,
`members_behind_cleared`, `fresh_behind_cleared` (Returns/HeadSegment.lean) · `closed_behind_laid`
(Returns/ClosedReached.lean), `stated_of_close` (Returns/MembersReached.lean) · `mem_ids`,
`tree_of_opened` (Returns/OwnReached.lean) · `cut_kept` (Returns/CutsKept.lean) · `fin_book_reached`
(Returns/ArmsFree.lean), `finishFrontQ_rows` (Returns/ClosedArms.lean), `placeQ`
(Returns/PinReached.lean). The library's: `k7_sits`, `k7_sits_yes` (Johnson/IMR/FirstSeats.lean),
`k2_head_of`, `K2Is` (Johnson/IMR/K2Seat.lean), `yes_alone` (Johnson/IMR/SeatForm.lean),
`hear_at_flat` (Johnson/IMR/FlatIx.lean), `flatIx_scope` (Johnson/IMR/FlatScope.lean), `h1_fr`,
`hear_flat24`, `hear_commitQ24` (Johnson/IMR/FrameAll.lean) · `front_nums_head`
(Johnson/IMR/HeadFront.lean), `frontAt_of` (Johnson/Top/H0/Tw/K2C/HeldAtYes.lean) · `andThen_yes`,
`fold_next`, `fold_back` (Johnson/IMR/FoldTools.lean) · `link_inv`
(Johnson/Top/H0/Tw/K2C/Closed.lean), `headOpenQ_book` (Johnson/Top/H0/Tw/K2C/BookKept.lean),
`finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) · `open_fits`, `open_has`
(Johnson/IMR/WalkGivesAt.lean), `open_recAll` (Johnson/IMR/ListsEnds.lean), `rows_of_pub`
(Johnson/IMR/FrontPin.lean), `fin_link`, `front_len` (Johnson/IMR/FinPin.lean), `fold_cut`
(Johnson/IMR/GroupRest.lean) · `n0_at_head_paid`, `n0_at_finish_paid` (Johnson/IMR/ToldPaid.lean),
`plan_of` (Johnson/P1K2R/FoldSidePaid.lean), `n0At` (Johnson/Top/H0/K2Hears/PlaceNums.lean), `shW`
(Johnson/Top/H0/K2Hands/FrontsFull.lean) · `reach_raw`, `Reach.fold`
(Johnson/Top/H0/Walk/Reach.lean). `h2_zero`'s and `head_step_zero`'s walks are `h2_count`'s and
`entry_count_head`'s (Returns/HeadSegment.lean); `fin_unopened_reached`'s first lines are
`fin_own_reached`'s (Returns/OwnFinish.lean).

Limits. DEVICES: `decide +kernel` twice, under a raised recursion limit: the closed test and its
control. The control shows that the test can say no at one changed number, no more. THE FULL SIZE
ALONE. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. The quiet front's yes and `here` are premises. This file's
imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.UnopenedLinks
import Johnson.Desc.K2.Honest.Returns.OwnFinish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (finFrontOf finishFrontQ finishFrontQ_rest frontAt_of n0At)
open VerifiableInference.Desc.First.K2Hands (shW)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (open_fits open_has open_recAll rows_of_pub fin_link front_len fold_cut fold_next
  fold_back andThen_yes frontOf front_nums_head h1_fr hear_flat24 hear_commitQ24 msgsAt)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- The output head's switch leaves what it lays itself opened at no list. -/
theorem h2_zero {G₀ : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a)
    (hfit : BookFits s.book)
    (hin : ∀ o ∈ (singleRowsOracles a.fr.rows).toList, o < s.book.place.size) :
    newZero s.book.trees.size t.book := by
  rcases hx with ⟨-, hm⟩ | ⟨P', n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨w, a1, a2⟩ := andThen_yes (n := x.name) h
      have a1' : First.K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) s _ _ =
          .ok w := a1
      have a2' : First.K2.headOpenQ HP w = .ok t := a2
      intro j tr hj ht
      rw [(First.K2.headOpenQ_book a2').1] at ht
      refine yes_fresh a1' hfit (fun x' hF o ho => ?_) hj ht
      rcases hF with ⟨k, -⟩ | ⟨-, a', G, ha', -, rfl⟩ | ⟨k, -⟩
      · cases k
      · obtain rfl : a' = a := by
          have e' : VerifiableInference.Desc.First.Here.head a' = .head a := ha'.symm.trans ha
          cases e'
          rfl
        exact hin o ho
      · cases k
    · rw [e] at h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ :=
        First.K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl h
      rw [Lk.hHere] at ha
      cases ha

/-- **At the seat.** -/
theorem head_step_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₁ R₂ : List Fmt.RoundView} {C C₁ C₂ : List VerifiableInference.Desc.OpenedColumn}
    {t₁ t₂ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (339)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (340)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    newZero t₁.book.trees.size t₂.book := by
  have hlen : 339 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f₁
  obtain ⟨Lk, b0, eL, e0, J, -⟩ := IM.k7_sits hS hR O
  obtain ⟨Lk', b1, x, eL', e1, -, la, hx⟩ := IM.k2_head_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have q := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 0] at q
  have i1 : c.blocksInOrder[339]? = some b1 := by
    have q := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1] at q
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  obtain ⟨a, ha, -⟩ := h1_fr (IM.k7_sits_yes hS hR O J d0).1
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
  have d1' := ((IM.yes_alone la (by intro k; cases k) _ _ rs1 gs1).1 d1).1
  obtain ⟨G, hG, -⟩ := h2_count hx d1' ha
  have hrows : a.fr.rows = t₀.check.frame.rows :=
    (front_nums_head hS hR O f₀ f₁ (q := placeQ .head) rfl
      (frontAt_of (Or.inr (Or.inl ⟨rfl, a, G, ha, hG, rfl⟩)))).2.2.1
  obtain ⟨owed, f, S₀, es, rc, xc, hxc, hfc, hgc⟩ :=
    closed_behind_laid hS hR O (l := 23) (by omega) f₀
  have H := stated_of_close hxc hgc
  rw [← hfc, ← hrows] at H
  have up := counts_rise O (by omega : 338 ≤ 339) hlen f₀ f₁
  refine h2_zero hx d1' ha (open_fits O hlen f₁) fun o ho => ?_
  rw [open_has O hlen f₁]
  exact Nat.lt_of_lt_of_le (H o ho) up

/-- **At the seat: a later sending of the output head's segment.** -/
theorem commit_step_stays24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 4 ∨ j = 6) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (338 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (338 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q')) :
    treesStay (coreS s) (coreS s') := by
  obtain ⟨Lk, eL, -, hA⟩ := hear_flat24 hS hR O
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ24 hS hR O hj eL e d'
  exact treesStay_trans (commit_stays Q lk mo ar cm)
    (treesStay_same (coreS v) (coreS s') qv.1.2.2.1 qv.1.2.2.2)

/-- **The output head's segment's trees have been opened at no list at 353.** -/
theorem unopened_last (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ RE : List Fmt.RoundView} {C C₀ CE : List VerifiableInference.Desc.OpenedColumn}
    {t₀ s : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (339)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (s, RE, CE))
    (hc : s.st.oracles.size = t₀.st.oracles.size +
      (1 + (First.K2.targetAt Z.first.shape 24).kept.size + (msgsAt Z.first.shape 24 0 + 1)) +
      msgsAt Z.first.shape 24 1 + msgsAt Z.first.shape 24 2) :
    newZero t₀.book.trees.size s.book := by
  have hk : 353 ≤ (frontOf c).length := le_of_eq (front_len hS hR O).symm
  obtain ⟨t6, R6, C6, g6⟩ := fold_cut (k := 345) 8 f
  obtain ⟨t₅, R₅, C₅, g₅⟩ := fold_cut (k := 344) 1 g6
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 343) 1 g₅
  obtain ⟨t₃, R₃, C₃, g₃⟩ := fold_cut (k := 342) 1 g₄
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 340) 2 g₃
  obtain ⟨c1, c4, c6⟩ := counts_head hS hR O f₀ g₁ g₃ g₄ g₅ g6
  have u13 := counts_rise O (by omega : 340 ≤ 342) (by omega) g₁ g₃
  have u45 := counts_rise O (by omega : 343 ≤ 344) (by omega) g₄ g₅
  have u6s := counts_rise O (by omega : 345 ≤ 353) hk g6 f
  have e13 : t₃.book = t₁.book := book_same_between O (by omega) (by omega) g₁ g₃ (by omega)
  have e45 : t₅.book = t₄.book := book_same_between O (by omega) (by omega) g₄ g₅ (by omega)
  have e6s : s.book = t6.book := book_same_between O (by omega) hk g6 f (by omega)
  have z1 := head_step_zero hS hR O f₀ g₁
  have z3 : newZero t₀.book.trees.size t₃.book := by rw [e13]; exact z1
  have z4 : newZero t₀.book.trees.size t₄.book :=
    newZero_stays (a := coreS t₃) (b := coreS t₄) z3
      (commit_step_stays24 hS hR O (j := 4) (Or.inl rfl) g₃ g₄)
  have z5 : newZero t₀.book.trees.size t₅.book := by rw [e45]; exact z4
  have z6 : newZero t₀.book.trees.size t6.book :=
    newZero_stays (a := coreS t₅) (b := coreS t6) z5
      (commit_step_stays24 hS hR O (j := 6) (Or.inr rfl) g₅ g6)
  rw [e6s]
  exact z6

/-! ## The closed half -/

set_option maxRecDepth 1000000 in
/-- **At the written shape: what the output head's segment's three sendings add.** -/
theorem last_total : n0At 25 = n0At 24 +
      (1 + (First.K2.targetAt shW 24).kept.size + (msgsAt shW 24 0 + 1)) +
      msgsAt shW 24 1 + msgsAt shW 24 2 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one message more the equation is false. -/
theorem last_total_can_fail : n0At 25 ≠ n0At 24 +
      (1 + (First.K2.targetAt shW 24).kept.size + (msgsAt shW 24 0 + 1)) +
      msgsAt shW 24 1 + msgsAt shW 24 2 + 1 := by
  decide +kernel

/-! ## At a reached state -/

/-- **Behind the last segment.** -/
theorem fin_unopened_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hq : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup)
    (P9 : Par9) (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    ∀ τ ∈ treesOf (inFront P9 (finFrontOf t a Q) t.book y rL cols), ∀ tree,
      t.book.trees[τ]? = some tree → tree.lists = 0 := by
  have hlen : 353 ≤ (frontOf c).length := le_of_eq (front_len hS hR O).symm
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  have eb : t.book = s.book := (finishFrontQ_rest hq).1
  obtain ⟨a', ha', hrows⟩ := finishFrontQ_rows hq
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  have hp : ∀ k, ∀ b ∈ c.blocksInOrder.take k, b.planOk = true :=
    fun k b hb => P1K2.plan_of O hpl b (List.mem_of_mem_take hb)
  intro τ hτ tree ht
  obtain ⟨o, ho, e⟩ := tree_of_opened hτ
  have hlt := (fin_book_reached hS hR O hr hq here Q P9 y rL cols).1 o ho
  have hlt' : o < t.book.place.size := hlt
  have po : t.book.place[o]? = some (τ, (t.book.place.getD o (0, 0)).2) := by
    have e' : (t.book.place.getD o (0, 0)).1 = τ := e
    rw [← e', Array.getElem?_eq_getElem hlt']
    simp [Array.getD, hlt']
  rw [eb] at po ht
  have ho' : o ∈ (singleRowsOracles s.check.frame.rows).toList := by
    rw [← hrows]
    exact ho
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, hmem⟩ :=
    members_behind_cleared hS hR O f₂
  have hfresh := fresh_behind_cleared hS hR O g₀ f₂
  have hmasks : s.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega) hlen f₂).walk
      (by rw [fin_link hS hR O f₂]; omega)).2.2
  have hids : singleRowsOracles s.check.frame.rows =
      s.check.frame.rows.layout.members.push s.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, hfresh, mem_ids] at ho'
  have u3 := counts_rise O (by omega : 339 ≤ 342) (by omega) g₀ g₃
  have u5 := counts_rise O (by omega : 339 ≤ 344) (by omega) g₀ g₅
  have hge : t₀.st.oracles.size ≤ o := by
    rcases ho' with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ <;> omega
  have K₀ := cut_kept O (by omega : 339 ≤ 353) hlen g₀ f₂
  rw [open_has O (by omega) g₀] at K₀
  have hτ' : t₀.book.trees.size ≤ τ := by
    have k := K₀.2.2 o τ _ po
    rcases Nat.lt_or_ge τ t₀.book.trees.size with lt | ge
    · have lo : o < t₀.st.oracles.size := k.2 lt
      omega
    · exact ge
  refine unopened_last hS hR O g₀ f₂ ?_ τ tree hτ' ht
  rw [hsh, Meaning.Carry.n0_at_head_paid hS hR O hcut (hp _) z rs cl (t₀, R₀, C₀) g₀,
    ← last_total]
  exact Meaning.Carry.n0_at_finish_paid hS hR O hcut (hp _) z rs cl (s, [], []) f₂

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.h2_zero
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_step_zero
#print axioms VerifiableInference.Desc.K2.Honest.Returns.commit_step_stays24
#print axioms VerifiableInference.Desc.K2.Honest.Returns.unopened_last
#print axioms VerifiableInference.Desc.K2.Honest.Returns.last_total
#print axioms VerifiableInference.Desc.K2.Honest.Returns.last_total_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_unopened_reached
