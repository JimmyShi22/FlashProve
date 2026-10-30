-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FiveReached.lean: FIVE OF THE SEVEN THINGS A TREE THAT THE CODE
SWITCH's READING ASKS, AT A REACHED STATE, AT ALL 25 OF THE KIND's PLACES: the trees of the opened
messages, in rising order, and the plan's list of read trees `n.read` run pair by pair: the tree is
in the book · its depth is at most the old main code's · its number, depth and width are the entry's
(`AllFive`, Returns/FiveTest.lean). In the goals' scope, UNDER SIX PREMISES THAT THE HEADS
`P5J.AtMg` | `P5J.AtMgA` PAY: the plan's own test · the written cut · the written shape · the row on
the made plan · the test on the sendings · the laid list is the written one. Four definitions;
statements with their proofs: calls and ONE CLOSED TEST BY LEAN's KERNEL WITH ITS CONTROL.

  `idsWAt l`, `readWAt link`, `logW`, `fiveAtB l link` at the written values: the numbers of the
                    messages that the switch into group l opens · the plan's list of read trees at a
                    place's link · the old main code's depth · `treesFiveB` at these and the written
                    laid list `LFull`
  `five_at` at a state whose book carries `LFull`'s seats, numbers its trees in order and fits: the
                    opened messages are idsW's members · the test's yes ⊢ `AllFive`
  `seats_reached`, `read_written`, `logW_of` the book carries `LFull`'s seats at a switch's number ·
                    `n.read` is `readWAt`'s value · the depth
  `five_full`, `five_can_fail`, `five_link`, `five_spent` THE CLOSED HALF: the test says yes at l =
                    1 … 24 (link l) and at 25 (no link); a control: at group 2's messages against
                    group 3's list it says no, and that list is there; the yes at one l; the yes at
                    the plan's own list
  `link_five_reached`, `head_five_reached`, `fin_five_reached` THE TOPS: every m < 23 | 339 | 353
                    behind the quiet front's yes: `AllFive 0 logW` of the book, `treesOf` of the
                    reading's input and `n.read`

By, this folder's: `allFive_of`, `trees_written`, `place_written` (Returns/FiveTest.lean) ·
`opened_range`, `opened_range_first`, `opened_range_last` (Returns/OpenedRange.lean) · `seg_total`
(Returns/UnopenedLinks.lean), `first_total` (Returns/UnopenedFirst.lean), `last_total`
(Returns/UnopenedFinish.lean) · `finishFrontQ_rows` (Returns/ClosedArms.lean), `placeQ`
(Returns/PinReached.lean). The library's: `seatsCarried_field` (Johnson/IMR/SeatsField.lean),
`noMark_switch`, `IsSwitchNo` (Johnson/P1K2R/BookTight.lean) · `prep_pinned`, `prepW`
(Johnson/IMR/SendsPinned.lean), `Open.blank` (Johnson/IMR/SeatOpen.lean) · `LFull`
(Johnson/HB/LLHARD/LaidWritten.lean), `csW`, `shW` (Johnson/Top/H0/K2Hands/FrontsFull.lean), `n0At`
(Johnson/Top/H0/K2Hears/PlaceNums.lean) · `bookInOrder_reached`, `bookFits_reached`,
`bookHas_reached` (Johnson/IMR/AtReach.lean), `placed_of_fits` (Johnson/Desc/Book/BookFits.lean) ·
`n0_at_link_paid`, `n0_at_head_paid`, `n0_at_finish_paid` (Johnson/IMR/ToldPaid.lean), `plan_of`
(Johnson/P1K2R/FoldSidePaid.lean) · `front_nums_head` (Johnson/IMR/HeadFront.lean), `frontAt_of`
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean), `finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) ·
`listOfT_eq` (OnBytes/Chain/Draws.lean), `listOf_mem` (Fmt/Rules6Laws.lean) · `fold_back`
(Johnson/IMR/FoldTools.lean), `front_len` (Johnson/IMR/FinPin.lean) · `reach_raw`, `Reach.fold`
(Johnson/Top/H0/Walk/Reach.lean). NEAR RELATIVES, NOT CALLED: under the head `P5J.AtMgA` the field
`seatsCarried` (Johnson/Desc/First/FoldFacts.lean) of `AtMgA.fold_full`
(Johnson/P5J/MaskLettersAtMg.lean) has `seats_reached`'s end at every reached state without a mark ·
`prepFull`, `nums_answer` (Johnson/Top/H0/Tw/K2C/Members/DebtsAtFull.lean): the written numbers'
ground under another name, with a closed fact on the groups' numbers.

Limits. DEVICES: `decide +kernel` twice, under a raised recursion limit: the closed test and its
control. The control shows that the test can say no at one wrong pairing, no more. THE FULL SIZE
ALONE. Nothing on the two other things a tree (`leafOk`; "not opened": Returns/UnopenedLinks.lean
and its two sisters). "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN
FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. At the two arms `here`, the group's look-up
and the quiet front's yes are premises. This file's imports are heavy. Nothing on any property.




-/
import Johnson.Desc.K2.Honest.Returns.FiveTest
import Johnson.Desc.K2.Honest.Returns.OpenedRange
import Johnson.Desc.K2.Honest.Returns.UnopenedFirst
import Johnson.Desc.K2.Honest.Returns.UnopenedFinish
import Johnson.IMR.SendsPinned
import Johnson.IMR.SeatsField
import Johnson.P1K2R.BookTight
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf finFrontOf finishFrontQ finishFrontQ_rest
  frontAt_of n0At)
open VerifiableInference.Desc.First.K2Hands (shW csW)
open VerifiableInference.Desc.Book (BookFits NumberedC placed_of_fits)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB atFirstSeats snAt sendsAreB laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull madeRow)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (bookInOrder_reached bookFits_reached bookHas_reached front_len fold_back frontOf
  front_nums_head msgsAt)
open P1K2 (Prep Nums prepOf numsAt)
open _root_.Tw.K2 (Par9 Sent Col SwIn)
open ProofFile (Cl)

/-! ## At the written values -/

/-- The numbers of the messages that the switch into group l opens. -/
def idsWAt (l : Nat) : List Nat :=
  if l = 1 then
    List.range (msgsAt shW 0 0 + 1) ++
      List.range' (msgsAt shW 0 0 + 1 + shW.atStart.length) (msgsAt shW 0 1 + msgsAt shW 0 2)
  else List.range' (n0At (l - 1)) (n0At l - n0At (l - 1))

/-- The plan's list of read trees at a place's link. -/
def readWAt (link : Option Nat) : Option (List (Nat × Nat × Nat)) :=
  (IM.prepW.bind fun Pw => numsAt Pw link).map (·.read)

/-- The old main code's depth. -/
def logW : Nat := ((csW.base[shW.code]?).map (·.logN)).getD 0

/-- The test at group l and a place's link. -/
def fiveAtB (l : Nat) (link : Option Nat) : Bool :=
  match readWAt link with
  | some rd =>
    treesFiveB LFull logW (listOfT ((idsWAt l).map fun o => (LFull.places.getD o (0, 0)).1)) rd
  | none => false

/-! ## At a state -/

/-- **From the test's yes, at a state whose book carries the written seats.** -/
theorem five_at {s : S} {i : SwIn} (hb : i.book = s.book) (hSe : atFirstSeats LFull s = true)
    (hN : NumberedC 0 (coreS s)) (hfit : BookFits s.book) {idsW : List Nat}
    (hm : ∀ o, o ∈ (idsOf i).toList ↔ o ∈ idsW) (hlt : ∀ o ∈ idsW, o < s.book.place.size)
    {logN : Nat} {rd : List (Nat × Nat × Nat)}
    (hT : treesFiveB LFull logN
      (listOfT (idsW.map fun o => (LFull.places.getD o (0, 0)).1)) rd = true) :
    AllFive 0 logN s.book (treesOf i) rd := by
  have hSe' : seatsCarriedB LFull s.book = true := hSe
  have e : treesOf i = listOfT (idsW.map fun o => (LFull.places.getD o (0, 0)).1) := by
    unfold treesOf placesOf
    rw [hb]
    have e1 : (((idsOf i).map fun o => s.book.place.getD o (0, 0)).map (·.1)).toList =
        (idsOf i).toList.map fun o => (s.book.place.getD o (0, 0)).1 := by simp
    rw [e1]
    exact trees_written hSe' hm hlt
  rw [e]
  refine allFive_of hSe' (fun j t h => (hN.2 j t h).1) logN _ rd (fun t ht => ?_) hT
  rw [listOfT_eq, Fmt.listOf_mem, List.mem_map] at ht
  obtain ⟨o, ho, rfl⟩ := ht
  have lt := hlt o ho
  rw [← place_written hSe' lt]
  have h1 : s.book.place[o]? = some s.book.place[o] := Array.getElem?_eq_getElem lt
  rw [Array.getD_eq_getD_getElem?, h1]
  exact placed_of_fits hfit o _ h1

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- The book carries the written seats at a switch's number. -/
theorem seats_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some LFull) {k : Nat}
    (hk : P1K2.IsSwitchNo k) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) : atFirstSeats LFull s = true :=
  IM.seatsCarried_field hS hR O
    (fun k (x : ProofFile.InstPub × S) => Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x) id
    (fun k a h => by
      obtain ⟨-, rs, cols, f⟩ := (reach_raw h).fold
      exact ⟨rs, cols, [], [], f⟩) hpl hB hLd k (z, s) hr (P1K2.noMark_switch hS hR O hk hr)

/-- The plan's list of read trees is the written one. -/
theorem read_written (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hy : madeRow Z = true) {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    {link : Option Nat} (hn : numsAt Pp link = some n) : readWAt link = some n.read := by
  unfold readWAt
  rw [← IM.prep_pinned O.pub hy O.blank, hP]
  simp only [Option.bind_some, hn, Option.map_some]

theorem logW_of {c₀ : Code} (h : csW.base[shW.code]? = some c₀) : c₀.logN = logW := by
  unfold logW
  rw [h]
  rfl

/-! ## The closed half -/

set_option maxRecDepth 1000000 in
/-- **At the written values the test says yes at all 25 places.** -/
theorem five_full :
    (((List.range' 1 24).all fun l => fiveAtB l (some l)) && fiveAtB 25 none) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: group 2's messages against group 3's list. -/
theorem five_can_fail : fiveAtB 2 (some 3) = false ∧ (readWAt (some 3)).isSome = true := by
  decide +kernel

theorem five_link {l : Nat} (h1 : 1 ≤ l) (h24 : l ≤ 24) : fiveAtB l (some l) = true := by
  have h := five_full
  rw [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1 l (by rw [List.mem_range'_1]; omega)

/-- The test's yes, at the plan's own list. -/
theorem five_spent {l : Nat} {link : Option Nat} {rd : List (Nat × Nat × Nat)}
    (h : fiveAtB l link = true) (hrd : readWAt link = some rd) :
    treesFiveB LFull logW
      (listOfT ((idsWAt l).map fun o => (LFull.places.getD o (0, 0)).1)) rd = true := by
  unfold fiveAtB at h
  rw [hrd] at h
  exact h

/-! ## At a reached state -/

/-- **At every switch into a later group.** -/
theorem link_five_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    (hy : madeRow Z = true) (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some LFull)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    AllFive 0 logW s.book (treesOf (inFront P9 (frontAt s L Q) s.book y rL cols)) n.read := by
  have hlen : 14 * (m + 1) + 2 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  have hp : ∀ k, ∀ b ∈ c.blocksInOrder.take k, b.planOk = true :=
    fun k b hb => P1K2.plan_of O hpl b (List.mem_of_mem_take hb)
  have hcnt : s.st.oracles.size = n0At (m + 1) :=
    Meaning.Carry.n0_at_link_paid hS hR O hcut (by omega) (by omega) (hp _) z rs cl (s, [], []) f₂
  have hhas := bookHas_reached O (reach_raw hr) hlen
  refine five_at (i := (inFront P9 (frontAt s L Q) s.book y rL cols)) rfl
    (seats_reached hS hR O hpl hB hLd (Or.inl ⟨m, h23, rfl⟩) hr)
    (bookInOrder_reached O (reach_raw hr) hlen) (bookFits_reached O (reach_raw hr) hlen)
    (idsW := idsWAt (m + 1)) (fun o => ?_) (fun o ho => ?_)
    (five_spent (five_link (by omega) (by omega)) (read_written O hy hP hn))
  · show o ∈ (singleRowsOracles s.check.frame.rows).toList ↔ _
    rcases Nat.eq_zero_or_pos m with rfl | h1
    · rw [opened_range_first hS hR O f₂ (by rw [hsh, ← first_total]; exact hcnt), hsh, hcnt]
      have ft := first_total
      have e01 : n0At (0 + 1) = n0At 1 := rfl
      simp only [idsWAt, if_true, List.mem_append, List.mem_range, List.mem_range'_1]
      omega
    · obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
      have f : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 8 + 8)) (ProofFile.startS Z z) rs cl =
          .ok (s, [], []) := by
        rw [show 14 * (l + 1) + 8 + 8 = 14 * (l + 1 + 1) + 2 by omega]
        exact f₂
      have st := seg_total (k := l + 1) (by omega) (by omega)
      rw [opened_range hS hR O (by omega : l + 1 < 24) (n₀ := n0At (l + 1)) (Nat.le_refl 8)
        (by omega) f₂ f (fun t R' C' g => Meaning.Carry.n0_at_link_paid hS hR O hcut (by omega)
          (by omega) (hp _) z rs cl (t, R', C') g) (by rw [hsh, ← st]; exact hcnt), hcnt]
      have hne : ¬ (l + 1 + 1 = 1) := by omega
      simp only [idsWAt, if_neg hne, List.mem_range'_1, Nat.add_sub_cancel]
      omega
  · rw [hhas, hcnt]
    rcases Nat.eq_zero_or_pos m with rfl | h1
    · have ft := first_total
      have e01 : n0At (0 + 1) = n0At 1 := rfl
      simp only [idsWAt, if_true, List.mem_append, List.mem_range, List.mem_range'_1] at ho
      omega
    · have hne : ¬ (m + 1 = 1) := by omega
      simp only [idsWAt, if_neg hne, List.mem_range'_1, Nat.add_sub_cancel] at ho
      omega

/-- **At the output head's switch.** -/
theorem head_five_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    (hy : madeRow Z = true) (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some LFull)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) {G : ReqGroup}
    (group : s.check.frame.groups[s.check.frame.link]? = some G) (T : SwitchTarget) (P9 : Par9)
    (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    AllFive 0 logW s.book (treesOf (inFront P9 (headFrontOf s a T) s.book y rL cols)) n.read := by
  have hlen : 339 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨-, rs, cl, f⟩ := (reach_raw hr).fold
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f
  have hrows : a.fr.rows = tm.check.frame.rows :=
    (front_nums_head hS hR O fm f (q := placeQ .head) rfl
      (frontAt_of (Or.inr (Or.inl ⟨rfl, a, G, here, group, rfl⟩)))).2.2.1
  have hp : ∀ k, ∀ b ∈ c.blocksInOrder.take k, b.planOk = true :=
    fun k b hb => P1K2.plan_of O hpl b (List.mem_of_mem_take hb)
  have hcnt : s.st.oracles.size = n0At 24 :=
    Meaning.Carry.n0_at_head_paid hS hR O hcut (hp _) z rs cl (s, [], []) f
  have hhas := bookHas_reached O (reach_raw hr) hlen
  have st := seg_total (k := 23) (by omega) (by omega)
  have hne : ¬ (24 = 1) := by omega
  have e23 : n0At (24 - 1) = n0At 23 := rfl
  refine five_at (i := (inFront P9 (headFrontOf s a T) s.book y rL cols)) rfl
    (seats_reached hS hR O hpl hB hLd (Or.inr (Or.inl rfl)) hr)
    (bookInOrder_reached O (reach_raw hr) hlen) (bookFits_reached O (reach_raw hr) hlen)
    (idsW := idsWAt 24) (fun o => ?_) (fun o ho => ?_)
    (five_spent (five_link (by omega) (by omega)) (read_written O hy hP hn))
  · show o ∈ (singleRowsOracles a.fr.rows).toList ↔ _
    rw [hrows, opened_range hS hR O (l := 22) (by omega) (n₀ := n0At 23) (d := 9) (by omega)
      (by omega) fm f (fun t R' C' g => Meaning.Carry.n0_at_link_paid hS hR O hcut (l := 23)
        (by omega) (by omega) (hp _) z rs cl (t, R', C') g) (by rw [hsh, ← st]; exact hcnt), hcnt]
    simp only [idsWAt, if_neg hne, List.mem_range'_1]
    omega
  · rw [hhas, hcnt]
    simp only [idsWAt, if_neg hne, List.mem_range'_1] at ho
    omega

/-- **Behind the last segment.** -/
theorem fin_five_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : F.planOk = true) (hcut : cutOf c.blocksInOrder = cutFirstFull) (hsh : Z.first.shape = shW)
    (hy : madeRow Z = true) (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some LFull)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hq : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup)
    (P9 : Par9) (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    AllFive 0 logW t.book (treesOf (inFront P9 (finFrontOf t a Q) t.book y rL cols)) n.read := by
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
  have hcnt : s.st.oracles.size = n0At 25 :=
    Meaning.Carry.n0_at_finish_paid hS hR O hcut (hp _) z rs cl (s, [], []) f₂
  have hhas := bookHas_reached O (reach_raw hr) hlen
  have lt := last_total
  have hne : ¬ (25 = 1) := by omega
  have e24 : n0At (25 - 1) = n0At 24 := rfl
  have h5 : fiveAtB 25 none = true := by
    have h := five_full
    rw [Bool.and_eq_true] at h
    exact h.2
  have key : AllFive 0 logW s.book
      (treesOf (inFront P9 (finFrontOf t a' Q) t.book y rL cols)) n.read := by
    refine five_at (i := (inFront P9 (finFrontOf t a' Q) t.book y rL cols)) eb
      (seats_reached hS hR O hpl hB hLd (Or.inr (Or.inr rfl)) hr)
      (bookInOrder_reached O (reach_raw hr) hlen) (bookFits_reached O (reach_raw hr) hlen)
      (idsW := idsWAt 25) (fun o => ?_) (fun o ho => ?_)
      (five_spent h5 (read_written O hy hP hn))
    · show o ∈ (singleRowsOracles a'.fr.rows).toList ↔ _
      rw [hrows, opened_range_last hS hR O (n₀ := n0At 24) f₂
        (fun t R' C' g => Meaning.Carry.n0_at_head_paid hS hR O hcut (hp _) z rs cl (t, R', C') g)
        (by rw [hsh, ← lt]; exact hcnt), hcnt]
      simp only [idsWAt, if_neg hne, List.mem_range'_1]
      omega
    · rw [hhas, hcnt]
      simp only [idsWAt, if_neg hne, List.mem_range'_1] at ho
      omega
  rw [← eb] at key
  exact key

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.five_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.seats_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.read_written
#print axioms VerifiableInference.Desc.K2.Honest.Returns.logW_of
#print axioms VerifiableInference.Desc.K2.Honest.Returns.five_full
#print axioms VerifiableInference.Desc.K2.Honest.Returns.five_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.five_link
#print axioms VerifiableInference.Desc.K2.Honest.Returns.five_spent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_five_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_five_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_five_reached
