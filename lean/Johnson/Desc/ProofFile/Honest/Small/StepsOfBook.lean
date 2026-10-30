-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/StepsOfBook.lean: CONDITIONAL but for `stretchesBy_length`,
`planParts_length` and `segmentWants_part`. Statements with their proofs; no definition. No kind is
named in the code. By the writers of the feed-forward layers' own rounds (sub-protocol K4). It
stands over Honest/BookPlain.lean and Honest/BookRowStretch.lean, of other writers, and
Honest/Small/SpentOfWants.lean.

What is here. TWO OF THE TESTS THAT `chainSteps` (Honest/Frame.lean) MAKES AT A SUB-PROTOCOL WITH A
PROVER's SIDE, AT THE WHOLE BOOK OF COINS (`bookWhole`, Honest/BookWhole.lean): that the book has
no row, and no entry, for a part that the side does not have. They are shown at a sub-protocol of
the first chain that holds no round "SEND seed" and no round "FOLD epsilon". No row of the first
table stands at its place at all: `plain_no_row` (Honest/BookPlain.lean) states the count 0 there,
which a row of the count 0 would meet too; here the stronger sentence is stated, by that file's own
helpers (`bookRaw_first`, `spendingBook_first`, `rowsIn_seed`, `switchRows_seed`, `seed_named`,
`round_not_here`). An entry whose spender stands at its place is a spending one: that is
`plain_all_spent` (Honest/BookPlain.lean), called here; and by `pick_whole`
(Honest/BookRowStretch.lean) it is one of the maker's stretches for a segment or for a sumcheck
outside one; these name as spenders parts of `planParts` of members of the first chain, which are
numbered from 0.

  `stretchesBy_length`, `planParts_length`   no hypothesis: a sub-protocol has as many parts as its
      cut has members.
  `segmentWants_part`, `linksWants_part`   whose parts the segments' stretches name as their
      spenders, by `BookRow.partsWants_spender`; for the sumchecks outside a segment:
      `BookRow.loneWants_spender` (both Honest/BookRowKit.lean), called here.
  `bookWhole_no_row_at`   **no row of the first table stands at the place.** hF is not asked.
  `bookWhole_spender_at`   **an entry whose spender stands at the place is a spending entry of one
      of the sub-protocol's parts.** Its first half is `plain_all_spent`; the second is shown here.
  `bookWhole_tests_at`   **THE TWO TESTS, IN `chainSteps`' OWN WORDS**, at every number n from the
      cut's length on.

Called besides: `BookRow.planParts_place` (Honest/BookRowKit.lean), `planParts_addr`
(Honest/Small/SpentOfWants.lean), `orderOf_nodup` (Honest/Law/Rule/Tests.lean), `checked_ok`
(Honest/BookSharedLaw.lean), `ex_bindE`, `ex_mapE` (Honest/BookSharedKit.lean).

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES; that the description passes its test on
places. THAT ANY SUB-PROTOCOL OF THE PROTOCOL HOLDS NO SUCH ROUND: hS and hF are premises. Nothing
at a sub-protocol that holds a sending; at one that holds a fold and no sending,
`bookWhole_no_row_at` alone. The first chain alone. That a prover's side has as many parts as the
cut has members: that is the test on the cut, each kind's own. The other tests of `chainSteps`;
that `chainSteps` returns. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookPlain
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.Desc.ProofFile.Honest.Small.SpentOfWants

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi S Cl : Type}

/-! ## 1 As many parts as the cut has members -/

/-- No hypothesis. -/
theorem stretchesBy_length {α : Type} : ∀ (ks : List Nat) (l : List α),
    (stretchesBy l ks).length = ks.length
  | [], _ => rfl
  | k :: ks, l => by
    show (l.take k :: stretchesBy (l.drop k) ks).length = (k :: ks).length
    rw [List.length_cons, List.length_cons, stretchesBy_length ks]

/-- No hypothesis. **A sub-protocol has as many parts as its cut has members.** -/
theorem planParts_length (b : Block S Cl) : (planParts b).length = (partsCut b).length := by
  unfold planParts
  rw [List.length_map, List.length_zipIdx, stretchesBy_length]

/-! ## 2 Whose parts the maker's stretches name -/

/-- A segment's stretches name parts of members of the list. -/
theorem segmentWants_part (bs : List (Block S Cl)) (l : Nat) (row idx : MsgAt)
    (merges : List Addr) (t : Nat) :
    ∀ w ∈ (segmentWants bs l row idx merges t).1, ∃ x ∈ bs, ∃ q ∈ planParts x,
      w.spender = q.addr := by
  intro w hw
  obtain ⟨q, hq, e⟩ := BookRow.partsWants_spender row idx merges _ 0 t w hw
  obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
  exact ⟨x, (List.mem_filter.1 hx).1, q, hq2, e⟩

/-- So do all segments'. -/
theorem linksWants_part {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok r →
      ∀ w ∈ r.1, ∃ x ∈ bs, ∃ q ∈ planParts x, w.spender = q.addr
  | [], t, r, h, w, hw => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l' :: ls, t, r, h, w, hw => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e] at hw
      rcases List.mem_append.1 hw with h1 | h1
      · exact segmentWants_part bs l' row idx merges t w h1
      · exact linksWants_part ls _ y hy w h1

/-! ## 3 The statements -/

/-- CONDITIONAL on h, hp, hb and hS. **NO ROW OF THE FIRST TABLE STANDS AT THE PLACE OF A
SUB-PROTOCOL OF THE FIRST CHAIN THAT HOLDS NO "SEND seed".** -/
theorem bookWhole_no_row_at {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder)
    (hS : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed") :
    ∀ r ∈ B.rowsOf 0, r.1.place ≠ b.place := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, r0, hB, hr0, eF⟩ := BookPlain.bookRaw_first hW
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  intro y hy hpl
  have hy' : y ∈ B₀.first ++ r0 := by
    rw [← eF]
    exact hy
  have hold : ∃ j ∈ seedRounds F.first.blocksInOrder, addrOfRound F.first.blocksInOrder j = some y.1 := by
    rcases List.mem_append.1 hy' with h1 | h1
    · exact BookPlain.rowsIn_seed (BookPlain.spendingBook_first hB) y h1
    · exact BookPlain.switchRows_seed hr0 y h1
  obtain ⟨j, hj, ha⟩ := hold
  obtain ⟨r, hr, hnm⟩ := BookPlain.seed_named hj
  exact BookPlain.round_not_here hn hb hS ha hr hnm hpl

/-- CONDITIONAL on h, hp, hb, hS and hF. **AN ENTRY OF THE WHOLE BOOK WHOSE SPENDER STANDS AT THE
PLACE IS A SPENDING ENTRY OF ONE OF THE SUB-PROTOCOL's PARTS.** -/
theorem bookWhole_spender_at {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder)
    (hS : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed")
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∀ e ∈ B.ahead, e.spender.place = b.place →
      e.once = true ∧ e.spender.part < (planParts b).length := by
  obtain ⟨idx, a, -, ha, -, hpick⟩ := pick_whole h hp hb hF
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  intro e he hpl
  have hs : e.spender = ⟨b.place, e.spender.part⟩ := by
    rw [← hpl]
  have ho : e.once = true := plain_all_spent h hp hb hS hF e he hpl
  refine ⟨ho, ?_⟩
  have hm : e ∈ BookRow.pick ⟨b.place, e.spender.part⟩ B.ahead :=
    List.mem_filter.2 ⟨List.mem_filter.2 ⟨he, beq_iff_eq.2 hs⟩, ho⟩
  rw [hpick] at hm
  obtain ⟨w, hw, ew⟩ := List.mem_map.1 hm
  obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
  have hws : w.spender = ⟨b.place, e.spender.part⟩ := beq_iff_eq.1 hw2
  have hpart : ∃ x ∈ F.first.blocksInOrder, ∃ q ∈ planParts x, w.spender = q.addr := by
    rcases List.mem_append.1 hw1 with h1 | h1
    · exact linksWants_part _ _ a ha w h1
    · obtain ⟨q, hq, eq⟩ := BookRow.loneWants_spender _ _ _ _ w h1
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      exact ⟨x, (List.mem_filter.1 hx).1, q, hq2, eq⟩
  obtain ⟨x, hx, q, hq, eq⟩ := hpart
  have hxp : x.place = b.place := by
    have e1 := planParts_place hq
    rw [← eq, hws] at e1
    exact e1.symm
  have ex : x = b := List.inj_on_of_nodup_map hn hx hb hxp
  rw [ex] at hq
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hq
  have ea := planParts_addr b i q hi
  have hlt : i < (planParts b).length := (List.getElem?_eq_some_iff.1 hi).1
  have e2 : (⟨b.place, e.spender.part⟩ : Addr) = ⟨b.place, i⟩ := hws.symm.trans (eq.trans ea)
  have e3 : e.spender.part = i := congrArg Addr.part e2
  rw [e3]
  exact hlt

/-- CONDITIONAL on h, hp, hb, hS, hF and hn. **THE TWO TESTS OF `chainSteps` ON ROWS AND ENTRIES
BEYOND THE PARTS, IN ITS OWN WORDS**, at every number n from the cut's length on: neither finds
anything. -/
theorem bookWhole_tests_at {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder)
    (hS : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed")
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") {n : Nat}
    (hn : (partsCut b).length ≤ n) :
    (B.rowsOf 0).any (fun r => r.1.place == b.place && decide (n ≤ r.1.part)) = false ∧
      B.ahead.any (fun e => e.spender.place == b.place && decide (n ≤ e.spender.part)) =
        false := by
  constructor
  · refine List.any_eq_false.2 fun r hr hh => ?_
    rw [Bool.and_eq_true] at hh
    exact bookWhole_no_row_at h hp hb hS r hr (beq_iff_eq.1 hh.1)
  · refine List.any_eq_false.2 fun e he hh => ?_
    rw [Bool.and_eq_true] at hh
    have h1 := (bookWhole_spender_at h hp hb hS hF e he (beq_iff_eq.1 hh.1)).2
    have h2 : n ≤ e.spender.part := of_decide_eq_true hh.2
    rw [planParts_length] at h1
    omega

end ProofFile.Honest

#print axioms ProofFile.Honest.stretchesBy_length
#print axioms ProofFile.Honest.planParts_length
#print axioms ProofFile.Honest.segmentWants_part
#print axioms ProofFile.Honest.linksWants_part
#print axioms ProofFile.Honest.bookWhole_no_row_at
#print axioms ProofFile.Honest.bookWhole_spender_at
#print axioms ProofFile.Honest.bookWhole_tests_at
