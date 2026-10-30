-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/CutOfBook.lean: CONDITIONAL. Statements with their proofs; no
definition. NO KIND IS NAMED. By the writers of the feed-forward layers' own rounds (sub-protocol
K4). It stands over Honest/BookRowKit.lean and what that file imports.

What is here. IN THE WHOLE BOOK OF COINS (`bookWhole`, Honest/BookWhole.lean) THE CUT THAT STANDS
AT A SUB-PROTOCOL's PLACE IS THAT SUB-PROTOCOL's OWN CUT (`partsCut`, Honest/BookOf.lean), at each
sub-protocol of the three lists that has a round. It is the left side of the second test that
`chainSteps` (Honest/Frame.lean) makes at a sub-protocol with a prover's side. The book's field
cuts is the maker's list `cutsOf`: `spendingBook` (Honest/BookAll.lean) lays it, and neither
`bookRaw` nor the book's own tests turn it. That list is the three chains' lists in a row, and a
lookup takes the first row at a place: under the library's test on places (`FileDescription.placesOk`,
Johnson/Desc/Block.lean) no two sub-protocols of a list stand at one place, and a place's chain
number tells the three lists apart.

  `bookWhole_cut_first`, `bookWhole_cut_shared`, `bookWhole_cut_second`   **THE STATEMENT**, once
      for each of the three lists: their states' types differ.
  `bookWhole_cuts`   the whole book's field cuts is `cutsOf`; `spendingBook_cuts`, `bookRaw_cuts`
      beneath it.
  `cutsIn_cons`, `cutsIn_lookup`, `cutsIn_lookup_none`   one list: at a member's place; at no
      member's place.
  `cutsIn_lookup_roundless`, `bookWhole_cut_first_roundless`   **THE TOOTH FOR THE PREMISE hr**: at
      a member that has no round the list, and the whole book, have no cut: so the statement without
      hr would be false at every such member. In the whole book it is shown for the first chain.
  `lookup_append_some`, `lookup_append_none`   a lookup in two lists in a row.

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES; that the description passes its test on
places. THAT `partsCut b` IS WHAT ANY PROVER's SIDE's PARTS HAVE AS THEIR NUMBERS OF MOVES: the
right side of that test is each kind's own. THAT ANY DESCRIPTION HAS A SUB-PROTOCOL WITHOUT A
ROUND: the tooth is a law on such members, no example of one. Nothing on the other tests of
`chainSteps`. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi S Cl : Type}

/-! ## 1 The book's field -/

theorem spendingBook_cuts {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) : B₀.cuts = cutsOf F := by
  unfold spendingBook at h
  obtain ⟨r0, -, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  rcases hidx : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
      "link 0, moment 0" isIndexMaskMsg with _ | idx
  · rw [hidx] at h
    obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  rw [hidx] at h
  obtain ⟨idx', -, h⟩ := ex_bind h
  obtain ⟨a, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨f0, -, h⟩ := ex_bind h
  obtain ⟨f1, -, h⟩ := ex_bind h
  obtain ⟨f2, -, h⟩ := ex_bind h
  have e := Except.ok.inj h
  subst e
  rfl

theorem bookRaw_cuts {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (h : bookRaw F p0 p1 p2 M = .ok W) : W.cuts = cutsOf F := by
  unfold bookRaw at h
  obtain ⟨B₀, hB, h⟩ := ex_bind h
  obtain ⟨m0, -, h⟩ := ex_bind h
  obtain ⟨m1, -, h⟩ := ex_bind h
  obtain ⟨r0, -, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨seg, -, h⟩ := ex_bind h
  obtain ⟨iF, -, h⟩ := ex_bind h
  obtain ⟨cF, -, h⟩ := ex_bind h
  obtain ⟨iO, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨cO, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨pq, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨tail, -, h⟩ := ex_bind h
  have e := Except.ok.inj h
  subst e
  show B₀.cuts = cutsOf F
  exact spendingBook_cuts hB

/-- One premise. **The whole book's field cuts is the maker's list.** -/
theorem bookWhole_cuts {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (h : bookWhole F p0 p1 p2 M = .ok B) : B.cuts = cutsOf F := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  exact bookRaw_cuts hW

/-! ## 2 A lookup in one list, and in two in a row -/

/-- No hypothesis. `cutsIn` at a list with a first member. -/
theorem cutsIn_cons (x : Block S Cl) (bs : List (Block S Cl)) :
    cutsIn (x :: bs) =
      if x.rounds.isEmpty = true then cutsIn bs else (x.place, partsCut x) :: cutsIn bs := by
  unfold cutsIn
  by_cases h : x.rounds.isEmpty = true
  · rw [List.filter_cons_of_neg (by simp [h]), if_pos h]
  · rw [List.filter_cons_of_pos (by simp [h]), if_neg h]
    rfl

/-- In one list of sub-protocols at places without a twin: at a member that has a round. -/
theorem cutsIn_lookup {bs : List (Block S Cl)} (hn : (bs.map (·.place)).Nodup) {b : Block S Cl}
    (hb : b ∈ bs) (hr : b.rounds ≠ []) : (cutsIn bs).lookup b.place = some (partsCut b) := by
  induction bs with
  | nil => cases hb
  | cons x bs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rw [cutsIn_cons]
    by_cases hx : b = x
    · subst hx
      have h0 : ¬ b.rounds.isEmpty = true := by simpa using hr
      rw [if_neg h0, List.lookup_cons_self]
    · have h2 : b ∈ bs := (List.mem_cons.1 hb).resolve_left hx
      have hne : b.place ≠ x.place := fun e => hn.1 (List.mem_map.2 ⟨b, h2, e⟩)
      have e0 : (b.place == x.place) = false := beq_eq_false_iff_ne.2 hne
      split
      · exact ih hn.2 h2
      · rw [List.lookup_cons, e0]
        exact ih hn.2 h2

/-- At a place of none of its sub-protocols a list has no cut. -/
theorem cutsIn_lookup_none {bs : List (Block S Cl)} {a : Place} (ha : a ∉ bs.map (·.place)) :
    (cutsIn bs).lookup a = none := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
    have h1 : a ≠ x.place := fun e => ha (by rw [e]; exact List.Mem.head _)
    have h2 : a ∉ bs.map (·.place) := fun h => ha (List.Mem.tail _ h)
    have e0 : (a == x.place) = false := beq_eq_false_iff_ne.2 h1
    rw [cutsIn_cons]
    split
    · exact ih h2
    · rw [List.lookup_cons, e0]
      exact ih h2

/-- **THE TOOTH FOR hr**: in one list of sub-protocols at places without a twin: at a member that
has NO round the list has no cut. So `cutsIn_lookup` without its premise hr would be false at every
such member. -/
theorem cutsIn_lookup_roundless {bs : List (Block S Cl)} (hn : (bs.map (·.place)).Nodup)
    {b : Block S Cl} (hb : b ∈ bs) (hr : b.rounds = []) : (cutsIn bs).lookup b.place = none := by
  induction bs with
  | nil => cases hb
  | cons x bs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rw [cutsIn_cons]
    by_cases hx : b = x
    · subst hx
      have h0 : b.rounds.isEmpty = true := by
        rw [hr]
        rfl
      rw [if_pos h0]
      exact cutsIn_lookup_none hn.1
    · have h2 : b ∈ bs := (List.mem_cons.1 hb).resolve_left hx
      have hne : b.place ≠ x.place := fun e => hn.1 (List.mem_map.2 ⟨b, h2, e⟩)
      have e0 : (b.place == x.place) = false := beq_eq_false_iff_ne.2 hne
      split
      · exact ih hn.2 h2
      · rw [List.lookup_cons, e0]
        exact ih hn.2 h2

/-- What the first of two lists has at a key, the two in a row have. -/
theorem lookup_append_some {β : Type} : ∀ (l l' : List (Place × β)) (a : Place) (v : β),
    l.lookup a = some v → (l ++ l').lookup a = some v
  | [], _, _, _, h => by cases h
  | (k, w) :: l, l', a, v, h => by
    rw [List.lookup_cons] at h
    rw [List.cons_append, List.lookup_cons]
    cases e : a == k with
    | true =>
      rw [e] at h
      exact h
    | false =>
      rw [e] at h
      exact lookup_append_some l l' a v h

/-- Where the first of two lists has nothing at a key, the two in a row have what the second has. -/
theorem lookup_append_none {β : Type} : ∀ (l l' : List (Place × β)) (a : Place),
    l.lookup a = none → (l ++ l').lookup a = l'.lookup a
  | [], _, _, _ => rfl
  | (k, w) :: l, l', a, h => by
    rw [List.lookup_cons] at h
    rw [List.cons_append, List.lookup_cons]
    cases e : a == k with
    | true =>
      rw [e] at h
      cases h
    | false =>
      rw [e] at h
      exact lookup_append_none l l' a h

/-! ## 3 The statement -/

/-- CONDITIONAL on h, hp, hb and hr. **IN THE WHOLE BOOK THE CUT AT THE PLACE OF A SUB-PROTOCOL OF
THE FIRST CHAIN THAT HAS A ROUND IS ITS OWN.** -/
theorem bookWhole_cut_first {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) (hr : b.rounds ≠ []) :
    B.cuts.lookup b.place = some (partsCut b) := by
  rw [bookWhole_cuts h]
  unfold cutsOf
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  exact lookup_append_some _ _ _ _ (lookup_append_some _ _ _ _ (cutsIn_lookup hn hb hr))

/-- The like in the shared chain. -/
theorem bookWhole_cut_shared {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₂ F.Cl} (hb : b ∈ F.shared.blocksInOrder) (hr : b.rounds ≠ []) :
    B.cuts.lookup b.place = some (partsCut b) := by
  rw [bookWhole_cuts h]
  unfold cutsOf
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.shared.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).2.1
  have c2 : b.place.chain = 2 := chain_shared hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  have n1 : b.place ∉ F.first.blocksInOrder.map (·.place) := fun hm => by
    have c1 := chain_first hp _ hm
    omega
  refine lookup_append_some _ _ _ _ ?_
  rw [lookup_append_none _ _ _ (cutsIn_lookup_none n1)]
  exact cutsIn_lookup hn hb hr

/-- The like in the second chain. -/
theorem bookWhole_cut_second {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₃ F.Cl} (hb : b ∈ F.second.blocksInOrder) (hr : b.rounds ≠ []) :
    B.cuts.lookup b.place = some (partsCut b) := by
  rw [bookWhole_cuts h]
  unfold cutsOf
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.second.blocksInOrder.map (·.place)).Nodup := (List.nodup_append.1 hord).2.1
  have c3 : b.place.chain = 3 := chain_second hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  have n1 : b.place ∉ F.first.blocksInOrder.map (·.place) := fun hm => by
    have c1 := chain_first hp _ hm
    omega
  have n2 : b.place ∉ F.shared.blocksInOrder.map (·.place) := fun hm => by
    have c2 := chain_shared hp _ hm
    omega
  rw [lookup_append_none _ _ _ (by
    rw [lookup_append_none _ _ _ (cutsIn_lookup_none n1)]
    exact cutsIn_lookup_none n2)]
  exact cutsIn_lookup hn hb hr

/-- CONDITIONAL on h, hp, hb and hr. **THE TOOTH IN THE WHOLE BOOK**: at the place of a sub-protocol
of the first chain that has NO round the whole book has no cut. -/
theorem bookWhole_cut_first_roundless {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) (hr : b.rounds = []) :
    B.cuts.lookup b.place = none := by
  rw [bookWhole_cuts h]
  unfold cutsOf
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  have n2 : b.place ∉ F.shared.blocksInOrder.map (·.place) := fun hm => by
    have c2 := chain_shared hp _ hm
    omega
  have n3 : b.place ∉ F.second.blocksInOrder.map (·.place) := fun hm => by
    have c3 := chain_second hp _ hm
    omega
  rw [lookup_append_none _ _ _ (by
    rw [lookup_append_none _ _ _ (cutsIn_lookup_roundless hn hb hr)]
    exact cutsIn_lookup_none n2)]
  exact cutsIn_lookup_none n3

end ProofFile.Honest

#print axioms ProofFile.Honest.spendingBook_cuts
#print axioms ProofFile.Honest.bookRaw_cuts
#print axioms ProofFile.Honest.bookWhole_cuts
#print axioms ProofFile.Honest.cutsIn_cons
#print axioms ProofFile.Honest.cutsIn_lookup
#print axioms ProofFile.Honest.cutsIn_lookup_none
#print axioms ProofFile.Honest.cutsIn_lookup_roundless
#print axioms ProofFile.Honest.lookup_append_some
#print axioms ProofFile.Honest.lookup_append_none
#print axioms ProofFile.Honest.bookWhole_cut_first
#print axioms ProofFile.Honest.bookWhole_cut_shared
#print axioms ProofFile.Honest.bookWhole_cut_second
#print axioms ProofFile.Honest.bookWhole_cut_first_roundless
