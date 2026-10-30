-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookCarryKit.lean: what the whole book of coins (`bookWhole`,
Honest/BookWhole.lean) hands a part of the first chain to carry: which entries, as a written
function of the chain's sendings. One definition with code; lemmas with their proofs; two tests.

  `segmentCarriesAt`   what `segmentCarries` (Honest/BookCarry.lean) lays for the part at an
     address, written out: fresh table by fresh table, in the order of sending
  `segmentCarries_filter`   where `segmentCarries` returns: of its entries those whose spender is
     the address are that list: at every address
  `bookWhole_carries`   where `bookWhole` returns B: at an address of the first chain the carrying
     entries (`carryE`, Honest/Law/Rule/Cell.lean) are that list, at the chain's messages as
     `sentIn` returns them
  `bookWhole_carries_named`   the same under `Ahead.named`: the form of the premise `hca` of
     `lendPart_of_fit` (Honest/BookLends.lean)
  `segmentCarriesAt_none`   at an address that is no fold's and no sender's behind one: nothing
  In the namespace `BookRow`, the lemmas under them: `mapM_flatten_filter`, `carry_filter`,
     `carry_spent`, `carry_other`, `carry_kept`, `foldEntries_once`, `splitEntry_once`

Where the carrying entries of the other chains end is not shown anew: `groupCarries_ends`,
`pair_ends`, `ownFresh_behind` and `due_some` are called (Honest/BookPlain.lean, by the authors of
the attention sub-protocol's parts). So this file stands over a file of other authors.

`segmentCarriesAt` IS A SECOND TEXT OF A PART OF `segmentCarries`, ON PURPOSE. The first is an
`Except` and lays all parts' entries in one list; the second is total and lays one part's.
`segmentCarries_filter` holds the second to the first at every address, under the first's return: by
a proof, not by `rfl`. If the first text turns in what it lays where it returns, and the second does
not follow, that proof fails; a turn that only makes the first refuse more often need not break it.
WHERE THE FIRST REFUSES THE TWO PART: see `segmentCarriesAt`'s own comment, below.

Limits.
  * That `bookWhole` returns, and `F.placesOk`, are hypotheses.
  * WHAT IS CARRIED IS THE SENDER's WHOLE RUN FOR A MESSAGE, its tails and its pads: more than a
    part's text may read. Whoever counts what is known at an owner has to count these.
  * `fresh` and `masks` are read off a message's shape, and the link off a sending's label
    (Honest/BookCarry.lean): a message that is wrongly taken for no mask message would be carried.
  * That the list is what a part states as its `carries` is not said here: it is an equation on that
    part's own text.
  * Nothing is said of a spender in the shared or the second chain: there the book has other
    carrying entries, and `bookWhole_carries` would be false.
  * The lemmas speak of entries: names, owners, starts, counts. Nothing on the value of a coin.
  * Where the first chain has no fresh table both sides of `bookWhole_carries` are empty.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.Desc.ProofFile.Honest.BookPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain

variable {Xi S Cl : Type}

/-! ## 0 The definition -/

/-- **What `segmentCarries` lays for the part at `a`**, written out: for each fresh table of a link,
in the order of sending: where `a` is the fold behind it, the messages that the fold carries; where
`a` is the part that sends what the fold leaves, the messages that this part carries. Public data
alone: labels, rounds, addresses, counts. A SILENT DEFAULT: for a fresh table behind which
`behindFold` finds no fold, or no sending, this text lays NOTHING (its last arm, `[]`), where
`segmentCarries` returns an error for the whole list. So it is what `segmentCarries` lays only where
that returns (`segmentCarries_filter`'s premise); `segmentCarriesAt_none` has no such premise and
speaks of this text alone. -/
def segmentCarriesAt (here : List PlanB) (ms : List SentMsg) (a : Addr) : List Ahead :=
  (ms.filter fun m => m.fresh && (linkOf m.label).isSome).flatMap fun f =>
    match behindFold here f.round, linkOf f.label with
    | some (p, q), some l =>
      (if p == a then (ms.filter fun m => !m.masks && ((linkOf m.label).any fun j =>
          decide (j < l) || (j == l && !m.fresh))).map (·.carry a) else []) ++
      (if q == a then (ms.filter fun m => !m.masks && ((linkOf m.label).any fun j =>
          decide (j ≤ l))).map (·.carry a) else [])
    | _, _ => []

namespace BookRow

/-! ## 1 Lists -/

/-- Where `mapM` returns lists: a filter of them all, laid in a row, piece by piece. -/
theorem mapM_flatten_filter {ε α β : Type} {f : α → Except ε (List β)} {g : α → List β}
    {p : β → Bool} :
    ∀ (l : List α) (r : List (List β)), (∀ a ∈ l, ∀ b, f a = .ok b → b.filter p = g a) →
      l.mapM f = .ok r → r.flatten.filter p = l.flatMap g
  | [], r, _, h => by
    rw [List.mapM_nil] at h
    have e := Except.ok.inj h
    subst e
    rfl
  | a :: l, r, hf, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := ex_bind h
    obtain ⟨bs, hbs, h⟩ := ex_bind h
    have e := Except.ok.inj h
    rw [← e, List.flatten_cons, List.filter_append, List.flatMap_cons,
      hf a (List.Mem.head _) b hb,
      mapM_flatten_filter l bs (fun a' ha' => hf a' (List.Mem.tail _ ha')) hbs]

/-- Of the entries by which one part carries messages, those whose spender is `a`: all or none. -/
theorem carry_filter (ms : List SentMsg) (d a : Addr) :
    (ms.map (·.carry d)).filter (fun e => e.spender == a) =
      if d == a then ms.map (·.carry a) else [] := by
  by_cases h : d = a
  · subst h
    rw [if_pos (beq_self_eq_true d)]
    refine List.filter_eq_self.2 fun e he => ?_
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 he
    exact beq_self_eq_true d
  · rw [if_neg (fun hh => h (beq_iff_eq.1 hh))]
    refine List.filter_eq_nil_iff.2 fun e he hh => ?_
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 he
    exact h (beq_iff_eq.1 hh)

theorem carry_spent {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.once = true) :
    (l.filter fun e => e.spender == a).filter (fun e => !e.once) = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    have h1 := h e (List.mem_filter.1 he).1
    simp [h1]

theorem carry_other {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.spender ≠ a) :
    (l.filter fun e => e.spender == a).filter (fun e => !e.once) = [] := by
  have h0 : l.filter (fun e => e.spender == a) = [] :=
    List.filter_eq_nil_iff.2 fun e he => by
      have hne := h e he
      simp [hne]
  rw [h0]
  rfl

theorem carry_kept {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.once = false) :
    (l.filter fun e => e.spender == a).filter (fun e => !e.once) =
      l.filter fun e => e.spender == a :=
  List.filter_eq_self.2 fun e he => by
    have h1 := h e (List.mem_filter.1 he).1
    simp [h1]

/-! ## 2 What is spent once -/

/-- A fold's entry on a fresh table that was sent ahead is a spending entry. -/
theorem foldEntries_once {here later : List PlanB} {c : Johnson.G.ChainSends} {l : List Ahead}
    (h : foldEntries here later c = .ok l) : ∀ e ∈ l, e.once = true := by
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, a.once = true) ?_ hll inner hin a ha
    intro x _ r hr
    refine mapM_all _ r ?_ hr
    intro j _ b hb
    try dsimp only at hb
    split at hb
    · cases hb
    · cases hb
    · split at hb
      · have e2 := Except.ok.inj hb
        subst e2
        rfl
      · cases hb

theorem splitEntry_once {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {e : Ahead}
    (h : splitEntry bs c = some e) : e.once = true := by
  unfold splitEntry at h
  dsimp only at h
  obtain ⟨p, -, h⟩ := opt_bind h
  obtain ⟨m, -, h⟩ := opt_map h
  subst h
  rfl

end BookRow

/-! ## 3 The second text is the first's, address by address -/

/-- **Of what `segmentCarries` returns, the entries whose spender is `a` are `segmentCarriesAt`'s**:
at every address, in the same order. -/
theorem segmentCarries_filter {here : List PlanB} {ms : List SentMsg} {seg : List Ahead}
    (h : segmentCarries here ms = .ok seg) (a : Addr) :
    seg.filter (fun e => e.spender == a) = segmentCarriesAt here ms a := by
  unfold segmentCarries at h
  obtain ⟨ll, hll, e⟩ := ex_map h
  rw [← e]
  unfold segmentCarriesAt
  refine mapM_flatten_filter _ ll ?_ hll
  intro f _ r hr
  try dsimp only at hr
  try dsimp only
  split at hr
  · rename_i p q k hb hk
    have e2 := Except.ok.inj hr
    rw [hb, hk, ← e2, List.filter_append, carry_filter, carry_filter]
  · cases hr

/-- **THE TOOTH**: at an address that is no fold's behind a fresh table, and no sender's behind such
a fold, nothing is laid. -/
theorem segmentCarriesAt_none {here : List PlanB} {ms : List SentMsg} {a : Addr}
    (hn : ∀ f ∈ ms, f.fresh = true → ∀ p q, behindFold here f.round = some (p, q) →
      p ≠ a ∧ q ≠ a) : segmentCarriesAt here ms a = [] := by
  unfold segmentCarriesAt
  refine List.flatMap_eq_nil_iff.2 fun f hf => ?_
  have hf' := List.mem_filter.1 hf
  have hfr : f.fresh = true := (Bool.and_eq_true_iff.1 hf'.2).1
  have hn' := hn f hf'.1 hfr
  try dsimp only
  split
  · rename_i p q k hb hk
    obtain ⟨h1, h2⟩ := hn' p q hb
    rw [if_neg (fun hh => h1 (beq_iff_eq.1 hh)), if_neg (fun hh => h2 (beq_iff_eq.1 hh))]
    rfl
  · rfl

/-! ## 4 At the whole book -/

/-- **WHAT THE WHOLE BOOK HANDS A PART OF THE FIRST CHAIN TO CARRY**: where `bookWhole` returns B
and the description's test on the places passes: at an address whose place is of the first chain the
carrying entries are `segmentCarriesAt`'s, at the first chain's plan and at its messages as
`sentIn` returns them. -/
theorem bookWhole_carries {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {a : Addr}
    (ha : a.place ∈ F.first.blocksInOrder.map (·.place)) :
    ∃ m0, sentIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok m0 ∧
      carryE B a = segmentCarriesAt (planOf F.first.blocksInOrder) m0 a := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, -, hseg, -, hcF, -, hcO, hpq, -,
    eW⟩ := bookRaw_ahead hW
  obtain ⟨idx, w, f0, f1, f2, -, -, -, hf0, hf1, hf2, eB⟩ := spendingBook_open hB
  refine ⟨m0, hm0, ?_⟩
  have c1 : a.place.chain = 1 := chain_first hp _ ha
  have n2 : ∀ x : Addr, x.place ∈ F.shared.blocksInOrder.map (·.place) → x ≠ a := by
    intro x hx e
    have h2 := chain_shared hp _ hx
    rw [e] at h2
    omega
  have n3 : ∀ x : Addr, x.place ∈ F.second.blocksInOrder.map (·.place) → x ≠ a := by
    intro x hx e
    have h2 := chain_second hp _ hx
    rw [e] at h2
    omega
  have in2 : ∀ (e : Ahead) (x : PlanB), x ∈ planOf F.shared.blocksInOrder → x.place = e.spender.place →
      e.spender ≠ a := by
    intro e x hx ex
    refine n2 _ ?_
    rw [← ex, ← planOf_places]
    exact List.mem_map_of_mem hx
  have in3 : ∀ (e : Ahead) (x : PlanB), x ∈ planOf F.second.blocksInOrder → x.place = e.spender.place →
      e.spender ≠ a := by
    intro e x hx ex
    refine n3 _ ?_
    rw [← ex, ← planOf_places]
    exact List.mem_map_of_mem hx
  -- the spending book's entries are spent once
  have s0 : ∀ e ∈ B₀.ahead, e.once = true := by
    rw [eB]
    intro e he
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · rcases List.mem_append.1 he with he | he
        · rcases List.mem_append.1 he with he | he
          · obtain ⟨w', -, rfl⟩ := List.mem_map.1 he
            rfl
          · exact foldEntries_once hf0 e he
        · exact foldEntries_once hf1 e he
      · exact foldEntries_once hf2 e he
    · cases hsp : splitEntry F.shared.blocksInOrder p1 with
      | none =>
        rw [hsp] at he
        cases he
      | some e' =>
        rw [hsp] at he
        rw [mem_one he]
        exact splitEntry_once hsp
  -- the two groups of the shared chain, and its own fresh tables: spenders of the shared chain
  have s2 : ∀ e ∈ cF, e.spender ≠ a := by
    intro e he
    obtain ⟨x, hx, ex, -⟩ := groupCarries_ends hcF e he
    exact in2 e x hx ex
  have s3 : ∀ e ∈ cO, e.spender ≠ a := by
    intro e he
    obtain ⟨x, hx, ex, -⟩ := groupCarries_ends hcO e he
    exact in2 e x hx ex
  -- the second chain's first fold
  have s4 : ∀ (reach : List SentMsg) (own : Option SentMsg),
      ∀ e ∈ carryPair pq.1 pq.2 reach own, e.spender ≠ a := by
    intro reach own e he
    obtain ⟨x, hx, ex, -⟩ := pair_ends (p := pq.1) (q := pq.2) (due_some hpq) e he
    exact in3 e x hx ex
  have s5 : ∀ e ∈ (ownFreshIn F.shared.blocksInOrder).map (·.carry tail), e.spender ≠ a := by
    intro e he
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
    exact n2 _ (ownFresh_behind ho)
  unfold carryE
  rw [eW]
  simp only [List.filter_append]
  rw [carry_spent s0, carry_kept (segmentCarries_once hseg), carry_other s2, carry_other s3,
    carry_other (s4 _ _), carry_other s5]
  simp only [List.nil_append, List.append_nil]
  exact segmentCarries_filter hseg a

/-- The same under `Ahead.named`: the book's side of the third premise of `lendPart_of_fit`
(Honest/BookLends.lean). -/
theorem bookWhole_carries_named {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {a : Addr}
    (ha : a.place ∈ F.first.blocksInOrder.map (·.place)) :
    ∃ m0, sentIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok m0 ∧
      (carryE B a).map Ahead.named =
        (segmentCarriesAt (planOf F.first.blocksInOrder) m0 a).map Ahead.named := by
  obtain ⟨m0, h0, e⟩ := bookWhole_carries h hp ha
  exact ⟨m0, h0, by rw [e]⟩

/-! ### Tests at Honest/BookCarry.lean's made-up lists -/

namespace BookCarryKitToy

-- at the second segment's sender: the first segment's message, its fresh table, the later sending's
-- message: what the filter of `segmentCarries` shows there (Honest/BookCarry.lean's own test)
#guard (segmentCarriesAt toyChain toyMoments ⟨⟨1, some 1, 1, .K2⟩, 0⟩).map (fun e =>
    (e.owner.place.piece, e.start.e)) == [(1, 0), (1, 1), (4, 0)]
-- at the first closing: the two messages, not its fresh table; at a third address: nothing
#guard (segmentCarriesAt toyChain toyMoments ⟨⟨1, some 0, 2, .K10⟩, 0⟩).map (fun e =>
    (e.owner.place.piece, e.start.e)) == [(1, 0), (4, 0)] &&
  (segmentCarriesAt toyChain toyMoments ⟨⟨1, some 0, 1, .K1⟩, 0⟩).isEmpty

end BookCarryKitToy

end ProofFile.Honest

#print axioms ProofFile.Honest.BookRow.mapM_flatten_filter
#print axioms ProofFile.Honest.BookRow.carry_filter
#print axioms ProofFile.Honest.BookRow.carry_spent
#print axioms ProofFile.Honest.BookRow.carry_other
#print axioms ProofFile.Honest.BookRow.carry_kept
#print axioms ProofFile.Honest.BookRow.foldEntries_once
#print axioms ProofFile.Honest.BookRow.splitEntry_once
#print axioms ProofFile.Honest.segmentCarries_filter
#print axioms ProofFile.Honest.segmentCarriesAt_none
#print axioms ProofFile.Honest.bookWhole_carries
#print axioms ProofFile.Honest.bookWhole_carries_named
