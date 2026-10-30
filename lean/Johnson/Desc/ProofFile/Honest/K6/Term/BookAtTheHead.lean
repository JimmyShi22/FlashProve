--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/BookAtTheHead.lean: what the book of coins of the honest prover's
maker says of the sub-protocol "the output head's own rounds" (kind K6), gathered in one structure, at
ANY return of the maker: the book lends K6's row its runs at every run's coins; what the row spends is
ONE STRETCH OF 173 COINS OF ONE OWNER, named: the part number 0 at chain 1, link 24, piece 2, of the
kind K2 (what the book's maker finds as the owner of link 24's mask row: `k6_row_named`,
AtFullSide/K6/StretchNamed.lean), from that part's coin number 439 + 1995 on; the eight parts state
runs of 173 coins in all; and no other part spends one of these coins.

WHAT IT IS NOT. Calls alone: every clause is another file's theorem. PUBLIC DATA ALONE: a book is a
table of entries: nothing on a coin's value, on a law or on a run. THAT THE OWNER's COINS ARE FRESH FOR
K6, and what the parts that CARRY the same coins later show, is not here
(Honest/K6/Term/OwedBeside.lean names what is owed). The owner's address and the number 439 rest on
another group's closed fact, one evaluation in Lean's kernel at the library's written description
(AtFullSide/K6/StretchNamed.lean's limits). The library's hypothesis (`P5J.AtMgA`) and "the maker
returns" are premises. Nothing on soundness, completeness or hiding.

  `headOwner`        the owner's address, written out
  `BookAtTheHead`    the structure
  `bookAtTheHead`    it holds at any return of the maker
  `owner_of_the_heads_coins`, `the_six_spend_of_the_owner`   entry by entry: a part of which one of K6's eight
        spends a coin is `headOwner`; each of the six parts that state a run does spend of it
  `the_lent_coins_are_the_owners`, `the_heads_coins_are_173`, `headPads_are_the_owners_coins`   coin by
        coin: what the row spends is that stretch of the owner's coins
-/
import AtFullSide.K6.StretchNamed
import Johnson.Desc.ProofFile.Honest.BookApartWhole
import Johnson.Desc.ProofFile.Honest.BookStretch
import Johnson.Desc.ProofFile.Honest.K6.Law.LendsAtBook
import Johnson.Desc.ProofFile.Honest.K6.Law.LentInside
import Johnson.Desc.ProofFile.Honest.K6.Law.SpendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Kinds (Head.parOf Head.Par)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open OnBytes.Maker (WholeD)

/-- **The owner of the coins that K6 spends**: part number 0 at chain 1, link 24, piece 2, kind K2. -/
def headOwner : Addr := ⟨⟨1, some 24, 2, .K2⟩, 0⟩

variable {W₀ Rc Tr X₀ X : Type}

/-- **What the maker's book says of K6's row.** `reader`: the row's reader of the small input;
`numbers`: the place's public numbers. A definition that is meant to stand at the end of a theorem. -/
structure BookAtTheHead (returned : OnlineProverWithDescription W₀ Rc Tr X₀ X)
    (reader : Local W₀ Rc Inst Tr → HeadAsk) (numbers : Head.Par) : Prop where
  /-- the book lends the row its runs, at every run's coins. What is lent is not said -/
  lent : ∀ coins : Coins returned.B, ∃ c, lendRow returned.B (returned.B.rowsOf 0) (coins.look 0)
    IM.k6Place (headRow (X := X) reader numbers IM.k6Place) 0 = .ok c
  /-- the spending entries that name the row's eight parts are one stretch: its owner, the number of
  its first coin among the owner's coins of the extension field, its count -/
  stretch : oneStretch (rowEntries returned.B IM.k6Place 8 0) = some (headOwner, 439 + 1995, 173)
  /-- the eight parts state runs of 173 coins of the extension field in all -/
  stated : (((headParts numbers IM.k6Place).map (·.spends)).flatten.map (·.2.e)).sum = 173
  /-- at each of the eight parts the book's spending entries bear the names and counts of the runs that
  the part states, in order, and its carrying entries those of the runs that the part carries (K6's
  parts carry none: `k6_plain`, Honest/K6/Law/LendsAtBook.lean) -/
  entries : ∀ i p, (headParts numbers IM.k6Place)[i]? = some p →
    (spentE returned.B ⟨IM.k6Place, i⟩).map Ahead.named = p.spends ∧
      (carryE returned.B ⟨IM.k6Place, i⟩).map Ahead.named = p.carries
  /-- an entry by which a part of K6's spends shares no coin with an entry by which a part at another
  address spends. Of entries that carry it says nothing -/
  apart : ∀ i, ∀ other : Addr, other ≠ ⟨IM.k6Place, i⟩ →
    ∀ e ∈ spentE returned.B ⟨IM.k6Place, i⟩, ∀ e' ∈ spentE returned.B other, e.shares e' = false

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h; the maker returns. **It holds at any return of the maker**, at
every reader. General in the filling. -/
theorem bookAtTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (reader : Local W₀ Rc Inst Tr → HeadAsk) :
    BookAtTheHead A reader (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) := by
  obtain ⟨p0, p1, p2, hB⟩ := k6_book_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  refine ⟨k6_row_is_lent h hA reader, k6_stretch_numerals (X := X) h hA reader, ?_, ?_,
    fun i other hne e he e' he' => bookWhole_spentApart_parts hB (Ne.symm hne) e he e' he'⟩
  · rw [k6_spends_at_head h IM.k6Place]
    rfl
  · rw [eF] at hB
    exact fun i p hi => (k6_fits_at_book h hB i p hi).2

/-! ## Who the owner is, entry by entry -/

/-- The entries that the walk `runOn` passes are the owner's. -/
theorem runOn_owner (o : Addr) (s : Nat) : ∀ (fs : List Ahead) (c c' : Nat),
    runOn o s c fs = some c' → ∀ f ∈ fs, f.owner = o
  | [], _, _, _, _, hf => absurd hf List.not_mem_nil
  | g :: gs, c, c', h, f, hf => by
    unfold runOn at h
    split at h
    · rename_i hg
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact hg.1
      · exact runOn_owner o s gs _ _ h f hf'
    · cases h

/-- The entries of one stretch are its owner's. -/
theorem oneStretch_owner {es : List Ahead} {o : Addr} {s₀ cnt : Nat}
    (h : oneStretch es = some (o, s₀, cnt)) : ∀ e ∈ es, e.owner = o := by
  cases es with
  | nil => cases h
  | cons e es =>
    have h' : (runOn e.owner e.start.e e.count.e es).map (fun c => (e.owner, e.start.e, c)) =
        some (o, s₀, cnt) := h
    cases hr : runOn e.owner e.start.e e.count.e es with
    | none =>
      rw [hr] at h'
      cases h'
    | some c =>
      rw [hr] at h'
      have e' : (e.owner, e.start.e, c) = (o, s₀, cnt) := Option.some.inj h'
      cases e'
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf'
      · rfl
      · exact runOn_owner _ _ es _ _ hr f hf'

/-- A spending entry of one of a row's parts is among the row's entries. -/
theorem mem_rowEntries (Bk : ProverCoinCounts) (p : Place) : ∀ (n j t : Nat), t < n →
    ∀ e ∈ spentE Bk ⟨p, j + t⟩, e ∈ rowEntries Bk p n j
  | 0, _, _, ht, _, _ => absurd ht (Nat.not_lt_zero _)
  | n + 1, j, 0, _, e, he => List.mem_append_left _ he
  | n + 1, j, t + 1, ht, e, he => by
    refine List.mem_append_right _ (mem_rowEntries Bk p n (j + 1) t (Nat.lt_of_succ_lt_succ ht) e ?_)
    have ej : j + 1 + t = j + (t + 1) := by omega
    rw [ej]
    exact he

section
variable {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X} {reader : Local W₀ Rc Inst Tr → HeadAsk}
  {numbers : Head.Par}

/-- **Every coin that one of K6's eight parts spends is `headOwner`'s**: a part of which one of them
spends a coin is that part. -/
theorem owner_of_the_heads_coins (s : BookAtTheHead returned reader numbers) (o : Addr) (i : Nat)
    (hi : i < 8) (h : returned.B.spentBy o ⟨IM.k6Place, i⟩ ≠ []) : o = headOwner := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ h
  have hf := (List.mem_filter.1 he).2
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have hE : e ∈ spentE returned.B ⟨IM.k6Place, 0 + i⟩ := by
    rw [Nat.zero_add]
    exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨(List.mem_filter.1 he).1, by
      simp only [beq_iff_eq]; exact hf.1.2⟩, hf.2⟩
  rw [← hf.1.1]
  exact oneStretch_owner s.stretch e (mem_rowEntries returned.B IM.k6Place 8 0 i hi e hE)

/-- **At each of the six parts that state a run (numbers 1, 2, 4, 5, 6, 7) the book has an entry by which
it spends a coin of `headOwner`'s.** -/
theorem the_six_spend_of_the_owner (s : BookAtTheHead returned reader numbers) :
    ∀ i ∈ [1, 2, 4, 5, 6, 7], returned.B.spentBy headOwner ⟨IM.k6Place, i⟩ ≠ [] := by
  have key : ∀ i, i < 8 → spentE returned.B ⟨IM.k6Place, i⟩ ≠ [] →
      returned.B.spentBy headOwner ⟨IM.k6Place, i⟩ ≠ [] := by
    intro i hi hne
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    have ho := oneStretch_owner s.stretch e (mem_rowEntries returned.B IM.k6Place 8 0 i hi e
      (by rw [Nat.zero_add]; exact he))
    have h1 := List.mem_filter.1 he
    have h2 := List.mem_filter.1 h1.1
    refine List.ne_nil_of_mem (a := e) (List.mem_filter.2 ⟨h2.1, ?_⟩)
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨ho, by simpa using h2.2⟩, h1.2⟩
  have step : ∀ i p, (headParts numbers IM.k6Place)[i]? = some p → p.spends ≠ [] →
      spentE returned.B ⟨IM.k6Place, i⟩ ≠ [] := by
    intro i p hp hs h0
    have e := (s.entries i p hp).1
    rw [h0] at e
    exact hs e.symm
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 1 (by omega) (step 1 _ rfl (List.cons_ne_nil _ _))
  · exact key 2 (by omega) (step 2 _ rfl (List.cons_ne_nil _ _))
  · exact key 4 (by omega) (step 4 _ rfl (List.cons_ne_nil _ _))
  · exact key 5 (by omega) (step 5 _ rfl (List.cons_ne_nil _ _))
  · exact key 6 (by omega) (step 6 _ rfl (List.cons_ne_nil _ _))
  · exact key 7 (by omega) (step 7 _ rfl (List.cons_ne_nil _ _))

/-- **What the row is lent to spend IS that stretch of the owner's coins**: wherever the book lends the
row its coins, the runs that the row's parts spend, one behind the other, are the owner's coins number
439 + 1995 to 439 + 1995 + 172. What each part makes of them is the part's own text. -/
theorem the_lent_coins_are_the_owners (s : BookAtTheHead returned reader numbers)
    (coins : Coins returned.B) {c : RowCoins (headRow (X := X) reader numbers IM.k6Place)}
    (hc : lendRow returned.B (returned.B.rowsOf 0) (coins.look 0) IM.k6Place
      (headRow (X := X) reader numbers IM.k6Place) 0 = .ok c) :
    spentOf (headRow (X := X) reader numbers IM.k6Place) c =
      ((coinsE (coins.look 0 headOwner).2).drop (439 + 1995)).take 173 := by
  rw [spentOf_row _ _ _ _ _ 0 c hc]
  exact rowIsStretch_of (ch := 0) s.stretch coins

/-- **At the first chain's purse these are 173 coins**, at every run's coins. -/
theorem the_heads_coins_are_173 (s : BookAtTheHead returned reader numbers)
    (coins : Coins returned.B) :
    (rowSpent returned.B (coins.look 0) IM.k6Place 8 0).length = 173 := by
  obtain ⟨c, hc⟩ := s.lent coins
  have room : 439 + 1995 + 173 ≤ (coins.look 0 headOwner).1.e := stretch_of_lent hc s.stretch
  rw [rowIsStretch_of (ch := 0) s.stretch coins, List.length_take, List.length_drop,
    coinsE_length]
  omega

end

/-- **So, coin by coin: what the row spends is the owner's coins from number 439 + 1995 on, 173 of them
or as many as that purse has.** It is the library's `RowIsStretch` (Honest/Law/Rule/TiesFall.lean), a
premise of its rule for the tie of the mask row to the lent coins. chain: in which chain's purse the
coins are looked up; the owner's coins lie in the first chain's (number 0), and there they are 173
(`the_heads_coins_are_173`); in another chain's purse both sides may be shorter. -/
theorem headPads_are_the_owners_coins {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    {reader : Local W₀ Rc Inst Tr → HeadAsk} {numbers : Head.Par}
    (s : BookAtTheHead returned reader numbers) (chain : Nat) :
    RowIsStretch returned.B chain IM.k6Place 8 headOwner (439 + 1995) 173 :=
  rowIsStretch_of s.stretch

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headOwner
#print axioms ProofFile.Honest.K6.BookAtTheHead
#print axioms ProofFile.Honest.K6.bookAtTheHead
#print axioms ProofFile.Honest.K6.runOn_owner
#print axioms ProofFile.Honest.K6.oneStretch_owner
#print axioms ProofFile.Honest.K6.mem_rowEntries
#print axioms ProofFile.Honest.K6.owner_of_the_heads_coins
#print axioms ProofFile.Honest.K6.the_six_spend_of_the_owner
#print axioms ProofFile.Honest.K6.the_lent_coins_are_the_owners
#print axioms ProofFile.Honest.K6.the_heads_coins_are_173
#print axioms ProofFile.Honest.K6.headPads_are_the_owners_coins
