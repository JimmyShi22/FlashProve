-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/MakerBook.lean

Conditionals: nothing here shows that the maker returns a book.

What it proves. "One owner and one start" at the book of random values that the maker returns
(bookWhole, Honest/BookWhole.lean), at a proximity test that is the first sub-protocol with a round
in the last chain (the request's own test): the test on the book's entries that our laws on the pair
take as a premise (tiesB, AgreeBook.lean in the folder above) says yes. General in the description
and in the library's three lists of sendings, which are letters: so at every plan, under the
premises named below.

Names.
  carr_append, carr_none, carr_all, carr_off   on the list of the entries that a part carries.
  carried_core, ties_core   from the shape of the book's list alone: no maker, no description.
  planOf_cut   a helper.
  ties_second               at the book that bookWhole returns.
  ties_of_lent_second       so where the lending of the pair's row has returned.

By what. spent_is_sent's sister sent_is_spent, sent_round, addrOfRound_lt (MakerTies.lean);
behindFold_test, spender_at_test (MakerAddr.lean); cut_k12 (MakerCut.lean). ProofFile's bookRaw_ahead,
spendingBook_ahead, checked_ok (Honest/BookSharedLaw.lean), ex_bindE (Honest/BookSharedKit.lean),
chain_first, chain_shared, chain_second (Honest/Law/Rule/Tests.lean), lendRow_cons_ok
(Law/Rule/RowModel.lean), lendPart_ok, lend_names (Law/Rule/PartCell.lean), foldEntries_once,
splitEntry_once, carry_filter (Honest/BookCarryKit.lean). Of the authors of the attention
sub-protocol's honest side: due_some, segmentCarries_ends, groupCarries_ends, ownFresh_behind
(Honest/BookPlain.lean). Of the writers of the hash build's side: planOf_rounds
(Honest/K14/BookMakers.lean).

Limits.
- hno is a premise, and it is the one place where a label stands: the maker picks the fresh table
  that the second part carries by the label "W", and the one that the first part spends by position
  (the first fold behind its round): that the two are one message is no law of the maker's text: it
  hangs on where the library's list has the sending under that label. It is paid at no plan here.
- hpre: no round stands in front of the test in its chain: at another description the law is silent.
- h1, h2 are read off the lending in ties_of_lent_second; that the lending returns is not shown.
- Owner and start alone: no count but through tiesB's fourth clause; nothing on what a part takes.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MakerAddr
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.BookCarryKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared (ex_bindE)
open ProofFile.Honest.K14 (planOf_rounds)
open ProofFile.Honest.BookRow (foldEntries_once splitEntry_once carry_filter)
open ProofFile.Honest.BookPlain (due_some segmentCarries_ends groupCarries_ends ownFresh_behind)

/-- The entries that a part carries, over two lists in a row. -/
theorem carr_append (a : Addr) (l l' : List Ahead) :
    ((l ++ l').filter fun e => e.spender == a).filter (fun e => !e.once) =
      (l.filter fun e => e.spender == a).filter (fun e => !e.once) ++
        (l'.filter fun e => e.spender == a).filter fun e => !e.once := by
  rw [List.filter_append, List.filter_append]

/-- None, where no carrying entry names the part. -/
theorem carr_none (a : Addr) (l : List Ahead) (h : ∀ e ∈ l, e.once = false → e.spender ≠ a) :
    (l.filter fun e => e.spender == a).filter (fun e => !e.once) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he h3
  obtain ⟨h1, h2⟩ := List.mem_filter.1 he
  have h4 : e.once = false := by
    cases ho : e.once with
    | false => rfl
    | true =>
      rw [ho] at h3
      cases h3
  exact h e h1 h4 (beq_iff_eq.1 h2)

/-- All, of messages carried to the part. -/
theorem carr_all (a : Addr) (ms : List SentMsg) :
    ((ms.map (·.carry a)).filter fun e => e.spender == a).filter (fun e => !e.once) =
      ms.map (·.carry a) := by
  rw [carry_filter, if_pos (beq_self_eq_true a), List.filter_eq_self]
  intro e he
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 he
  rfl

/-- None, of messages carried to another part. -/
theorem carr_off (a a' : Addr) (hne : a' ≠ a) (ms : List SentMsg) :
    ((ms.map (·.carry a')).filter fun e => e.spender == a).filter (fun e => !e.once) = [] := by
  rw [carry_filter, if_neg fun h => hne (beq_iff_eq.1 h)]
  rfl

/-- With it: what the two parts carry, by the same premises. -/
theorem carried_core (Bk : ProverCoinCounts) (pl : Place) (X Y : List Ahead) (reach : List SentMsg)
    (own : Option SentMsg)
    (hA : Bk.ahead = X ++ carryPair ⟨pl, 0⟩ ⟨pl, 1⟩ reach own ++ Y)
    (hX : ∀ e ∈ X ++ Y, e.once = false → e.spender ≠ ⟨pl, 0⟩ ∧ e.spender ≠ ⟨pl, 1⟩) :
    carryE Bk ⟨pl, 0⟩ = reach.map (·.carry ⟨pl, 0⟩) ∧
      carryE Bk ⟨pl, 1⟩ = (reach ++ own.toList).map (·.carry ⟨pl, 1⟩) := by
  have h01 : (⟨pl, 1⟩ : Addr) ≠ ⟨pl, 0⟩ := by
    intro h
    cases h
  have h10 : (⟨pl, 0⟩ : Addr) ≠ ⟨pl, 1⟩ := by
    intro h
    cases h
  have hXa : ∀ e ∈ X, e.once = false → e.spender ≠ ⟨pl, 0⟩ ∧ e.spender ≠ ⟨pl, 1⟩ :=
    fun e he => hX e (List.mem_append_left _ he)
  have hYa : ∀ e ∈ Y, e.once = false → e.spender ≠ ⟨pl, 0⟩ ∧ e.spender ≠ ⟨pl, 1⟩ :=
    fun e he => hX e (List.mem_append_right _ he)
  unfold carryE
  rw [hA]
  unfold carryPair
  constructor
  · rw [carr_append, carr_append, carr_append, carr_none _ X fun e he ho => (hXa e he ho).1,
      carr_none _ Y fun e he ho => (hYa e he ho).1, carr_all, carr_off _ _ h01, List.nil_append,
      List.append_nil, List.append_nil]
  · rw [carr_append, carr_append, carr_append, carr_none _ X fun e he ho => (hXa e he ho).2,
      carr_none _ Y fun e he ho => (hYa e he ho).2, carr_all, carr_off _ _ h10, List.nil_append,
      List.nil_append, List.append_nil]

/-- **The test on the book's entries (tiesB, AgreeBook.lean) from the shape of the book's list**:
where the book's entries are some list X, then one fold's carrying entries (carryPair) at a place's
two parts with the fold's fresh table m sent ahead, then some list Y; no carrying entry of X or Y
names either part; and the first entry that the first part spends has m's sender and start: the test
says yes at the number of the messages in reach. On lists alone: no maker, no description. -/
theorem ties_core (Bk : ProverCoinCounts) (pl : Place) (X Y : List Ahead) (reach : List SentMsg) (m : SentMsg)
    (hA : Bk.ahead = X ++ carryPair ⟨pl, 0⟩ ⟨pl, 1⟩ reach (some m) ++ Y)
    (hX : ∀ e ∈ X ++ Y, e.once = false → e.spender ≠ ⟨pl, 0⟩ ∧ e.spender ≠ ⟨pl, 1⟩)
    (e : Ahead) (hs : (spentE Bk ⟨pl, 0⟩)[0]? = some e) (ho : e.owner = m.sender)
    (hst : e.start = m.start) : tiesB Bk pl reach.length = true := by
  obtain ⟨c0, c1⟩ := carried_core Bk pl X Y reach (some m) hA hX
  have c1' : carryE Bk ⟨pl, 0 + 1⟩ = (reach ++ [m]).map (·.carry ⟨pl, 1⟩) := c1
  unfold tiesB
  rw [c0, c1', hs]
  have g1 : ((reach ++ [m]).map (·.carry ⟨pl, 1⟩))[reach.length]? = some (m.carry ⟨pl, 1⟩) := by
    rw [List.getElem?_map, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have g2 : ((reach.map (·.carry ⟨pl, 0⟩)).take reach.length).map
      (fun e => (e.owner, e.start, e.count)) =
      (((reach ++ [m]).map (·.carry ⟨pl, 1⟩)).take reach.length).map
        fun e => (e.owner, e.start, e.count) := by
    rw [← List.map_take, ← List.map_take, List.take_length, List.take_left', List.map_map,
      List.map_map]
    · rfl
    · rfl
  rw [g1, g2, List.length_map]
  have g3 : (e.owner, e.start.e) = ((m.carry ⟨pl, 1⟩).owner, (m.carry ⟨pl, 1⟩).start.e) := by
    show (e.owner, e.start.e) = (m.sender, m.start.e)
    rw [ho, hst]
  simp only [Option.isSome_some, Option.map_some, g3, beq_self_eq_true, Nat.le_refl, decide_true,
    Bool.and_self]

/-- planOf at a list cut at one sub-protocol. -/
theorem planOf_cut {S Cl : Type} (pre t : List (Block S Cl)) (b : Block S Cl) :
    planOf (pre ++ b :: t) = planOf pre ++ ⟨b.place, partsCut b, b.rounds⟩ :: planOf t := by
  unfold planOf
  rw [List.map_append, List.map_cons]

/-- **One owner and one start, at the book that the maker returns, at a proximity test that is the
first sub-protocol with a round in the last chain.** Where bookWhole returns B and the description's
test on the places says yes; the last chain's list is pre, b, t, with no round in pre; b is of the
kind K12 and declares the rounds that the numbers N give (two stages or more). From the lending (h1,
h2): B hands the first part one spent entry, and the second part one carried entry more than the
first. hno, on the description and the library's list: behind the round of the fresh table that the
maker finds under the label "W", the first chain has no "FOLD epsilon". Then tiesB says yes at b's
place, at the number of entries that the first part carries. -/
theorem ties_second {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (pre t : List (Block F.S₃ F.Cl)) (b : Block F.S₃ F.Cl) (hcut : F.second.blocksInOrder = pre ++ b :: t)
    (hpre : pre.flatMap (·.rounds) = []) (hk : b.place.kind = .K12) (N : H2U.TestNums)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds)
    (h1 : (spentE B ⟨b.place, 0⟩).length = 1)
    (h2 : (carryE B ⟨b.place, 1⟩).length = (carryE B ⟨b.place, 0⟩).length + 1)
    (hno : ∀ m0 m, sentIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok m0 →
      (BookShared.under m0 "W").find? (·.fresh) = some m →
      ∀ j y, m.round + 1 ≤ j → (F.first.blocksInOrder.flatMap (·.rounds))[j]? = some y →
        (y.entry.name != "FOLD epsilon") = true) :
    tiesB B b.place (carryE B ⟨b.place, 0⟩).length = true := by
  unfold bookWhole at h
  obtain ⟨Wb, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB₀, hm0, hm1, hseg, -, hcF, -, hcO, hpq, -,
    hA⟩ := bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, -, hf0, hf1, hf2, hA₀⟩ := spendingBook_ahead hB₀
  have hcb : (⟨b.place, partsCut b, b.rounds⟩ : PlanB).cut =
      [firstLen N.stages, restLen N.stages] := cut_k12 b hk N s next rest hst hr
  have hpre' : ((planOf pre).flatMap (·.rounds)) = [] := by
    rw [planOf_rounds, hpre]
  -- the pair
  have hbf : behindFold (planOf F.second.blocksInOrder) 0 = some (⟨b.place, 0⟩, ⟨b.place, 1⟩) := by
    rw [hcut, planOf_cut]
    exact behindFold_test (planOf pre) (planOf t) ⟨b.place, partsCut b, b.rounds⟩ N s next rest hst
      hr hcb 0 0 (by rw [hpre']; rfl) (Nat.le_refl 0) fun j y _ h2 => absurd h2 (Nat.not_lt_zero j)
  obtain rfl : ((⟨b.place, 0⟩, ⟨b.place, 1⟩) : Addr × Addr) = pq :=
    Option.some.inj (hbf.symm.trans (due_some hpq))
  -- where b stands
  have hb3 : b.place.chain = 3 := chain_second hp b.place (by
    rw [hcut]
    exact List.mem_map.2 ⟨b, List.mem_append_right _ List.mem_cons_self, rfl⟩)
  have off1 : ∀ a : Addr, a.place ∈ F.first.blocksInOrder.map (·.place) →
      a ≠ ⟨b.place, 0⟩ ∧ a ≠ ⟨b.place, 1⟩ := by
    intro a ha
    have h1 := chain_first hp a.place ha
    constructor <;>
    · rintro rfl
      rw [hb3] at h1
      cases h1
  have off2 : ∀ a : Addr, a.place ∈ F.shared.blocksInOrder.map (·.place) →
      a ≠ ⟨b.place, 0⟩ ∧ a ≠ ⟨b.place, 1⟩ := by
    intro a ha
    have h1 := chain_shared hp a.place ha
    constructor <;>
    · rintro rfl
      rw [hb3] at h1
      cases h1
  have inPlan : ∀ {S Cl : Type} (bs : List (Block S Cl)) (x : PlanB), x ∈ planOf bs →
      x.place ∈ bs.map (·.place) := by
    intro S Cl bs x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map.2 ⟨y, hy, rfl⟩
  -- the book's list
  have hA' : Wb.ahead = (ws.map (·.entry) ++ f0 ++ f1 ++ f2 ++
      (splitEntry F.shared.blocksInOrder p1).toList ++ seg ++ cF ++ cO) ++
      carryPair ⟨b.place, 0⟩ ⟨b.place, 1⟩
        (m0.filter (·.masks) ++ (BookShared.under m0 "W").filter (!·.fresh) ++
          (BookShared.under m1 "Omega").filter (!·.masks))
        ((BookShared.under m0 "W").find? (·.fresh)) ++
      (ownFreshIn F.shared.blocksInOrder).map (·.carry tail) := by
    rw [hA, hA₀]
  have hX : ∀ e ∈ (ws.map (·.entry) ++ f0 ++ f1 ++ f2 ++
      (splitEntry F.shared.blocksInOrder p1).toList ++ seg ++ cF ++ cO) ++
      (ownFreshIn F.shared.blocksInOrder).map (·.carry tail), e.once = false →
      e.spender ≠ ⟨b.place, 0⟩ ∧ e.spender ≠ ⟨b.place, 1⟩ := by
    intro e he ho
    have no : e.once = true → e.spender ≠ ⟨b.place, 0⟩ ∧ e.spender ≠ ⟨b.place, 1⟩ := by
      intro h1
      rw [ho] at h1
      cases h1
    simp only [List.mem_append] at he
    rcases he with (((((((he | he) | he) | he) | he) | he) | he) | he) | he
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 he
      exact no rfl
    · exact no (foldEntries_once hf0 e he)
    · exact no (foldEntries_once hf1 e he)
    · exact no (foldEntries_once hf2 e he)
    · exact no (splitEntry_once (Option.mem_toList.1 he))
    · obtain ⟨x, hx, hxp, -⟩ := segmentCarries_ends hseg e he
      exact off1 e.spender (hxp ▸ inPlan _ x hx)
    · obtain ⟨x, hx, hxp, -⟩ := groupCarries_ends hcF e he
      exact off2 e.spender (hxp ▸ inPlan _ x hx)
    · obtain ⟨x, hx, hxp, -⟩ := groupCarries_ends hcO e he
      exact off2 e.spender (hxp ▸ inPlan _ x hx)
    · obtain ⟨o, ho', rfl⟩ := List.mem_map.1 he
      exact off2 o.behind (ownFresh_behind ho')
  obtain ⟨c0, c1⟩ := carried_core Wb b.place _ _ _ _ hA' hX
  -- the fresh table is there
  obtain ⟨m, hfind⟩ : ∃ m, (BookShared.under m0 "W").find? (·.fresh) = some m := by
    cases hf : (BookShared.under m0 "W").find? (·.fresh) with
    | some m => exact ⟨m, rfl⟩
    | none =>
      rw [c0, c1, hf] at h2
      simp only [List.length_map, Option.toList_none, List.append_nil] at h2
      omega
  have hmf : m.fresh = true := List.find?_some hfind
  have hmm : m ∈ m0 := List.mem_of_mem_filter (List.mem_of_find?_eq_some hfind)
  -- its spending entry
  have hm0' : sentIn F.first.blocksInOrder p0 ((planOf F.second.blocksInOrder).flatMap (·.rounds)) = .ok m0 := by
    rw [planOf_rounds]
    exact hm0
  obtain ⟨e, he, f, k, hfb, hsp, hrec⟩ :=
    sent_is_spent F.first.blocksInOrder (planOf F.second.blocksInOrder) p0 f0 m0 hf0 hm0' m hmm hmf
  have hlt := addrOfRound_lt _ _ _ (sent_round _ _ _ _ hm0 m hmm)
  have hlist : planOf F.first.blocksInOrder ++ planOf F.second.blocksInOrder =
      (planOf F.first.blocksInOrder ++ planOf pre) ++ ⟨b.place, partsCut b, b.rounds⟩ :: planOf t := by
    rw [hcut, planOf_cut, List.append_assoc]
  have hcount : ((planOf F.first.blocksInOrder ++ planOf pre).flatMap (·.rounds)) =
      F.first.blocksInOrder.flatMap (·.rounds) := by
    rw [List.flatMap_append, hpre', List.append_nil, planOf_rounds]
  rw [hlist] at hfb hsp
  obtain ⟨hs0, -, -⟩ := spender_at_test (planOf F.first.blocksInOrder ++ planOf pre) (planOf t)
    ⟨b.place, partsCut b, b.rounds⟩ N s next rest hst hr hcb m.round
    (F.first.blocksInOrder.flatMap (·.rounds)).length (by rw [hcount]) (Nat.le_of_lt hlt)
    (fun j y h1 _ h3 => hno m0 m hm0 hfind j y h1 (by rw [hcount] at h3; exact h3)) f k false hfb
  have hspe : e.spender = ⟨b.place, 0⟩ := Option.some.inj (hsp.symm.trans hs0)
  have hmem : e ∈ spentE Wb ⟨b.place, 0⟩ := by
    unfold spentE
    refine List.mem_filter.2 ⟨List.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
    · rw [hA']
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr he))))))))
    · rw [hspe]
      exact beq_self_eq_true _
    · rw [hrec]
  have hs : (spentE Wb ⟨b.place, 0⟩)[0]? = some e := by
    cases hl : spentE Wb ⟨b.place, 0⟩ with
    | nil =>
      rw [hl] at h1
      cases h1
    | cons x l =>
      rw [hl] at h1 hmem
      have hn : l = [] := List.eq_nil_of_length_eq_zero (by
        rw [List.length_cons] at h1
        omega)
      subst hn
      rw [List.mem_singleton.1 hmem]
      rfl
  rw [hfind] at hA'
  have hT := ties_core Wb b.place _ _ _ m hA' hX e hs (by rw [hrec]) (by rw [hrec])
  rw [c0, List.length_map]
  exact hT

/-- **So the premise on the book of five_at_second (hT) is a conclusion, where the lending of the
pair's row has returned**: h1 and h2 are read off the lending (ProofFile's lendPart_ok, lend_names). -/
theorem ties_of_lent_second {Xi V W X : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (pre t : List (Block F.S₃ F.Cl)) (b : Block F.S₃ F.Cl) (hcut : F.second.blocksInOrder = pre ++ b :: t)
    (hpre : pre.flatMap (·.rounds) = []) (hk : b.place.kind = .K12) (J : TestJob W X)
    (f : Addr × ℕ) (hfr : J.fresh = some f) (hpl : J.p.place = b.place)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hr : H2U.roundsOfNums J.p.nums = some b.rounds)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (hl : lendRow B rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c)
    (hno : ∀ m0 m, sentIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok m0 →
      (BookShared.under m0 "W").find? (·.fresh) = some m →
      ∀ j y, m.round + 1 ≤ j → (F.first.blocksInOrder.flatMap (·.rounds))[j]? = some y →
        (y.entry.name != "FOLD epsilon") = true) :
    tiesB B J.p.place J.members.length = true := by
  obtain ⟨p, ms, fr, r, ro, tr⟩ := J
  obtain rfl : fr = some f := hfr
  obtain ⟨l0, hl'⟩ := lendRow_cons_ok hl
  obtain ⟨l1, -⟩ := lendRow_cons_ok hl'
  obtain ⟨-, s0, k0⟩ := lendPart_ok l0
  obtain ⟨-, -, k1⟩ := lendPart_ok l1
  have n0 := congrArg List.length (lend_names _ _ _ _ s0)
  have n1 := congrArg List.length (lend_names _ _ _ _ k0)
  have n2 := congrArg List.length (lend_names _ _ _ _ k1)
  rw [List.length_map] at n0 n1 n2
  have hpl' : p.place = b.place := hpl
  have e0 : (spentE B ⟨b.place, 0⟩).length = 1 := by
    rw [← hpl']
    exact n0
  have e1 : (carryE B ⟨b.place, 0⟩).length = ms.length := by
    rw [← hpl']
    exact n1.trans (List.length_map _)
  have e2 : (carryE B ⟨b.place, 1⟩).length = ms.length + 1 := by
    rw [← hpl']
    refine n2.trans ?_
    show (List.map _ ms ++ [_]).length = _
    rw [List.length_append, List.length_map]
    rfl
  have hT := ties_second h hp pre t b hcut hpre hk p.nums s next rest hst hr e0 (by rw [e2, e1]) hno
  rw [e1, ← hpl'] at hT
  exact hT

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carr_append
#print axioms ProofFile.Honest.K12.AtProof.carr_none
#print axioms ProofFile.Honest.K12.AtProof.carr_all
#print axioms ProofFile.Honest.K12.AtProof.carr_off
#print axioms ProofFile.Honest.K12.AtProof.carried_core
#print axioms ProofFile.Honest.K12.AtProof.ties_core
#print axioms ProofFile.Honest.K12.AtProof.planOf_cut
#print axioms ProofFile.Honest.K12.AtProof.ties_second
#print axioms ProofFile.Honest.K12.AtProof.ties_of_lent_second
