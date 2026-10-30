-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtOmega.lean: kind K14: **WHERE THE FRAME's MAKERS OF THE BOOK
OF COINS RETURN (the short list sharedAhead, Honest/BookShared.lean; the raw book bookRaw and the
whole book bookWhole, Honest/BookWhole.lean), at a shared list of the form SharedForm and a list of
sendings of the form SharedSends (Honest/K14/BookAtShared.lean), AND WHERE THE PUBLIC TESTS ON THE
PLACES AND THE NUMBERS ACCEPT (F.placesOk, omegaNumbersB): AT THE PART AT "send o_omega": JUST ONE
ENTRY SPENDS OF THAT PART's COINS, o_sp's FIRST COIN; EVERY OTHER ENTRY WITH THAT OWNER CARRIES
o_omega's OR o_sp's WHOLE RUN, TO A PART THAT STANDS BEHIND THE SPENDER IN THE DESCRIPTION's OWN
ORDER OF PLACES; AND SO, WHERE o_sp HAS AN ENTRY THAT IS NO PAD AND THE THREE TESTS ON THE PLAN
ACCEPT TOO (sendingsFit, the split, freshPublicB), THE TEST FOR THAT PART (spOwner,
Honest/K14/FreshOwner.lean) ACCEPTS WHAT IS RETURNED**: the raw book too: the book before its own
tests are asked. General in the description. One definition with code; statements with their proofs.

  omegaNumbersB codes sent first len   **a test on public numbers**: the sending has two notices;
                  neither is a fold's fresh table; the index-mask message is number 1; by the
                  maker's own arithmetic (msgStretch, maskStart, at k := 0) message 0's whole run is
                  (⟨0, 0⟩, ⟨0, first⟩), message 1's (⟨0, first⟩, ⟨0, len⟩), and message 1's mask
                  entries begin at ⟨0, first⟩
  msgDue_idle … maskStart_idle   where no notice is a fresh table the maker's number k is idle
  numbers_give    what the test on the numbers gives, clause by clause
  sent_at_omega   of the shared chain's listed messages those that the part sends have, by start
                  and count, o_omega's or o_sp's whole run
  folds_not_omega no fold's spending entry has that owner
  split_at_omega  the split's coin: its entry is there; owner, start, count
  whole_of_short  **the short list passes the short test** (wholeOrSpent,
                  Honest/K14/OwnerWholeTest.lean)
  carriers_all    **THE CORE ON THE ORDER: in the short list, at that owner: the split's entry
                  (what splitEntry returns) lies in the list and spends, its spender the part s of
                  the round 7 ("SPLIT"); every other entry carries, to a part k with
                  StandsBehind (orderOf F) s k** (Honest/K14/BookMakers.lean). "Other" is by value:
                  that the entry stands once in the list: whole_of_short's proof alone has it
  known_nil_of_short   **in the frame's own term: ProverCoinCounts.knownBy at s is empty**
  knownBelow_of_short, carriers_behind   so the short list passes both tests on the order:
                  knownBelow (Honest/K14/FreshDefs.lean) at every number, behindSpenderB
                  (Honest/K14/OwnerOrder.lean) at every run
  spOwner_ok_of_short, spOwner_ok_of_raw, spOwner_ok_of_book   **the owner's test accepts the short
                  list, laid into any book; THE RAW BOOK; every book that bookWhole returns**. The
                  last is the second with the frame's checked_ok: that the whole book has passed its
                  own tests is not used

How it goes. At an owner in the shared chain the raw book's entries are the short list's
(bookRaw_ahead_shared, Honest/K14/BookRawShared.lean); the tests read the entries at the owner alone
(Honest/K14/OwnerAt.lean). The order: a part that is handed a carried run holds a round named "FOLD
epsilon", or a later one, or stands in the second chain; by SharedForm's eight names such a round
has a number from 8 on; the first nine members declare just the rounds 0 to 7; no place stands twice
in the order. Called of the frame's: before_places (Honest/Law/Rule/Order.lean), Addr.not_before
(Honest/Law/Rule/Lent.lean), orderOf_nodup, chain_first, chain_second (Honest/Law/Rule/Tests.lean),
checked_ok (Honest/BookSharedLaw.lean).
What the proofs use of the sub-protocols behind the ninth: their places, and of their rounds the
name "FOLD epsilon". (The makers read more.)
What is assumed. That sharedAhead, bookRaw or bookWhole returns · SharedForm of the description's
shared list · the description's test on the places · SharedSends: what the library's list of
sendings begins with · omegaNumbersB · for the owner's test: o_sp has an entry that is no pad, and
the three tests on the plan.
What is not claimed. That any of these makers returns at any file. IN THIS FILE THE PREMISES ARE
SHOWN TO HOLD TOGETHER AT NO LETTERS, NOT AT A SMALL EXAMPLE: BY THIS FILE THE STATEMENTS MAY BE
EMPTY. (That the short list returns at the proof file's IOP as written in Lean:
Honest/K14/SharedAheadAtHead.lean; of bookRaw and bookWhole no file shows it.) THAT THE RAW BOOK
PASSES ITS OWN TESTS: no lemma here leads to the eighth test's yes. Nothing on what is or is not
hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookAtShared
import Johnson.Desc.ProofFile.Honest.K14.OwnerOrder
import Johnson.Desc.ProofFile.Honest.K14.BookRawShared
import Johnson.Desc.ProofFile.Honest.Law.Rule.Order
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block FileDescription Place)
open OnBytes (Codes OracleNotice)
open ProofFile.Honest.BookShared

/-- **The test on the numbers.** -/
def omegaNumbersB (codes : Codes) (sent : List OracleNotice) (first len : Nat) : Bool :=
  sent.length == 2 && sent.all (fun x => !isFresh x) && sent.findIdx isIndexMaskMsg == 1 &&
    msgStretch codes 0 sent 0 == some (⟨0, 0⟩, ⟨0, first⟩) &&
    msgStretch codes 0 sent 1 == some (⟨0, first⟩, ⟨0, len⟩) &&
    maskStart codes 0 sent 1 == some ⟨0, first⟩

/-! ## 1 The maker's number k is idle where no notice is fresh -/

/-- One message's coins. -/
theorem msgDue_idle (codes : Codes) (k : Nat) (x : OracleNotice) (h : isFresh x = false) :
    msgDue codes k x = msgDue codes 0 x := by
  unfold msgDue
  simp only [h, Bool.false_eq_true, if_false]

/-- A sending's coins. -/
theorem sendDue_idle (codes : Codes) (k : Nat) (ns : List OracleNotice)
    (h : ∀ x ∈ ns, isFresh x = false) : sendDue codes k ns = sendDue codes 0 ns := by
  unfold sendDue
  rw [mapM_agree ns fun x hx => msgDue_idle codes k x (h x hx)]

/-- The message number j's coins. -/
theorem msgAt_idle (codes : Codes) (k : Nat) (ns : List OracleNotice)
    (h : ∀ x ∈ ns, isFresh x = false) (j : Nat) :
    ns[j]?.bind (msgDue codes k) = ns[j]?.bind (msgDue codes 0) := by
  cases hj : ns[j]? with
  | none => rfl
  | some x => exact msgDue_idle codes k x (h x (List.mem_of_getElem? hj))

/-- A message's whole run. -/
theorem msgStretch_idle (codes : Codes) (k : Nat) (ns : List OracleNotice)
    (h : ∀ x ∈ ns, isFresh x = false) (j : Nat) :
    msgStretch codes k ns j = msgStretch codes 0 ns j := by
  unfold msgStretch
  rw [sendDue_idle codes k _ fun x hx => h x (List.mem_of_mem_take hx), msgAt_idle codes k ns h]

/-- Where a message's mask entries begin. -/
theorem maskStart_idle (codes : Codes) (k : Nat) (ns : List OracleNotice)
    (h : ∀ x ∈ ns, isFresh x = false) (j : Nat) :
    maskStart codes k ns j = maskStart codes 0 ns j := by
  unfold maskStart
  rw [sendDue_idle codes k _ fun x hx => h x (List.mem_of_mem_take hx), msgAt_idle codes k ns h]

/-! ## 2 The short list's six lists, one by one -/

variable {S Cl : Type} {xs : List (Block S Cl)} {p1 : Johnson.G.ChainSends} {codes : Codes}
  {sentU sentO : List OracleNotice} {first len : Nat}

/-- What the test on the numbers gives. -/
theorem numbers_give (h : omegaNumbersB codes sentO first len = true) :
    sentO.length = 2 ∧ (∀ x ∈ sentO, isFresh x = false) ∧ sentO.findIdx isIndexMaskMsg = 1 ∧
      (∀ k, msgStretch codes k sentO 0 = some (⟨0, 0⟩, ⟨0, first⟩)) ∧
      (∀ k, msgStretch codes k sentO 1 = some (⟨0, first⟩, ⟨0, len⟩)) ∧
      ∀ k, maskStart codes k sentO 1 = some ⟨0, first⟩ := by
  unfold omegaNumbersB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, fun k => (msgStretch_idle codes k sentO h2 0).trans h4,
    fun k => (msgStretch_idle codes k sentO h2 1).trans h5,
    fun k => (maskStart_idle codes k sentO h2 1).trans h6⟩

/-- **Of the shared chain's listed messages those that the part at "send o_omega" sends have
o_omega's or o_sp's whole run.** -/
theorem sent_at_omega (hX : SharedForm xs) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) {ms : List SentMsg}
    (h : sentIn xs p1 = .ok ms) :
    ∀ m ∈ ms, m.sender = { place := sendPlace 5, part := 0 } →
      (m.start, m.count) = ((⟨0, 0⟩, ⟨0, first⟩) : Due × Due) ∨
        (m.start, m.count) = ((⟨0, first⟩, ⟨0, len⟩) : Due × Due) := by
  obtain ⟨hc, sU, sO, rest, hs, -, -, -, eO, wU, wO, hr⟩ := hS
  obtain ⟨n2, -, -, g0, g1, -⟩ := numbers_give hN
  obtain ⟨a1, a4, -⟩ := form_addr hX
  unfold sentIn at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    rw [hs, form_pairs hX wU wO hr] at hll
    intro m hm
    rw [← e] at hm
    obtain ⟨inner, hin, hm⟩ := List.mem_flatten.1 hm
    refine mapM_all _ ll (P := fun inner => ∀ m ∈ inner,
      m.sender = { place := sendPlace 5, part := 0 } →
      (m.start, m.count) = ((⟨0, 0⟩, ⟨0, first⟩) : Due × Due) ∨
        (m.start, m.count) = ((⟨0, first⟩, ⟨0, len⟩) : Due × Due)) ?_ hll inner hin m hm
    intro x hx r hr'
    try dsimp only at hr'
    refine mapM_all _ r ?_ hr'
    intro n hn b hb
    try dsimp only at hb
    split at hb
    · rename_i a st ha hst
      rw [← Except.ok.inj hb]
      intro hsend
      rcases mem_two hx with rfl | rfl
      · rw [a1] at ha
        have : a = { place := sendPlace 5, part := 0 } := hsend
        rw [← Option.some.inj ha] at this
        exact absurd this (by decide)
      · rw [hc, eO] at hst
        have hj : n.2 < 2 := by
          have h9 : n.2 < 0 + sO.sent.length := (List.mem_zipIdx hn).2.1
          rw [eO, n2] at h9
          omega
        have hj' : n.2 = 0 ∨ n.2 = 1 := by omega
        rcases hj' with e0 | e0
        · rw [e0, g0] at hst
          rw [← Option.some.inj hst]
          exact Or.inl rfl
        · rw [e0, g1] at hst
          rw [← Option.some.inj hst]
          exact Or.inr rfl
    · cases hb

/-- **No fold's spending entry has that owner**: "Omega"'s sending has no fresh table. -/
theorem folds_not_omega (hX : SharedForm xs) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) {f1 : List Ahead}
    (h : foldEntries (planOf xs) [] p1 = .ok f1) :
    ∀ e ∈ f1, e.owner ≠ { place := sendPlace 5, part := 0 } := by
  obtain ⟨-, sU, sO, rest, hs, -, -, -, eO, wU, wO, hr⟩ := hS
  obtain ⟨-, nf, -⟩ := numbers_give hN
  obtain ⟨a1, -, -⟩ := form_addr hX
  have hp := form_pairs hX wU wO hr
  unfold seedRounds at hp
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    rw [planOf_rounds, hs, hp] at hll
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner,
      a.owner ≠ { place := sendPlace 5, part := 0 }) ?_ hll inner hin a ha
    intro x hx r hr'
    refine mapM_all _ r ?_ hr'
    intro j hj b hb
    try dsimp only at hb
    rcases mem_two hx with rfl | rfl
    · split at hb
      · cases hb
      · cases hb
      · split at hb
        · rename_i o p st ho _ _
          rw [← Except.ok.inj hb]
          rw [addrIn_planOf, a1] at ho
          rw [← Option.some.inj ho]
          show ({ place := sendPlace 2, part := 0 } : Addr) ≠ _
          decide
        · cases hb
    · exfalso
      unfold freshOf at hj
      obtain ⟨y, hy, -⟩ := List.mem_map.1 hj
      have h1 := List.mem_filter.1 hy
      have h2 : y.1 ∈ sO.sent := List.fst_mem_of_mem_zipIdx h1.1
      rw [eO] at h2
      rw [nf y.1 h2] at h1
      exact Bool.false_ne_true h1.2

/-- **The split's coin**: its entry is there: the owner is the part at "send o_omega", the run
o_sp's first coin; it is spent. -/
theorem split_at_omega (hX : SharedForm xs) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) :
    ∃ e, splitEntry xs p1 = some e ∧ e.owner = { place := sendPlace 5, part := 0 } ∧
      e.start = ⟨0, first⟩ ∧ e.count = ⟨0, 1⟩ ∧ e.once = true := by
  obtain ⟨hc, sU, sO, rest, hs, lU, -, lO, eO, -, -, -⟩ := hS
  obtain ⟨n2, -, ix, -, g1, gm⟩ := numbers_give hN
  obtain ⟨-, a4, a7⟩ := form_addr hX
  obtain ⟨more, hm⟩ := form_seeds hX
  obtain ⟨r1, s2, a2, r4, s5, a5, r7, r8, T, hR, m1, m2, m3, m4, m5, m6, m7, m8⟩ := form_rounds hX
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 a7
  have hi : (xs.flatMap (·.rounds)).findIdx (fun r => r.entry.name == "SPLIT") = 7 := by
    rw [hR]
    simp [List.findIdx_cons, m1, m2, m3, m4, m5, m6, m7, m8]
  have hfind : ((seedRounds xs).zip p1.sends).find? (fun x => x.2.label == "Omega") =
      some (4, sO) := by
    rw [hm, hs]
    simp [lU, lO]
  obtain ⟨y, hy⟩ : ∃ y, sentO[1]? = some y := by
    have : 1 < sentO.length := by omega
    exact ⟨sentO[1], List.getElem?_eq_getElem this⟩
  have hdue : ∀ k, ∃ d, msgDue codes k y = some d := fun k => by
    have h1 := g1 k
    unfold msgStretch at h1
    obtain ⟨_, -, h1⟩ := opt_bind h1
    obtain ⟨d, h1, -⟩ := opt_map h1
    rw [hy] at h1
    exact ⟨d, h1⟩
  unfold splitEntry ownerOf
  simp only [hi, hp, hfind, Option.bind_some, hc, eO, ix, a4]
  generalize (foldK _).getD 0 = K
  obtain ⟨d, hd⟩ := hdue K
  simp only [gm K, hy, hd, Option.bind_some, Option.map_some]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3 The short list passes the short test -/

/-- **The short list passes the test.** B₀: any book; of it nothing is read. -/
theorem whole_of_short {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hS : SharedSends p1 codes sentU sentO) (hN : omegaNumbersB codes sentO first len = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    wholeOrSpent ⟨0, first⟩ ⟨0, 1⟩ [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)]
      { B₀ with ahead := l } { place := sendPlace 5, part := 0 } = true := by
  unfold sharedAhead at h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨m1, hm1, h⟩ := ex_bind h
  dsimp only at h
  obtain ⟨iF, -, h⟩ := ex_bind h
  obtain ⟨cF, hcF, h⟩ := ex_bind h
  obtain ⟨iO, -, h⟩ := ex_bind h
  obtain ⟨cO, hcO, h⟩ := ex_bind h
  obtain ⟨pq, -, h⟩ := ex_bind h
  obtain ⟨tail, -, h⟩ := ex_bind h
  have hl : f1 ++ (splitEntry F.shared.blocksInOrder p1).toList ++ cF ++ cO ++
      carryPair pq.1 pq.2 ((m1.filter fun m => m.label == "Omega").filter (!·.masks)) none ++
      (ownFreshIn F.shared.blocksInOrder).map (·.carry tail) = l := Except.ok.inj h
  have hm : ∀ m ∈ m1, m.sender = { place := sendPlace 5, part := 0 } →
      (m.start, m.count) ∈ [((⟨0, 0⟩, ⟨0, first⟩) : Due × Due), (⟨0, first⟩, ⟨0, len⟩)] :=
    fun m hmem hsend => by
      rcases sent_at_omega hX hS hN hm1 m hmem hsend with q | q
      · rw [q]
        exact List.Mem.head _
      · rw [q]
        exact List.Mem.tail _ (List.Mem.head _)
  have k1 := folds_not_omega hX hS hN hf1
  obtain ⟨e₀, hsp, o0, s0, c0, t0⟩ := split_at_omega hX hS hN
  have k3 : ∀ e ∈ cF, CarriedRunAt { place := sendPlace 5, part := 0 }
        [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)] e :=
    carriedRunAt_of_form hm (groupCarries_form hcF)
      (fun m hmem => by
        rcases List.mem_append.1 hmem with q | q
        · exact (List.mem_filter.1 (List.mem_filter.1 q).1).1
        · exact (List.mem_filter.1 (List.mem_filter.1 q).1).1)
      fun m hmem => (List.mem_filter.1 (List.mem_of_find?_eq_some hmem)).1
  have k4 : ∀ e ∈ cO, CarriedRunAt { place := sendPlace 5, part := 0 }
        [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)] e :=
    carriedRunAt_of_form hm (groupCarries_form hcO) (fun m hmem => (List.mem_filter.1 hmem).1)
      fun m hmem => by cases hmem
  have k5 : ∀ e ∈ carryPair pq.1 pq.2
      ((m1.filter fun m => m.label == "Omega").filter (!·.masks)) none,
      CarriedRunAt { place := sendPlace 5, part := 0 }
        [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)] e :=
    carriedRunAt_of_form hm carryPair_form
      (fun m hmem => (List.mem_filter.1 (List.mem_filter.1 hmem).1).1) fun m hmem => by cases hmem
  have k6 : ∀ e ∈ (ownFreshIn F.shared.blocksInOrder).map (·.carry tail),
      CarriedRunAt { place := sendPlace 5, part := 0 }
        [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)] e := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
    exact ⟨rfl, fun hown => absurd (congrArg Addr.place hown) (own_not_at hX w hw).2⟩
  have nil_of : ∀ L : List Ahead, (∀ e ∈ L, CarriedRunAt { place := sendPlace 5, part := 0 }
        [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)] e) →
      L.filter (fun e => e.once && e.owner == ({ place := sendPlace 5, part := 0 } : Addr)) =
        [] := fun L hL => List.filter_eq_nil_iff.2 fun e he => by rw [(hL e he).1]; simp
  unfold wholeOrSpent
  rw [Bool.and_eq_true]
  constructor
  · have hs : spendersOf { B₀ with ahead := l } { place := sendPlace 5, part := 0 } = [e₀] := by
      show l.filter (fun e => e.once &&
        e.owner == ({ place := sendPlace 5, part := 0 } : Addr)) = [e₀]
      rw [← hl, hsp]
      simp only [List.filter_append, nil_of cF k3, nil_of cO k4, nil_of _ k5, nil_of _ k6,
        List.append_nil]
      have z1 : f1.filter (fun e => e.once &&
          e.owner == ({ place := sendPlace 5, part := 0 } : Addr)) = [] :=
        List.filter_eq_nil_iff.2 fun e he => by simp [k1 e he]
      rw [z1]
      simp [t0, o0]
    rw [hs]
    simp [s0, c0]
  · rw [List.all_eq_true]
    intro e he
    have he' := List.mem_filter.1 he
    have hown : e.owner = { place := sendPlace 5, part := 0 } := beq_iff_eq.1 he'.2
    have hmem : e ∈ l := he'.1
    have fin : CarriedRunAt { place := sendPlace 5, part := 0 }
        [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)] e → (e.once ||
        [((⟨0, 0⟩, ⟨0, first⟩) : Due × Due), (⟨0, first⟩, ⟨0, len⟩)].contains
          (e.start, e.count)) = true := fun hc => by
      rw [Bool.or_eq_true]
      exact Or.inr (List.contains_iff_mem.2 (hc.2 hown))
    rw [← hl, hsp] at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((((q | q) | q) | q) | q) | q
    · exact absurd hown (k1 e q)
    · rw [mem_one q, t0]
      rfl
    · exact fin (k3 e q)
    · exact fin (k4 e q)
    · exact fin (k5 e q)
    · exact fin (k6 e q)

/-! ## 4 Whoever carries stands behind the spender -/

/-- **THE CORE: IN THE SHORT LIST, AT THE OWNER ⟨"send o_omega", 0⟩: THE SPLIT's ENTRY e₀, WHICH
splitEntry RETURNS, LIES IN THE LIST AND SPENDS ONE COIN OF THAT OWNER, THE NUMBER first; ITS
SPENDER IS THE PART s THAT HOLDS THE ROUND NUMBER 7 ("SPLIT"); EVERY OTHER ENTRY CARRIES, AND IS
HANDED TO A PART THAT STANDS BEHIND s** in the description's own order of places. "Other" is by
value: that e₀ stands once in the list is not said here. -/
theorem carriers_all {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) {l : List Ahead}
    (h : sharedAhead F p1 = .ok l) :
    ∃ (s : Addr) (e₀ : Ahead), addrOfRound F.shared.blocksInOrder 7 = some s ∧
      splitEntry F.shared.blocksInOrder p1 = some e₀ ∧ e₀ ∈ l ∧
      e₀.owner = { place := sendPlace 5, part := 0 } ∧ e₀.start = ⟨0, first⟩ ∧
      e₀.count = ⟨0, 1⟩ ∧ e₀.spender = s ∧
      e₀.once = true ∧ ∀ k ∈ l, k.owner = { place := sendPlace 5, part := 0 } →
        k = e₀ ∨ (k.once = false ∧ StandsBehind (orderOf F) s k.spender) := by
  obtain ⟨l₁, l₂, s, hpl2, h7, hs1, hix, hlate⟩ := rounds_behind_nine hX
  have hnd := orderOf_nodup hpl
  have hord : orderOf F = (F.first.blocksInOrder.map (·.place) ++ l₁) ++
      (l₂ ++ F.second.blocksInOrder.map (·.place)) := by
    unfold orderOf
    rw [hpl2]
    simp
  have hdis := (List.nodup_append.1 (hord ▸ hnd)).2.2
  -- a part at a place of the later stretch stands behind s
  have far : ∀ a : Addr, a.place ∈ l₂ ++ F.second.blocksInOrder.map (·.place) →
      StandsBehind (orderOf F) s a := fun a ha => by
    have hs' : s.place ∈ F.first.blocksInOrder.map (·.place) ++ l₁ := List.mem_append_right _ hs1
    have hno : a.place ∉ F.first.blocksInOrder.map (·.place) ++ l₁ := fun hm => hdis _ hm _ ha rfl
    exact ⟨before_places hnd hord hs' ha, by rw [hord]; exact Addr.not_before hs' hno,
      fun e => hno (by rw [e]; exact hs')⟩
  have farFold : ∀ i p q, behindFold (planOf F.shared.blocksInOrder) i = some (p, q) →
      StandsBehind (orderOf F) s p ∧ StandsBehind (orderOf F) s q := by
    intro i p q hb
    obtain ⟨e, t, ρ, hρ, hn, het, hp, hq⟩ := behindFold_rounds hb
    rw [planOf_rounds] at hρ
    rw [addrIn_planOf] at hp hq
    have h8 := fold_round_late hX hρ hn
    exact ⟨far p (List.mem_append_left _ (hlate e p h8 hp)),
      far q (List.mem_append_left _ (hlate t q (by omega) hq))⟩
  unfold sharedAhead at h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨m1, hm1, h⟩ := ex_bind h
  dsimp only at h
  obtain ⟨iF, -, h⟩ := ex_bind h
  obtain ⟨cF, hcF, h⟩ := ex_bind h
  obtain ⟨iO, -, h⟩ := ex_bind h
  obtain ⟨cO, hcO, h⟩ := ex_bind h
  obtain ⟨pq, hpq, h⟩ := ex_bind h
  obtain ⟨tail, -, h⟩ := ex_bind h
  have hl : f1 ++ (splitEntry F.shared.blocksInOrder p1).toList ++ cF ++ cO ++
      carryPair pq.1 pq.2 ((m1.filter fun m => m.label == "Omega").filter (!·.masks)) none ++
      (ownFreshIn F.shared.blocksInOrder).map (·.carry tail) = l := Except.ok.inj h
  have k1 := folds_not_omega hX hS hN hf1
  obtain ⟨e₀, hsp, o0, s0, c0, t0⟩ := split_at_omega hX hS hN
  have hmem0 : e₀ ∈ l := by
    rw [← hl, hsp]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))))
  have hsp0 : e₀.spender = s := by
    have := split_spender hsp
    rw [hix, h7] at this
    exact (Option.some.inj this).symm
  have grp : ∀ (i : Nat) (G : List SentMsg) (own : Option SentMsg) (r : List Ahead),
      groupCarries (planOf F.shared.blocksInOrder) i G own = .ok r →
      ∀ k ∈ r, k.once = false ∧ StandsBehind (orderOf F) s k.spender := by
    intro i G own r hr k hk
    obtain ⟨m, -, -, -, -, hc⟩ := groupCarries_form hr k hk
    unfold groupCarries at hr
    split at hr
    · rename_i p q hb
      rw [← Except.ok.inj hr] at hk
      obtain ⟨fp, fq⟩ := farFold i p q hb
      rcases carryPair_spender k hk with e | e
      · rw [e]
        exact ⟨hc, fp⟩
      · rw [e]
        exact ⟨hc, fq⟩
    · cases hr
  have k5 : ∀ k ∈ carryPair pq.1 pq.2
      ((m1.filter fun m => m.label == "Omega").filter (!·.masks)) none,
      k.once = false ∧ StandsBehind (orderOf F) s k.spender := by
    intro k hk
    obtain ⟨m, -, -, -, -, hc⟩ := carryPair_form k hk
    have hb := due?_ok hpq
    obtain ⟨e, t, ρ, -, -, -, hp, hq⟩ := behindFold_rounds (p := pq.1) (q := pq.2) hb
    have p2 := addrIn_place _ _ _ hp
    have q2 := addrIn_place _ _ _ hq
    rw [planOf_places] at p2 q2
    rcases carryPair_spender k hk with e' | e'
    · rw [e']
      exact ⟨hc, far _ (List.mem_append_right _ p2)⟩
    · rw [e']
      exact ⟨hc, far _ (List.mem_append_right _ q2)⟩
  refine ⟨s, e₀, h7, hsp, hmem0, o0, s0, c0, hsp0, t0, fun k hk hown => ?_⟩
  rw [← hl, hsp] at hk
  simp only [List.mem_append] at hk
  rcases hk with ((((q | q) | q) | q) | q) | q
  · exact absurd hown (k1 k q)
  · exact Or.inl (mem_one q)
  · exact Or.inr (grp _ _ _ _ hcF k q)
  · exact Or.inr (grp _ _ _ _ hcO k q)
  · exact Or.inr (k5 k q)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 q
    exact absurd (congrArg Addr.place hown) (own_not_at hX w hw).2

/-- **IN THE FRAME's OWN TERM: AT THE SPENDER NOTHING ELSE OF THE OWNER's COINS IS KNOWN**:
ProverCoinCounts.knownBy (Honest/Frame.lean) at the short list, laid into any book, is empty at the part that
holds "SPLIT". -/
theorem known_nil_of_short {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) {l : List Ahead}
    (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    ∃ s, addrOfRound F.shared.blocksInOrder 7 = some s ∧
      (∀ e ∈ spendersOf { B₀ with ahead := l } { place := sendPlace 5, part := 0 },
        e.spender = s) ∧
      ({ B₀ with ahead := l } : ProverCoinCounts).knownBy (orderOf F) { place := sendPlace 5, part := 0 } s =
        [] := by
  obtain ⟨s, e₀, h7, -, -, -, -, -, hs0, t0, hall⟩ := carriers_all hX hpl hS hN h
  refine ⟨s, h7, fun e he => ?_, List.filter_eq_nil_iff.2 fun k hk => ?_⟩
  · have he' := List.mem_filter.1 he
    have heo := he'.2
    simp only [Bool.and_eq_true, beq_iff_eq] at heo
    rcases hall e he'.1 heo.2 with q | q
    · rw [q, hs0]
    · rw [heo.1] at q
      cases q.1
  · intro hq
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at hq
    obtain ⟨⟨hko, hkn⟩, hkb⟩ := hq
    rcases hall k hk hko with q | q
    · rw [q, hs0, t0] at hkn
      simp at hkn
    · rcases hkb with b | b
      · exact q.2.2.2 b
      · rw [q.2.2.1] at b
        cases b

/-- So the short list passes the test knownBelow (Honest/K14/FreshDefs.lean), at every number. -/
theorem knownBelow_of_short {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) {l : List Ahead}
    (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) (room : Nat) :
    knownBelow { B₀ with ahead := l } (orderOf F) { place := sendPlace 5, part := 0 } room =
      true := by
  obtain ⟨s, -, hsp, hk⟩ := known_nil_of_short hX hpl hS hN h B₀
  unfold knownBelow
  rw [List.all_eq_true]
  intro e he
  rw [hsp e he, hk]
  rfl

/-- **THE SHORT LIST PASSES THE TEST ON THE ORDER**, at every run. B₀: any book; of it nothing is
read. (By the tie; the core says more: carriers_all.) -/
theorem carriers_behind {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (hS : SharedSends p1 codes sentU sentO)
    (hN : omegaNumbersB codes sentO first len = true) {l : List Ahead}
    (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) (g n : Nat) :
    behindSpenderB g n { B₀ with ahead := l } (orderOf F)
      { place := sendPlace 5, part := 0 } = true :=
  behindSpender_of_knownBelow (knownBelow_of_short hX hpl hS hN h B₀ g) n

/-! ## 5 The owner's test: at the short list, at the raw book, at the whole book -/

/-- **THE OWNER's TEST ACCEPTS THE SHORT LIST**, laid into any book: no test of a book's own is
called. -/
theorem spOwner_ok_of_short {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes sentU (Desc.K14.withOmega A.P.S).toList)
    (hN : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true) (hn : 0 < spEntries A)
    (hfit : sendingsFit A.P = true) (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S (spEntries A) (spMaskCode A).r = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    (spOwner A).ok { B₀ with ahead := l } (orderOf F) { place := sendPlace 5, part := 0 } = true :=
  spOwner_ok_of_order A (spEntries A) (whole_of_short hX hS hN h B₀)
    (carriers_behind hX hpl hS hN h B₀ _ _) hn hfit hs hP

/-- **AT THE RAW BOOK: THE BOOK THAT bookRaw RETURNS, BEFORE ANY OF ITS OWN TESTS IS ASKED**: the
short test and the owner's test accept it, and at the part that holds "SPLIT" nothing else of the
owner's coins is known. THE TYPE BEARS IT: no test of the book's own stands between. -/
theorem spOwner_ok_of_raw {Xi : Type} {F : FileDescription Xi} {p0 p2 : Johnson.G.ChainSends}
    {M : Merges} {W : ProverCoinCounts} (hW : bookRaw F p0 p1 p2 M = .ok W)
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes sentU (Desc.K14.withOmega A.P.S).toList)
    (hN : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true) (hn : 0 < spEntries A)
    (hfit : sendingsFit A.P = true) (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S (spEntries A) (spMaskCode A).r = true) :
    spWholeB A W = true ∧
      (∃ s, addrOfRound F.shared.blocksInOrder 7 = some s ∧
        W.knownBy (orderOf F) { place := sendPlace 5, part := 0 } s = []) ∧
      (spOwner A).ok W (orderOf F) { place := sendPlace 5, part := 0 } = true := by
  obtain ⟨l, hl, hfil⟩ := bookRaw_ahead_shared hW
  have h := hfil { place := sendPlace 5, part := 0 }
    (fun h => absurd (chain_first hpl _ h) (by decide))
    (fun h => absurd (chain_second hpl _ h) (by decide))
  have hc : aheadAt { W with ahead := l } { place := sendPlace 5, part := 0 } =
      aheadAt W { place := sendPlace 5, part := 0 } := h.symm
  obtain ⟨s, h7, -, hk⟩ := known_nil_of_short hX hpl hS hN hl W
  refine ⟨?_, ⟨s, h7, (knownBy_congr (orderOf F) s hc).symm.trans hk⟩,
    (spOwner_ok_congr (orderOf F) hc A (spEntries A)).symm.trans
      (spOwner_ok_of_short hX hpl A hS hN hn hfit hs hP hl W)⟩
  unfold spWholeB spStretches
  rw [← wholeOrSpent_congr hc]
  exact whole_of_short hX hS hN hl W

/-- **AND EVERY BOOK THAT bookWhole RETURNS**: it is the raw book (the frame's checked_ok): that it
has passed its own tests is not used. -/
theorem spOwner_ok_of_book {Xi : Type} {F : FileDescription Xi} {p0 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (hB : bookWhole F p0 p1 p2 M = .ok B)
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes sentU (Desc.K14.withOmega A.P.S).toList)
    (hN : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true) (hn : 0 < spEntries A)
    (hfit : sendingsFit A.P = true) (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S (spEntries A) (spMaskCode A).r = true) :
    spWholeB A B = true ∧
      (spOwner A).ok B (orderOf F) { place := sendPlace 5, part := 0 } = true := by
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨h1, -, h3⟩ := spOwner_ok_of_raw hW hX hpl A hS hN hn hfit hs hP
  exact ⟨h1, h3⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.msgDue_idle
#print axioms ProofFile.Honest.K14.sendDue_idle
#print axioms ProofFile.Honest.K14.msgAt_idle
#print axioms ProofFile.Honest.K14.msgStretch_idle
#print axioms ProofFile.Honest.K14.maskStart_idle
#print axioms ProofFile.Honest.K14.numbers_give
#print axioms ProofFile.Honest.K14.sent_at_omega
#print axioms ProofFile.Honest.K14.folds_not_omega
#print axioms ProofFile.Honest.K14.split_at_omega
#print axioms ProofFile.Honest.K14.whole_of_short
#print axioms ProofFile.Honest.K14.carriers_all
#print axioms ProofFile.Honest.K14.known_nil_of_short
#print axioms ProofFile.Honest.K14.knownBelow_of_short
#print axioms ProofFile.Honest.K14.carriers_behind
#print axioms ProofFile.Honest.K14.spOwner_ok_of_short
#print axioms ProofFile.Honest.K14.spOwner_ok_of_raw
#print axioms ProofFile.Honest.K14.spOwner_ok_of_book
