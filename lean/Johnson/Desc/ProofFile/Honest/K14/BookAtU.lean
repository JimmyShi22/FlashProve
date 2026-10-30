-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtU.lean: kind K14: **WHERE THE FRAME's SHORT LIST OF THE
BOOK's ENTRIES (sharedAhead, Honest/BookShared.lean) RETURNS l, UNDER THE PREMISES NAMED BELOW: THE
ENTRIES OF l AT THE PART AT "send o_u" ARE FOUR: ONE SPENDS THE FIRST MASK's COEFFICIENTS AND IS
HANDED TO THE FOLD's PART p; o_u's WHOLE RUN IS CARRIED TO p AND TO q, THE PART THAT SENDS WHAT THE
FOLD LEAVES; THE FIRST MASK's WHOLE RUN IS CARRIED TO q** (an equation of lists); and so, where one
test with code (foldTwoPartsB: p and q are two) accepts, the test for that part (maskOwner,
Honest/K14/MaskOwner.lean) accepts the short list, the frame's raw book and its book, at the order
of places of the IOP as written in Lean (below: the description), with none of the book's own tests
used. Five definitions, two with code; statements with their proofs. On lists of entries, numbers
and an order of places alone: no distribution occurs.

  uNumbersB codes sent k first len, uNumbers_give, fresh_flags   the test on the numbers: two
                  notices, the second alone a fold's fresh table; the makers' stretches of the two
                  messages; the mask's start
  sent_form_u     the listed messages written out: o_u's, the first mask's, then those of "Omega"
  folds_at_u      of the folds' spending entries just one has that owner; it is handed to p
  MaskFourAt l p q k first len, four_at_u   **the four entries**
  MaskCarriersAt, maskCarriers_of_four   who spends and who carries, as a form on the members of l
  behindSpender_of_carriers, known_some_of_carriers   what that weaker form alone gives: the test on
                  the order accepts; at p o_u's whole run is known
  whole_of_four, behindSpender_of_four, known_of_four   from the four entries: the short test
                  accepts; where q is not in front of p and is not p the test on the order accepts,
                  and **what is known at p (ProverCoinCounts.knownBy, Honest/Frame.lean) is one entry: o_u's
                  whole run**
  foldTwoPartsB l i   the test: behind the round i stands a fold with a sending behind it, and the
                  fold's part and the part that sends what it leaves are two. NO GENERAL LAW OF THE
                  MAKERS: at a proximity test the cut has two parts at the most
                  (Honest/BookOf.lean): at a later fold of one test the two are one part
  fold_not_before the part q is not in front of p, at the description's own order
  whole_of_short_u, maskCarriers_all, maskCarriers_behind   at the short list
  MaskAtBook A B ord p q, maskAtBook_of_four   all that is shown of a book at this owner, as a form:
                  the four entries; the three tests accept; what is known at p
  maskAtBook_of_filter   **every book whose entries at this owner are the short list's**
  maskAtBook_of_short, maskOwner_ok_of_short, maskAtBook_of_raw, maskAtBook_of_book   its cases: the
                  short list; **the raw book** (bookRaw, Honest/BookWhole.lean): before any of the
                  book's own tests is asked; the book that bookWhole returns
  maskWholeB_of_book, maskOwner_ok_of_book   at the book that bookWhole returns: by the book's own
                  tests (bookWhole_word, Honest/AtPureLaw.lean), and so without foldTwoPartsB. IN
                  THIS ONE STATEMENT (maskOwner_ok_of_book) THE FACT ON THE ORDER IS NOT SHOWN: IT
                  LIES INSIDE "bookWhole RETURNS": in the eighth of the book's eleven own tests
                  (ProverCoinCounts.clauses, Honest/Frame.lean), which alone pays the guard's clause at the
                  first mask's own carried run

What is assumed. That sharedAhead, bookRaw or bookWhole returns · SharedForm of the description's
shared list · the description's test on the places · SharedSends: what the library's list of
sendings begins with · hk: THE DECLARED ROUNDS "FOLD round" OF THE FIRST FOLD BEHIND THE SENDING ARE
AS MANY AS THE SHAPE's FIRST STAGE HAS VARIABLES · uNumbersB, and omegaNumbersB
(Honest/K14/BookAtOmega.lean: by it the split's coin is the other sending's) · foldTwoPartsB at the
round 1 · the three tests on the plan · in the last two statements (maskWholeB_of_book,
maskOwner_ok_of_book), in the place of the test on the places: that the place "send o_u" is no place
of the first or the second chain.
What is not claimed. That any of the three makers returns at any file; that any of these premises
holds at any file (at the description: Honest/K14/BookAtUHead.lean): in this file's own light the
statements may be empty. That p stands in front of q: at the description alone. THAT NONE OF THE
BOOK's OWN TESTS IS USED IS, AT THE BOOK THAT bookWhole RETURNS, A WORD ON THE PROOFS:
maskAtBook_of_raw alone bears it in its statement. The entries at the owner are had by the frame's
bookWhole_ahead_shared (Honest/BookSharedLaw.lean) and by bookRaw_ahead_shared
(Honest/K14/BookRawShared.lean). Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookAtOmega
import Johnson.Desc.ProofFile.Honest.K14.MaskWhole
import Johnson.Desc.ProofFile.Honest.K14.BookRawShared
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block FileDescription Place)
open OnBytes (Codes OracleNotice)
open ProofFile.Honest.BookShared

variable {S Cl : Type} {xs : List (Block S Cl)} {p1 : Johnson.G.ChainSends} {codes : Codes}
  {sentU sentO : List OracleNotice} {k first len firstO lenO : Nat}

/-! ## 1 The numbers; the makers' text at this owner -/

/-- **The test on the numbers**: the sending has two notices, of which the second alone is a fold's
fresh table; and by the makers' own arithmetic (msgStretch, Honest/BookCoins.lean; maskStart,
Honest/BookRows.lean) at a fold of k rounds: the first message's run begins at 0 and has first
coins, the second's begins at first and has len, all of the extension field; the mask begins at
first. -/
def uNumbersB (codes : Codes) (sent : List OracleNotice) (k first len : Nat) : Bool :=
  sent.length == 2 && freshOf sent == [1] &&
    msgStretch codes k sent 0 == some (⟨0, 0⟩, ⟨0, first⟩) &&
    msgStretch codes k sent 1 == some (⟨0, first⟩, ⟨0, len⟩) &&
    maskStart codes k sent 1 == some ⟨0, first⟩

/-- What the test on the numbers gives. -/
theorem uNumbers_give (h : uNumbersB codes sentU k first len = true) :
    sentU.length = 2 ∧ freshOf sentU = [1] ∧
      msgStretch codes k sentU 0 = some (⟨0, 0⟩, ⟨0, first⟩) ∧
      msgStretch codes k sentU 1 = some (⟨0, first⟩, ⟨0, len⟩) ∧
      maskStart codes k sentU 1 = some ⟨0, first⟩ := by
  unfold uNumbersB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The sending's two notices: the first is no fold's fresh table, the second is one. -/
theorem fresh_flags (h : uNumbersB codes sentU k first len = true) :
    ∃ n0 n1, sentU = [n0, n1] ∧ isFresh n0 = false ∧ isFresh n1 = true := by
  obtain ⟨n2, nf, -, -, -⟩ := uNumbers_give h
  match sentU, n2, nf with
  | [n0, n1], _, nf =>
    refine ⟨n0, n1, rfl, ?_⟩
    have hz : [n0, n1].zipIdx = [(n0, 0), (n1, 1)] := rfl
    unfold freshOf at nf
    rw [hz] at nf
    cases h0 : isFresh n0 <;> cases h1 : isFresh n1 <;> simp [h0, h1] at nf ⊢

/-- **The shared chain's listed messages, written out**: o_u's, the first mask's, then those of
"Omega". -/
theorem sent_form_u (hX : SharedForm xs) (hS : SharedSends p1 codes sentU sentO)
    (hk : foldK ((xs.flatMap (·.rounds)).drop 2) = some k)
    (hN : uNumbersB codes sentU k first len = true) {ms : List SentMsg}
    (h : sentIn xs p1 = .ok ms) :
    ∃ mA mB rO, ms = mA :: mB :: rO ∧
      (mA.label = "the folded row" ∧ mA.round = 1 ∧
        mA.sender = { place := sendPlace 2, part := 0 } ∧ mA.start = ⟨0, 0⟩ ∧
        mA.count = ⟨0, first⟩ ∧ mA.fresh = false) ∧
      (mB.label = "the folded row" ∧ mB.round = 1 ∧
        mB.sender = { place := sendPlace 2, part := 0 } ∧ mB.start = ⟨0, first⟩ ∧
        mB.count = ⟨0, len⟩ ∧ mB.fresh = true) ∧
      ∀ m ∈ rO, m.label = "Omega" ∧ m.sender = { place := sendPlace 5, part := 0 } := by
  obtain ⟨hc, sU, sO, rest, hs, lU, eU, lO, -, wU, wO, hr⟩ := hS
  obtain ⟨-, -, g0, g1, -⟩ := uNumbers_give hN
  obtain ⟨n0, n1, e01, f0, f1⟩ := fresh_flags hN
  obtain ⟨a1, a4, -⟩ := form_addr hX
  have hk' : foldK ((xs.flatMap (fun b : Block S Cl => b.rounds) ++ []).drop (1 + 1)) =
      some k := by
    rw [List.append_nil]
    exact hk
  unfold sentIn at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    rw [hs, form_pairs hX wU wO hr, List.mapM_cons] at hll
    obtain ⟨r1, h1, hll⟩ := ex_bind hll
    obtain ⟨rs, hrs, hll⟩ := ex_bind hll
    have ell : r1 :: rs = ll := Except.ok.inj hll
    have hrest : ∀ inner ∈ rs, ∀ m ∈ inner,
        m.label = "Omega" ∧ m.sender = ({ place := sendPlace 5, part := 0 } : Addr) := by
      refine mapM_all _ rs ?_ hrs
      intro x hx r hr'
      dsimp only at hr'
      refine mapM_all _ r ?_ hr'
      intro n _ b hb
      obtain rfl := mem_one hx
      split at hb
      · rename_i a st ha _
        rw [← Except.ok.inj hb]
        rw [a4] at ha
        exact ⟨lO, (Option.some.inj ha).symm⟩
      · cases hb
    dsimp only at h1
    have hz : sU.sent.zipIdx = [(n0, 0), (n1, 1)] := by
      rw [eU, e01]
      rfl
    rw [hz, List.mapM_cons] at h1
    obtain ⟨bA, hA, h1⟩ := ex_bind h1
    obtain ⟨t1, ht1, h1⟩ := ex_bind h1
    rw [List.mapM_cons, List.mapM_nil] at ht1
    obtain ⟨bB, hB, ht1⟩ := ex_bind ht1
    obtain ⟨nl, hnl, ht1⟩ := ex_bind ht1
    have enl : [] = nl := Except.ok.inj hnl
    have et1 : bB :: nl = t1 := Except.ok.inj ht1
    have er1 : bA :: t1 = r1 := Except.ok.inj h1
    refine ⟨bA, bB, rs.flatten, ?_, ?_, ?_, ?_⟩
    · rw [← e, ← ell, ← er1, ← et1, ← enl]
      rfl
    · split at hA
      · rename_i a st ha hst
        rw [a1] at ha
        rw [hc, eU, hk', Option.getD_some, g0] at hst
        rw [← Except.ok.inj hA, ← Option.some.inj ha, ← Option.some.inj hst]
        exact ⟨lU, rfl, rfl, rfl, rfl, f0⟩
      · cases hA
    · split at hB
      · rename_i a st ha hst
        rw [a1] at ha
        rw [hc, eU, hk', Option.getD_some, g1] at hst
        rw [← Except.ok.inj hB, ← Option.some.inj ha, ← Option.some.inj hst]
        exact ⟨lU, rfl, rfl, rfl, rfl, f1⟩
      · cases hB
    · intro m hm
      obtain ⟨inner, hin, hm⟩ := List.mem_flatten.1 hm
      exact hrest inner hin m hm

/-- **Of the folds' spending entries just one has that owner: the first; it is the run of the first
mask's coefficients, and it is handed to the fold's part.** -/
theorem folds_at_u (hX : SharedForm xs) (hS : SharedSends p1 codes sentU sentO)
    (hk : foldK ((xs.flatMap (·.rounds)).drop 2) = some k)
    (hN : uNumbersB codes sentU k first len = true) {f1 : List Ahead}
    (h : foldEntries (planOf xs) [] p1 = .ok f1) :
    ∃ e r4, f1 = e :: r4 ∧ e.owner = { place := sendPlace 2, part := 0 } ∧
      e.start = ⟨0, first⟩ ∧ e.count = ⟨0, 2 * k + 1⟩ ∧ e.once = true ∧
      (∀ p q, behindFold (planOf xs) 1 = some (p, q) → e.spender = p) ∧
      ∀ a ∈ r4, a.owner ≠ { place := sendPlace 2, part := 0 } := by
  obtain ⟨hc, sU, sO, rest, hs, -, eU, -, -, wU, wO, hr⟩ := hS
  obtain ⟨-, nf, -, -, gm⟩ := uNumbers_give hN
  obtain ⟨a1, a4, -⟩ := form_addr hX
  have hp := form_pairs hX wU wO hr
  unfold seedRounds at hp
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    rw [planOf_rounds, hs, hp, List.mapM_cons] at hll
    obtain ⟨r1, h1, hll⟩ := ex_bind hll
    obtain ⟨rs, hrs, hll⟩ := ex_bind hll
    have ell : r1 :: rs = ll := Except.ok.inj hll
    have hrest : ∀ inner ∈ rs, ∀ a ∈ inner,
        a.owner ≠ ({ place := sendPlace 2, part := 0 } : Addr) := by
      refine mapM_all _ rs ?_ hrs
      intro x hx r hr'
      refine mapM_all _ r ?_ hr'
      intro j _ b hb
      obtain rfl := mem_one hx
      split at hb
      · cases hb
      · cases hb
      · split at hb
        · rename_i o p st ho _ _
          rw [← Except.ok.inj hb]
          rw [addrIn_planOf, a4] at ho
          rw [← Option.some.inj ho]
          show ({ place := sendPlace 5, part := 0 } : Addr) ≠ _
          decide
        · cases hb
    dsimp only at h1
    rw [eU, nf, List.mapM_cons, List.mapM_nil] at h1
    obtain ⟨b, hb, h1⟩ := ex_bind h1
    obtain ⟨nl, hnl, h1⟩ := ex_bind h1
    have enl : [] = nl := Except.ok.inj hnl
    have er1 : b :: nl = r1 := Except.ok.inj h1
    refine ⟨b, rs.flatten, ?_, ?_⟩
    · rw [← e, ← ell, ← er1, ← enl]
      rfl
    · split at hb
      · cases hb
      · cases hb
      · rename_i e' k' hfb
        have hk2 := foldBehind_foldK hfb
        rw [List.append_nil, planOf_rounds] at hk2
        have ek : k' = k := Option.some.inj (hk2.symm.trans hk)
        subst ek
        split at hb
        · rename_i o p st ho hp' hst
          rw [← Except.ok.inj hb]
          rw [addrIn_planOf, a1] at ho
          rw [hc, gm] at hst
          refine ⟨(Option.some.inj ho).symm, (Option.some.inj hst).symm, rfl, rfl, ?_, ?_⟩
          · intro p₀ q₀ hpq
            obtain ⟨f, hf, hp₀⟩ := behindFold_fold hpq
            rw [List.append_nil] at hfb hp'
            have ef : f = (e', false, k') := Option.some.inj (hf.symm.trans hfb)
            rw [ef] at hp₀
            exact Option.some.inj (hp'.symm.trans hp₀)
          intro a ha
          obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
          exact hrest inner hin a ha
        · cases hb

/-! ## 2 The four entries -/

/-- **The four entries, as a form**: the entries of l with the owner ⟨"send o_u", 0⟩, in l's order:
e₁ spends the run of 2 k + 1 coins from the number first on, and is handed to p; x₁ carries o_u's
whole run to p; x₂ carries it to q; x₃ carries the first mask's whole run (len coins from the number
first on) to q. -/
def MaskFourAt (l : List Ahead) (p q : Addr) (k first len : Nat) : Prop :=
  ∃ e₁ x₁ x₂ x₃ : Ahead,
    l.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [e₁, x₁, x₂, x₃] ∧
    (e₁.once = true ∧ e₁.spender = p ∧ e₁.start = ⟨0, first⟩ ∧ e₁.count = ⟨0, 2 * k + 1⟩) ∧
    (x₁.once = false ∧ x₁.spender = p ∧ x₁.start = ⟨0, 0⟩ ∧ x₁.count = ⟨0, first⟩) ∧
    (x₂.once = false ∧ x₂.spender = q ∧ x₂.start = ⟨0, 0⟩ ∧ x₂.count = ⟨0, first⟩) ∧
    (x₃.once = false ∧ x₃.spender = q ∧ x₃.start = ⟨0, first⟩ ∧ x₃.count = ⟨0, len⟩)

/-- **THE CORE: WHERE THE SHORT LIST RETURNS l, ITS ENTRIES AT THIS OWNER ARE THE FOUR**, at the two
parts p, q that the maker's behindFold finds behind the round 1. -/
theorem four_at_u {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hS : SharedSends p1 codes sentU sentO)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some k)
    (hN : uNumbersB codes sentU k first len = true)
    (hNO : omegaNumbersB codes sentO firstO lenO = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) :
    ∃ p q, behindFold (planOf F.shared.blocksInOrder) 1 = some (p, q) ∧
      MaskFourAt l p q k first len := by
  unfold sharedAhead at h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨m1, hm1, h⟩ := ex_bind h
  dsimp only at h
  obtain ⟨iF, hiF, h⟩ := ex_bind h
  obtain ⟨cF, hcF, h⟩ := ex_bind h
  obtain ⟨iO, -, h⟩ := ex_bind h
  obtain ⟨cO, hcO, h⟩ := ex_bind h
  obtain ⟨pq, -, h⟩ := ex_bind h
  obtain ⟨tail, -, h⟩ := ex_bind h
  have hl : f1 ++ (splitEntry F.shared.blocksInOrder p1).toList ++ cF ++ cO ++
      carryPair pq.1 pq.2 ((m1.filter fun m => m.label == "Omega").filter (!·.masks)) none ++
      (ownFreshIn F.shared.blocksInOrder).map (·.carry tail) = l := Except.ok.inj h
  obtain ⟨mA, mB, rO, em, ⟨lA, rA, sA, stA, cA, fA⟩, ⟨lB, rB, sB, stB, cB, fB⟩, hrO⟩ :=
    sent_form_u hX hS hk hN hm1
  -- the messages under the two labels
  have hfr : m1.filter (fun m => m.label == "the folded row") = [mA, mB] := by
    have z : rO.filter (fun m => m.label == "the folded row") = [] :=
      List.filter_eq_nil_iff.2 fun m hm => by rw [(hrO m hm).1]; decide
    rw [em, List.filter_cons, List.filter_cons, z, lA, lB]
    rfl
  have noOm : ∀ m ∈ m1.filter (fun m => m.label == "Omega"),
      m.sender ≠ { place := sendPlace 2, part := 0 } := by
    intro m hm hsend
    have hm' := List.mem_filter.1 hm
    have hlab : m.label = "Omega" := beq_iff_eq.1 hm'.2
    rw [em] at hm'
    rcases List.mem_cons.1 hm'.1 with rfl | g
    · rw [lA] at hlab
      exact absurd hlab (by decide)
    · rcases List.mem_cons.1 g with rfl | g
      · rw [lB] at hlab
        exact absurd hlab (by decide)
      · rw [(hrO m g).2] at hsend
        exact absurd hsend (by decide)
  rw [hfr] at hiF hcF
  have eiF : iF = 1 := by
    have h9 : some mA.round = some iF := due?_ok hiF
    rw [← Option.some.inj h9, rA]
  subst eiF
  have hG : [mA, mB].filter (!·.fresh) = [mA] := by
    rw [List.filter_cons, List.filter_cons, fA, fB]
    rfl
  have hown : [mA, mB].find? (·.fresh) = some mB := by
    rw [List.find?_cons, fA, List.find?_cons, fB]
  rw [hG, hown] at hcF
  unfold groupCarries at hcF
  split at hcF
  · rename_i p q hb
    have ecF := Except.ok.inj hcF
    obtain ⟨e₁, r4, ef1, o1, s1, c1, t1, hsp1, k1⟩ := folds_at_u hX hS hk hN hf1
    obtain ⟨e₀, hsp, o0, -, -, -⟩ := split_at_omega hX hS hNO
    -- a list none of whose members has the owner
    have nilP : ∀ L : List Ahead, (∀ x ∈ L, x.owner ≠ { place := sendPlace 2, part := 0 }) →
        L.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [] :=
      fun L hL => List.filter_eq_nil_iff.2 fun x hx => by
        rw [beq_iff_eq]
        exact hL x hx
    have keep : ∀ (x : Ahead) (L : List Ahead), x.owner = { place := sendPlace 2, part := 0 } →
        (x :: L).filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) =
          x :: L.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) :=
      fun x L hx => by
        rw [List.filter_cons, hx]
        rfl
    have z1 : (e₁ :: r4).filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) =
        [e₁] := by rw [keep _ _ o1, nilP r4 k1]
    have z2 : (some e₀).toList.filter
        (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [] :=
      nilP _ fun x hx => by
        rw [mem_one hx, o0]
        decide
    have zX : ∀ a : Addr, (((m1.filter fun m => m.label == "Omega").filter (·.masks)).map
        (·.carry a)).filter
        (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [] :=
      fun a => nilP _ fun x hx => by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
        exact noOm m (List.mem_filter.1 hm).1
    have z3 : cF.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) =
        [mA.carry p, mA.carry q, mB.carry q] := by
      rw [← ecF]
      unfold carryPair
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_append, List.map_nil,
        Option.toList_some]
      rw [keep _ _ (show (mA.carry p).owner = _ from sA), List.filter_append, zX p,
        List.nil_append, keep _ _ (show (mA.carry q).owner = _ from sA), List.filter_append, zX q,
        List.nil_append, keep _ _ (show (mB.carry q).owner = _ from sB)]
      rfl
    have z4 : cO.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [] :=
      nilP _ fun x hx hown' => by
        obtain ⟨m, hm, e1, -, -, -⟩ := groupCarries_form hcO x hx
        rcases hm with hm | hm
        · exact noOm m hm (e1 ▸ hown')
        · cases hm
    have z5 : (carryPair pq.1 pq.2 ((m1.filter fun m => m.label == "Omega").filter (!·.masks))
        none).filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [] :=
      nilP _ fun x hx hown' => by
        obtain ⟨m, hm, e1, -, -, -⟩ := carryPair_form x hx
        rcases hm with hm | hm
        · exact noOm m (List.mem_filter.1 hm).1 (e1 ▸ hown')
        · cases hm
    have z6 : ((ownFreshIn F.shared.blocksInOrder).map (·.carry tail)).filter
        (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = [] :=
      nilP _ fun x hx hown' => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        exact (own_not_at hX w hw).1 (congrArg Addr.place hown')
    refine ⟨p, q, hb, e₁, mA.carry p, mA.carry q, mB.carry q, ?_, ⟨t1, hsp1 p q hb, s1, c1⟩,
      ⟨rfl, rfl, stA, cA⟩, ⟨rfl, rfl, stA, cA⟩, ⟨rfl, rfl, stB, cB⟩⟩
    rw [← hl, hsp, ef1]
    simp only [List.filter_append]
    rw [z1, z2, z3, z4, z5, z6]
    rfl
  · cases hcF

/-- **Who spends and who carries, as a form**: in the list l, at the owner ⟨"send o_u", 0⟩: one
entry e₁ spends: the run of 2 k + 1 coins from the number first on, and it is handed to p; an entry
x₀ carries o_u's whole run to p; and every other entry carries: o_u's whole run, to p or to q; or
the first mask's whole run (len coins from the number first on), TO q. -/
def MaskCarriersAt (l : List Ahead) (p q : Addr) (k first len : Nat) : Prop :=
  ∃ e₁ x₀ : Ahead,
    (e₁ ∈ l ∧ e₁.owner = { place := sendPlace 2, part := 0 } ∧ e₁.once = true ∧ e₁.spender = p ∧
      e₁.start = ⟨0, first⟩ ∧ e₁.count = ⟨0, 2 * k + 1⟩) ∧
    (x₀ ∈ l ∧ x₀.owner = { place := sendPlace 2, part := 0 } ∧ x₀.once = false ∧ x₀.spender = p ∧
      x₀.start = ⟨0, 0⟩ ∧ x₀.count = ⟨0, first⟩) ∧
    ∀ x ∈ l, x.owner = { place := sendPlace 2, part := 0 } → x = e₁ ∨ (x.once = false ∧
      ((x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, first⟩ ∧ (x.spender = p ∨ x.spender = q)) ∨
        (x.start = ⟨0, first⟩ ∧ x.count = ⟨0, len⟩ ∧ x.spender = q)))

/-- The four entries have that form. -/
theorem maskCarriers_of_four {l : List Ahead} {p q : Addr}
    (h : MaskFourAt l p q k first len) : MaskCarriersAt l p q k first len := by
  obtain ⟨e₁, x₁, x₂, x₃, hl, ⟨t1, p1', s1, c1⟩, ⟨t2, p2, s2, c2⟩, ⟨t3, p3, s3, c3⟩,
    ⟨t4, p4, s4, c4⟩⟩ := h
  have mem : ∀ x, x ∈ [e₁, x₁, x₂, x₃] → x ∈ l ∧ x.owner = { place := sendPlace 2, part := 0 } := by
    intro x hx
    rw [← hl] at hx
    exact ⟨(List.mem_filter.1 hx).1, beq_iff_eq.1 (List.mem_filter.1 hx).2⟩
  obtain ⟨m1, o1⟩ := mem e₁ (List.Mem.head _)
  obtain ⟨m2, o2⟩ := mem x₁ (List.Mem.tail _ (List.Mem.head _))
  refine ⟨e₁, x₁, ⟨m1, o1, t1, p1', s1, c1⟩, ⟨m2, o2, t2, p2, s2, c2⟩, fun x hx hown => ?_⟩
  have hx' : x ∈ [e₁, x₁, x₂, x₃] := by
    rw [← hl]
    exact List.mem_filter.2 ⟨hx, by rw [hown]; exact beq_self_eq_true _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨t2, Or.inl ⟨s2, c2, Or.inl p2⟩⟩
  · exact Or.inr ⟨t3, Or.inl ⟨s3, c3, Or.inr p3⟩⟩
  · exact Or.inr ⟨t4, Or.inr ⟨s4, c4, p4⟩⟩

/-- **From the form to the test on the order**, at every order of places in which q is not in front
of p, where q is not p. B₀: any book; of it nothing is read. -/
theorem behindSpender_of_carriers {l : List Ahead} {p q : Addr} {ord : List Place}
    (hC : MaskCarriersAt l p q k first len) (hbe : q.before ord p = false) (hne : q ≠ p)
    (B₀ : ProverCoinCounts) :
    behindSpenderB first len { B₀ with ahead := l } ord { place := sendPlace 2, part := 0 } =
      true := by
  obtain ⟨e₁, x₀, ⟨-, -, t1, hsp1, -, -⟩, -, all⟩ := hC
  unfold behindSpenderB
  rw [List.all_eq_true]
  intro e he
  have he' := List.mem_filter.1 he
  have heo := he'.2
  simp only [Bool.and_eq_true, beq_iff_eq] at heo
  have ee : e = e₁ := by
    rcases all e he'.1 heo.2 with g | g
    · exact g
    · rw [heo.1] at g
      cases g.1
  rw [List.all_eq_true]
  intro x hx
  have hx' := List.mem_filter.1 hx
  rcases all x hx'.1 (beq_iff_eq.1 hx'.2) with g | ⟨g0, ⟨a1, a2, -⟩ | ⟨-, -, g⟩⟩
  · rw [g, t1]
    rfl
  · rw [g0, a1, a2]
    simp [meets]
  · rw [g0, g, ee, hsp1, hbe]
    simp [hne]

/-- **In the frame's own term: something is known at the part that spends**: o_u's whole run. -/
theorem known_some_of_carriers {l : List Ahead} {p q : Addr}
    (hC : MaskCarriersAt l p q k first len) (ord : List Place) (B₀ : ProverCoinCounts) :
    ∃ x ∈ ({ B₀ with ahead := l } : ProverCoinCounts).knownBy ord { place := sendPlace 2, part := 0 } p,
      x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, first⟩ := by
  obtain ⟨e₁, x₀, -, ⟨hx, ho, hc, hs, a1, a2⟩, -⟩ := hC
  refine ⟨x₀, List.mem_filter.2 ⟨hx, ?_⟩, a1, a2⟩
  rw [ho, hs, hc]
  simp

/-- **From the four entries: the short test accepts.** B₀: any book; of it nothing is read. -/
theorem whole_of_four {l : List Ahead} {p q : Addr} (h : MaskFourAt l p q k first len)
    (B₀ : ProverCoinCounts) :
    wholeOrSpent ⟨0, first⟩ ⟨0, 2 * k + 1⟩ [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)]
      { B₀ with ahead := l } { place := sendPlace 2, part := 0 } = true := by
  obtain ⟨e₁, x₁, x₂, x₃, hl, ⟨t1, -, s1, c1⟩, ⟨t2, -, s2, c2⟩, ⟨t3, -, s3, c3⟩,
    ⟨t4, -, s4, c4⟩⟩ := h
  have ha : aheadAt { B₀ with ahead := l } { place := sendPlace 2, part := 0 } =
      [e₁, x₁, x₂, x₃] := hl
  unfold wholeOrSpent
  rw [spenders_of_aheadAt, ha]
  simp [t1, t2, t3, t4, s1, c1, s2, c2, s3, c3, s4, c4]

/-- **From the four entries: the test on the order accepts**, at every order of places in which q is
not in front of p, where q is not p. -/
theorem behindSpender_of_four {l : List Ahead} {p q : Addr} {ord : List Place}
    (h : MaskFourAt l p q k first len) (hbe : q.before ord p = false) (hne : q ≠ p) (B₀ : ProverCoinCounts) :
    behindSpenderB first len { B₀ with ahead := l } ord { place := sendPlace 2, part := 0 } =
      true := by
  obtain ⟨e₁, x₁, x₂, x₃, hl, ⟨t1, p1', -, -⟩, ⟨t2, -, s2, c2⟩, ⟨t3, -, s3, c3⟩,
    ⟨t4, p4, -, -⟩⟩ := h
  have ha : aheadAt { B₀ with ahead := l } { place := sendPlace 2, part := 0 } =
      [e₁, x₁, x₂, x₃] := hl
  unfold behindSpenderB
  rw [spenders_of_aheadAt, ha]
  simp [t1, t2, t3, t4, s2, c2, s3, c3, p1', p4, hbe, hne, meets]

/-- **From the four entries, in the frame's own term: what is known at p is one entry: o_u's whole
run**, at every order of places in which q is not in front of p, where q is not p. -/
theorem known_of_four {l : List Ahead} {p q : Addr} {ord : List Place}
    (h : MaskFourAt l p q k first len) (hbe : q.before ord p = false) (hne : q ≠ p) (B₀ : ProverCoinCounts) :
    ∃ x, ({ B₀ with ahead := l } : ProverCoinCounts).knownBy ord { place := sendPlace 2, part := 0 } p = [x] ∧
      x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, first⟩ := by
  obtain ⟨e₁, x₁, x₂, x₃, hl, ⟨t1, p1', -, -⟩, ⟨t2, p2, s2, c2⟩, ⟨t3, p3, -, -⟩,
    ⟨t4, p4, -, -⟩⟩ := h
  have ha : aheadAt { B₀ with ahead := l } { place := sendPlace 2, part := 0 } =
      [e₁, x₁, x₂, x₃] := hl
  refine ⟨x₁, ?_, s2, c2⟩
  rw [knownBy_of_aheadAt, ha]
  simp [t1, t2, t3, t4, p1', p2, p3, p4, hbe, hne]

/-! ## 3 The short list, the raw book, the book -/

/-- **The test**: behind the round i stands a fold with a sending behind it, and the fold's part and
the part that sends what it leaves are two. -/
def foldTwoPartsB (l : List PlanB) (i : Nat) : Bool := (behindFold l i).any fun pq => pq.1 != pq.2

/-- The part that sends what the fold leaves is not in front of the fold's part, at the
description's own order of places. -/
theorem fold_not_before {Xi : Type} {F : FileDescription Xi} (hpl : F.placesOk = true) {i : Nat}
    {p q : Addr} (hb : behindFold (planOf F.shared.blocksInOrder) i = some (p, q)) :
    q.before (orderOf F) p = false := by
  obtain ⟨e, t, ρ, -, -, het, hp, hq⟩ := behindFold_rounds hb
  rw [addrIn_planOf] at hp hq
  exact addr_not_before F.shared.blocksInOrder _ _ e t p q (orderOf_nodup hpl) (Nat.le_of_lt het) hp hq

/-- **The short list passes the short test**, under the premises named. B₀: any book; of it nothing
is read. -/
theorem whole_of_short_u {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hS : SharedSends p1 codes sentU sentO)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some k)
    (hN : uNumbersB codes sentU k first len = true)
    (hNO : omegaNumbersB codes sentO firstO lenO = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    wholeOrSpent ⟨0, first⟩ ⟨0, 2 * k + 1⟩ [(⟨0, 0⟩, ⟨0, first⟩), (⟨0, first⟩, ⟨0, len⟩)]
      { B₀ with ahead := l } { place := sendPlace 2, part := 0 } = true := by
  obtain ⟨p, q, -, h4⟩ := four_at_u hX hS hk hN hNO h
  exact whole_of_four h4 B₀

/-- **Who spends and who carries, at the short list**: p and q are the two parts that the maker's
behindFold finds behind the round 1; q is not in front of p, and by the test foldTwoPartsB it is
not p. -/
theorem maskCarriers_all {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (hS : SharedSends p1 codes sentU sentO)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some k)
    (hN : uNumbersB codes sentU k first len = true)
    (hNO : omegaNumbersB codes sentO firstO lenO = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) :
    ∃ p q, behindFold (planOf F.shared.blocksInOrder) 1 = some (p, q) ∧
      q.before (orderOf F) p = false ∧ q ≠ p ∧ MaskCarriersAt l p q k first len := by
  obtain ⟨p, q, hb, h4⟩ := four_at_u hX hS hk hN hNO h
  have hne : q ≠ p := by
    unfold foldTwoPartsB at h2
    rw [hb] at h2
    have : (p != q) = true := h2
    exact fun e => (bne_iff_ne.1 this) e.symm
  exact ⟨p, q, hb, fold_not_before hpl hb, hne, maskCarriers_of_four h4⟩

/-- **The short list passes the test on the order**, at the first mask's whole run. B₀: any book; of
it nothing is read. -/
theorem maskCarriers_behind {Xi : Type} {F : FileDescription Xi} (hX : SharedForm F.shared.blocksInOrder)
    (hpl : F.placesOk = true) (hS : SharedSends p1 codes sentU sentO)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some k)
    (hN : uNumbersB codes sentU k first len = true)
    (hNO : omegaNumbersB codes sentO firstO lenO = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    behindSpenderB first len { B₀ with ahead := l } (orderOf F)
      { place := sendPlace 2, part := 0 } = true := by
  obtain ⟨p, q, hb, h4⟩ := four_at_u hX hS hk hN hNO h
  have hne : q ≠ p := by
    unfold foldTwoPartsB at h2
    rw [hb] at h2
    have : (p != q) = true := h2
    exact fun e => (bne_iff_ne.1 this) e.symm
  exact behindSpender_of_four h4 (fold_not_before hpl hb) hne B₀

/-- **All that is shown of a book at this owner, as a form**: its entries there are the four; the
short test, the test on the order at the first mask's whole run, and the owner's test accept it; and
what is known at p is one entry: o_u's whole run. -/
def MaskAtBook (A : SendPub) (B : ProverCoinCounts) (ord : List Place) (p q : Addr) : Prop :=
  MaskFourAt B.ahead p q (maskRounds A) (maskFirstCoin A) (maskRun A).2 ∧
    maskWholeB A B = true ∧
    behindSpenderB (maskRun A).1 (maskRun A).2 B ord { place := sendPlace 2, part := 0 } = true ∧
    (∃ x, B.knownBy ord { place := sendPlace 2, part := 0 } p = [x] ∧ x.start = ⟨0, 0⟩ ∧
      x.count = ⟨0, maskFirstCoin A⟩) ∧
    (maskOwner A).ok B ord { place := sendPlace 2, part := 0 } = true

/-- **From the four entries to all of it**, at every order of places in which q is not in front of
p, where q is not p and the three tests on the plan accept. -/
theorem maskAtBook_of_four {B : ProverCoinCounts} {ord : List Place} {p q : Addr} (A : SendPub)
    (h4 : MaskFourAt B.ahead p q (maskRounds A) (maskFirstCoin A) (maskRun A).2)
    (hbe : q.before ord p = false) (hne : q ≠ p)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) : MaskAtBook A B ord p q := by
  have hA : maskWholeB A B = true := whole_of_four h4 B
  have hO : behindSpenderB (maskRun A).1 (maskRun A).2 B ord
      { place := sendPlace 2, part := 0 } = true := behindSpender_of_four h4 hbe hne B
  exact ⟨h4, hA, hO, known_of_four h4 hbe hne B, maskOwner_ok_of_order A hA hO hfit hm hs⟩

/-- **Every book whose entries at this owner are the short list's**: all of it, at the description's
own order of places. None of a book's own tests is used. -/
theorem maskAtBook_of_filter {Xi : Type} {F : FileDescription Xi}
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) {B : ProverCoinCounts}
    (hf : B.ahead.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) =
      l.filter fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) :
    ∃ p q, behindFold (planOf F.shared.blocksInOrder) 1 = some (p, q) ∧
      MaskAtBook A B (orderOf F) p q := by
  obtain ⟨p, q, hb, e₁, x₁, x₂, x₃, hl4, rest⟩ := four_at_u hX hS hk hN hNO h
  have hne : q ≠ p := by
    unfold foldTwoPartsB at h2
    rw [hb] at h2
    have : (p != q) = true := h2
    exact fun e => (bne_iff_ne.1 this) e.symm
  exact ⟨p, q, hb, maskAtBook_of_four A ⟨e₁, x₁, x₂, x₃, hf.trans hl4, rest⟩
    (fold_not_before hpl hb) hne hfit hm hs⟩

/-- **At the short list**, laid into any book. -/
theorem maskAtBook_of_short {Xi : Type} {F : FileDescription Xi}
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    ∃ p q, behindFold (planOf F.shared.blocksInOrder) 1 = some (p, q) ∧
      MaskAtBook A { B₀ with ahead := l } (orderOf F) p q :=
  maskAtBook_of_filter hX hpl A hS hk hN hNO h2 hfit hm hs h rfl

/-- The owner's test accepts the short list, laid into any book: none of a book's own
tests is used. -/
theorem maskOwner_ok_of_short {Xi : Type} {F : FileDescription Xi}
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true)
    {l : List Ahead} (h : sharedAhead F p1 = .ok l) (B₀ : ProverCoinCounts) :
    (maskOwner A).ok { B₀ with ahead := l } (orderOf F) { place := sendPlace 2, part := 0 } =
      true := by
  obtain ⟨p, q, -, -, -, -, -, hok⟩ := maskAtBook_of_short hX hpl A hS hk hN hNO h2 hfit hm hs h B₀
  exact hok

/-- **AT THE RAW BOOK: THE BOOK THAT bookRaw RETURNS, BEFORE ANY OF ITS OWN TESTS IS ASKED.** -/
theorem maskAtBook_of_raw {Xi : Type} {F : FileDescription Xi} {p0 p2 : Johnson.G.ChainSends}
    {M : Merges} {W : ProverCoinCounts} (hW : bookRaw F p0 p1 p2 M = .ok W)
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) :
    ∃ p q, behindFold (planOf F.shared.blocksInOrder) 1 = some (p, q) ∧
      MaskAtBook A W (orderOf F) p q := by
  obtain ⟨l, hl, hfil⟩ := bookRaw_ahead_shared hW
  exact maskAtBook_of_filter hX hpl A hS hk hN hNO h2 hfit hm hs hl
    (hfil { place := sendPlace 2, part := 0 }
      (fun h => absurd (chain_first hpl _ h) (by decide))
      (fun h => absurd (chain_second hpl _ h) (by decide)))

/-- **At the book that bookWhole returns**: by the same steps: none of the book's own tests is
used. -/
theorem maskAtBook_of_book {Xi : Type} {F : FileDescription Xi} {p0 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (hB : bookWhole F p0 p1 p2 M = .ok B)
    (hX : SharedForm F.shared.blocksInOrder) (hpl : F.placesOk = true) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true)
    (h2 : foldTwoPartsB (planOf F.shared.blocksInOrder) 1 = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) :
    ∃ p q, behindFold (planOf F.shared.blocksInOrder) 1 = some (p, q) ∧
      MaskAtBook A B (orderOf F) p q := by
  obtain ⟨l, hl, hfil⟩ := bookWhole_ahead_shared hB
  exact maskAtBook_of_filter hX hpl A hS hk hN hNO h2 hfit hm hs hl
    (hfil { place := sendPlace 2, part := 0 }
      (fun h => absurd (chain_first hpl _ h) (by decide))
      (fun h => absurd (chain_second hpl _ h) (by decide)))

/-- **Where bookWhole returns a book, that book passes maskWholeB**, UNDER THE PREMISES NAMED: the
form of the shared list; the place is no place of the other two chains; what the list of sendings
begins with; hk: the fold's declared rounds are as many as the shape's first stage has variables;
the two tests on numbers. -/
theorem maskWholeB_of_book {Xi : Type} {F : FileDescription Xi} {p0 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (hB : bookWhole F p0 p1 p2 M = .ok B)
    (hX : SharedForm F.shared.blocksInOrder) (h1 : sendPlace 2 ∉ F.first.blocksInOrder.map (·.place))
    (h3 : sendPlace 2 ∉ F.second.blocksInOrder.map (·.place)) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true) : maskWholeB A B = true := by
  obtain ⟨l, hl, hfil⟩ := bookWhole_ahead_shared hB
  have h := hfil { place := sendPlace 2, part := 0 } h1 h3
  have hc : aheadAt { B with ahead := l } { place := sendPlace 2, part := 0 } =
      aheadAt B { place := sendPlace 2, part := 0 } := h.symm
  unfold maskWholeB maskStretches
  rw [← wholeOrSpent_congr hc]
  exact whole_of_short_u hX hS hk hN hNO hl B

/-- **So the owner's test accepts at the book that bookWhole returns**, at the description's own
order of places, under the same premises and the three tests on the plan: here by the book's own
tests (bookWhole_word, Honest/AtPureLaw.lean), and so without the test foldTwoPartsB: THE FACT ON
THE ORDER IS NOT SHOWN HERE: IT LIES INSIDE THE PREMISE, in the eighth of the book's eleven own
tests. -/
theorem maskOwner_ok_of_book {Xi : Type} {F : FileDescription Xi} {p0 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (hB : bookWhole F p0 p1 p2 M = .ok B)
    (hX : SharedForm F.shared.blocksInOrder) (h1 : sendPlace 2 ∉ F.first.blocksInOrder.map (·.place))
    (h3 : sendPlace 2 ∉ F.second.blocksInOrder.map (·.place)) (A : SendPub)
    (hS : SharedSends p1 A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList
      (Desc.K14.withOmega A.P.S).toList)
    (hk : foldK ((F.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds A))
    (hN : uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A)
      (maskFirstCoin A) (maskRun A).2 = true)
    (hNO : omegaNumbersB A.P.codes (Desc.K14.withOmega A.P.S).toList (spFirstCoin A)
      (spEntries A + 1 + (spMaskCode A).r) = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) :
    (maskOwner A).ok B (orderOf F) { place := sendPlace 2, part := 0 } = true :=
  maskOwner_ok_of_whole A (bookWhole_word hB) (maskWholeB_of_book hB hX h1 h3 A hS hk hN hNO) hfit
    hm hs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.uNumbers_give
#print axioms ProofFile.Honest.K14.fresh_flags
#print axioms ProofFile.Honest.K14.sent_form_u
#print axioms ProofFile.Honest.K14.folds_at_u
#print axioms ProofFile.Honest.K14.four_at_u
#print axioms ProofFile.Honest.K14.maskCarriers_of_four
#print axioms ProofFile.Honest.K14.behindSpender_of_carriers
#print axioms ProofFile.Honest.K14.known_some_of_carriers
#print axioms ProofFile.Honest.K14.whole_of_four
#print axioms ProofFile.Honest.K14.behindSpender_of_four
#print axioms ProofFile.Honest.K14.known_of_four
#print axioms ProofFile.Honest.K14.fold_not_before
#print axioms ProofFile.Honest.K14.whole_of_short_u
#print axioms ProofFile.Honest.K14.maskCarriers_all
#print axioms ProofFile.Honest.K14.maskCarriers_behind
#print axioms ProofFile.Honest.K14.maskAtBook_of_four
#print axioms ProofFile.Honest.K14.maskAtBook_of_filter
#print axioms ProofFile.Honest.K14.maskAtBook_of_short
#print axioms ProofFile.Honest.K14.maskOwner_ok_of_short
#print axioms ProofFile.Honest.K14.maskAtBook_of_raw
#print axioms ProofFile.Honest.K14.maskAtBook_of_book
#print axioms ProofFile.Honest.K14.maskWholeB_of_book
#print axioms ProofFile.Honest.K14.maskOwner_ok_of_book
