-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SharedAheadOwners.lean: AT THE WRITTEN SHORT LIST (writtenShort,
Honest/K14/SharedAheadWritten.lean), LAID INTO ANY BOOK, AT THE ORDER OF THE LIBRARY's WRITTEN
DESCRIPTION's PLACES AND AT THE WRITTEN SIZES, BOTH SHORT TESTS, BOTH TESTS ON THE ORDER AND BOTH
OWNERS' TESTS ACCEPT: BY THE GENERAL LAWS, CALLED: SO THESE LAWS' PREMISE "sharedAhead F p1 = .ok l"
IS MET AT ONE VALUE AT LEAST, A WRITTEN ONE; THAT ANY DESCRIPTION HAS THESE ROUNDS, THIS CUT OR
THESE SIZES IS NO THEOREM HERE. Definitions with code and statements, each with its proof.

  namesAre, sharedFormB, namesAre_none, namesAre_one, namesAre_two, sharedForm_of_test   A TEST WITH
                  CODE for SharedForm (Honest/K14/BookAtShared.lean), general in the list, and its
                  law, in the one direction that is used: where the test accepts, the form holds
  form_written, form_bites   it accepts the written description's shared list; it rejects that list
                  without its first member, and with its eighth and ninth members in the other order
  atWritten, shapesFit_written   the public data at the library's own written parameters of the
                  shared chain (p14W, Johnson/AtFull/Desc/LaterSeats.lean); the tests on the shapes
                  accept there
  omega_numbers_written, u_numbers_written, numbers_tie   the tests on the numbers accept there; the
                  numbers, written out: 42,853 and 216; 7, 10,808 and 167
  foldK_at_written, twoParts_at_written   the two closed facts on the written rounds that the laws
                  at "send o_u" ask
  whole_omega_written, order_omega_written, spOwner_written   **at "send o_omega"**: whole_of_short,
                  carriers_behind, spOwner_ok_of_short, CALLED
  split_part_written, behind_omega_written, behind_omega_named,
  known_omega_written   **"behind", typed, there**: carriers_all, CALLED: the entry that the frame's
                  splitEntry yields lies in the list and spends, its spender holds the round
                  number 7 ("SPLIT": part 0 at the piece 8, by evaluation), and every other entry
                  of that owner is handed to a part that stands behind it; behind_omega_named: that
                  entry by its written value (splitEntryWritten, Honest/K14/SplitEntryWritten.lean);
                  known_nil_of_short, CALLED: in the frame's own term nothing else of the owner's
                  coins is known at that part
  whole_u_written, order_u_written, maskOwner_written   **at "send o_u"**: whole_of_short_u,
                  maskCarriers_behind, maskOwner_ok_of_short, CALLED
  known_u_written   mask_known_at_fold, CALLED: what is known at the fold's part is o_u's whole run
  fold_parts_written, carriers_u_written   maskCarriers_all, CALLED: who spends and who carries at
                  that owner, as a form; the fold's part and the part that sends what the fold
                  leaves are parts 0 and 1 at the piece 9, by evaluation
  maskAtBook_written   maskAtBook_of_short, CALLED: all that is shown of a book at that owner, as
                  one form (MaskAtBook, Honest/K14/BookAtU.lean): its entries there are four
  earlyShort, earlyMask, order_bites   THE TESTS ON THE ORDER CAN FAIL AT THIS LIST, by evaluation,
                  at the shared chain's own order: earlyShort hands what part 0 of the first test's
                  place carries (one entry of each owner) to the part at "LIN zeta": the test at
                  "send o_omega" rejects it; THE TEST AT "send o_u" ACCEPTS IT (the entry of that
                  owner holds no coin of the first mask); earlyMask hands the first mask's whole run
                  to that part: the test at "send o_u" rejects it

Which are called and which evaluated. Eleven statements on writtenShort are general laws, called
(ten of the eleven laws have the premise on sharedAhead; the eleventh, mask_known_at_fold, is paid
through two of them); every premise is a closed fact: by the kernel here (form_written,
shapesFit_written, foldK_at_written, twoParts_at_written), by the library (wp_placesOk), or by
another file of this kind (sharedSends_written, headNumbers_written, uNumbers_written,
sharedAhead_written). The negative lines are evaluations.

Limits. FACTS ON WRITTEN VALUES: no member under the library's head. That the head's own parameters
of the shared chain are p14W is the library's p14_written (Johnson/AtFull/Desc/SharedShare.lean),
under four premises by field, which are not paid here. B0 is any book: of it nothing
is read: no test of a book's own is called, and that any maker returns a book is not said. The
owners' tests are tests: what follows from their yes is the owners' laws' to say. Nothing on what is
or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SharedAheadWritten
import Johnson.Desc.ProofFile.Honest.K14.SplitEntryWritten
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten
import Johnson.Desc.ProofFile.Honest.K14.BookAtUHead
import Johnson.AtFull.ProofPlan.At.PlacesOk
import Johnson.AtFull.Desc.LaterSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open VerifiableInference.PlanWritten (proofSizedFull)
open P2Law.ProofPlan (WP wp_placesOk)
open Johnson.G (proofSendsFull)
open Johnson.AtFull.Desc (p14W)

/-! ## A test with code for SharedForm -/

variable {S Cl : Type}

/-- A sub-protocol's declared rounds have these names, in order. -/
def namesAre (b : Block S Cl) (l : List String) : Bool := b.rounds.map (·.entry.name) == l

/-- **The test**: what SharedForm says of a list's first nine members and of the places. (Proved
below: where it accepts, the form holds; the converse is not typed.) -/
def sharedFormB (xs : List (Block S Cl)) : Bool :=
  match xs with
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl =>
    namesAre x0 [] && namesAre x1 ["LIN point"] && namesAre x2 ["SEND seed", "SEND answer"] &&
      namesAre x3 [] && namesAre x4 ["LOC"] && namesAre x5 ["SEND seed", "SEND answer"] &&
      namesAre x6 [] && namesAre x7 ["LIN zeta"] && namesAre x8 ["SPLIT"] &&
      decide (x2.place = sendPlace 2) && decide (x5.place = sendPlace 5) &&
      ((x6 :: x7 :: x8 :: tl).all fun y =>
        decide (y.place ≠ sendPlace 5) && decide (y.place ≠ sendPlace 2)) &&
      ([x0, x1, x3, x4].all fun y =>
        decide (y.place ≠ sendPlace 5) && decide (y.place ≠ sendPlace 2))
  | _ => false

/-- No name: no round. -/
theorem namesAre_none {b : Block S Cl} (h : namesAre b [] = true) : b.rounds = [] :=
  List.map_eq_nil_iff.1 (beq_iff_eq.1 h)

/-- One name: one round, of that name. -/
theorem namesAre_one {b : Block S Cl} {a : String} (h : namesAre b [a] = true) :
    ∃ r, b.rounds = [r] ∧ r.entry.name = a := by
  have h' : b.rounds.map (·.entry.name) = [a] := beq_iff_eq.1 h
  match hb : b.rounds, h' with
  | [r], h' => exact ⟨r, rfl, (List.cons.inj h').1⟩

/-- Two names: two rounds, of these names. -/
theorem namesAre_two {b : Block S Cl} {a c : String} (h : namesAre b [a, c] = true) :
    ∃ r s, b.rounds = [r, s] ∧ r.entry.name = a ∧ s.entry.name = c := by
  have h' : b.rounds.map (·.entry.name) = [a, c] := beq_iff_eq.1 h
  match hb : b.rounds, h' with
  | [r, s], h' =>
    exact ⟨r, s, rfl, (List.cons.inj h').1, (List.cons.inj (List.cons.inj h').2).1⟩

/-- **Where the test accepts, the list has the form.** -/
theorem sharedForm_of_test {xs : List (Block S Cl)} (h : sharedFormB xs = true) :
    SharedForm xs := by
  unfold sharedFormB at h
  split at h
  · rename_i x0 x1 x2 x3 x4 x5 x6 x7 x8 tl
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩, n8⟩, p2⟩, p5⟩, hb⟩, hf⟩ := h
    obtain ⟨r1, e1, m1⟩ := namesAre_one n1
    obtain ⟨s2, a2, e2, m2, m2'⟩ := namesAre_two n2
    obtain ⟨r4, e4, m4⟩ := namesAre_one n4
    obtain ⟨s5, a5, e5, m5, m5'⟩ := namesAre_two n5
    obtain ⟨r7, e7, m7⟩ := namesAre_one n7
    obtain ⟨r8, e8, m8⟩ := namesAre_one n8
    have f0 := hf x0 (by simp)
    have f1 := hf x1 (by simp)
    have f3 := hf x3 (by simp)
    have f4 := hf x4 (by simp)
    exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, r1, s2, a2, r4, s5, a5, r7, r8, rfl,
      ⟨namesAre_none n0, e1, e2, namesAre_none n3, e4, e5, namesAre_none n6, e7, e8⟩,
      ⟨m1, m2, m2', m4, m5, m5', m7, m8⟩, ⟨p2, p5⟩, hb, ⟨f0.1, f1.1, f3.1, f4.1⟩,
      ⟨f0.2, f1.2, f3.2, f4.2⟩⟩
  · cases h

/-- The written description's shared list has the form. -/
theorem form_written : SharedForm WP.shared.blocksInOrder :=
  sharedForm_of_test (by decide +kernel)

/-- **THE TEST CAN FAIL**: at the written list without its first member; and with its eighth and
ninth members, "LIN zeta" and "SPLIT", in the other order. -/
theorem form_bites : sharedFormB (WP.shared.blocksInOrder.drop 1) = false ∧
    sharedFormB (WP.shared.blocksInOrder.take 7 ++ ((WP.shared.blocksInOrder.drop 7).take 2).reverse ++
      WP.shared.blocksInOrder.drop 9) = false := by decide +kernel

/-! ## The written sizes -/

/-- The public data at the library's written parameters of the shared chain (p14W,
Johnson/AtFull/Desc/LaterSeats.lean), at any number of "LIN point". -/
def atWritten (a : Nat) : SendPub := ⟨p14W, a⟩

/-- The tests on the shapes accept at the written sizes: the one test on the two sendings' shapes;
the shape splits; masks are sent ahead; the test on G_u has a first stage. -/
theorem shapesFit_written : sendingsFit p14W = true ∧
    p14W.S.sharedSplitNeeded = true ∧ p14W.S.masksAhead = true ∧
    p14W.S.testU.head?.isSome = true := by decide +kernel

/-- At the written rounds the first fold behind "send o_u" has as many rounds "FOLD round" as the
written shape's first stage has variables. -/
theorem foldK_at_written (a : Nat) :
    foldK ((WP.shared.blocksInOrder.flatMap (·.rounds)).drop 2) = some (maskRounds (atWritten a)) := by
  have h : foldK ((WP.shared.blocksInOrder.flatMap (·.rounds)).drop 2) =
      some ((p14W.S.testU.head?.map (·.k)).getD 0) := by decide +kernel
  exact h

/-- At the written cut that fold and the sending behind it are held by two parts. -/
theorem twoParts_at_written : foldTwoPartsB (planOf WP.shared.blocksInOrder) 1 = true := by decide +kernel

/-! ## "send o_omega" -/

/-- What headNumbersB gives at the written sizes. -/
theorem omega_numbers_written (a : Nat) :
    omegaNumbersB (atWritten a).P.codes (Desc.K14.withOmega (atWritten a).P.S).toList
        (spFirstCoin (atWritten a)) (spEntries (atWritten a) + 1 + (spMaskCode (atWritten a)).r) =
        true ∧ 0 < spEntries (atWritten a) ∧
      Desc.K14.Honest.freshPublicB (atWritten a).P.codes (atWritten a).P.S (spEntries (atWritten a))
        (spMaskCode (atWritten a)).r = true :=
  headNumbers_give (atWritten a) shapesFit_written.2.1 headNumbers_written.1

/-- **The numbers, written out**: o_sp's first coin and whole run; the fold's variables, the first
mask's first coin and whole run. They are the written list's. -/
theorem numbers_tie (a : Nat) : spFirstCoin (atWritten a) = 42853 ∧
    spEntries (atWritten a) + 1 + (spMaskCode (atWritten a)).r = 216 ∧
    maskRounds (atWritten a) = 7 ∧ maskFirstCoin (atWritten a) = 10808 ∧
    (maskRun (atWritten a)).2 = 167 := by
  have h : spFirstCoin (atWritten 0) = 42853 ∧
      spEntries (atWritten 0) + 1 + (spMaskCode (atWritten 0)).r = 216 ∧
      maskRounds (atWritten 0) = 7 ∧ maskFirstCoin (atWritten 0) = 10808 ∧
      (maskRun (atWritten 0)).2 = 167 := by decide +kernel
  exact h

/-- **whole_of_short, CALLED**: the short test at "send o_omega" accepts the written list. -/
theorem whole_omega_written (a : Nat) (B₀ : ProverCoinCounts) :
    wholeOrSpent ⟨0, spFirstCoin (atWritten a)⟩ ⟨0, 1⟩
      [(⟨0, 0⟩, ⟨0, spFirstCoin (atWritten a)⟩), (⟨0, spFirstCoin (atWritten a)⟩,
        ⟨0, spEntries (atWritten a) + 1 + (spMaskCode (atWritten a)).r⟩)]
      { B₀ with ahead := writtenShort } { place := sendPlace 5, part := 0 } = true :=
  whole_of_short form_written sharedSends_written (omega_numbers_written a).1 sharedAhead_written B₀

/-- **carriers_behind, CALLED**: the test on the order accepts it, at every run. -/
theorem order_omega_written (B₀ : ProverCoinCounts) (g n : Nat) :
    behindSpenderB g n { B₀ with ahead := writtenShort } (orderOf WP)
      { place := sendPlace 5, part := 0 } = true :=
  carriers_behind form_written wp_placesOk sharedSends_written (omega_numbers_written 0).1
    sharedAhead_written B₀ g n

/-- **spOwner_ok_of_short, CALLED: THE OWNER's TEST AT "send o_omega" ACCEPTS THE WRITTEN LIST**,
laid into any book. -/
theorem spOwner_written (a : Nat) (B₀ : ProverCoinCounts) :
    (spOwner (atWritten a)).ok { B₀ with ahead := writtenShort } (orderOf WP)
      { place := sendPlace 5, part := 0 } = true :=
  spOwner_ok_of_short form_written wp_placesOk (atWritten a) sharedSends_written
    (omega_numbers_written a).1 (omega_numbers_written a).2.1 shapesFit_written.1
    shapesFit_written.2.1 (omega_numbers_written a).2.2 sharedAhead_written B₀

/-- The part that holds the round number 7 of the written shared chain, "SPLIT": part 0 at the
piece 8. -/
theorem split_part_written :
    addrOfRound WP.shared.blocksInOrder 7 = some ⟨⟨2, none, 8, .K14⟩, 0⟩ := by decide +kernel

/-- **carriers_all, CALLED: "BEHIND", TYPED**: in the written list, at the owner at "send o_omega":
the entry e₀ that the frame's splitEntry yields LIES IN THE LIST, has that owner, one coin at the
first coin of o_sp's run, spends, and its spender is the part that holds "SPLIT"; every other entry
of that owner carries, and is handed to a part that stands behind that part in the written
description's own order of places. (e₀ by its written value: behind_omega_named.) -/
theorem behind_omega_written :
    ∃ (s : Addr) (e₀ : Ahead), addrOfRound WP.shared.blocksInOrder 7 = some s ∧
      splitEntry WP.shared.blocksInOrder proofSendsFull.2.1 = some e₀ ∧ e₀ ∈ writtenShort ∧
      e₀.owner = { place := sendPlace 5, part := 0 } ∧
      e₀.start = ⟨0, spFirstCoin (atWritten 0)⟩ ∧ e₀.count = ⟨0, 1⟩ ∧ e₀.spender = s ∧
      e₀.once = true ∧ ∀ k ∈ writtenShort, k.owner = { place := sendPlace 5, part := 0 } →
        k = e₀ ∨ (k.once = false ∧ StandsBehind (orderOf WP) s k.spender) :=
  carriers_all form_written wp_placesOk sharedSends_written (omega_numbers_written 0).1
    sharedAhead_written

/-- **THE SAME WITH BOTH LETTERS NAMED**: the entry that spends IS IN THE LIST: the split's one
coin; its spender is part 0 at the piece 8; every other entry of that owner carries, and is handed
to a part that stands behind that part. -/
theorem behind_omega_named : splitEntryWritten ∈ writtenShort ∧
    ∀ k ∈ writtenShort, k.owner = { place := sendPlace 5, part := 0 } →
      k = splitEntryWritten ∨
        (k.once = false ∧ StandsBehind (orderOf WP) ⟨⟨2, none, 8, .K14⟩, 0⟩ k.spender) := by
  have hm : splitEntryWritten ∈ writtenShort := .tail _ (.head _)
  obtain ⟨s, e₀, h7, -, -, -, -, -, -, -, hall⟩ := behind_omega_written
  obtain rfl : (⟨⟨2, none, 8, .K14⟩, 0⟩ : Addr) = s :=
    Option.some.inj (split_part_written.symm.trans h7)
  obtain rfl : splitEntryWritten = e₀ := by
    rcases hall _ hm rfl with q | q
    · exact q
    · exact absurd q.1 (by decide)
  exact ⟨hm, hall⟩

/-- **known_nil_of_short, CALLED**: in the frame's own term: at the part that holds "SPLIT" nothing
else of the owner's coins is known, at the written list laid into any book. -/
theorem known_omega_written (B₀ : ProverCoinCounts) :
    ∃ s, addrOfRound WP.shared.blocksInOrder 7 = some s ∧
      (∀ e ∈ spendersOf { B₀ with ahead := writtenShort } { place := sendPlace 5, part := 0 },
        e.spender = s) ∧
      ({ B₀ with ahead := writtenShort } : ProverCoinCounts).knownBy (orderOf WP)
        { place := sendPlace 5, part := 0 } s = [] :=
  known_nil_of_short form_written wp_placesOk sharedSends_written (omega_numbers_written 0).1
    sharedAhead_written B₀

/-! ## "send o_u" -/

/-- What uHeadNumbersB gives at the written sizes. -/
theorem u_numbers_written (a : Nat) :
    uNumbersB (atWritten a).P.codes ((Desc.K14.withU (atWritten a).P.S).getD #[]).toList
      (maskRounds (atWritten a)) (maskFirstCoin (atWritten a)) (maskRun (atWritten a)).2 = true :=
  uNumbers_of (atWritten a) uNumbers_written.1

/-- **whole_of_short_u, CALLED**: the short test at "send o_u" accepts the written list. -/
theorem whole_u_written (a : Nat) (B₀ : ProverCoinCounts) :
    wholeOrSpent ⟨0, maskFirstCoin (atWritten a)⟩ ⟨0, 2 * maskRounds (atWritten a) + 1⟩
      [(⟨0, 0⟩, ⟨0, maskFirstCoin (atWritten a)⟩), (⟨0, maskFirstCoin (atWritten a)⟩,
        ⟨0, (maskRun (atWritten a)).2⟩)]
      { B₀ with ahead := writtenShort } { place := sendPlace 2, part := 0 } = true :=
  whole_of_short_u form_written sharedSends_written (foldK_at_written a) (u_numbers_written a)
    (omega_numbers_written a).1 sharedAhead_written B₀

/-- **maskCarriers_behind, CALLED**: the test on the order accepts it, at the first mask's run. -/
theorem order_u_written (a : Nat) (B₀ : ProverCoinCounts) :
    behindSpenderB (maskFirstCoin (atWritten a)) (maskRun (atWritten a)).2
      { B₀ with ahead := writtenShort } (orderOf WP) { place := sendPlace 2, part := 0 } = true :=
  maskCarriers_behind form_written wp_placesOk sharedSends_written (foldK_at_written a)
    (u_numbers_written a) (omega_numbers_written a).1 twoParts_at_written sharedAhead_written B₀

/-- **maskOwner_ok_of_short, CALLED: THE OWNER's TEST AT "send o_u" ACCEPTS THE WRITTEN LIST**, laid
into any book. -/
theorem maskOwner_written (a : Nat) (B₀ : ProverCoinCounts) :
    (maskOwner (atWritten a)).ok { B₀ with ahead := writtenShort } (orderOf WP)
      { place := sendPlace 2, part := 0 } = true :=
  maskOwner_ok_of_short form_written wp_placesOk (atWritten a) sharedSends_written
    (foldK_at_written a) (u_numbers_written a) (omega_numbers_written a).1 twoParts_at_written
    shapesFit_written.1 shapesFit_written.2.2.1 shapesFit_written.2.2.2 sharedAhead_written B₀

/-- **mask_known_at_fold, CALLED**: in the frame's own term: every other entry that hands coins of
the owner at "send o_u" to the part that spends of them, or to a part in front of it, is o_u's whole
run. -/
theorem known_u_written (a : Nat) (B₀ : ProverCoinCounts) :
    ∀ e ∈ spendersOf { B₀ with ahead := writtenShort } { place := sendPlace 2, part := 0 },
      ∀ x ∈ ({ B₀ with ahead := writtenShort } : ProverCoinCounts).knownBy (orderOf WP)
          { place := sendPlace 2, part := 0 } e.spender,
        x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, maskFirstCoin (atWritten a)⟩ :=
  mask_known_at_fold (atWritten a) (whole_u_written a B₀) (order_u_written a B₀)
    shapesFit_written.2.2.2

/-- The fold behind "send o_u" and the sending behind that fold are held by parts 0 and 1 at the
piece 9. -/
theorem fold_parts_written : behindFold (planOf WP.shared.blocksInOrder) 1 =
    some (⟨⟨2, none, 9, .K12⟩, 0⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩) := by decide +kernel

/-- **maskCarriers_all, CALLED**: who spends and who carries at the owner at "send o_u", in the
written list. -/
theorem carriers_u_written (a : Nat) :
    ∃ p q, behindFold (planOf WP.shared.blocksInOrder) 1 = some (p, q) ∧
      q.before (orderOf WP) p = false ∧ q ≠ p ∧
      MaskCarriersAt writtenShort p q (maskRounds (atWritten a)) (maskFirstCoin (atWritten a))
        (maskRun (atWritten a)).2 :=
  maskCarriers_all form_written wp_placesOk sharedSends_written (foldK_at_written a)
    (u_numbers_written a) (omega_numbers_written a).1 twoParts_at_written sharedAhead_written

/-- **maskAtBook_of_short, CALLED**: all that is shown of a book at the owner at "send o_u", as one
form, at the written list laid into any book, with the two parts named. -/
theorem maskAtBook_written (a : Nat) (B₀ : ProverCoinCounts) :
    MaskAtBook (atWritten a) { B₀ with ahead := writtenShort } (orderOf WP)
      ⟨⟨2, none, 9, .K12⟩, 0⟩ ⟨⟨2, none, 9, .K12⟩, 1⟩ := by
  obtain ⟨p, q, hb, h⟩ := maskAtBook_of_short form_written wp_placesOk (atWritten a)
    sharedSends_written (foldK_at_written a) (u_numbers_written a) (omega_numbers_written a).1
    twoParts_at_written shapesFit_written.1 shapesFit_written.2.2.1 shapesFit_written.2.2.2
    sharedAhead_written B₀
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (fold_parts_written.symm.trans hb))
  exact h

/-! ## The tests on the order can fail at this list -/

/-- The written list, but for this: the two entries that are carried to part 0 of the first test's
place (one of each owner) are handed to the part at "LIN zeta" instead, in front of "SPLIT" and of
that test. -/
def earlyShort : List Ahead :=
  writtenShort.map fun e =>
    if e.spender == ⟨⟨2, none, 9, .K12⟩, 0⟩ && !e.once then
      { e with spender := ⟨⟨2, none, 7, .K14⟩, 0⟩ } else e

/-- The written list, but for this: the entry that carries the first mask's whole run is handed to
the part at "LIN zeta" instead, in front of the fold that spends its coefficients. -/
def earlyMask : List Ahead :=
  writtenShort.map fun e =>
    if e.start == ⟨0, 10808⟩ && !e.once then
      { e with spender := ⟨⟨2, none, 7, .K14⟩, 0⟩ } else e

/-- **THE TESTS ON THE ORDER CAN FAIL AT THIS LIST**, at the shared chain's own order of places:
both accept writtenShort; the test at "send o_omega" rejects earlyShort; THE TEST AT "send o_u"
ACCEPTS earlyShort (the bent entry of that owner, o_u's whole run, holds no coin of the first mask)
and rejects earlyMask. -/
theorem order_bites :
    behindSpenderB 42853 216 ⟨[], [], [], writtenShort, []⟩ (WP.shared.blocksInOrder.map (·.place))
        { place := sendPlace 5, part := 0 } = true ∧
      behindSpenderB 42853 216 ⟨[], [], [], earlyShort, []⟩ (WP.shared.blocksInOrder.map (·.place))
        { place := sendPlace 5, part := 0 } = false ∧
      behindSpenderB 10808 167 ⟨[], [], [], writtenShort, []⟩ (WP.shared.blocksInOrder.map (·.place))
        { place := sendPlace 2, part := 0 } = true ∧
      behindSpenderB 10808 167 ⟨[], [], [], earlyShort, []⟩ (WP.shared.blocksInOrder.map (·.place))
        { place := sendPlace 2, part := 0 } = true ∧
      behindSpenderB 10808 167 ⟨[], [], [], earlyMask, []⟩ (WP.shared.blocksInOrder.map (·.place))
        { place := sendPlace 2, part := 0 } = false := by decide +kernel

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.namesAre_none
#print axioms ProofFile.Honest.K14.namesAre_one
#print axioms ProofFile.Honest.K14.namesAre_two
#print axioms ProofFile.Honest.K14.sharedForm_of_test
#print axioms ProofFile.Honest.K14.form_written
#print axioms ProofFile.Honest.K14.form_bites
#print axioms ProofFile.Honest.K14.shapesFit_written
#print axioms ProofFile.Honest.K14.foldK_at_written
#print axioms ProofFile.Honest.K14.twoParts_at_written
#print axioms ProofFile.Honest.K14.omega_numbers_written
#print axioms ProofFile.Honest.K14.numbers_tie
#print axioms ProofFile.Honest.K14.whole_omega_written
#print axioms ProofFile.Honest.K14.order_omega_written
#print axioms ProofFile.Honest.K14.spOwner_written
#print axioms ProofFile.Honest.K14.split_part_written
#print axioms ProofFile.Honest.K14.behind_omega_written
#print axioms ProofFile.Honest.K14.behind_omega_named
#print axioms ProofFile.Honest.K14.known_omega_written
#print axioms ProofFile.Honest.K14.u_numbers_written
#print axioms ProofFile.Honest.K14.whole_u_written
#print axioms ProofFile.Honest.K14.order_u_written
#print axioms ProofFile.Honest.K14.maskOwner_written
#print axioms ProofFile.Honest.K14.known_u_written
#print axioms ProofFile.Honest.K14.fold_parts_written
#print axioms ProofFile.Honest.K14.carriers_u_written
#print axioms ProofFile.Honest.K14.maskAtBook_written
#print axioms ProofFile.Honest.K14.order_bites
