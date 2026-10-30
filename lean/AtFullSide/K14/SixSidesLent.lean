-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K14/SixSidesLent.lean: kind K14: at the full size the book of coins of the honest prover
that onlineProverFromPublicFiles makes fits the six sides that stand at the eight sub-protocols of the linear claim's
shared rounds (numbers 1 to 8 of the shared chain's list, counted from 0): what the frame's set-up
routine chainSteps (Honest/Frame.lean) tests at each of the six, it finds. Five definitions, all
with code; statements with their proofs.

The six sides are the kind's own four (proverSidesOfSharedRounds, Honest/K14/Parts.lean: at "LIN point", "LOC",
"LIN zeta" and "SPLIT") and the two sendings' (proverSidesOfSharedSendings, Honest/K14/Sendings.lean: "send o_u" and
"send o_omega"). Each has one part. Two of the eight sub-protocols have no round and no side. Before
a run the frame asks six things at the sub-protocol b at a side's place: (1) b has as many lists of
oracle messages as rounds; (2) the side has as many rounds as b; (3) the book cuts the place as the
side's parts do; (4) no row of the book names a part beyond the side's; (5) nor does an entry of the
book; (6) the book's lending to the side's parts (lendRow) returns. (6) binds both ways: each part
takes exactly the count that the book has for it; the entries that it states are, by name and count
and in order, the book's entries that name it as their spender; and each such block can be cut out
of its owner's coins.

TWO WAYS OF COUNTING CHAINS MEET HERE. A place's field "chain" is 1, 2 or 3: the shared chain is 2.
The frame's rowsOf and look count from 0: the shared chain is 1.

  noneToSix           a test: no entry of a list is handed to a part at one of the six places
                      (sixPlaces, Honest/K14/HalvesAmong.lean)
  noneToSix_of_first, noneToSix_wants, noneToSix_seg, noneToSix_short, noneToSix_bent   it accepts a
                      list whose entries all go to the first chain; so, by the library's wants_first
                      and seg_first (AtFullSide/K12/TiesAtLaid.lean), the two pieces of rawAheadW
                      that are not written out; by an evaluation in Lean's kernel seven of the eight
                      written pieces; it rejects the eighth, the split's entry
  filter_of_none, toSix_raw, eq_split_of_six, filter_raw   **of the library's list of all the book's
                      entries (rawAheadW) exactly one is handed to a part at one of the six places:
                      the split's one coin**, in three forms
  hasForW, hasForW_table   what the written book has for part 0 at each of the six places: the
                      count, the entries spent, the entries carried. An evaluation
  sizesOf, blockTest, blockTest_written, blockTest_bent   a test on a list of sub-protocols' sizes,
                      a list of cuts and a list of rows, for (1) to (4); it accepts at the six, at
                      the written description's shared chain, its cuts and the written rows; each of
                      its four askings can reject
  places_written      at each of the six places the written shared chain has a sub-protocol
  takesB, takesB_plan, takes_real, takes_at_head   at the full size the two sendings' parts take
                      10975 and 43069 coins
  book_made_written, hasFor_made   at the full size the made prover's book has the library's list of
                      entries, the written rows of the shared chain and the written description's
                      cuts
  tests_at_made       the six things at any side with one part that states what hasForW has
  six_tests_at_made   **THE SIX THINGS AT EACH OF THE SIX SIDES**
  blocks_there, six_at_places, six_blocks_there, six_found   against emptiness: the six sides stand
                      at the six places; at the place of each the description's shared chain has a
                      sub-protocol; and in a list that begins with the six, a search by a side's
                      place finds that side

The conclusion of six_tests_at_made is, to the letter, the premise of the law that turns the six
things into "chainSteps returns at that sub-protocol" (sidePays_of_tests; it is called in
AtFullSide/K14/SixSidesPay.lean and is not among this file's imports).

"At the full size" is the premise h : P5J.AtMgA (Johnson/P5J/MgAtAll.lean) at the hash
OnBytes.secondHashFunction. "Made" is the premise hA: onlineProverFromPublicFiles returns A at that public part's three files. The
filling P is free: of A the statements read the book alone. Free too: the sides' own types (of the
index, of the committer's random values, of the key and of the sides' state), the two readers, and
the numbers of the rounds that the parts read; of the sides' public data only the shape and the plan
are fixed, at the shared chain's own (qAt Zp Np).

Kin. filter_off, ahead_at (AtFullSide/K12/TiesAtLaid.lean) and rawShortW
(AtFullSide/K14/RawEntriesKit.lean) cut rawAheadW down at one ADDRESS outside the first chain; (5)
and the premise of lendRow_ok filter by PLACE, which is why toSix_raw is here.
makers_ahead_at_atPure (AtFullSide/K14/MakersBookOne.lean) has book_made_written's first clause; the
rows and the cuts at the made book are new. sendNumbersB (Honest/K12/SendNumbersAtHead.lean) has
"at least 10975" and "at least 43069"; lendPart asks equality. The cuts are read off cutsOf_written
(Honest/BookWritten/Cuts.lean). ProofFile.Honest.K14.six_places (Honest/K14/NoStray.lean) says of the same
list that each side's place is among eight spelled places, at every shape; six_at_places is the
equation at the full size.

Limits.
  * THE PREMISE h IS A HYPOTHESIS. It gathers conditions on the public files at the full size. This
    file does not show them to be met, and the verifier does not ask them. By the head of
    Johnson/P5J/MgAtAll.lean a member is proved at two written sets of public files
    (AtFullSide/Top/: headMember_zFull, headMember_zGap), and at no others.
  * That onlineProverFromPublicFiles returns is a premise. Where it does not return, the statements that take hA say
    nothing.
  * "The set-up returns" says nothing on whether a part plays, a round is reached or a verifier
    accepts.
  * That the lending returns does not say WHOSE coin is the right one: that coin number 42853 of
    "send o_omega" is the entry of the split's mask message to which "SPLIT" must add its scalar is
    not said here.
  * That a prover's list of sides begins with these six is not said.
  * The numbers are those of one written description. Nothing is said at another size.
  * takes_real is a sentence on what the library's realSized returns; it would hold of nothing if
    that were none. takes_at_head has the member from written_at_head (Honest/K12/FitAtHead.lean).
  * maxRecDepth is raised to 1000000 in front of three evaluations.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.K14.MakersBookOne
import AtFullSide.K14.RawTwinKit
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K12.TiesAtLaid
import E2E.KeyBookLends
import OnBytes.K.Left.Asm
import Johnson.Desc.ProofFile.Honest.BookWritten.Cuts
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K14.HalvesAmong
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Chain Place Block)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open P2Law.ProofPlan (WP)
open P5J (TS F0T)
open AtPublicFiles.KeyBook (hasFor Within lendRow_ok look_due)
open ProofFile.Honest.K12.Light (planOf written_at_head qAt_written)

/-! ## 1 The entries that are handed to the six places -/

/-- **A test**: no entry of the list is handed to a part at one of the six places. -/
def noneToSix (l : List Ahead) : Bool := l.all fun e => !(sixPlaces.contains e.spender.place)

/-- It accepts a list all of whose entries are handed to parts of the first chain (the field
"chain" is 1): the six places stand in the shared chain (there it is 2). -/
theorem noneToSix_of_first {l : List Ahead}
    (h : (l.all fun e => e.spender.place.chain == 1) = true) : noneToSix l = true := by
  refine List.all_eq_true.2 fun e he => ?_
  have h1 : e.spender.place.chain = 1 := beq_iff_eq.1 (List.all_eq_true.1 h e he)
  cases c : sixPlaces.contains e.spender.place with
  | false => rfl
  | true =>
    have hm : e.spender.place ∈ sixPlaces := List.contains_iff_mem.1 c
    simp only [sixPlaces, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with q | q | q | q | q | q <;> (rw [q] at h1; exact absurd h1 (by decide))

/-- It accepts the entries of the first chain's stretches. -/
theorem noneToSix_wants : noneToSix (rawWantsW.map (·.entry)) = true :=
  noneToSix_of_first AtFullSide.K12.wants_first

/-- It accepts the short written pieces, the split's entry left out. -/
theorem noneToSix_short : noneToSix (foldsFirstW ++ foldsSharedW ++ []) = true ∧
    noneToSix rawCarriedShortW = true := by
  decide +kernel

/-- It accepts the carrying entries of the chain of segments. -/
theorem noneToSix_seg : noneToSix rawSegW = true :=
  noneToSix_of_first AtFullSide.K12.seg_first

/-- The test can reject: it rejects the split's entry. -/
theorem noneToSix_bent : noneToSix [splitEntryWritten] = false := by decide +kernel

/-- Where the test accepts, the filter by the six places leaves nothing. -/
theorem filter_of_none {l : List Ahead} (h : noneToSix l = true) :
    l.filter (fun e => sixPlaces.contains e.spender.place) = [] := by
  refine List.filter_eq_nil_iff.2 fun e he c => ?_
  have := List.all_eq_true.1 h e he
  rw [c] at this
  cases this

/-- **Of the library's list of all the book's entries exactly one is handed to a part at one of the
six places: the split's one coin.** -/
theorem toSix_raw :
    rawAheadW.filter (fun e => sixPlaces.contains e.spender.place) = [splitEntryWritten] := by
  have e : rawSpentW =
      rawWantsW.map (·.entry) ++ (foldsFirstW ++ foldsSharedW ++ []) ++ [splitEntryWritten] := by
    unfold rawSpentW
    simp only [List.append_assoc]
  have hs : sixPlaces.contains splitEntryWritten.spender.place = true := by decide
  rw [rawAhead_three, e, List.filter_append, List.filter_append, List.filter_append,
    List.filter_append, filter_of_none noneToSix_wants, filter_of_none noneToSix_short.1,
    filter_of_none noneToSix_seg, filter_of_none noneToSix_short.2,
    List.filter_cons_of_pos (p := fun e : Ahead => sixPlaces.contains e.spender.place) hs]
  rfl

/-- An entry of that list that is handed to a part at one of the six places is the split's. -/
theorem eq_split_of_six {e : Ahead} (he : e ∈ rawAheadW)
    (hp : sixPlaces.contains e.spender.place = true) : e = splitEntryWritten := by
  have : e ∈ rawAheadW.filter (fun e => sixPlaces.contains e.spender.place) :=
    List.mem_filter.2 ⟨he, hp⟩
  rw [toSix_raw] at this
  exact List.mem_singleton.1 this

/-- A filter that passes only entries handed to the six places reads the split's entry alone. -/
theorem filter_raw (p : Ahead → Bool)
    (hp : ∀ e, p e = true → sixPlaces.contains e.spender.place = true) :
    rawAheadW.filter p = [splitEntryWritten].filter p := by
  rw [← toSix_raw, List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  cases h : p e with
  | false => rfl
  | true => rw [hp e h]; rfl

/-! ## 2 What the written book has for the six parts -/

/-- What the written book has for the part at a, where a stands at one of the six places: its count
in the shared chain's written rows; the names and counts of the entries that it spends; those of the
entries that it carries. -/
def hasForW (a : Addr) : Due × List (String × Due) × List (String × Due) :=
  (dueAt rawRowsSharedW a,
    (([splitEntryWritten].filter fun e => e.spender == a).filter (·.once)).map Ahead.named,
    (([splitEntryWritten].filter fun e => e.spender == a).filter (!·.once)).map Ahead.named)

/-- **The six, written out.** The two sendings' parts have coins of their own and are handed none;
the part at "SPLIT" has none of its own and spends one, under the name that it states; the three
others have none and are handed none. -/
theorem hasForW_table :
    hasForW ⟨place 1, 0⟩ = (⟨0, 0⟩, [], []) ∧ hasForW ⟨sendPlace 2, 0⟩ = (⟨0, 10975⟩, [], []) ∧
    hasForW ⟨place 4, 0⟩ = (⟨0, 0⟩, [], []) ∧ hasForW ⟨sendPlace 5, 0⟩ = (⟨0, 43069⟩, [], []) ∧
    hasForW ⟨place 7, 0⟩ = (⟨0, 0⟩, [], []) ∧
    hasForW ⟨place 8, 0⟩ = (⟨0, 0⟩, [(splitRun, ⟨0, 1⟩)], []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 3 The sub-protocols, the cuts and the rows -/

/-- Of each sub-protocol of a list: its place, how many lists of oracle messages it has, how many
rounds. -/
def sizesOf {S Cl : Type} (bs : List (Block S Cl)) : List (Place × Nat × Nat) :=
  bs.map fun b => (b.place, b.oracles.length, b.rounds.length)

/-- **A test** at a place a and a number n of rounds. sz: sub-protocols' sizes: each at a has as
many lists of oracle messages as rounds, and n rounds. cuts: they have one part of n rounds at a.
rows: none names a part at a beyond part 0. -/
def blockTest (sz : List (Place × Nat × Nat)) (cuts : List (Place × List Nat))
    (rows : List (Addr × Due)) (a : Place) (n : Nat) : Bool :=
  (sz.all fun x => !(x.1 == a) || (x.2.1 == x.2.2 && x.2.2 == n)) &&
  (cuts.lookup a == some [n]) &&
  !(rows.any fun r => r.1.place == a && decide (1 ≤ r.1.part))

set_option maxRecDepth 1000000 in
/-- It accepts at the six places, at one round, and at two at the two sendings: at the written
description's shared chain, its cuts, and the shared chain's written rows. -/
theorem blockTest_written :
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (place 1) 1 = true ∧
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (sendPlace 2) 2 = true ∧
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (place 4) 1 = true ∧
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (sendPlace 5) 2 = true ∧
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (place 7) 1 = true ∧
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (place 8) 1 = true := by
  rw [cutsOf_written]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 1000000 in
/-- **Each of its four askings can reject**, at the place of "LIN point", where it accepts at one
round: with a sub-protocol of two rounds laid in front; with one laid in front that has a round and
no list of oracle messages; with a cut of two rounds laid in front; with a row for a part number 1
laid in front. At each bend the three other askings still accept. -/
theorem blockTest_bent :
    blockTest ((place 1, 2, 2) :: sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (place 1) 1 =
      false ∧
    blockTest ((place 1, 0, 1) :: sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW (place 1) 1 =
      false ∧
    blockTest (sizesOf WP.shared.blocksInOrder) ((place 1, [2]) :: cutsOf WP) rawRowsSharedW (place 1) 1 =
      false ∧
    blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) ((⟨place 1, 1⟩, ⟨0, 1⟩) :: rawRowsSharedW)
      (place 1) 1 = false := by
  rw [cutsOf_written]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of the six places the written description's shared chain has a sub-protocol. -/
theorem places_written :
    (sixPlaces.all fun a => (WP.shared.blocksInOrder.map (·.place)).contains a) = true := by decide +kernel

/-! ## 4 The two sendings' counts -/

/-- A test on the two sendings' counts. -/
def takesB (A : SendPub) : Bool :=
  (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort == ⟨0, 10975⟩) &&
  (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort == ⟨0, 43069⟩)

/-- It reads of the public data the codes and the shape alone. -/
theorem takesB_plan (A : SendPub) : takesB A = takesB (planOf A.P.codes A.P.S) := rfl

/-- It accepts at the typed sizes over a proof file's own codes: at what realSized returns. -/
theorem takes_real : (realSized.all fun q => takesB (planOf q.2 q.1.shape)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **At the full size the two sendings' parts take 10975 and 43069 coins of the extension field**,
whatever the number a of the round that they read. -/
theorem takes_at_head {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) (a : Nat) :
    (sendingPart (jobU ⟨qAt Zp Np, a⟩)).takes = ⟨0, 10975⟩ ∧
      (sendingPart (jobOmega ⟨qAt Zp Np, a⟩)).takes = ⟨0, 43069⟩ := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := takes_real
  rw [hx] at k
  have k' : takesB (planOf codesFull2 x.shape) = true := k
  have k2 : takesB ⟨qAt Zp Np, a⟩ = true := by
    rw [takesB_plan, qAt_written Wr Np]
    exact k'
  unfold takesB at k2
  simp only [Bool.and_eq_true, beq_iff_eq] at k2
  exact k2

/-! ## 5 The made prover's book -/

variable {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **At the full size the made prover's book has the library's list of entries, the written rows of
the shared chain, and the written description's cuts.** -/
theorem book_made_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.B.ahead = rawAheadW ∧ A.B.shared = rawRowsSharedW ∧ A.B.cuts = cutsOf WP := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  obtain rfl : W = A.B :=
    Except.ok.inj ((bookWhole_same_at_made (bookWhole_returns_raw W hW) h).symm.trans
      (atPure_book_at_head h hA))
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := bookRaw_rows hW
  exact ⟨rawAhead_written _ hW, (rawBookRows_written _ _ hW).2.1, hc⟩

/-- What the made prover's book has for a part at one of the six places is what the written book
has. -/
theorem hasFor_made (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (a : Addr)
    (ha : sixPlaces.contains a.place = true) : hasFor A.B (A.B.rowsOf 1) a = hasForW a := by
  obtain ⟨e1, e2, -⟩ := book_made_written h hA
  have hr : A.B.rowsOf 1 = A.B.shared := rfl
  unfold hasFor hasForW
  rw [hr, e1, e2, filter_raw (fun e => e.spender == a) fun e he => by
    rw [beq_iff_eq.1 he]
    exact ha]

/-! ## 6 The six things -/

/-- **The six things at a side with one part**, at one of the six places, where the test on the
sub-protocols, the cuts and the rows accepts at the part's number of rounds and the part states what
the written book has for it. -/
theorem tests_at_made (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {V W Y : Type} (a : Place)
    (p : Part V W Y) (ha : sixPlaces.contains a = true)
    (hb : blockTest (sizesOf WP.shared.blocksInOrder) (cutsOf WP) rawRowsSharedW a p.moves.length = true)
    (hs : (p.takes, p.spends, p.carries) = hasForW ⟨a, 0⟩) :
    ∀ b ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder,
      b.place = (⟨a, [p]⟩ : Placed V W Y).place →
      b.oracles.length = b.rounds.length ∧ (⟨a, [p]⟩ : Placed V W Y).rounds = b.rounds.length ∧
      A.B.cuts.lookup b.place = some ((⟨a, [p]⟩ : Placed V W Y).parts.map (·.moves.length)) ∧
      (A.B.rowsOf 1).any (fun r => r.1.place == b.place &&
        decide ((⟨a, [p]⟩ : Placed V W Y).parts.length ≤ r.1.part)) = false ∧
      A.B.ahead.any (fun e => e.spender.place == b.place &&
        decide ((⟨a, [p]⟩ : Placed V W Y).parts.length ≤ e.spender.part)) = false ∧
      ∃ (k₀ : Coins A.B) (c : RowCoins (⟨a, [p]⟩ : Placed V W Y).parts),
        lendRow A.B (A.B.rowsOf 1) (k₀.look 1) b.place (⟨a, [p]⟩ : Placed V W Y).parts 0 =
          .ok c := by
  intro b hbm hpl
  obtain rfl : b.place = a := hpl
  obtain ⟨e1, e2, e3⟩ := book_made_written h hA
  have hr : A.B.rowsOf 1 = A.B.shared := rfl
  obtain ⟨b', hb', al⟩ :=
    OnBytes.K.Left.forall₂_mem_right (alike_shared_at_laid h.scope h.laid) b hbm
  unfold blockTest at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hb
  obtain ⟨⟨t1, t2⟩, t3⟩ := hb
  have t1' : (!(b'.place == b.place) ||
      (b'.oracles.length == b'.rounds.length && b'.rounds.length == p.moves.length)) = true :=
    List.all_eq_true.1 t1 _ (List.mem_map.2 ⟨b', hb', rfl⟩)
  rw [al.1] at t1'
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at t1'
  rw [al.2.1, al.2.2.1] at t1'
  refine ⟨t1'.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t1'.2]
    exact Nat.zero_add _
  · rw [e3, t2]
    rfl
  · rw [hr, e2]
    exact t3
  · rw [e1]
    refine Bool.eq_false_iff.2 fun c => ?_
    obtain ⟨e, he, hc⟩ := List.any_eq_true.1 c
    obtain ⟨c1, c2⟩ := Bool.and_eq_true_iff.1 hc
    obtain rfl := eq_split_of_six he (by rw [beq_iff_eq.1 c1]; exact ha)
    have c3 : 1 ≤ 0 := of_decide_eq_true c2
    exact absurd c3 (by decide)
  · refine ⟨default, lendRow_ok A.B (A.B.rowsOf 1) _ b.place (fun j => ?_) (fun e he hp => ?_)
      [p] 0 fun i q hq => ?_⟩
    · rw [look_due]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · rw [e1] at he
      obtain rfl := eq_split_of_six he (by rw [hp]; exact ha)
      unfold Within
      rw [look_due]
      show _ ≤ (dueAt A.B.shared _).f ∧ _ ≤ (dueAt A.B.shared _).e
      rw [e2]
      decide
    · match i, hq with
      | 0, hq =>
        obtain rfl : p = q := Option.some.inj hq
        exact hs.trans (hasFor_made h hA ⟨b.place, 0⟩ ha).symm

variable {W₁ Rc₁ Ky₁ X₁ : Type}

/-- **THE SIX THINGS AT EACH OF THE SIX SIDES.** Dt: the public data of the kind's own sides, of the
plan's shape (hS). a: the number of the round that the sendings' parts read. At every pair of
readers and at all types of the sides. -/
theorem six_tests_at_made (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (Dt : Data)
    (hS : Dt.S = (qAt Zp Np).S) (a : Nat) (weights : W₁ → Weights) (rand : Rc₁ → TableRand) :
    ∀ g ∈ (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings ⟨qAt Zp Np, a⟩ weights rand :
        List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)),
      ∀ b ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, b.place = g.place →
        b.oracles.length = b.rounds.length ∧ g.rounds = b.rounds.length ∧
        A.B.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
        (A.B.rowsOf 1).any
          (fun r => r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = false ∧
        A.B.ahead.any
          (fun e => e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) =
            false ∧
        ∃ (k₀ : Coins A.B) (c : RowCoins g.parts),
          lendRow A.B (A.B.rowsOf 1) (k₀.look 1) b.place g.parts 0 = .ok c := by
  obtain ⟨w1, w2, w4, w5, w7, w8⟩ := hasForW_table
  obtain ⟨b1, b2, b4, b5, b7, b8⟩ := blockTest_written
  obtain ⟨tU, tO⟩ := takes_at_head h.toAtMg a
  have hsp : Dt.S.sharedSplitNeeded = true := by
    rw [hS]
    exact (sendings_at_head h).2.1
  intro g hg
  rw [halves_eq, sendHalves_eq, if_pos hsp] at hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((rfl | rfl | rfl) | rfl) | rfl | rfl
  · exact tests_at_made h hA _ _ (by decide) b1 w1.symm
  · exact tests_at_made h hA _ _ (by decide) b4 w4.symm
  · exact tests_at_made h hA _ _ (by decide) b7 w7.symm
  · exact tests_at_made h hA _ _ (by decide) b8 w8.symm
  · exact tests_at_made h hA _ _ (by decide) b2
      ((congrArg (fun d : Due => (d, ([] : List (String × Due)), ([] : List (String × Due))))
        tU).trans w2.symm)
  · exact tests_at_made h hA _ _ (by decide) b5
      ((congrArg (fun d : Due => (d, ([] : List (String × Due)), ([] : List (String × Due))))
        tO).trans w5.symm)

/-! ## 7 Against emptiness -/

/-- At each of the six places the description's shared chain has a sub-protocol. -/
theorem blocks_there {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ a ∈ sixPlaces, ∃ b ∈ (F0T o Zp Np cF).shared.blocksInOrder, b.place = a := by
  intro a ha
  have t := List.all_eq_true.1 places_written a ha
  rw [VerifiableInference.Desc.alike₂_place _ _ (alike_shared_at_laid h.scope h.laid)] at t
  obtain ⟨b, hb, e⟩ := List.mem_map.1 (List.contains_iff_mem.1 t)
  exact ⟨b, hb, e⟩

/-- At the full size the sides are six, and they stand, in this order, at the six places. -/
theorem six_at_places {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMgA o Z D r Zp Np cF x₀) (Dt : Data)
    (hS : Dt.S = (qAt Zp Np).S) (B : SendPub) (weights : W₁ → Weights) (rand : Rc₁ → TableRand) :
    (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings B weights rand :
        List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)).map (·.place) = sixPlaces := by
  have hsp : Dt.S.sharedSplitNeeded = true := by
    rw [hS]
    exact (sendings_at_head h).2.1
  rw [halves_eq, sendHalves_eq, if_pos hsp]
  rfl

/-- **At the place of each of the sides the description's shared chain has a sub-protocol**: so the
six things are asked of something at each. -/
theorem six_blocks_there {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) (Dt : Data)
    (B : SendPub) (weights : W₁ → Weights) (rand : Rc₁ → TableRand) :
    ∀ g ∈ (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings B weights rand :
        List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)),
      ∃ b ∈ (F0T o Zp Np cF).shared.blocksInOrder, b.place = g.place :=
  fun g hg => blocks_there h g.place ((six_apart Dt B weights rand).2 g hg)

/-- **In a list that begins with the sides, a search by a side's place finds that side**, whatever
stands behind them. -/
theorem six_found (Dt : Data) (B : SendPub) (weights : W₁ → Weights) (rand : Rc₁ → TableRand)
    (rest : List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)) :
    ∀ g ∈ (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings B weights rand :
        List (Placed Empty (Common W₁ Rc₁ Ky₁) X₁)),
      (proverSidesOfSharedRounds Dt weights ++ proverSidesOfSharedSendings B weights rand ++ rest).find?
        (fun q => q.place == g.place) = some g := by
  intro g hg
  rw [List.find?_append, find_of_mem _ g (six_apart Dt B weights rand).1 hg]
  rfl

end AtFullSide.K14

#print axioms AtFullSide.K14.noneToSix_of_first
#print axioms AtFullSide.K14.noneToSix_wants
#print axioms AtFullSide.K14.noneToSix_short
#print axioms AtFullSide.K14.noneToSix_seg
#print axioms AtFullSide.K14.noneToSix_bent
#print axioms AtFullSide.K14.filter_of_none
#print axioms AtFullSide.K14.toSix_raw
#print axioms AtFullSide.K14.eq_split_of_six
#print axioms AtFullSide.K14.filter_raw
#print axioms AtFullSide.K14.hasForW_table
#print axioms AtFullSide.K14.blockTest_written
#print axioms AtFullSide.K14.blockTest_bent
#print axioms AtFullSide.K14.places_written
#print axioms AtFullSide.K14.takesB_plan
#print axioms AtFullSide.K14.takes_real
#print axioms AtFullSide.K14.takes_at_head
#print axioms AtFullSide.K14.book_made_written
#print axioms AtFullSide.K14.hasFor_made
#print axioms AtFullSide.K14.tests_at_made
#print axioms AtFullSide.K14.six_tests_at_made
#print axioms AtFullSide.K14.blocks_there
#print axioms AtFullSide.K14.six_at_places
#print axioms AtFullSide.K14.six_blocks_there
#print axioms AtFullSide.K14.six_found
