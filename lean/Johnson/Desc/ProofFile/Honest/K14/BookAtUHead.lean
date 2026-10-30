-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtUHead.lean: kind K14: **WHERE THE FRAME's SHORT LIST
sharedAhead, ITS RAW BOOK bookRaw OR ITS BOOK bookWhole RETURNS at the proof file's IOP as written
in Lean (below: the description) and the library's written list of sendings: THE ENTRIES AT THE PART
AT "send o_u" ARE THE FOUR (MaskFourAt, Honest/K14/BookAtU.lean), AT THE PARTS 0 AND 1 OF THE FOLDED
ROW's PROXIMITY TEST; THE PART 1 STANDS BEHIND THE PART 0; AND THE SHORT TEST, THE TEST ON THE ORDER
AND THE OWNER's TEST (maskOwner, Honest/K14/MaskOwner.lean) ACCEPT**, with none of the book's own
tests used: for all public files Z that pass the library's test InScope and every public part Zp of
which the library's LaidAt holds, at the format's own earlier hash. Here all premises of
Honest/K14/BookAtU.lean's statements that go by the four entries are paid, but "returns": hk, the
numbers and foldTwoPartsB in this file; the form of the shared list and the other sending's numbers
by form_at_files and numbers_at_files (Honest/K14/BookAtOmegaHead.lean); what the list of sendings
begins with by sharedSends_at_files (Honest/K14/SharedSendsWritten.lean); the three tests on the
plan by sendings_of_laid (Honest/K14/SendingsAtHead.lean). Two definitions with code; statements
with their proofs. On lists of entries, numbers and an order of places alone: no distribution
occurs.

  uSortOf, uHeadNumbersB codes S, uNumbers_of   one test on public numbers: uNumbersB at o_u's count
                  and the first mask's count as the part counts them, at the number of variables of
                  the shape's first stage; what follows where it accepts
  uNumbers_written, uNumbers_bite, uNumbers_at_files   **it accepts at the written sizes**: seven
                  variables; o_u's run has 10,808 coins, the first mask's 167; **and it can fail**:
                  uNumbersB rejects there at a first coin greater by one, at a length smaller by
                  one, and at eight variables
  shared_entries_written   in scope the entries of the description's shared rounds are the written
                  ones
  foldK_written, foldK_at_files   **the first fold behind "send o_u" has as many declared rounds
                  "FOLD round" as the shape's first stage has variables**: seven
  foldSeed_written, foldSeed_bite   at the written list of the shared chain's rounds (68: the
                  library's dryProofFull_length, Johnson/G/DryProofLit.lean): behind the round 1:
                  the rounds 9 and 17; behind the round 17: the rounds 19 and 25
  test_at_files   **the tenth member of the shared list stands at ⟨2, none, 9, K12⟩ and declares the
                  written rounds of the folded row's test**: by the library's plan_at_seat_U,
                  nums_in_scope_U (Johnson/Loose/H2K12/ClosedAtSeats.lean), k12_rounds
                  (Johnson/Desc/K12/FrameLaws.lean) and rounds_UFull
                  (Johnson/Desc/K12/Law/StretchFull.lean)
  test_cut_written, parts_at_files   the frame's cut at these rounds' names: 9 rounds, then 26; the
                  parts of the list's rounds 9, 17, 19 and 25: 0, 1, 1 and 1 of that member
  foldParts_at_files, fold_in_front, foldTwoParts_at_files   behindFold's two parts there; the first
                  stands in front of the second at every order; **so foldTwoPartsB accepts at the
                  round 1**, where the maker's behindFold returns
  foldTwoParts_bite   **and it can fail: at the same description it does not accept at the round
                  17** (as stated: also where behindFold returns nothing there; that the test's
                  second fold and the sending behind it lie in one part: foldSeed_bite with
                  parts_at_files)
  maskAtBook_at_filter   **at the description: every book whose entries at this owner are the short
                  list's**: MaskAtBook at the parts 0 and 1, and the part 1 stands behind the part 0
                  (StandsBehind, Honest/K14/BookMakers.lean)
  maskAtBook_at_files, maskAtBook_at_raw, maskAtBook_at_written, maskAtBook_at_made   its cases: the
                  short list; **the raw book**, before any of the book's own tests is asked; the
                  book that bookWhole returns, at the written list and at the public part's own
  carriersU_at_files   who spends and who carries, as a form on the members of the short list

What is assumed. That sharedAhead, bookRaw or bookWhole returns: OF THAT PREMISE IS USED: that a
book is there whose entries at the owner are the short list's, and that none of the short list's
eight steps that can reject has rejected · InScope Z, LaidAt. SIX STATEMENTS ARE EVALUATIONS IN
LEAN's KERNEL (decide +kernel): uNumbers_written · uNumbers_bite · foldK_written · foldSeed_written
· foldSeed_bite · test_cut_written. FOUR OF THEM BEAR ALL STATEMENTS OF § 4 (uNumbers_written ·
foldK_written · foldSeed_written · test_cut_written), with cut_send (Honest/K14/BookAtShared.lean)
and, beneath, the library's rounds_UFull: THEY ARE WHY ALL HOLDS AT THE FULL SIZE ALONE.
What is not claimed. That any of the three returns at any file: in this file's own light the
statements that have that premise may be empty. All holds at the order orderOf F alone, at the full
size alone. THAT NONE OF THE BOOK's OWN TESTS IS USED IS, AT THE BOOK THAT bookWhole RETURNS, A WORD
ON THE PROOFS: maskAtBook_at_raw alone bears it in its statement. Nothing on what is or is not
hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookAtU
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten
import Johnson.P5J.NumbersAtHead
import Johnson.Loose.H2K12.ClosedAtSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes (Codes OracleNotice)
open Johnson.G (dryProofFull proofSendsFull)
open H2K.JointK (descN guEntry pGu)
open H2K.Member (piUFull dsOf)
open ProofFile.Honest.BookShared
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)
open AtPublicFiles.TreeReads (sized_at written_proof)

/-! ## 1 The numbers -/

/-- How the part at "send o_u" lays its messages, of the shape alone: a second text of the field
sort of jobU (Honest/K14/Sendings.lean), with the shape as a letter: uNumbers_of holds the two
together by unfolding, and fails if either turns. Where the shape has no first stage: plainly. -/
def uSortOf (S : OnBytes.Params.LinShape) : Nat → MsgSort := fun k =>
  if k == 0 then .plain S.fold.rowsHigh else
    match S.testU.head? with
    | some s => .fresh s.k s.h
    | none => .plain false

/-- **One test on public numbers**: uNumbersB (Honest/K14/BookAtU.lean) at the sending's notices as
the shape has them, at the number of variables of the shape's first stage (0 where there is none),
at o_u's count and the first mask's count as the part counts them. -/
def uHeadNumbersB (codes : Codes) (S : OnBytes.Params.LinShape) : Bool :=
  uNumbersB codes ((Desc.K14.withU S).getD #[]).toList ((S.testU.head?.map (·.k)).getD 0)
    (offsetOf codes ((Desc.K14.withU S).getD #[]) (uSortOf S) 1)
    (dueOf codes (((Desc.K14.withU S).getD #[]).getD 1 default).shape (uSortOf S 1))

/-- What follows where it accepts, at every plan with these codes and this shape. -/
theorem uNumbers_of (A : SendPub) (h : uHeadNumbersB A.P.codes A.P.S = true) :
    uNumbersB A.P.codes ((Desc.K14.withU A.P.S).getD #[]).toList (maskRounds A) (maskFirstCoin A)
      (maskRun A).2 = true := by
  have e : (jobU A).Q.sent = (Desc.K14.withU A.P.S).getD #[] := Desc.K14.Law.parK1_sent _ _ _ _
  unfold maskRun maskFirstCoin maskRounds
  rw [e]
  exact h

/-- **The test accepts at the written sizes**; the three numbers there. -/
theorem uNumbers_written : uHeadNumbersB proofSizedFull.codes proofSizedFull.batch.shape = true ∧
    (proofSizedFull.batch.shape.testU.head?.map (·.k)).getD 0 = 7 ∧
    offsetOf proofSizedFull.codes ((Desc.K14.withU proofSizedFull.batch.shape).getD #[])
      (uSortOf proofSizedFull.batch.shape) 1 = 10808 ∧
    dueOf proofSizedFull.codes
      (((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).getD 1 default).shape
      (uSortOf proofSizedFull.batch.shape 1) = 167 := by decide +kernel

/-- **IT CAN FAIL**: at the written sizes uNumbersB accepts at 7, 10,808 and 167, and rejects at a
first coin greater by one, at a length smaller by one, and at eight variables. -/
theorem uNumbers_bite :
    uNumbersB proofSizedFull.codes ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).toList
        7 10808 167 = true ∧
      uNumbersB proofSizedFull.codes ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).toList
        7 10809 167 = false ∧
      uNumbersB proofSizedFull.codes ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).toList
        7 10808 166 = false ∧
      uNumbersB proofSizedFull.codes ((Desc.K14.withU proofSizedFull.batch.shape).getD #[]).toList
        8 10808 167 = false := by decide +kernel

/-! ## 2 The rounds' entries -/

/-- At the written list of the shared chain's rounds: the first fold behind round 1 has seven rounds
"FOLD round". -/
theorem foldK_written :
    foldK ((dryProofFull.2.1.map fun x => ({ entry := x.1.entry } : Fmt.DeclaredRound)).drop 2) =
      some 7 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **In scope the entries of the description's shared rounds are the written ones.** -/
theorem shared_entries_written (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ((F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).map (·.entry) =
      dryProofFull.2.1.map (·.1.entry) := by
  have hw := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z scope
    (LPFD.asks_written L.asks)).1
  exact (Johnson.G.OfPlan.writtenOf_entries hw).2.1.symm

/-- **At the description the first fold behind "send o_u" has as many declared rounds "FOLD round"
as the shape's first stage has variables.** -/
theorem foldK_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) :
    foldK (((F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).drop 2) =
      some (maskRounds ⟨qAt Zp Np, a⟩) := by
  have e1 : maskRounds ⟨qAt Zp Np, a⟩ = 7 := by
    show (Zp.p.chains.made.sized.proof.batch.shape.testU.head?.map (·.k)).getD 0 = 7
    rw [sized_at scope L, written_proof]
    exact uNumbers_written.2.1
  rw [e1, ← foldK_written]
  refine foldK_congr ?_
  rw [List.map_drop, List.map_drop, shared_entries_written scope L, List.map_map]
  rfl

/-- The test on the numbers accepts at the description's plan. -/
theorem uNumbers_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    uHeadNumbersB (qAt Zp Np).codes (qAt Zp Np).S = true := by
  show uHeadNumbersB Zp.p.chains.made.sized.proof.codes
    Zp.p.chains.made.sized.proof.batch.shape = true
  rw [sized_at scope L, written_proof]
  exact uNumbers_written.1

/-- **At the written list of the shared chain's rounds**: behind the round 1: the rounds 9 and
17. -/
theorem foldSeed_written : foldSeedAt (dryProofFull.2.1.map (·.1.entry)) 1 = some (9, 17) := by
  decide +kernel

/-- Behind the round 17: the rounds 19 and 25. -/
theorem foldSeed_bite : foldSeedAt (dryProofFull.2.1.map (·.1.entry)) 17 = some (19, 25) := by
  decide +kernel

/-- The frame's cut at the names of the written rounds of the folded row's test: 9 rounds, then 26;
there are 35. -/
theorem test_cut_written :
    cutOfNames .K12 ((dsOf piUFull).map (·.entry.name)) = [9, 26] ∧ (dsOf piUFull).length = 35 := by
  decide +kernel

/-! ## 3 The folded row's test -/

/-- **At the description the tenth member of the shared list stands at the folded row's test's place
and declares that test's written rounds.** -/
theorem test_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ t rest, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.drop 9 = t :: rest ∧
      t.place = { chain := 2, link := none, piece := 9, kind := .K12 } ∧
      t.rounds = dsOf piUFull := by
  have hp : (descN OnBytes.secondHashFunction ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF).planOk = true := L.planOk
  have hpin := LPFD.asks_written L.asks
  have hn := H2K.JointK.nums_in_scope_U scope Zp L.pub ProofFile.pureRoad.links Np cF L.places hp hpin
  have hq := H2K.JointK.plan_at_seat_U OnBytes.secondHashFunction Zp ProofFile.pureRoad.links Np cF hp
  have hr := VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts (pGu Np) hq
  rw [hn, H2K.Member.rounds_UFull] at hr
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := made_of_laid L
  have hsh : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = _ :=
    H2K.JointK.descN_shared OnBytes.secondHashFunction ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF
  have hlen : (H2K.JointK.sharedPre ProofFile.Cl Zp.p.chains (H2K.JointK.p14N Zp Np) Np).length = 9 := by
    have hb' : Desc.K14.blocks (H2K.JointK.p14N Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8] := hb
    unfold H2K.JointK.sharedPre Desc.K14.blocksOr
    rw [hb']
    rfl
  refine ⟨guEntry ProofFile.Cl Np, (Np.O.toList.map fun nO => H2K.JointK.omegaEntry ProofFile.Cl nO) ++
    [H2K.JointK.sharedEnd ProofFile.Cl (H2K.JointK.p14N Zp Np) Np], ?_, ?_, ?_⟩
  · rw [hsh]
    exact List.drop_left' hlen
  · show (proximityTestKind guardedProximityTestParts (pGu Np) : Block VerifiableInference.Desc.K12.T12 Unit).place = _
    rw [H2K.JointK.place_of_k12]
    exact H2K.JointK.place_of_p12At _ _
  · rw [(H2K.JointK.guEntry_sits ProofFile.Cl Np).rounds]
    exact (Option.some.inj hr).symm

/-- **The parts of the shared list's rounds 9, 17, 19 and 25**: the parts 0, 1, 1 and 1 of the
folded row's test. -/
theorem parts_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 9 =
        some { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } ∧
      addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 17 =
        some { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } ∧
      addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 19 =
        some { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } ∧
      addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder 25 =
        some { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  obtain ⟨t, rest, hd, hpl, hrd⟩ := test_at_files scope L
  have hX := form_at_files scope L
  have hcut : partsCut t = [9, 26] := by
    unfold partsCut
    rw [hpl, hrd]
    exact test_cut_written.1
  have hlen : t.rounds.length = 35 := by
    rw [hrd]
    exact test_cut_written.2
  have at_ : ∀ j, j < 35 → addrOfRound (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder (8 + j) =
      some ⟨{ chain := 2, link := none, piece := 9, kind := .K12 },
        (([0, 9] : List Nat).filter (· ≤ j)).length - 1⟩ := by
    intro j hj
    rw [form_skip9 hX j, hd, addrOfRound, if_pos (by rw [hlen]; exact hj), hcut, hpl]
    rfl
  exact ⟨at_ 1 (by omega), at_ 9 (by omega), at_ 11 (by omega), at_ 17 (by omega)⟩

/-- **The fold behind the round 1, and the part that sends what it leaves: the parts 0 and 1 of the
folded row's test**, where the maker's behindFold returns there. -/
theorem foldParts_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {p q : Addr}
    (h : behindFold (planOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) 1 = some (p, q)) :
    p = { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } ∧
      q = { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  obtain ⟨e, s, hes, hp, hq⟩ := behindFold_seeds h
  rw [planOf_rounds, shared_entries_written scope L, foldSeed_written] at hes
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hes)
  rw [addrIn_planOf] at hp hq
  obtain ⟨a9, a17, -, -⟩ := parts_at_files scope L
  exact ⟨Option.some.inj (hp.symm.trans a9), Option.some.inj (hq.symm.trans a17)⟩

/-- **The part 0 of the folded row's test stands in front of its part 1**, at every order of places:
a case of the frame's Addr.before_same (Honest/Law/Rule/Tests.lean): the second arm of Addr.before:
the same place, the smaller number of the part. -/
theorem fold_in_front (ord : List Place) :
    Addr.before ord { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } = true :=
  Addr.before_same ord _ (by decide)

/-- **So the test foldTwoPartsB accepts at the round 1**, where the maker's behindFold returns. -/
theorem foldTwoParts_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : (behindFold (planOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) 1).isSome = true) :
    foldTwoPartsB (planOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) 1 = true := by
  obtain ⟨⟨p, q⟩, hpq⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨rfl, rfl⟩ := foldParts_at_files scope L hpq
  unfold foldTwoPartsB
  rw [hpq]
  decide

/-- **IT CAN FAIL: at the same description the test does not accept at the round 17.** As stated
that holds also where behindFold returns nothing there; that the folded row's test's second fold and
the sending behind it lie in one part: foldSeed_bite with parts_at_files. -/
theorem foldTwoParts_bite (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    foldTwoPartsB (planOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) 17 = false := by
  unfold foldTwoPartsB
  cases hb : behindFold (planOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) 17 with
  | none => rfl
  | some pq =>
    obtain ⟨p, q⟩ := pq
    obtain ⟨e, s, hes, hp, hq⟩ := behindFold_seeds hb
    rw [planOf_rounds, shared_entries_written scope L, foldSeed_bite] at hes
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hes)
    rw [addrIn_planOf] at hp hq
    obtain ⟨-, -, a19, a25⟩ := parts_at_files scope L
    obtain rfl := Option.some.inj (hp.symm.trans a19)
    obtain rfl := Option.some.inj (hq.symm.trans a25)
    decide

/-! ## 4 At the description -/

/-- **AT THE DESCRIPTION: EVERY BOOK WHOSE ENTRIES AT THIS OWNER ARE THE SHORT LIST's**, where the
short list returns at the written list of sendings: its entries there are the four, at the parts 0
and 1 of the folded row's test; the three tests accept; what is known at the part 0 is one entry,
o_u's whole run; and the part 1 stands behind the part 0 in the description's own order. -/
theorem maskAtBook_at_filter (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) {l : List Ahead}
    (h : sharedAhead (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.2.1 = .ok l) {B : ProverCoinCounts}
    (hf : B.ahead.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) =
      l.filter fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) :
    MaskAtBook ⟨qAt Zp Np, a⟩ B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } ∧
      StandsBehind (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  obtain ⟨hfit, hs, -, -, hm, s, hst⟩ := sendings_of_laid scope L
  obtain ⟨hNO, -, -⟩ := headNumbers_give ⟨qAt Zp Np, a⟩ hs (numbers_at_files scope L)
  have hX := form_at_files scope L
  have hpl := ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places
  have hS := sharedSends_at_files scope L
  have hk := foldK_at_files scope L a
  have hN := uNumbers_of ⟨qAt Zp Np, a⟩ (uNumbers_at_files scope L)
  obtain ⟨p₀, q₀, hb₀, -⟩ := four_at_u hX hS hk hN hNO h
  have h2 := foldTwoParts_at_files scope L (by rw [hb₀]; rfl)
  obtain ⟨p, q, hb, hA⟩ := maskAtBook_of_filter hX hpl ⟨qAt Zp Np, a⟩ hS hk hN hNO h2 hfit hm
    (by show (qAt Zp Np).S.testU.head?.isSome = true; rw [hst]; rfl) h hf
  obtain ⟨rfl, rfl⟩ := foldParts_at_files scope L hb
  exact ⟨hA, fold_in_front _, Addr.before_asymm _ (fold_in_front _), by decide⟩

/-- **At the short list**, laid into any book. -/
theorem maskAtBook_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) {l : List Ahead}
    (h : sharedAhead (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.2.1 = .ok l) (B₀ : ProverCoinCounts) :
    MaskAtBook ⟨qAt Zp Np, a⟩ { B₀ with ahead := l } (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } ∧
      StandsBehind (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } :=
  maskAtBook_at_filter scope L a h rfl

/-- Who spends and who carries, as a form on the members of the short list: the one entry that
spends is handed to the part 0 of the folded row's test; o_u's whole run is carried to that part,
and else to the parts 0 and 1 alone; AN ENTRY THAT CARRIES THE FIRST MASK's WHOLE RUN CARRIES IT TO
THE PART 1 (that there is such an entry this form does not say: MaskFourAt, in maskAtBook_at_files,
does); and the part 1 stands behind the part 0. -/
theorem carriersU_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) {l : List Ahead}
    (h : sharedAhead (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.2.1 = .ok l) :
    MaskCarriersAt l { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 }
        (maskRounds ⟨qAt Zp Np, a⟩) (maskFirstCoin ⟨qAt Zp Np, a⟩) (maskRun ⟨qAt Zp Np, a⟩).2 ∧
      StandsBehind (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  obtain ⟨hA, hB⟩ := maskAtBook_at_files scope L a h ⟨[], [], [], [], []⟩
  exact ⟨maskCarriers_of_four hA.1, hB⟩

/-- **AT THE RAW BOOK: THE BOOK THAT bookRaw RETURNS, BEFORE ANY OF ITS OWN TESTS IS ASKED**, at the
written list. -/
theorem maskAtBook_at_raw (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat)
    {p0 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (hW : bookRaw (F0T OnBytes.secondHashFunction Zp Np cF) p0 proofSendsFull.2.1 p2 M = .ok W) :
    MaskAtBook ⟨qAt Zp Np, a⟩ W (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  have hpl := ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places
  obtain ⟨l, hl, hfil⟩ := bookRaw_ahead_shared hW
  exact (maskAtBook_at_filter scope L a hl (hfil { place := sendPlace 2, part := 0 }
    (fun h => absurd (chain_first hpl _ h) (by decide))
    (fun h => absurd (chain_second hpl _ h) (by decide)))).1

/-- **At the book that bookWhole returns**, at the written list. -/
theorem maskAtBook_at_written (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat)
    {p0 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) p0 proofSendsFull.2.1 p2 M = .ok B) :
    MaskAtBook ⟨qAt Zp Np, a⟩ B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  have hpl := ((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).places
  obtain ⟨l, hl, hfil⟩ := bookWhole_ahead_shared hB
  exact (maskAtBook_at_filter scope L a hl (hfil { place := sendPlace 2, part := 0 }
    (fun h => absurd (chain_first hpl _ h) (by decide))
    (fun h => absurd (chain_second hpl _ h) (by decide)))).1

/-- The same at the public part's own three lists. -/
theorem maskAtBook_at_made (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 M = .ok B) :
    MaskAtBook ⟨qAt Zp Np, a⟩ B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF))
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  rw [made_sends_at_files scope L] at hB
  exact maskAtBook_at_written scope L a hB

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.uNumbers_of
#print axioms ProofFile.Honest.K14.uNumbers_written
#print axioms ProofFile.Honest.K14.uNumbers_bite
#print axioms ProofFile.Honest.K14.foldK_written
#print axioms ProofFile.Honest.K14.shared_entries_written
#print axioms ProofFile.Honest.K14.foldK_at_files
#print axioms ProofFile.Honest.K14.uNumbers_at_files
#print axioms ProofFile.Honest.K14.foldSeed_written
#print axioms ProofFile.Honest.K14.foldSeed_bite
#print axioms ProofFile.Honest.K14.test_cut_written
#print axioms ProofFile.Honest.K14.test_at_files
#print axioms ProofFile.Honest.K14.parts_at_files
#print axioms ProofFile.Honest.K14.foldParts_at_files
#print axioms ProofFile.Honest.K14.fold_in_front
#print axioms ProofFile.Honest.K14.foldTwoParts_at_files
#print axioms ProofFile.Honest.K14.foldTwoParts_bite
#print axioms ProofFile.Honest.K14.maskAtBook_at_filter
#print axioms ProofFile.Honest.K14.maskAtBook_at_files
#print axioms ProofFile.Honest.K14.carriersU_at_files
#print axioms ProofFile.Honest.K14.maskAtBook_at_raw
#print axioms ProofFile.Honest.K14.maskAtBook_at_written
#print axioms ProofFile.Honest.K14.maskAtBook_at_made
