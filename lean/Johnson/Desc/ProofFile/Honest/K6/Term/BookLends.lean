-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/BookLends.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN, AND WHERE THE MAKER RETURNS,
THE BOOK OF COINS LENDS THIS KIND's SIDE ITS RUNS. The proofs of HeadRowPaysAtAnyBook,
BookLendsTheKindAtTheBase and BookLendsTheKindAtTheFilling (Honest/K6/Term/Statements.lean).

WHAT IT IS NOT. It does not say that a verifier accepts anything, that a part plays or that a round
is reached: "a side pays" (SidePays, Honest/Law/ReadyOfSides.lean) says that the frame's set-up
routine chainSteps returns at the one member at which the side stands; what it returns is not said.
The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and "the maker
returns" are premises of every theorem from sixTestsAtTheMember on: that the maker returns at any
filling is not shown here, and where it does not return these theorems hold of nothing. Nothing on
soundness, on completeness as a whole, or on what a proof hides.

WORDS. The maker is onlineProverFromPublicFiles (Honest/AtPure.lean): of the three public files and a filling it makes
the online description, the book of coins and the prover. A filling (OnlineProverParts) holds the senders that
the maker lays into the prover. A side is one sender, seated at one place of a chain; the row is
this kind's side, headRow (Honest/K6/Part.lean), a list of eight parts. The book's maker is
bookWhole (Honest/BookWhole.lean). A member is a sub-protocol of a chain's flat list; this kind's is
number 341 of the first chain, counted from 0. A letter is an argument that is left general. The
base filling is onlineProverPartsInUse; the honest prover's own filling is that filling read through two
readers, one of the index and one of the stored tables' randomness (onlineFillingAt).

WHAT IT IS. No definition; eleven theorems. Up to stepsReturnAtTheProversList the filling, the types
of the index and of the stored tables' randomness and the row's reader are letters.

  rowCutInNumerals        under the hypothesis: the row's eight parts have 1, 1, 26, 1, 1, 13, 13,
                          26 rounds
  memberCutInNumerals     under the hypothesis: the book's maker cuts the member at the kind's place
                          into the same eight numbers
  rowIsCutAsTheMember     so the row's parts' numbers of moves are the member's cut
  sixTestsAtTheMember     the six premises of sidePays_of_tests at that member, at the book of any
                          return of the maker
  headRowPaysAtAnyBook    **the statement HeadRowPaysAtAnyBook**
  kindPaysOfTheOnlySide   at any return of the maker, under a third premise: the row is the only
                          side of the kind in the prover's first chain. Then every side of the kind
                          pays, in all three chains. In the two later chains there is no such side
                          (laterSidesLackTheKind, Honest/K6/Term/LaterChains.lean), so these two
                          clauses hold of nothing
  stepsReturnAtTheProversList   against emptiness, under the same three premises: a member of the
                          first chain does stand at the place, and chainSteps returns at it at the
                          prover's own list of sides
  bookLendsTheKindAtTheBase, stepsReturnAtTheBase   **the statement BookLendsTheKindAtTheBase**, and
                          that it is not empty: these two lemmas at the base filling, where the
                          third premise is sideAtTheBase (Honest/K6/Term/SideAtFilling.lean)
  bookLendsTheKindAtTheFilling, stepsReturnAtTheFilling   **the statement
                          BookLendsTheKindAtTheFilling**, and that it is not empty: the same at the
                          filling read through, by sideAtTheFilling

WHERE EACH OF THE SIX COMES FROM. (1) the member has as many lists of oracle messages as rounds: the
description's own test on the plan (planOk_all, shaped_parts). (2) as many rounds: rounds_of_cut.
(3) the book's cut at the place: bookWhole_cut_first. (4), (5) no row and no entry of the book for a
ninth part: bookWhole_tests_at. (6) the lending returns: k6_row_is_lent
(Honest/K6/Law/LendsAtBook.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.Statements
import Johnson.Desc.ProofFile.Honest.K6.Term.SideAtFilling
import Johnson.Desc.ProofFile.Honest.K6.Term.LaterChains
import Johnson.Desc.ProofFile.Honest.K6.Law.LendsAtBook
import Johnson.Desc.ProofFile.Honest.K6.Law.Plays
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.Small.StepsOfBook
import Johnson.Desc.ProofFile.Honest.Small.RoundsOfCut
import Johnson.Desc.ProofFile.Honest.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (numbers_in_scope)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

variable {W₀ Rc X₀ : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 The row and the member are cut alike -/

/-- Under the library's hypothesis on the first chain: **how many rounds each of the row's eight
parts has**, in numerals. -/
theorem rowCutInNumerals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    headCut (headNumbers Zp) = [1, 1, 26, 1, 1, 13, 13, 26] := by
  have numbers := numbers_in_scope h.scope h.reads h.pubOne
  have positions : headLt (headNumbers Zp) = 10 := numbers.lt
  have features : headLPd (headNumbers Zp) = 13 := by
    show OnBytes.Model.clog2 (P5J.At.X Zp).hS.d = 13
    rw [numbers.d]
    decide
  have written : headCut (headNumbers Zp) =
      [1, 1, headLPd (headNumbers Zp) + headLt (headNumbers Zp) + 3, 1, 1,
        headLt (headNumbers Zp) + 3, headLt (headNumbers Zp) + 3,
        headLt (headNumbers Zp) + headLPd (headNumbers Zp) + 3] := rfl
  rw [positions, features] at written
  exact written

/-- Under the same hypothesis: **the book's maker cuts the member at the kind's place into the same
eight numbers.** -/
theorem memberCutInNumerals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {member : Block TS Cl}
    (isMember : member ∈ cF.blocksInOrder) (atPlace : member.place = IM.k6Place) :
    partsCut member = [1, 1, 26, 1, 1, 13, 13, 26] := by
  have kind : member.place.kind = .K6 := by rw [atPlace]
  unfold partsCut
  rw [k6_rounds_at_head h isMember atPlace, kind, k6_names_of]
  exact k6_cut_closed

/-- So **the row's parts' numbers of moves are the member's cut.** -/
theorem rowIsCutAsTheMember (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {member : Block TS Cl}
    (isMember : member ∈ cF.blocksInOrder) (atPlace : member.place = IM.k6Place)
    (reader : Local W₀ Rc Inst Cells → HeadAsk) :
    (headRow (X := Unit) reader (headNumbers Zp) IM.k6Place).map (·.moves.length) =
      partsCut member := by
  rw [headRow_cut, rowCutInNumerals h, memberCutInNumerals h isMember atPlace]

/-! ## 2 The six tests at the member -/

/-- **The six premises of sidePays_of_tests at the member at the kind's place, at the book of any
return of the maker.** The library's hypothesis on the first chain and "the maker returns" are
premises. -/
theorem sixTestsAtTheMember (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ Unit} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (reader : Local W₀ Rc Inst Cells → HeadAsk) {member : Block TS Cl}
    (isMember : member ∈ cF.blocksInOrder) (atPlace : member.place = IM.k6Place) :
    member.oracles.length = member.rounds.length ∧
    (⟨IM.k6Place, headRow reader (headNumbers Zp) IM.k6Place⟩ :
      Placed (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) Unit).rounds =
        member.rounds.length ∧
    A.B.cuts.lookup member.place =
      some ((headRow (X := Unit) reader (headNumbers Zp) IM.k6Place).map (·.moves.length)) ∧
    (A.B.rowsOf 0).any (fun row => row.1.place == member.place &&
      decide ((headRow (X := Unit) reader (headNumbers Zp) IM.k6Place).length ≤ row.1.part)) =
        false ∧
    A.B.ahead.any (fun entry => entry.spender.place == member.place &&
      decide ((headRow (X := Unit) reader (headNumbers Zp) IM.k6Place).length ≤
        entry.spender.part)) = false ∧
    ∃ (coins₀ : Coins A.B)
      (lent : RowCoins (headRow (X := Unit) reader (headNumbers Zp) IM.k6Place)),
      lendRow A.B (A.B.rowsOf 0) (coins₀.look 0) member.place
        (headRow (X := Unit) reader (headNumbers Zp) IM.k6Place) 0 = .ok lent := by
  -- the maker's book is the whole book at the hypothesis's own description
  obtain ⟨p0, p1, p2, hB⟩ := k6_book_of_atPure hA
  rw [(atPure_at_laid h.laid hA).2] at hB
  have placesOk := k6_placesOk_at_head h
  have kind : member.place.kind = .K6 := by rw [atPlace]
  have cut := rowIsCutAsTheMember h isMember atPlace reader
  have noSeed := k6_seedless_at_head h isMember atPlace
  have noFold : ∀ round ∈ member.rounds, round.entry.name ≠ "FOLD epsilon" :=
    (k6_numbers_of_rounds kind (k6_rounds_at_head h isMember atPlace) cF.blocksInOrder).2.2.2
  have hasRound : member.rounds ≠ [] := by
    intro empty
    have sum := (partsCut_sum member).1
    rw [memberCutInNumerals h isMember atPlace, empty] at sum
    exact absurd sum (by decide)
  have parts : (partsCut member).length ≤
      (headRow (X := Unit) reader (headNumbers Zp) IM.k6Place).length :=
    Nat.le_of_eq (by rw [← cut, List.length_map])
  obtain ⟨noRow, noEntry⟩ := bookWhole_tests_at (F := F0T OnBytes.secondHashFunction Zp Np cF) hB placesOk
    (b := member) isMember noSeed noFold parts
  refine ⟨?_, rounds_of_cut cut, ?_, noRow, noEntry, default, ?_⟩
  · exact (shaped_parts ((planOk_all h.laid.planOk).1 member isMember).2).1
  · rw [cut]
    exact bookWhole_cut_first (F := F0T OnBytes.secondHashFunction Zp Np cF) hB placesOk (b := member) isMember
      hasRound
  · rw [atPlace]
    exact k6_row_is_lent h hA reader default

/-! ## 3 The statement -/

/-- **Under the library's hypothesis on the first chain, the row pays at the book of any return of
the maker.** The hypothesis and "the maker returns" are premises. -/
theorem headRowPaysAtAnyBook : HeadRowPaysAtAnyBook := by
  intro W₀ Rc X₀ Z D r Zp Np cF x P A reader h hA
  exact sidePays_of_tests A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
    (⟨IM.k6Place, headRow reader (headNumbers Zp) IM.k6Place⟩ :
      Placed (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) Unit)
    fun _ isMember atPlace => sixTestsAtTheMember h hA reader isMember atPlace

/-! ## 4 The kind pays -/

/-- **At any return of the maker: where the row is the only side of the kind in the prover's first
chain, the kind pays in all three chains.** In the shared and the last chain that holds of nothing:
the prover has no side of the kind there. The filling and the row's reader are letters. Three
premises: the library's hypothesis on the first chain, "the maker returns", and onlySide. -/
theorem kindPaysOfTheOnlySide (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ Unit} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (reader : Local W₀ Rc Inst Cells → HeadAsk)
    (onlySide : SideIsTheOnlyOne A.H.first
      ⟨IM.k6Place, headRow reader (headNumbers Zp) IM.k6Place⟩) :
    KindPays A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first .K6 ∧
      KindPays A.B 1 (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder A.H.shared .K6 ∧
      KindPays A.B 2 (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder A.H.second .K6 := by
  obtain ⟨sharedLacks, lastLacks⟩ := laterSidesLackTheKind h hA
  refine ⟨fun side isSide kind => ?_, fun side isSide kind => absurd kind (sharedLacks side isSide),
    fun side isSide kind => absurd kind (lastLacks side isSide)⟩
  rw [onlySide.2 side isSide kind]
  exact headRowPaysAtAnyBook W₀ Rc X₀ Z D r Zp Np cF x P A reader h hA

/-- **Against emptiness: it pays of something, at the prover's own list.** Under the same three
premises a member of the first chain does stand at the kind's place, and chainSteps returns at it at
the prover's own list of sides, at every view and every run's coins. -/
theorem stepsReturnAtTheProversList (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ Unit} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (reader : Local W₀ Rc Inst Cells → HeadAsk)
    (onlySide : SideIsTheOnlyOne A.H.first
      ⟨IM.k6Place, headRow reader (headNumbers Zp) IM.k6Place⟩) :
    ∃ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, member.place = IM.k6Place ∧
      ∀ (view : Option (Local W₀ Rc Inst Cells)) (coins : Coins A.B),
        ∃ steps, chainSteps A.B (A.B.rowsOf 0) (coins.look 0) view [member] A.H.first =
          .ok steps := by
  obtain ⟨member, isMember, atPlace⟩ := k6_member_there h
  refine ⟨member, isMember, atPlace, fun view coins => ?_⟩
  refine headRowPaysAtAnyBook W₀ Rc X₀ Z D r Zp Np cF x P A reader h hA member isMember atPlace
    A.H.first ?_ view coins
  rw [atPlace]
  exact onlySide.1

/-! ## 5 At the two fillings -/

/-- **The kind pays at the base filling**, in all three chains; in the shared and the last chain
that holds of nothing. Two premises: the library's hypothesis on the first chain and "the maker
returns at the base filling". -/
theorem bookLendsTheKindAtTheBase : BookLendsTheKindAtTheBase := by
  intro W₀ Z D r Zp Np cF x I S O A h hA
  exact kindPaysOfTheOnlySide h hA (headReader id I Zp A.G) (sideAtTheBase h I S O hA)

/-- **Against emptiness, at the base filling.** Under the same two premises a member of the first
chain stands at the kind's place, and chainSteps returns at it at the prover's own list of sides. -/
theorem stepsReturnAtTheBase (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, member.place = IM.k6Place ∧
      ∀ (view : Option (Local W₀ IndexCommitterCoins Inst Cells)) (coins : Coins A.B),
        ∃ steps, chainSteps A.B (A.B.rowsOf 0) (coins.look 0) view [member] A.H.first =
          .ok steps :=
  stepsReturnAtTheProversList h hA (headReader id I Zp A.G) (sideAtTheBase h I S O hA)

/-- **The kind pays at the filling read through**, which is the form of the honest prover's own
filling, in all three chains; in the shared and the last chain that holds of nothing. Two premises:
the library's hypothesis on the first chain and "the maker returns at that filling". -/
theorem bookLendsTheKindAtTheFilling : BookLendsTheKindAtTheFilling := by
  intro W₀ W₀' Rc' Z D r Zp Np cF x readIndex readRandomness namedIndex I S O A h hA
  exact kindPaysOfTheOnlySide h hA (headReader readIndex I Zp A.G)
    (sideAtTheFilling h readIndex readRandomness namedIndex I S O hA)

/-- **Against emptiness, at the filling read through.** Under the same two premises a member of the
first chain stands at the kind's place, and chainSteps returns at it at the prover's own list of
sides. -/
theorem stepsReturnAtTheFilling {W₀' Rc' : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A) :
    ∃ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, member.place = IM.k6Place ∧
      ∀ (view : Option (Local W₀' Rc' Inst Cells)) (coins : Coins A.B),
        ∃ steps, chainSteps A.B (A.B.rowsOf 0) (coins.look 0) view [member] A.H.first =
          .ok steps :=
  stepsReturnAtTheProversList h hA (headReader readIndex I Zp A.G)
    (sideAtTheFilling h readIndex readRandomness namedIndex I S O hA)

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.rowCutInNumerals
#print axioms ProofFile.Honest.K6.Term.memberCutInNumerals
#print axioms ProofFile.Honest.K6.Term.rowIsCutAsTheMember
#print axioms ProofFile.Honest.K6.Term.sixTestsAtTheMember
#print axioms ProofFile.Honest.K6.Term.headRowPaysAtAnyBook
#print axioms ProofFile.Honest.K6.Term.kindPaysOfTheOnlySide
#print axioms ProofFile.Honest.K6.Term.stepsReturnAtTheProversList
#print axioms ProofFile.Honest.K6.Term.bookLendsTheKindAtTheBase
#print axioms ProofFile.Honest.K6.Term.stepsReturnAtTheBase
#print axioms ProofFile.Honest.K6.Term.bookLendsTheKindAtTheFilling
#print axioms ProofFile.Honest.K6.Term.stepsReturnAtTheFilling
