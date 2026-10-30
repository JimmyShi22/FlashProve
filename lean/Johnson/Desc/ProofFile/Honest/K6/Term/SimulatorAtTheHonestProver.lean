--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/SimulatorAtTheHonestProver.lean: what the sub-protocol "the
output head's own rounds" (kind K6) hands in for the zero knowledge of the online honest prover, TIED
TO A PROVER. FIRST, AND THIS IS WHAT IS HANDED IN: TO THE BASE PROVER, the maker's return at the filling
before it is read through, at which the frame's invariants are laid and from which the statements on
zero knowledge are to cross once to the honest prover, by a lemma of other authors that this file
does not import. THE BASE PROVER IS NOT THE PROVER THAT PLAYS. THEN THE SAME AT THE HONEST PROVER OF THE
PROTOCOL (E2E/TheHonestProver.lean): K6 needs no crossing, because both follow from one statement
that is general in the filling.

One place under three names. `IM.k6Place` is chain 1, link 24, piece 4; it is number 341 of the first
chain's flat list; the paper pages call it H:4.

WHAT IS TIED, at public files in scope that pass the library's test, at whatever the maker returns
(`SimulatorShareAtTheProver`):
  * the returned description is `F0T secondHashFunction returned.Z places firstChain`, at the places and the first
    chain that the returned public part makes; at the honest prover also: the online honest prover IS
    `onlineProverAt` at that return, which plays at that term
  * the lot of rows with simulators lays one row, and that row's parts ARE the side of the returned
    prover at K6's place; every side of that prover of the kind, in any chain, is that side (that it
    stands once in the list, under the library's hypothesis on the first chain and where the maker
    returns: `sidesOfTheKindAtTheBase`, `sidesOfTheKindAtTheFilling`,
    Honest/K6/Term/SideAsAList.lean); no other member of the description is of the kind; the book
    lends that side its runs (these: E2E/OutputHeadAtTheHonestProverProved.lean). The prover that
    `onlineProverAt` hands to the frame is the returned one with its stored table and its key set by
    the committer; it has the same sides in the first chain (`framedProverKeepsTheSides`, there)
  * what the returned book says of the row: lent; one stretch of 173 coins of a named owner; shared
    with no other spender (`BookAtTheHead`, Honest/K6/Term/BookAtTheHead.lean)
  * at that row: `HeadSimulatorShare` (Honest/K6/Term/SimulatorShare.lean)
Beside it: all premises of the field `exact` can be met together at each of the row's eight members
(Honest/K6/Term/ExactIsAsked.lean), so that the share is asked somewhere.

WHAT IT IS NOT. All that the heads of Honest/K6/Term/SimulatorShare.lean and MarginalLaw.lean say holds
here: no zero knowledge, no hiding, no joint law; `plays` and `acc` hold emptily; the owner's `fresh`
and the carriers' `exact` are other kinds' (Honest/K6/Term/OwedBeside.lean); nothing of `Owed.runs`;
nothing at a zero challenge, which is no challenge that the verifier's rounds can draw.
  * IT DOES NOT GIVE "the kind pays" for a list of all kinds' rows. Whoever joins the rows has to show
    that a row of that list at a place of the kind K6 is this row, simulators, On and bud included.
    What is had for that: one row, at K6's place; the kind stands nowhere else.
  * THAT ANY PUBLIC FILES ARE IN SCOPE AND PASS THE TEST is not shown in this file: the two named
    sets do (`inScope_full`, `inScope_gap`, Johnson/Goal/Files/ScopeExample.lean; `theLive_zFull`,
    AtFullSide/Top/LiveAtFull.lean; `theLive_zGap`, AtFullSide/Top/LiveAtPolicies.lean).
    `simulatorShare_is_met` and `simulatorShare_is_met_at_the_base` say: where they do, the maker
    returns.
  * Of the filling (Honest/K1/Law/WSideAtFill.lean) this file ties one thing: the description to onlineProverFromPublicFiles's
    return (the field `description` here). Beside that, the lot's place among its lots (§ 1) and
    that the maker returns at it where the files pass (§ 4, § 5), it shows nothing of the filling.
  * The statements read neither the set of served requests nor any relation on inputs: `exact` stands
    at every state and every input, also at a request on which the model has no result. The
    statements on zero knowledge read the provers under `HonestProvers.refuseUnserved`
    (Johnson/Face/Protocol.lean, not imported here). No statement here names it.

  `headSimulatorLot_in_onlineFilling`, `headSimulatorLot_in_baseFilling`   the lot, its simulators
        forgotten, is a member of the filling's own list of lots
  `headSimulatorLot_is_the_ninth_base_lot`, `…_online_lot`   and in the filling's order: its ninth lot
  `onlineProverCoins`   the online prover's coins are the book's three purses and two run values
  `rowHalf_is_headSide`   the row's parts at its place are the side that the files on completeness name
        (`Term.headSide`, Honest/K6/Term/Statements.lean)
  `SimulatorShareAtTheProver`, `simulatorShare_of_sideAndBook`   the structure; the join, general in the filling
  `simulatorShare_at_the_base_prover`, `simulatorShare_is_met_at_the_base`, `exactIsAsked_at_the_base_prover`,
  `marginalLaw_at_the_base_prover`   AT THE BASE PROVER: what is handed in
  `simulatorShare_at_the_honest_prover`, `simulatorShare_is_met`, `exactIsAsked_at_the_honest_prover`,
  `marginalLaw_at_the_honest_prover`   the same at the honest prover
-/
import E2E.OutputHeadAtTheHonestProverProved
import AtFullSide.Honest.HonestProverLaws
import Johnson.P5J.ChainFree
import Johnson.Desc.ProofFile.Honest.K6.Term.BookAtTheHead
import Johnson.Desc.ProofFile.Honest.K6.Term.ExactIsAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open ProofFile.Honest.Term (matrixInput tableCoins onlineFilling onlineMaker OnlineReturn)
open ProofFile.Honest.K6.Term (SideIsTheOnlyOne)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm (onlineProver onlineProverAt RunValue)
open AtPublicFiles.AtFiles.HonestTerm.OutputHead (SideAndBook baseMaker)
open VerifiableInference.Desc (Chain)

/-! ## 1 The lot is the filling's own -/

/-- The lot of K6's rows, its simulators forgotten, is a member of the base filling's list of lots.
No premise. -/
theorem headSimulatorLot_in_baseFilling :
    (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).toHLot ∈
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots := by
  rw [headSimulatorLot_toHLot]
  exact Term.headLot_mem_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- The same at the online filling, which reads every lot of the base filling through two maps. No
premise. -/
theorem headSimulatorLot_in_onlineFilling (files : VerifierAndGoals.PublicFiles) :
    (headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).toHLot ∈
      (onlineFilling files).lots := by
  rw [headSimulatorLot_toHLot]
  exact Term.headLot_mem_filling id (tableCoins files) matrixInput.dummy matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest

/-- **In the filling's order**: it is the ninth of the base filling's lots (number 8, from 0). With the
like equation for each other lot, a list of lots with simulators has the filling's own list of lots
as its image, in order. No premise. -/
theorem headSimulatorLot_is_the_ninth_base_lot :
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots[8]? =
      some (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).toHLot := by
  rw [headSimulatorLot_toHLot]
  rfl

/-- The same at the online filling. No premise. -/
theorem headSimulatorLot_is_the_ninth_online_lot (files : VerifierAndGoals.PublicFiles) :
    (onlineFilling files).lots[8]? =
      some (headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).toHLot := by
  have e := headSimulatorLot_through (X := Unit) (id : FullSizeMatrix → FullSizeMatrix) (tableCoins files)
    matrixInput.weights
  show ((onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest).lots.map (HLot.thru (Local.thru id (tableCoins files))
      (Local.thru id (tableCoins files))))[8]? = _
  rw [List.getElem?_map, headSimulatorLot_is_the_ninth_base_lot, headSimulatorLot_toHLot]
  exact congrArg some e.symm

/-! ## 2 The prover's coins -/

/-- **The type of the online prover's coins is that of the book's three purses and two run values.**
An equation of types, by unfolding. That the strategy hands these purses to the frame's run as the
run's coins is the text of `honestBatchProverOfFile` (Honest/StratC.lean) and is not stated here. -/
theorem onlineProverCoins {files : VerifierAndGoals.PublicFiles} (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain P5J.TS ProofFile.Cl) :
    (onlineProverAt returned places firstChain).Coin =
      ((Purse returned.B.shared × RunValue) ×
        ((Purse returned.B.first × Purse returned.B.second) × RunValue)) := rfl

/-! ## 3 The share, tied to a prover -/

/-- The row's parts at its place are the side that the files on completeness name. No premise. -/
theorem rowHalf_is_headSide {Rc : Type} (Zp : Pub) (G : Ground) :
    (headUnlettered (Rc := Rc) (X := Unit) (headWit' id (matrixInput.weights Zp) Zp G)
      (Term.headNumbers Zp) IM.k6Place).half = Term.headSide id matrixInput Zp G :=
  headUnlettered_half _ _ _

/-- **K6's share for zero knowledge, tied to a prover that the maker returns at the matrices.** A
definition: a conclusion's form. -/
structure SimulatorShareAtTheProver {Rc : Type} (returned : OnlineProverWithDescription FullSizeMatrix Rc Cells Unit Unit)
    (places : H2U.Places4) (firstChain : Chain P5J.TS ProofFile.Cl)
    (row : Unlettered (Local FullSizeMatrix Rc Inst Cells) (Local FullSizeMatrix Rc Inst Cells) Unit Inst) : Prop where
  /-- the places are what the returned public part makes -/
  placesMade : H2U.placesOfMade returned.Z.made = .ok places
  /-- the first chain is what the returned public part makes -/
  chainMade : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain
  /-- the returned description is the term at which the online prover plays -/
  description : returned.F = P5J.F0T OnBytes.secondHashFunction returned.Z places firstChain
  /-- the lot of rows with simulators lays this one row -/
  oneRow : (headSimulatorLot (Rc := Rc) (X := Unit) matrixInput.weights).rows returned.Z returned.G =
    [row]
  /-- the prover's first side at K6's place is the row's parts, and every side of its first chain of
  the kind is that side. That it stands once in the list is not said -/
  side : SideIsTheOnlyOne returned.H.first row.half
  /-- where the kind stands in the description; that the two later chains have no side of the kind;
  that the book lends the side its runs -/
  sideAndBook : SideAndBook returned places firstChain
  /-- what the returned book says of the row: lent; one stretch of 173 coins of a named owner; shared
  with no other spender -/
  book : BookAtTheHead returned
    (headWit' id (matrixInput.weights returned.Z) returned.Z returned.G)
    (Term.headNumbers returned.Z)
  /-- fits, exact, fresh, On, bud, stops and coins at that row, at the returned description and book -/
  share : HeadSimulatorShare matrixInput.weights returned

section
variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h; the maker returns at a filling P at the matrices; sb: the completeness files'
statement there. The join. -/
theorem simulatorShare_of_sideAndBook {Rc : Type}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x) {P : OnlineProverParts FullSizeMatrix Rc Cells Unit Unit}
    {returned : OnlineProverWithDescription FullSizeMatrix Rc Cells Unit Unit}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned)
    (sb : P5J.AtMgA OnBytes.secondHashFunction files D r₀ returned.Z Np cF x → SideAndBook returned Np cF) :
    ∃ row, SimulatorShareAtTheProver returned Np cF row := by
  obtain ⟨eZ, eF⟩ := atPure_at_laid h.laid made
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some returned.G := by
    rw [← eZ]
    exact (atPure_ok made).2.1
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := sb (by rw [eZ]; exact h)
  refine ⟨headUnlettered (headWit' id (matrixInput.weights Zp) Zp returned.G)
    (Term.headNumbers Zp) IM.k6Place, ?_, ?_, ?_, ?_, ?_, hs, ?_,
    headSimulatorShare_at_maker h made _⟩
  · exact atPure_places h.laid made
  · rw [eZ]
    exact P5J.chain_free O
  · rw [eF, eZ]
  · rw [eZ]
    exact headSimulatorLot_one_row h hG _
  · rw [rowHalf_is_headSide]
    have hside := hs.side
    rw [eZ] at hside
    exact hside
  · rw [eZ]
    exact bookAtTheHead h made _

end

/-! ## 4 At the base prover: what is handed in -/

/-- The library's hypothesis at the full size, from the two tests on the public files. -/
theorem head_of_the_two_tests (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ Zp Np cF x, P5J.AtMgA OnBytes.secondHashFunction files (VerifierAndGoals.AtTheName.dpZ files)
      (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles files)) Zp Np cF x := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  exact P5J.head_exists_at_name files scope read live (P5J.owed_of_live live)

/-- **AT THE BASE PROVER**: the maker's return at the filling before it is read through. Where the
public files are in scope and pass the library's test, at whatever that maker returns. -/
theorem simulatorShare_at_the_base_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned) :
    ∃ places firstChain row, SimulatorShareAtTheProver returned places firstChain row := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  obtain ⟨row, s⟩ := simulatorShare_of_sideAndBook h made fun h' =>
    AtPublicFiles.AtFiles.HonestTerm.OutputHead.outputHeadAtTheBaseProver files returned Np cF _ _ x made h'
  exact ⟨Np, cF, row, s⟩

/-- **Where the files pass, the maker returns at the base filling.** That it returns is a theorem
of other authors (`AtFullSide.K12.atPure_returns_fillW_at`). That any files pass is shown by no theorem
here. -/
theorem simulatorShare_is_met_at_the_base (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned places firstChain row, baseMaker files = .ok returned ∧
      SimulatorShareAtTheProver returned places firstChain row := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  obtain ⟨returned, made, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest ProofFile.Honest.Term.range_matrixInput
  obtain ⟨places, firstChain, row, s⟩ := simulatorShare_at_the_base_prover files scope live made
  exact ⟨returned, places, firstChain, row, made, s⟩

/-- **The share is asked somewhere, at the base prover**: the row has a side with eight members, and
at each all premises of the field `exact` can be met together, at every `pre` and every input. The
challenges and the state are made up (Honest/K6/Term/ExactIsAsked.lean). -/
theorem exactIsAsked_at_the_base_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (falls : List (Fall returned.F.S₁)) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (input : Local FullSizeMatrix IndexCommitterCoins Inst Cells) :
    ∃ r ∈ (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G,
    ∃ σ, Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ ∧ σ.members.length = 8 ∧
    ∀ u ∈ σ.members, ∃ (m : Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit) (front : Before)
      (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
      m.st.input = input ∧ m.seen = front.seen ∧
      m.opened = front.opened (readsBefore pre front) ∧
      drawsFit (u.rounds.map (·.1)) ds = true ∧ r.bud u.number ds asks ∧
      front.holds 0 0 (u.rounds.map (·.1)) ds = true ∧
      u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact head_exact_is_asked_at_maker h made _ falls pre input ()

/-- **Each part's marginal law, over spent runs taken as fresh, is one at all states**, at the base prover's
maker's return. NOT the law of a run's view; true of any masked part, whatever it masks. All limits
of Honest/K6/Term/MarginalLaw.lean hold. Like `HeadSimulatorShare` it reads the returned public part,
ground and description and not the prover's sides: that the row is the prover's side is
`SimulatorShareAtTheProver`'s fields `oneRow` and `side`. -/
theorem marginalLaw_at_the_base_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned) :
    ∀ r ∈ (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G,
    ∀ (falls : List (Fall returned.F.S₁)) σ,
      Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ →
    ∀ u ∈ σ.members, ∀ (ca ca' : CsAll u.part.carries)
      (m m' : Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit) (ds : List Fmt.Drawn)
      (asks : List (List (List Nat))),
      drawsFit (u.rounds.map (·.1)) ds = true → r.bud u.number ds asks →
      shownLaw .own σ u ca m ds asks = shownLaw .own σ u ca' m' ds asks := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact head_marginal_law_at_maker h made _

/-! ## 5 The same at the honest prover -/

/-- **AT THE HONEST PROVER.** Where the public files are in scope and pass the library's test, at
whatever the online prover's maker returns: the online honest prover is `onlineProverAt` at that
return; the prover that it hands to the frame has the returned prover's sides in the first chain;
and K6's share stands at the return. -/
theorem simulatorShare_at_the_honest_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned) :
    ∃ places firstChain row,
      onlineProver files = onlineProverAt returned places firstChain ∧
        (AtPublicFiles.AtFiles.HonestTerm.OutputHead.framedProver returned).first = returned.H.first ∧
        SimulatorShareAtTheProver returned places firstChain row := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  obtain ⟨row, s⟩ := simulatorShare_of_sideAndBook h made fun h' =>
    AtPublicFiles.AtFiles.HonestTerm.OutputHead.outputHeadAtTheHonestProver files returned Np cF _ _ x made h'
  exact ⟨Np, cF, row,
    AtPublicFiles.AtFiles.HonestTerm.onlineProver_eq made s.placesMade s.chainMade, rfl, s⟩

/-- **Where the files pass, the online prover's maker returns.** That it returns is a theorem of
other authors (`ProofFile.Honest.Term.makerReturns`). That any files pass is shown by no theorem here. -/
theorem simulatorShare_is_met (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned places firstChain row, onlineMaker files = .ok returned ∧
      onlineProver files = onlineProverAt returned places firstChain ∧
        SimulatorShareAtTheProver returned places firstChain row := by
  obtain ⟨returned, made⟩ := ProofFile.Honest.Term.makerReturns files scope live
  obtain ⟨places, firstChain, row, e, -, s⟩ :=
    simulatorShare_at_the_honest_prover files scope live made
  exact ⟨returned, places, firstChain, row, made, e, s⟩

/-- The share is asked somewhere, at the honest prover's maker's return. All that is said at
`exactIsAsked_at_the_base_prover` holds. -/
theorem exactIsAsked_at_the_honest_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned)
    (falls : List (Fall returned.F.S₁)) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (input : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) :
    ∃ r ∈ (headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G,
    ∃ σ, Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ ∧ σ.members.length = 8 ∧
    ∀ u ∈ σ.members, ∃ (m : Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) Unit) (front : Before)
      (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
      m.st.input = input ∧ m.seen = front.seen ∧
      m.opened = front.opened (readsBefore pre front) ∧
      drawsFit (u.rounds.map (·.1)) ds = true ∧ r.bud u.number ds asks ∧
      front.holds 0 0 (u.rounds.map (·.1)) ds = true ∧
      u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact head_exact_is_asked_at_maker h made _ falls pre input ()

/-- The marginal law at the honest prover's maker's return. All that is said at
`marginalLaw_at_the_base_prover` holds. -/
theorem marginalLaw_at_the_honest_prover (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned) :
    ∀ r ∈ (headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G,
    ∀ (falls : List (Fall returned.F.S₁)) σ,
      Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ →
    ∀ u ∈ σ.members, ∀ (ca ca' : CsAll u.part.carries)
      (m m' : Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) Unit) (ds : List Fmt.Drawn)
      (asks : List (List (List Nat))),
      drawsFit (u.rounds.map (·.1)) ds = true → r.bud u.number ds asks →
      shownLaw .own σ u ca m ds asks = shownLaw .own σ u ca' m' ds asks := by
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact head_marginal_law_at_maker h made _

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSimulatorLot_in_baseFilling
#print axioms ProofFile.Honest.K6.headSimulatorLot_in_onlineFilling
#print axioms ProofFile.Honest.K6.headSimulatorLot_is_the_ninth_base_lot
#print axioms ProofFile.Honest.K6.headSimulatorLot_is_the_ninth_online_lot
#print axioms ProofFile.Honest.K6.onlineProverCoins
#print axioms ProofFile.Honest.K6.rowHalf_is_headSide
#print axioms ProofFile.Honest.K6.SimulatorShareAtTheProver
#print axioms ProofFile.Honest.K6.simulatorShare_of_sideAndBook
#print axioms ProofFile.Honest.K6.head_of_the_two_tests
#print axioms ProofFile.Honest.K6.simulatorShare_at_the_base_prover
#print axioms ProofFile.Honest.K6.simulatorShare_is_met_at_the_base
#print axioms ProofFile.Honest.K6.exactIsAsked_at_the_base_prover
#print axioms ProofFile.Honest.K6.marginalLaw_at_the_base_prover
#print axioms ProofFile.Honest.K6.simulatorShare_at_the_honest_prover
#print axioms ProofFile.Honest.K6.simulatorShare_is_met
#print axioms ProofFile.Honest.K6.exactIsAsked_at_the_honest_prover
#print axioms ProofFile.Honest.K6.marginalLaw_at_the_honest_prover
