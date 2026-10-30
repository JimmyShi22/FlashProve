-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/SideAsAList.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN, AND WHERE THE MAKER RETURNS,
THE SIDES OF THIS KIND IN THE PROVER's FIRST CHAIN ARE A LIST OF ONE: THE ROW. And no fall of the
first chain's list of falls stands at this kind's place.

WHAT IT IS NOT.
  * It says which sides a prover has, and where falls stand. It does not say that a part plays, that
    a round is reached, that a verifier accepts, or what a simulator shows.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and "the maker
    returns" are premises of every theorem on a prover here. That the maker returns at these
    fillings is not shown here: where it does not, these theorems hold of nothing.
  * The statement on falls speaks of fallsHead (Honest/Law/FallsHead.lean) at all five of its open
    arguments. The list that the online honest prover's sides are laid with is written in a file of
    other authors that is not beneath this one (E2E/TheFalls.lean): there it is a list fallsFull,
    which that file's own proofs treat as fallsHead at five values, and whatever the kinds add in
    their slots. That fallsFull is fallsHead at values, and that no kind adds a fall at this place,
    is held by no theorem here.
  * Nothing on soundness, completeness or what a proof hides.

WORDS. The maker is onlineProverFromPublicFiles (Honest/AtPure.lean). A side is one sender of the prover, seated at one
place. The row is this kind's side, headRow (Honest/K6/Part.lean). A lot is a list of sides that a
filling lays into the prover. A fall is a test that excuses a member's own step. The base filling is
onlineProverPartsInUse; the honest prover's own filling is that filling read through two readers
(onlineFillingAt, Honest/K6/Term/Statements.lean).

WHAT IT IS. No definition; ten theorems.

  sidesOfAKindByPairs       general, no kind named: where each lot of a list lays sides of one kind
                            alone, the sides of a kind are the sides of the lots of that kind, in
                            their order
  sidesOfAKindReadThrough   general: reading sides through two readers keeps which are of a kind
  headPairAlone             of the thirteen lots of the base filling, those of the kind K6 are a
                            list of one: the head's lot. No premise
  sidesOfTheKindAmongTheLots   so the sides of the kind among the base filling's lots are the head's
                            lot's sides. No premise
  sidesOfTheKindAtTheBase   **at the maker's return at the base filling the sides of the kind K6 in
                            the prover's first chain are [the row]**: so the row stands there once
  sidesOfTheKindAtTheFilling   **the same at that filling read through two readers**
  sidesOfTheKindAtACommitter   the same at that prover with a committer's columns and key laid in,
                            which is the form of the prover that the online honest prover runs
  fallsStandAtThreeKinds    every fall of fallsHead stands at a place of the kind K9, K4 or "frame"
  noFallAtTheKindsPlace     so none stands at this kind's place
  noFallSpeaksAtTheMember   so, under the hypothesis, at member 341 (counted from 0) the list's
                            falls are silent at every state and all challenges

CALLED. fillPairs, fillPairs_lots, fillPairs_kinds (Honest/Law/FillPairs.lean); headLotHasOneSide
(Honest/K6/Term/KindPaysAtTerm.lean); headHalf_through (Honest/K6/Term/RowThrough.lean); atPure_ok
(Honest/AtPureLaw.lean); P4.k6_member_at_mg, member_is (Honest/K6/Law/MemberIs.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.KindPaysAtTerm
import Johnson.Desc.ProofFile.Honest.Law.FallsHead
import Johnson.Desc.ProofFile.Honest.Law.FallFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain KindName)
open P5J (AtMgA TS)

/-! ## 1 General: the sides of a kind, lot by lot -/

/-- General. **Where each lot of a list lays sides of one kind alone, the sides of a kind are the
sides of the lots of that kind, in their order.** pairs: the lots, each with its kind. -/
theorem sidesOfAKindByPairs {V W X : Type} (Zq : Pub) (G : Ground) (kind : KindName) :
    ∀ pairs : List (HLot V W X × KindName),
      (∀ pair ∈ pairs, ∀ side ∈ pair.1.halves Zq G, side.place.kind = pair.2) →
      (firstOf Zq G (pairs.map (·.1))).filter (fun side => side.place.kind == kind) =
        firstOf Zq G ((pairs.filter fun pair => pair.2 == kind).map (·.1))
  | [], _ => rfl
  | pair :: rest, kinds => by
    have tail := sidesOfAKindByPairs Zq G kind rest fun other isOther =>
      kinds other (List.mem_cons_of_mem _ isOther)
    have own := kinds pair List.mem_cons_self
    unfold firstOf at tail ⊢
    rw [List.map_cons, List.flatMap_cons, List.filter_append, tail]
    by_cases same : pair.2 = kind
    · have all : (pair.1.halves Zq G).filter (fun side => side.place.kind == kind) =
          pair.1.halves Zq G :=
        List.filter_eq_self.2 fun side isSide => beq_iff_eq.2 ((own side isSide).trans same)
      rw [all, List.filter_cons_of_pos (p := fun other : HLot V W X × KindName => other.2 == kind)
        (beq_iff_eq.2 same), List.map_cons, List.flatMap_cons]
    · have none : (pair.1.halves Zq G).filter (fun side => side.place.kind == kind) = [] :=
        List.filter_eq_nil_iff.2 fun side isSide equal =>
          same ((own side isSide).symm.trans (beq_iff_eq.1 equal))
      rw [none, List.filter_cons_of_neg (p := fun other : HLot V W X × KindName => other.2 == kind)
        (fun equal => same (beq_iff_eq.1 equal)), List.nil_append]

/-- General. **Reading sides through two readers keeps which of them are of a kind.** -/
theorem sidesOfAKindReadThrough {V V' W W' X : Type} (see : V' → V) (wit : W' → W)
    (kind : KindName) (sides : List (Placed V W X)) :
    (sides.map (Placed.thru see wit)).filter (fun side => side.place.kind == kind) =
      (sides.filter fun side => side.place.kind == kind).map (Placed.thru see wit) := by
  rw [List.filter_map]
  rfl

/-! ## 2 The head's lot among the thirteen -/

/-- **Of the thirteen lots of the base filling, those of the kind K6 are a list of one: the head's
lot.** No premise. -/
theorem headPairAlone {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    ((fillPairs I o S O).filter fun pair => pair.2 == KindName.K6).map (·.1) =
      [headLotAt I.weights] := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}

/-- The sides of the kind among the base filling's lots, at a public part and a ground. -/
theorem sidesOfTheKindAmongTheLots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    (firstOf Zq G (onlineProverPartsInUse I o S O).lots).filter
        (fun side => side.place.kind == KindName.K6) =
      (headLotAt I.weights).halves Zq G := by
  rw [fillPairs_lots, sidesOfAKindByPairs Zq G .K6 _ (fillPairs_kinds I o S O Zq G),
    headPairAlone]
  unfold firstOf
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ## 3 At the maker's returns -/

/-- **At the maker's return at the base filling the sides of the kind K6 in the prover's first chain
are a list of one: the row.** Two premises: the library's hypothesis on the first chain and "the
maker returns at the base filling". -/
theorem sidesOfTheKindAtTheBase (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    A.H.first.filter (fun side => side.place.kind == KindName.K6) = [headSide id I Zp A.G] := by
  have one := headLotHasOneSide h hA I.weights
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1, sidesOfTheKindAmongTheLots]
  exact one

/-- **The same at the base filling read through two readers**, which is the form of the honest
prover's own filling. Two premises: the hypothesis and "the maker returns at that filling". -/
theorem sidesOfTheKindAtTheFilling {W₀' Rc' : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A) :
    A.H.first.filter (fun side => side.place.kind == KindName.K6) =
      [headSide readIndex I Zp A.G] := by
  have lots : firstOf A.Z A.G (onlineFillingAt readIndex readRandomness namedIndex I S O).lots =
      (firstOf A.Z A.G (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots).map
        (Placed.thru (Local.thru readIndex readRandomness)
          (Local.thru readIndex readRandomness)) := by
    unfold firstOf
    show ((onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots.map (HLot.thru _ _)).flatMap _ = _
    rw [List.flatMap_map, List.map_flatMap]
    rfl
  have one := headLotHasOneSide h hA fun Z' index => I.weights Z' (readIndex index)
  rw [headLotAt_through readIndex readRandomness I.weights] at one
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1, lots, sidesOfAKindReadThrough, sidesOfTheKindAmongTheLots]
  exact one

/-- **The same at that prover with a committer's columns and key laid in**: the form of the prover
that the online honest prover runs. The same two premises. -/
theorem sidesOfTheKindAtACommitter {W₀' Rc' Seed Column : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (readIndex : W₀' → W₀)
    (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A)
    (committer : Committer W₀' Rc' Seed Column Inst OnBytes.TableKey) (item : Nat) :
    (committer.proverAt item A.H).first.filter (fun side => side.place.kind == KindName.K6) =
      [headSide readIndex I Zp A.G] :=
  sidesOfTheKindAtTheFilling h readIndex readRandomness namedIndex I S O hA

/-! ## 4 No fall at the kind's place -/

/-- **Every fall of the first chain's list stands at a place of the kind K9, K4 or "frame".** At all
five open arguments of the list. No premise. -/
theorem fallsStandAtThreeKinds (Zq : Pub) (G₀ : Ground) (cols tau : Nat → Nat)
    (share notGood : Nat → Odds) (roundsBefore : Nat → Nat) :
    ∀ fall ∈ fallsHead Zq G₀ cols tau share notGood roundsBefore,
      fall.place.kind = KindName.K9 ∨ fall.place.kind = KindName.K4 ∨
        fall.place.kind = KindName.frame := by
  intro fall isFall
  unfold fallsHead at isFall
  rcases List.mem_append.1 isFall with atLink | atLayer
  · obtain ⟨l, -, inLink⟩ := List.mem_flatMap.1 atLink
    unfold linkFalls at inLink
    rcases List.mem_append.1 inLink with frontOrQuiet | shareFall
    · rcases List.mem_append.1 frontOrQuiet with front | quiet
      · rw [List.mem_singleton.1 front]
        exact .inl rfl
      · split at quiet
        · rw [List.mem_singleton.1 quiet]
          exact .inr (.inr rfl)
        · exact absurd quiet List.not_mem_nil
    · split at shareFall
      · rw [List.mem_singleton.1 shareFall]
        exact .inr (.inr rfl)
      · exact absurd shareFall List.not_mem_nil
  · obtain ⟨g, -, made⟩ := List.mem_filterMap.1 atLayer
    obtain ⟨hp, -, isIt⟩ := Option.map_eq_some_iff.1 made
    rw [← isIt]
    exact .inr (.inl rfl)

/-- **So no fall of the list stands at this kind's place.** No premise. -/
theorem noFallAtTheKindsPlace (Zq : Pub) (G₀ : Ground) (cols tau : Nat → Nat)
    (share notGood : Nat → Odds) (roundsBefore : Nat → Nat) :
    ∀ fall ∈ fallsHead Zq G₀ cols tau share notGood roundsBefore, fall.place ≠ IM.k6Place := by
  intro fall isFall atPlace
  rcases fallsStandAtThreeKinds Zq G₀ cols tau share notGood roundsBefore fall isFall with
    k | k | k <;> rw [atPlace] at k <;> exact absurd k (by decide)

/-- **So at member 341 of the first chain the list's falls are silent**, at every state and all
challenges: this kind's own step is excused nowhere. One premise: the library's hypothesis on the
first chain. -/
theorem noFallSpeaksAtTheMember (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Zq : Pub)
    (G₀ : Ground) (cols tau : Nat → Nat) (share notGood : Nat → Odds) (roundsBefore : Nat → Nat)
    (s : TS) (challenges : List Fmt.Drawn) :
    fallsBy (fallsHead Zq G₀ cols tau share notGood roundsBefore) cF.blocksInOrder 341 s challenges =
      none := by
  obtain ⟨member, at341, memberIs⟩ := P4.k6_member_at_mg h.toAtMg
  unfold fallsBy
  rw [at341]
  show fallOf _ member.place s challenges = none
  rw [(member_is memberIs).1]
  unfold fallOf
  rw [List.filter_eq_nil_iff.2 fun fall isFall equal =>
    noFallAtTheKindsPlace Zq G₀ cols tau share notGood roundsBefore fall isFall
      (beq_iff_eq.1 equal)]
  rfl

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.sidesOfAKindByPairs
#print axioms ProofFile.Honest.K6.Term.sidesOfAKindReadThrough
#print axioms ProofFile.Honest.K6.Term.headPairAlone
#print axioms ProofFile.Honest.K6.Term.sidesOfTheKindAmongTheLots
#print axioms ProofFile.Honest.K6.Term.sidesOfTheKindAtTheBase
#print axioms ProofFile.Honest.K6.Term.sidesOfTheKindAtTheFilling
#print axioms ProofFile.Honest.K6.Term.sidesOfTheKindAtACommitter
#print axioms ProofFile.Honest.K6.Term.fallsStandAtThreeKinds
#print axioms ProofFile.Honest.K6.Term.noFallAtTheKindsPlace
#print axioms ProofFile.Honest.K6.Term.noFallSpeaksAtTheMember
