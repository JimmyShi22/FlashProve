-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
(K-P1) THE KEY FILE's BOOK LENDS EACH OF THE TWO LOOKUPS' ROWS ITS RUNS, so that `chainSteps`, and then
  `ready` (Honest/Frame.lean), return at the offline prover: `SidePays` (Honest/Law/ReadyOfSides.lean) at
  `K3.proverSideOfLookupInChain (K3.keyOwners face) …`, at `keyBook` (E2E/KeyBook.lean) and at the key file's description. It pays the
  one hypothesis that `key_lends` (E2E/KeyBookLendsNamed.lean) leaves open at the two places (`Stated`), and it is the first
  time that the test `bookFitsOwned` (Honest/K3/Parts/OwnedLends.lean) is held against a book that another hand made.

E2E/Lookup/Key/LookupSidePaysAtTheKeyBook.lean. One structure of premises; theorems with proofs. No prover is named here:
the row is general in the reader of points, the summands and the reader of the input.
E2E/Lookup/Key/LookupKindPaysAtTheOfflineProver.lean [not in this library] calls it at `keyProver`.

  `LookupStandsAtTheKeyBook data number lookup`   THE PREMISE ON THE LETTERS: the lookup's public data bear the book's place
                                    `lookPlace number` and the book's face of that number; the book has two faces; the face
                                    has two planes or more
  `multiplicitiesOwnerIsOneName`    `K3.multRun` and `countsMaskRun` are one string
  `ownedStretchesAreTheSpansOwn`    stage by stage: what the owned row's part states (`runsAtOwned` at `keyOwners`) is what
                                    the book's span asks it to state (`Span.spends` at `seatOfLookup number`): NAMES AND COUNTS
  `keyBookEntriesAtALookupsPart`    the book's entries whose spender is part number j at the lookup's place are all marked
                                    as spent, and bear just the names and counts of stage number j
  `lookupRowStatesWhatTheKeyBookHas`  **`Stated` at every part of the owned seat**: `key_lends`' hypothesis
  `keyBookPlaceFitsTheLookup`       `placeFits` at the key's book
  `keyBookFitsTheOwnedRow`          **`bookFitsOwned (keyOwners face)` accepts the key's book at the written sizes**
  `keyBookRefusesTheRowOfOneOwner`  THE CONTROL: the same test at `oneOwner` refuses that book
  `lookupSidePaysAtTheKeyBook`      **the join: the side pays**, in scope, at the description that is named at the files
  `lookupsStandAtTheWrittenSizes`   NOT EMPTY: at the written sizes the book has a face at 0 and at 1, each with two planes
                                    or more and no shift: so `LookupStandsAtTheKeyBook` has a member at both numbers
  `aLookupStandsInTheKeysFirstChain`  NOT IDLE: in scope a member of the first chain stands at each lookup's place

CAN THE PREMISES HOLD TOGETHER AT THE STORED KEY FILE? `fullPub = some data`: `full_two` (E2E/KeyBookPassesNamed.lean, by the
kernel) has `atFull … = true`, which is false where `fullPub` is none. `LookupStandsAtTheKeyBook`:
`lookupsStandAtTheWrittenSizes` here. `InScope files` with `KeyNamed files …`: `key_named` (E2E/KeyProtocolOverDescription.lean) where
the verifier's own test on the public files accepts (`protocolDataWellFormed`); THAT ANY FILES PASS THAT TEST IS SHOWN IN NO FILE THAT THIS
ONE IMPORTS (T1 asks it by name: `SomeFilesPass`): a payer stands in the side library:
`AtFullSide.Top.headMember_zFull`.1 (`protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true`) with `VerifierAndGoals.filesRead.full`.1
(`InScope storedPublicFiles = true`).

Limits. "The side pays" says that `chainSteps` returns at the lookup's member: nothing on whether a part plays, a round is
reached or a verifier accepts. The full size alone (`fullPub`). On public data alone: no coin's value, no witness.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.KeyBookLendsNamed
import E2E.KeyBookHeldK3
import E2E.KeyBookThirdNamed
import E2E.KeyPlacesNamed
import E2E.KeyFacesFull
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K3.Key.OwnedSeatMeetsThePlaceTests
import Johnson.Desc.ProofFile.Honest.BookCutsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup.Key
open ProofFile.Honest
open ProofFile.Honest.K3 (Owners oneOwner keyOwners proverSideOfLookupInChain Reads LookJobs Stage stages)
open ProofFile.Honest.K3.Law (entriesAt placeFits)
open ProofFile.Honest.K3.Parts (runsAtOwned bookFitsOwned)
open AtPublicFiles.KeyBook
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open VerifierAndGoals (PublicFiles InScope)

/-! ## 1 The premise on the letters -/

/-- **A lookup's public data stand at the key file's book**, at the lookup's number (0 or 1). A statement of premises on
letters; `lookupsStandAtTheWrittenSizes` has members. The field `base` of the lookup's data is not bound here. -/
structure LookupStandsAtTheKeyBook (data : KeyPub) (number : Nat) (lookup : K3.At) : Prop where
  /-- the lookup's place is the book's place for that number -/
  place : lookup.place = lookPlace number
  /-- the lookup's face is the book's face of that number -/
  face : data.faces[number]? = some lookup.face
  /-- the book has two lookups -/
  twoFaces : data.faces.length = 2
  /-- the face has two planes or more -/
  planes : 2 ≤ lookup.face.planes

/-! ## 2 Names and counts -/

/-- The lookups' own message bears one name in the row's text and in the book's. -/
theorem multiplicitiesOwnerIsOneName : K3.multRun = countsMaskRun := rfl

/-- The first stretch of every stage is the multiplicities' mask rows'. -/
theorem keyOwnersFirstIsTheMultiplicities (face : K3.LFace) (stage : Stage) :
    (keyOwners face stage).1 = countsMaskRun := by
  cases stage <;> rfl

/-- The second stretch is the index-mask message's just at the last level of a key tree. -/
theorem keyOwnersSecondFollowsTheLastKey (face : K3.LFace) (stage : Stage) :
    (keyOwners face stage).2 = if lastKey face stage then indexMaskRun else countsMaskRun := by
  cases stage <;> rfl

/-- **Stage by stage, the owned row states what the book's span asks**: names and counts. General in the face. -/
theorem ownedStretchesAreTheSpansOwn (number : Nat) (lookup : K3.At) (place : lookup.place = lookPlace number)
    (stage : Stage) (part : Nat) :
    runsAtOwned (keyOwners lookup.face) lookup stage part =
      (spanOf lookup.face stage).spends (seatOfLookup number) part := by
  have sameSum : K3.sumNameBy (keyOwners lookup.face) stage lookup.place part =
      sumName (seatOfLookup number) part := by
    unfold K3.sumNameBy sumName
    rw [keyOwnersFirstIsTheMultiplicities, place]
    rfl
  have sameEnd : K3.endNameBy (keyOwners lookup.face) stage lookup.place part =
      endName (seatOfLookup number) (lastKey lookup.face stage) part := by
    unfold K3.endNameBy endName
    rw [keyOwnersSecondFollowsTheLastKey, place]
    rfl
  unfold runsAtOwned spanOf
  cases stage.call lookup.face with
  | none => rfl
  | some k =>
    show (K3.sumNameBy (keyOwners lookup.face) stage lookup.place part, (⟨0, ownRun k⟩ : Due)) ::
        endRuns (K3.endNameBy (keyOwners lookup.face) stage lookup.place part) k.ends =
      (sumName (seatOfLookup number) part, (⟨0, ownRun k⟩ : Due)) ::
        endRuns (endName (seatOfLookup number) (lastKey lookup.face stage) part) k.ends
    rw [sameSum, sameEnd]

/-- A spender of an entry that `layFrom` makes stands before the end of the list of spans: the sister of `lay_spender`. -/
theorem layFromSpenderIsBelowTheEnd (seat : Seat) (spans : List Span) (first own key : Nat) :
    ∀ e ∈ layFrom seat spans first own key, e.spender.part < first + spans.length := by
  induction spans generalizing first own key with
  | nil => intro e he; cases he
  | cons span rest below =>
    intro e he
    cases span with
    | draw name count =>
      have := below (first + 1) own key e he
      simp only [List.length_cons]
      omega
    | sum call second =>
      simp only [layFrom, List.mem_append, List.mem_singleton] at he
      simp only [List.length_cons]
      rcases he with (rfl | he) | he
      · show first < _
        omega
      · split at he
        · cases he
        · split at he <;> (rw [List.mem_singleton] at he; subst he; show first < _; omega)
      · have := below _ _ _ e he
        omega

/-- A lookup's number is 0 or 1: the book has two faces. -/
theorem lookupNumberIsZeroOrOne {data : KeyPub} {number : Nat} {lookup : K3.At}
    (stands : LookupStandsAtTheKeyBook data number lookup) : number = 0 ∨ number = 1 := by
  have below := (List.getElem?_eq_some_iff.1 stands.face).1
  rw [stands.twoFaces] at below
  omega

set_option maxRecDepth 100000 in
/-- The two lookups' places differ. -/
theorem lookupPlacesDiffer : lookPlace 0 ≠ lookPlace 1 := by decide

/-- The book's entries are the lookups' and some of the others: the carried ones may be left out. -/
theorem keyBookAheadIsTheLookupsAndSomeOthers (data : KeyPub) (carried : Bool) :
    ∃ rest, (keyBook data carried).ahead = data.looks ++ rest ∧ ∀ e ∈ rest, e ∈ data.others := by
  cases carried with
  | true => exact ⟨data.others, ahead_eq data, fun _ h => h⟩
  | false =>
    refine ⟨data.others.take 5, ?_, fun _ h => List.mem_of_mem_take h⟩
    show (data.looks ++ _) ++ [] = _
    rw [List.append_nil]
    rfl

set_option maxRecDepth 100000 in
/-- No entry outside the lookups' own has its spender at a lookup's place. -/
theorem othersStandAtNoLookup (data : KeyPub) (number : Nat) (isLookup : number = 0 ∨ number = 1) :
    ∀ e ∈ data.others, e.spender.place ≠ lookPlace number := by
  intro e he same
  have member : e.spender ∈ data.others.map (·.spender) := List.mem_map_of_mem he
  rw [others_spenders] at member
  have clear : (toyPub.others.map (·.spender)).all (fun a => a.place != lookPlace number) = true := by
    rcases isLookup with rfl | rfl <;> decide +kernel
  have atMember := List.all_eq_true.1 clear _ member
  rw [same] at atMember
  simp at atMember

/-- **The book's list around one lookup's entries**: nothing in front of them or behind them has its spender at the
lookup's place. -/
theorem keyBookSplitsAtALookup (data : KeyPub) (carried : Bool) (number : Nat) (face : K3.LFace)
    (twoFaces : data.faces.length = 2) (isFace : data.faces[number]? = some face)
    (isLookup : number = 0 ∨ number = 1) :
    ∃ (own key : Nat) (before after : List Ahead),
      (keyBook data carried).ahead = before ++ (bookEntries (seatOfLookup number) face own key ++ after) ∧
      (∀ e ∈ before, e.spender.place ≠ lookPlace number) ∧
      (∀ e ∈ after, e.spender.place ≠ lookPlace number) := by
  obtain ⟨f₀, f₁, faces⟩ := List.length_eq_two.1 twoFaces
  obtain ⟨rest, ahead, inOthers⟩ := keyBookAheadIsTheLookupsAndSomeOthers data carried
  have clearOfRest : ∀ e ∈ rest, e.spender.place ≠ lookPlace number :=
    fun e he => othersStandAtNoLookup data number isLookup e (inOthers e he)
  rw [faces] at isFace
  rcases isLookup with rfl | rfl
  · obtain rfl : f₀ = face := by simpa using isFace
    refine ⟨tableAt data.sMsg 0, tableAt data.sIdx 0, [],
      bookEntries (seatOfLookup 1) f₁ (tableAt data.sMsg 0 + takenOwn (spansOf f₀))
        (tableAt data.sIdx 0 + takenKey (spansOf f₀)) ++ rest, ?_, (fun e he => by cases he), ?_⟩
    · rw [ahead, (looks_two faces).1, List.nil_append, List.append_assoc]
    · intro e he
      rcases List.mem_append.1 he with he | he
      · rw [(lay_spender _ _ _ _ _ e he).1]
        exact lookupPlacesDiffer.symm
      · exact clearOfRest e he
  · obtain rfl : f₁ = face := by simpa using isFace
    refine ⟨tableAt data.sMsg 0 + takenOwn (spansOf f₀), tableAt data.sIdx 0 + takenKey (spansOf f₀),
      bookEntries (seatOfLookup 0) f₀ (tableAt data.sMsg 0) (tableAt data.sIdx 0), rest, ?_, ?_, clearOfRest⟩
    · rw [ahead, (looks_two faces).1, List.append_assoc]
    · intro e he
      rw [(lay_spender _ _ _ _ _ e he).1]
      exact lookupPlacesDiffer

/-- The entries at a part of a lookup are those of the lookup's own list. -/
theorem entriesAtALookupAreItsOwn (data : KeyPub) (carried : Bool) (number : Nat) (face : K3.LFace)
    (twoFaces : data.faces.length = 2) (isFace : data.faces[number]? = some face)
    (isLookup : number = 0 ∨ number = 1) :
    ∃ own key, ∀ part, entriesAt (keyBook data carried) (lookPlace number) part =
      (bookEntries (seatOfLookup number) face own key).filter
        fun e => e.spender == ⟨lookPlace number, part⟩ := by
  obtain ⟨own, key, before, after, ahead, clearBefore, clearAfter⟩ :=
    keyBookSplitsAtALookup data carried number face twoFaces isFace isLookup
  refine ⟨own, key, fun part => ?_⟩
  have nothing : ∀ l : List Ahead, (∀ e ∈ l, e.spender.place ≠ lookPlace number) →
      l.filter (fun e => e.spender == ⟨lookPlace number, part⟩) = [] := by
    intro l clear
    rw [List.filter_eq_nil_iff]
    intro e he same
    exact clear e he (by rw [beq_iff_eq.1 same])
  unfold entriesAt
  rw [ahead, List.filter_append, List.filter_append, nothing _ clearBefore, nothing _ clearAfter,
    List.nil_append, List.append_nil]

/-- **The book's entries at a part of a lookup**: all are marked as spent, and they bear, in the book's order, the names
and counts of that part's stage. With or without the carried entries. -/
theorem keyBookEntriesAtALookupsPart (data : KeyPub) (carried : Bool) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) (part : Nat) (stage : Stage)
    (isStage : (stages lookup.face)[part]? = some stage) :
    (entriesAt (keyBook data carried) lookup.place part).all (·.once) = true ∧
      (entriesAt (keyBook data carried) lookup.place part).map Ahead.named =
        runsAtOwned (keyOwners lookup.face) lookup stage part := by
  obtain ⟨own, key, entries⟩ := entriesAtALookupAreItsOwn data carried number lookup.face stands.twoFaces
    stands.face (lookupNumberIsZeroOrOne stands)
  rw [stands.place, entries part]
  constructor
  · rw [List.all_eq_true]
    intro e he
    exact lay_once _ _ _ _ _ e (List.mem_of_mem_filter he)
  · have span : (spansOf lookup.face)[part]? = some (spanOf lookup.face stage) := by
      rw [← spans_of_stages _ stands.planes, List.getElem?_map, isStage]
      rfl
    have named := named_lay (seatOfLookup number) (spansOf lookup.face) 0 own key part _ span
    rw [Nat.zero_add] at named
    rw [ownedStretchesAreTheSpansOwn number lookup stands.place stage part]
    exact named

set_option maxRecDepth 100000 in
/-- The first chain's table has no row at a lookup's place. -/
theorem firstTableHasNoRowAtALookup (data : KeyPub) (carried : Bool) (number : Nat)
    (isLookup : number = 0 ∨ number = 1) :
    ∀ r ∈ (keyBook data carried).rowsOf 0, r.1.place ≠ lookPlace number := by
  intro r hr
  have member : r.1.place ∈ [idxPlace, msgPlace, rngPlace, wPlace] :=
    List.mem_map_of_mem (f := fun r : Addr × Due => r.1.place) hr
  have clear : ∀ p ∈ [idxPlace, msgPlace, rngPlace, wPlace], p ≠ lookPlace number := by
    rcases isLookup with rfl | rfl <;> decide
  exact clear _ member

/-- So a part of a lookup has no coin of its own at the book. -/
theorem lookupPartHasNoOwnCoins (data : KeyPub) (carried : Bool) (number : Nat)
    (isLookup : number = 0 ∨ number = 1) (part : Nat) :
    dueAt ((keyBook data carried).rowsOf 0) ⟨lookPlace number, part⟩ = ⟨0, 0⟩ := by
  unfold dueAt
  rw [lookup_none (fun r hr => firstTableHasNoRowAtALookup data carried number isLookup r hr) part]
  rfl

/-- **EVERY PART OF THE OWNED SEAT STATES EXACTLY WHAT THE KEY FILE's BOOK HAS FOR IT**: the hypothesis of `key_lends`, at a
lookup's place. General in the book's data. -/
theorem lookupRowStatesWhatTheKeyBookHas {V₁ W₁ X₁ W : Type} (data : KeyPub) (carried : Bool) (number : Nat)
    (lookup : K3.At) (stands : LookupStandsAtTheKeyBook data number lookup) (reads : Reads) (jobs : LookJobs W)
    (wit : W₁ → W) (index : Nat) (part : Part V₁ W₁ X₁)
    (isPart : (proverSideOfLookupInChain (keyOwners lookup.face) reads jobs wit lookup).parts[index]? = some part) :
    Stated (keyBook data carried) ((keyBook data carried).rowsOf 0) ⟨lookup.place, index⟩ part := by
  have parts : (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) (keyOwners lookup.face) reads jobs wit lookup).parts =
      ((stages lookup.face).zipIdx 0).map fun x =>
        (K3.partOfOwned (V := Unit) (keyOwners lookup.face) reads jobs lookup x.1 x.2).lift (fun _ => ()) wit
          (fun _ => ()) fun x _ => x := by
    simp [proverSideOfLookupInChain, K3.lookRowOwned, List.map_map, Function.comp_def]
  rw [parts, List.getElem?_map] at isPart
  obtain ⟨x, atIndex, rfl⟩ := Option.map_eq_some_iff.1 isPart
  rw [List.getElem?_zipIdx] at atIndex
  simp only [Nat.zero_add] at atIndex
  obtain ⟨stage, isStage, rfl⟩ := Option.map_eq_some_iff.1 atIndex
  obtain ⟨takes, carries, spends⟩ := ProofFile.Honest.K3.Parts.ownedPart_facts (V₁ := V₁) (X₁ := X₁)
    (keyOwners lookup.face) reads jobs wit lookup (stage, index)
  obtain ⟨once, named⟩ := keyBookEntriesAtALookupsPart data carried number lookup stands index stage isStage
  have onceList := List.all_eq_true.1 once
  have keepsAll : (entriesAt (keyBook data carried) lookup.place index).filter (·.once) =
      entriesAt (keyBook data carried) lookup.place index :=
    List.filter_eq_self.2 onceList
  have keepsNone : (entriesAt (keyBook data carried) lookup.place index).filter (!·.once) = [] :=
    List.filter_eq_nil_iff.2 fun e he => by simp [onceList e he]
  have noCoins := lookupPartHasNoOwnCoins data carried number (lookupNumberIsZeroOrOne stands) index
  rw [← stands.place] at noCoins
  unfold Stated hasFor
  show (_, _, _) = (dueAt _ _, ((entriesAt (keyBook data carried) lookup.place index).filter (·.once)).map Ahead.named,
    ((entriesAt (keyBook data carried) lookup.place index).filter (!·.once)).map Ahead.named)
  rw [keepsAll, keepsNone, named, noCoins]
  exact Prod.ext takes (Prod.ext spends carries)

/-! ## 3 The two tests on the book -/

/-- The book's cut at a lookup's place is its spans' rounds. -/
theorem keyBookCutAtALookup (data : KeyPub) (carried : Bool) (number : Nat) (face : K3.LFace)
    (twoFaces : data.faces.length = 2) (isFace : data.faces[number]? = some face)
    (isLookup : number = 0 ∨ number = 1) :
    (keyBook data carried).cuts.lookup (lookPlace number) = some ((spansOf face).map Span.rounds) := by
  obtain ⟨f₀, f₁, faces⟩ := List.length_eq_two.1 twoFaces
  show data.cuts.lookup _ = _
  unfold KeyPub.cuts
  rw [faces] at isFace ⊢
  rcases isLookup with rfl | rfl
  · obtain rfl : f₀ = face := by simpa using isFace
    rfl
  · obtain rfl : f₁ = face := by simpa using isFace
    rfl

/-- The book's cut at the lookup's place is the stages' rounds; the book has no row and no spender at a part's number
that the row does not have. General in the book's data. -/
theorem keyBookPlaceFitsTheLookup (data : KeyPub) (carried : Bool) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) :
    placeFits (keyBook data carried) ((keyBook data carried).rowsOf 0) lookup = true := by
  have isLookup := lookupNumberIsZeroOrOne stands
  have cut : (keyBook data carried).cuts.lookup lookup.place =
      some ((stages lookup.face).map (Stage.rounds lookup.face)) := by
    rw [stands.place, keyBookCutAtALookup data carried number lookup.face stands.twoFaces stands.face isLookup,
      ← spans_of_stages _ stands.planes, List.map_map]
    congr 1
    apply List.map_congr_left
    intro stage _
    exact rounds_held _ stage
  obtain ⟨own, key, before, after, ahead, clearBefore, clearAfter⟩ :=
    keyBookSplitsAtALookup data carried number lookup.face stands.twoFaces stands.face isLookup
  simp only [placeFits, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨⟨cut, ?_⟩, ?_⟩
  · rw [List.any_eq_false]
    intro r hr atPlace
    simp only [Bool.and_eq_true, beq_iff_eq] at atPlace
    exact firstTableHasNoRowAtALookup data carried number isLookup r hr (atPlace.1.trans stands.place)
  · rw [List.any_eq_false]
    intro e he atPlace
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at atPlace
    obtain ⟨samePlace, tooFar⟩ := atPlace
    rw [stands.place] at samePlace
    rw [ahead] at he
    rcases List.mem_append.1 he with he | he
    · exact clearBefore e he samePlace
    · rcases List.mem_append.1 he with he | he
      · have below := layFromSpenderIsBelowTheEnd _ _ _ _ _ e he
        have sameLength : (spansOf lookup.face).length = (stages lookup.face).length := by
          rw [← spans_of_stages _ stands.planes, List.length_map]
        omega
      · exact clearAfter e he samePlace

/-- **THE TEST `bookFitsOwned` ACCEPTS THE KEY FILE's BOOK AT THE WRITTEN SIZES**, at the key file's letter for the
owners. -/
theorem keyBookFitsTheOwnedRow (data : KeyPub) (written : fullPub = some data) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) :
    bookFitsOwned (keyOwners lookup.face) (keyBook data) ((keyBook data).rowsOf 0) (dueAt (keyBook data).first)
      lookup = true := by
  have isLookup := lookupNumberIsZeroOrOne stands
  obtain ⟨f₀, f₁, faces⟩ := List.length_eq_two.1 stands.twoFaces
  have small := of_atFull full_lends written
  simp only [lendsSmall, decide_eq_true_eq, Bool.and_eq_true] at small
  obtain ⟨⟨-, topOwn⟩, topKey⟩ := small
  unfold bookFitsOwned
  rw [List.all_eq_true]
  rintro ⟨stage, index⟩ member
  have isStage : (stages lookup.face)[index]? = some stage := by
    simpa using List.mem_zipIdx_iff_getElem?.1 member
  obtain ⟨once, named⟩ := keyBookEntriesAtALookupsPart data true number lookup stands index stage isStage
  have noCoins := lookupPartHasNoOwnCoins data true number isLookup index
  rw [← stands.place] at noCoins
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨noCoins, once⟩, named⟩, ?_⟩
  rw [List.all_eq_true]
  intro e he
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  obtain ⟨inBook, atPart⟩ := List.mem_filter.1 he
  have inAhead : e ∈ (keyBook data).ahead := inBook
  rw [ahead_eq, List.mem_append] at inAhead
  rcases inAhead with inLooks | inOthers
  · obtain ⟨i, -, -, noBaseStart, noBaseCount, -, range⟩ := looks_block faces e inLooks
    rw [noBaseStart, noBaseCount]
    refine ⟨Nat.zero_le _, ?_⟩
    show _ ≤ (dueAt (keyBook data).first e.owner).e
    rcases range with ⟨owner, -, h⟩ | ⟨owner, -, h⟩ <;> rw [owner] <;> omega
  · have samePlace : e.spender.place = lookPlace number := by
      rw [beq_iff_eq.1 atPart]
      exact stands.place
    exact absurd samePlace (othersStandAtNoLookup data number isLookup e inOthers)

/-- **The control: at one owner, the segment's mask row, the same test refuses that book.** So the test can fail at this
book, and the row of one owner is not lent its coins by this road. -/
theorem keyBookRefusesTheRowOfOneOwner (data : KeyPub) (written : fullPub = some data) (number : Nat)
    (lookup : K3.At) (stands : LookupStandsAtTheKeyBook data number lookup) :
    bookFitsOwned oneOwner (keyBook data) ((keyBook data).rowsOf 0) (dueAt (keyBook data).first) lookup = false := by
  rw [Bool.eq_false_iff]
  intro accepts
  unfold bookFitsOwned at accepts
  rw [List.all_eq_true] at accepts
  have member : Stage.tie 0 ∈ stages lookup.face := by
    have planes := stands.planes
    simp only [K3.stages, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨0, by omega, rfl⟩)))))
  obtain ⟨index, isStage⟩ := List.mem_iff_getElem?.1 member
  have atStage := accepts (Stage.tie 0, index) (List.mem_zipIdx_iff_getElem?.2 (by simpa using isStage))
  simp only [Bool.and_eq_true, beq_iff_eq] at atStage
  obtain ⟨⟨⟨-, -⟩, namedOne⟩, -⟩ := atStage
  obtain ⟨-, namedKey⟩ := keyBookEntriesAtALookupsPart data true number lookup stands index _ isStage
  have same := namedOne.symm.trans namedKey
  have names : runName ProofFile.Honest.maskRowRun ⟨lookup.place, index⟩ "sum" =
      runName K3.multRun ⟨lookup.place, index⟩ "sum" :=
    congrArg Prod.fst (List.cons.inj same).1
  have chars := congrArg String.toList names
  simp only [runName, String.toList_append] at chars
  have oneChars : ProofFile.Honest.maskRowRun.toList =
      ['t', 'h', 'e', ' ', 's'] ++ ProofFile.Honest.maskRowRun.toList.drop 5 := by decide
  have keyChars : K3.multRun.toList = ['t', 'h', 'e', ' ', 'm'] ++ K3.multRun.toList.drop 5 := by decide
  rw [oneChars, keyChars] at chars
  simp at chars

/-! ## 4 The side pays -/

/-- A pair that a lookup in a list returns stands in the list. -/
theorem pairOfLookup {α β : Type} [BEq α] [LawfulBEq α] (k : α) (v : β) :
    ∀ l : List (α × β), l.lookup k = some v → (k, v) ∈ l
  | [], h => by cases h
  | (a, b) :: rest, h => by
    rw [List.lookup_cons] at h
    cases same : k == a with
    | true =>
      simp only [same] at h
      obtain rfl := Option.some.inj h
      obtain rfl := beq_iff_eq.1 same
      exact List.mem_cons_self
    | false =>
      simp only [same] at h
      exact List.mem_cons_of_mem _ (pairOfLookup k v rest h)

/-- The tenth of the book's own tests, as an equation at one cut: the sizes' lookup is the cut's sum. -/
theorem cutAddsUpAtTheBook {Xi : Type} {description : VerifiableInference.Desc.FileDescription Xi} {book : ProverCoinCounts}
    (word : book.word description = none) (cut : VerifiableInference.Desc.Place × List Nat)
    (isCut : cut ∈ book.cuts) :
    (description.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        description.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        description.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup cut.1 =
      some (cut.2.foldl (· + ·) 0) := by
  have tests := ProverCoinCounts.tests word
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at tests
  obtain ⟨-, -, -, -, -, -, -, -, -, tenth, -⟩ := tests
  have atCut := List.all_eq_true.1 tenth cut isCut
  simp only [Bool.and_eq_true, beq_iff_eq] at atCut
  exact atCut.1.1

set_option maxRecDepth 100000 in
/-- No place stands twice in the three literal lists. -/
theorem fullListsHaveEachPlaceOnce :
    ((fullFirst ++ fullShared ++ fullSecond).map (·.1)).Nodup := by
  decide +kernel

/-- **A side whose numbers of moves the book has as its cut has the member's rounds**, at a member of the key file's first
chain. -/
theorem sideRoundsAreTheMembers {V₁ W₁ X₁ : Type} {files : PublicFiles} {source : Source} {numbers : H2U.PlaceNums}
    {later : LaterPlaces} (scope : InScope files = true) (named : KeyNamed files source numbers later)
    (data : KeyPub) (written : fullPub = some data) {side : Placed V₁ W₁ X₁}
    (member : VerifiableInference.Desc.Block _ _)
    (isMember : member ∈ (keyFileDescription source numbers later).first.blocksInOrder)
    (cut : (keyBook data).cuts.lookup member.place = some (side.parts.map (·.moves.length))) :
    side.rounds = member.rounds.length := by
  obtain ⟨first, shared, second⟩ := places_named scope named
  have sizes := cutAddsUpAtTheBook (book_passes scope named data written) _
    (pairOfLookup _ _ _ cut)
  have rowsAreLists : ((keyFileDescription source numbers later).first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
      (keyFileDescription source numbers later).shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
      (keyFileDescription source numbers later).second.blocksInOrder.map fun b => (b.place, b.rounds.length)) =
      fullFirst ++ fullShared ++ fullSecond := by
    rw [← first, ← shared, ← second]
    rfl
  rw [rowsAreLists] at sizes
  have inLists : (member.place, member.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := by
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    rw [← first]
    exact List.mem_map_of_mem (f := fun b => (b.place, b.rounds.length)) isMember
  have found := lookup_of_nodup _ fullListsHaveEachPlaceOnce _ _ inLists
  have sameRounds := Option.some.inj (found.symm.trans sizes)
  rw [sameRounds]
  unfold Placed.rounds
  rw [List.foldl_map]

/-- **A LOOKUP's OWNED SEAT PAYS AT THE KEY FILE's BOOK AND DESCRIPTION.** Conditional: the files are in scope; the
description is the one named at the files; the book is at the written sizes; the lookup's data stand at the book. General
in the reader of points, the summands and the reader of the input. -/
theorem lookupSidePaysAtTheKeyBook {V₁ W₁ X₁ W : Type} {files : PublicFiles} {source : Source} {numbers : H2U.PlaceNums}
    {later : LaterPlaces} (scope : InScope files = true) (named : KeyNamed files source numbers later)
    (data : KeyPub) (written : fullPub = some data) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) (reads : Reads) (jobs : LookJobs W) (wit : W₁ → W) :
    SidePays (keyBook data) 0 (keyFileDescription source numbers later).first.blocksInOrder
      (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) (keyOwners lookup.face) reads jobs wit lookup) := by
  have tests := ProofFile.Honest.K3.Key.ownedSeatMeetsThePlaceTests (V₁ := V₁) (X₁ := X₁) (keyOwners lookup.face) reads
    jobs wit lookup (keyBook data) _ (keyBookPlaceFitsTheLookup data true number lookup stands)
  obtain ⟨cut, rows, spenders⟩ := tests
  obtain ⟨coins, lends, -⟩ := ProofFile.Honest.K3.Key.bookLendsTheOwnedSeatInTheFirstChain (V₁ := V₁) (X₁ := X₁)
    (keyOwners lookup.face) reads jobs wit lookup (keyBook data)
    (keyBookFitsTheOwnedRow data written number lookup stands) default
  refine sidePays_of_tests _ 0 _ _ fun member isMember samePlace => ?_
  have samePlace' : member.place = lookup.place := samePlace
  refine ⟨(ProofFile.Honest.shaped_parts ((planOk_all named.plan).1 member isMember).2).1, ?_, ?_, ?_, ?_, default, coins, ?_⟩
  · exact sideRoundsAreTheMembers scope named data written member isMember (samePlace'.symm ▸ cut)
  · rw [samePlace']
    exact cut
  · rw [samePlace']
    exact rows
  · rw [samePlace']
    exact spenders
  · rw [samePlace']
    exact lends

/-! ## 5 The premise has members -/

/-- The evaluation behind the next statement, in Lean's kernel. -/
theorem fullFacesHaveTwoPlanesAndNoShift :
    atFull (fun K => K.faces.length == 2 &&
      K.faces.all fun face => decide (2 ≤ face.planes) && !face.shifted) = true := by
  decide +kernel

/-- **At the written sizes the book has a face at 0 and at 1, each with two planes or more and without a shift.** So
`LookupStandsAtTheKeyBook data number ⟨lookPlace number, face, base⟩` holds at both numbers and every base. -/
theorem lookupsStandAtTheWrittenSizes (data : KeyPub) (written : fullPub = some data) :
    data.faces.length = 2 ∧
      ∀ number, number < 2 → ∃ face, data.faces[number]? = some face ∧ 2 ≤ face.planes ∧ face.shifted = false := by
  have atWritten := of_atFull fullFacesHaveTwoPlanesAndNoShift written
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at atWritten
  obtain ⟨two, everyFace⟩ := atWritten
  refine ⟨two, fun number below => ?_⟩
  have inRange : number < data.faces.length := by omega
  obtain ⟨planes, shifted⟩ := everyFace _ (List.getElem_mem inRange)
  exact ⟨data.faces[number], List.getElem?_eq_getElem inRange, planes, shifted⟩

set_option maxRecDepth 100000 in
/-- **In scope a member stands at each lookup's place in the key file's first chain**: so `lookupSidePaysAtTheKeyBook` does
not hold idly. -/
theorem aLookupStandsInTheKeysFirstChain {files : PublicFiles} {source : Source} {numbers : H2U.PlaceNums}
    {later : LaterPlaces} (scope : InScope files = true) (named : KeyNamed files source numbers later) :
    ∀ number, number < 2 → ∃ b ∈ (keyFileDescription source numbers later).first.blocksInOrder, b.place = lookPlace number := by
  intro number below
  have written : lookPlace number ∈ fullFirst.map (·.1) := by
    have isLookup : number = 0 ∨ number = 1 := by omega
    rcases isLookup with rfl | rfl <;> decide
  rw [← (places_named scope named).1, rows_places] at written
  obtain ⟨member, isMember, place⟩ := List.mem_map.1 written
  exact ⟨member, isMember, place⟩

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.multiplicitiesOwnerIsOneName
#print axioms AtPublicFiles.Lookup.Key.ownedStretchesAreTheSpansOwn
#print axioms AtPublicFiles.Lookup.Key.keyBookEntriesAtALookupsPart
#print axioms AtPublicFiles.Lookup.Key.lookupRowStatesWhatTheKeyBookHas
#print axioms AtPublicFiles.Lookup.Key.keyBookPlaceFitsTheLookup
#print axioms AtPublicFiles.Lookup.Key.keyBookFitsTheOwnedRow
#print axioms AtPublicFiles.Lookup.Key.keyBookRefusesTheRowOfOneOwner
#print axioms AtPublicFiles.Lookup.Key.lookupSidePaysAtTheKeyBook
#print axioms AtPublicFiles.Lookup.Key.lookupsStandAtTheWrittenSizes
#print axioms AtPublicFiles.Lookup.Key.aLookupStandsInTheKeysFirstChain
