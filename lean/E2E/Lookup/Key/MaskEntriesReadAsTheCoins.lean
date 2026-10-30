-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: the mask entries under a lookup's slots read as the coins that `maskOf` names, at borders 4 and 10 of the key's
  first thread. The frame divides the work in three (Honest/Law/Rule/TiesFall.lean): the ledger is ours and is paid here; that
  the message holds the coin at the number of a take is the sender's (`SenderLaysItsCoinsInTheOrderOfTaking`); that the thread's
  reader reads that message is the thread's. The last two are premises here, by name.

E2E/Lookup/Key/MaskEntriesReadAsTheCoins.lean. Theorems with proofs.

  `takesOfBothLookups`       what the two lookups take of each owner, together
  `takeOfSlot`               the number of take of a slot, in its owner's count
  `homeOfASlot`              the home under a slot is its owner's message at that number
  `takeOfASlotIsBelow`       that number is below what the two lookups take: the bound of the sender's debt
  `homesByTheDealAtTheKey`   the homes at border 4 or 10, as a list
  `maskEntriesReadAsTheCoinsOfTheTwoDebts`   **the top**

Limits. The two debts are premises. Each statement holds also where the thread stands at nothing. Nothing on any property of a
protocol.
-/
import E2E.Lookup.Key.LedgersStandAtTheLookupsBorders
import E2E.Lookup.Key.OneFaceUnderThreeNames

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open ProofFile.Honest
open ProofFile.Honest.K3 (keyOwners)
open ProofFile.Honest.K3.Parts (maskOf)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyThread
open AtPublicFiles.AtFiles (KeySourced)
open VerifiableInference.Desc.K3 (Face faceOfLkp fromKeys)
open VerifiableInference.Desc.Key (FirstState Lookup Source LaterPlaces Xi lookupsOf)
open OnBytes (Slot takenNo)
open Johnson.RunOne.KeyRows1 (plan₁)

/-! ## 1 A slot's number -/

/-- What the two lookups take of each owner, together. -/
def takesOfBothLookups (data : KeyPub) : Nat × Nat := takenBeforeLookup data 2

/-- Whose coin a slot's is. -/
abbrev slotOwner (face : Face) (j : Nat) : String :=
  (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).getD j ""

/-- **The number of take of a slot, in its owner's count**: the takes of the lookups in front, and this lookup's of that owner in
front of the slot. -/
def takeOfSlot (data : KeyPub) (number : Nat) (face : Face) (j : Nat) : Nat :=
  (if slotOwner face j == indexMaskRun then (takenBeforeLookup data number).2
   else (takenBeforeLookup data number).1) +
    ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count (slotOwner face j)

theorem unrolledLengthIsTheSlots (face : Face) (planes : 2 ≤ face.planes) :
    (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).length = face.slots := by
  rw [← List.length_map (f := (· == indexMaskRun)), ProofFile.Honest.K3.Parts.unroll_key face planes,
    AtPublicFiles.KeyLookup.fromKeys_length]

theorem slotOwnerStandsInTheLetter (face : Face) (j : Nat)
    (position : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).length) :
    slotOwner face j ∈ ProofFile.Honest.K3.Parts.unroll (keyOwners face) face := by
  show (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).getD j "" ∈ _
  rw [List.getD_eq_getElem _ _ position]
  exact List.getElem_mem position

theorem slotOwnerIsOneOfTwo (face : Face) (j : Nat)
    (position : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).length)
    (notIndex : (slotOwner face j == indexMaskRun) = false) : slotOwner face j = K3.multRun := by
  rcases membersOfTheKeyLetter face _ (slotOwnerStandsInTheLetter face j position) with h | h
  · exact h
  · rw [h] at notIndex
    simp at notIndex

/-- **The home under a slot is its owner's message at the slot's number of take.** -/
theorem homeOfASlot {home : Array Slot} {ownMessage keyMessage ownMaskRows keyMaskRows : Nat}
    (data : KeyPub) (number : Nat) (face : Face) (planes : 2 ≤ face.planes)
    (homesAre : home.toList =
      (deal (fromKeys face) (takenBeforeLookup data number).1 (takenBeforeLookup data number).2).map
        (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows 0 0))
    (j : Nat) (below : j < face.slots) :
    home[j]? = some
      (if slotOwner face j == indexMaskRun then
        ⟨keyMessage, takenNo keyMaskRows (takeOfSlot data number face j)⟩
       else ⟨ownMessage, takenNo ownMaskRows (takeOfSlot data number face j)⟩) := by
  have hMarks := ProofFile.Honest.K3.Parts.unroll_key face planes
  have hPosition : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).length := by
    rw [unrolledLengthIsTheSlots face planes]
    exact below
  rw [← hMarks] at homesAre
  have hDeal := dealAtAPosition
    ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).map (· == indexMaskRun))
    (takenBeforeLookup data number).1 (takenBeforeLookup data number).2 j
    (by rw [List.length_map]; exact hPosition)
  have hAt : home[j]? = (List.map (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows 0 0)
      (deal ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).map (· == indexMaskRun))
        (takenBeforeLookup data number).1 (takenBeforeLookup data number).2))[j]? := by
    rw [← homesAre, Array.getElem?_toList]
  rw [List.getElem?_map, hDeal, Option.map_some] at hAt
  have hMark : ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).map
      (· == indexMaskRun)).getD j false = (slotOwner face j == indexMaskRun) := by
    simp [slotOwner, List.getD_eq_getElem?_getD, hPosition]
  rw [hMark, ← List.map_take] at hAt
  unfold takeOfSlot
  cases hFlag : (slotOwner face j == indexMaskRun) with
  | true =>
    have hOwner : slotOwner face j = indexMaskRun := by simpa using hFlag
    rw [hFlag, marksCountTheIndexMasks] at hAt
    rw [hAt, hOwner]
    simp [homeOfCoin]
  | false =>
    have hOwner := slotOwnerIsOneOfTwo face j hPosition hFlag
    rw [hFlag, marksCountTheMultiplicities _
      fun w hw => membersOfTheKeyLetter face w (List.mem_of_mem_take hw)] at hAt
    rw [hAt, hOwner]
    simp [homeOfCoin]

/-- A member at a position is counted behind what stands in front of it. -/
theorem countInFrontIsBelowTheCount (letter : List String) (j : Nat) (position : j < letter.length) :
    (letter.take j).count (letter.getD j "") < letter.count (letter.getD j "") := by
  have hSplit : letter = letter.take j ++ letter[j] :: letter.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j letter, List.drop_eq_getElem_cons position]
  have hAt : letter.getD j "" = letter[j] := List.getD_eq_getElem _ _ position
  have hCount := congrArg (List.count letter[j]) hSplit
  rw [List.count_append, List.count_cons_self] at hCount
  rw [hAt]
  omega

/-- **A slot's number of take is below what the two lookups take of its owner.** -/
theorem takeOfASlotIsBelow (data : KeyPub) (number : Nat) (face : Face) (planes : 2 ≤ face.planes)
    (levels : ∀ v ∈ face.parts, 1 ≤ v)
    (ownBound : (takenBeforeLookup data number).1 + (face.slots - 2 * face.parts.length) ≤
      (takesOfBothLookups data).1)
    (keyBound : (takenBeforeLookup data number).2 + 2 * face.parts.length ≤ (takesOfBothLookups data).2)
    (j : Nat) (below : j < face.slots) :
    takeOfSlot data number face j <
      if slotOwner face j == indexMaskRun then (takesOfBothLookups data).2
      else (takesOfBothLookups data).1 := by
  have hMarks := ProofFile.Honest.K3.Parts.unroll_key face planes
  have hPosition : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).length := by
    rw [unrolledLengthIsTheSlots face planes]
    exact below
  have hFront := countInFrontIsBelowTheCount _ j hPosition
  have hTrue := AtPublicFiles.KeyLookup.fromKeys_true levels
  have hLength := AtPublicFiles.KeyLookup.fromKeys_length face
  have hBoth := AtPublicFiles.KeyLookup.count_tf (fromKeys face)
  unfold takeOfSlot
  cases hFlag : (slotOwner face j == indexMaskRun) with
  | true =>
    have hOwner : slotOwner face j = indexMaskRun := by simpa using hFlag
    have hCount : (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).count indexMaskRun =
        2 * face.parts.length := by
      rw [← marksCountTheIndexMasks, hMarks, hTrue]
    simp only [if_true]
    change _ + ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count (slotOwner face j) < _
    change ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count (slotOwner face j) <
      (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).count (slotOwner face j) at hFront
    rw [hOwner] at hFront ⊢
    omega
  | false =>
    have hOwner := slotOwnerIsOneOfTwo face j hPosition hFlag
    have hCount : (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).count K3.multRun =
        face.slots - 2 * face.parts.length := by
      rw [← marksCountTheMultiplicities _ (membersOfTheKeyLetter face), hMarks]
      omega
    simp only [Bool.false_eq_true, if_false]
    change _ + ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count (slotOwner face j) < _
    change ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count (slotOwner face j) <
      (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).count (slotOwner face j) at hFront
    rw [hOwner] at hFront ⊢
    omega

theorem dealKeepsTheLength : ∀ (marks : List Bool) (a b : Nat), (deal marks a b).length = marks.length
  | [], _, _ => rfl
  | false :: l, a, b => by
    show (deal l (a + 1) b).length + 1 = _
    rw [dealKeepsTheLength l]
    rfl
  | true :: l, a, b => by
    show (deal l a (b + 1)).length + 1 = _
    rw [dealKeepsTheLength l]
    rfl

/-- **Under a slot the reader reads the coin that `maskOf` names.** General in the reader: what it reads at the two messages, and
that these hold their owners' coins at the numbers of the takes, are premises. -/
theorem maskEntryReadsAsItsCoin {home : Array Slot} {ownMessage keyMessage ownMaskRows keyMaskRows : Nat}
    (data : KeyPub) (number : Nat) (face : Face) (planes : 2 ≤ face.planes)
    (levels : ∀ v ∈ face.parts, 1 ≤ v)
    (ownBound : (takenBeforeLookup data number).1 + (face.slots - 2 * face.parts.length) ≤
      (takesOfBothLookups data).1)
    (keyBound : (takenBeforeLookup data number).2 + 2 * face.parts.length ≤ (takesOfBothLookups data).2)
    (homesAre : home.toList =
      (deal (fromKeys face) (takenBeforeLookup data number).1 (takenBeforeLookup data number).2).map
        (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows 0 0))
    (look : Addr → (d : Due) × Cs d) (reader : Slot → OnBytes.Slice.GE) (own key : Nat → OnBytes.E)
    (readsOwn : ∀ ν, reader ⟨ownMessage, ν⟩ = Johnson.RunOne.KeyRows23.readE (own ν))
    (readsKey : ∀ ν, reader ⟨keyMessage, ν⟩ = Johnson.RunOne.KeyRows23.readE (key ν))
    (ownCoin : ∀ n, n < (takesOfBothLookups data).1 → own (takenNo ownMaskRows n) =
      (coinsE (look ⟨msgPlace, 0⟩).2).getD (tableAt data.sMsg 0 + n) OnBytes.zeroE)
    (keyCoin : ∀ n, n < (takesOfBothLookups data).2 → key (takenNo keyMaskRows n) =
      (coinsE (look ⟨idxPlace, 0⟩).2).getD (tableAt data.sIdx 0 + n) OnBytes.zeroE)
    (j : Nat) (inside : j < home.size) :
    reader (home.getD j default) =
      maskOf (keyOwners face) face (keyBookHomes data number) look 0 j := by
  have below : j < face.slots := by
    have hSize : home.size = home.toList.length := by simp
    rw [hSize, homesAre, List.length_map, dealKeepsTheLength, AtPublicFiles.KeyLookup.fromKeys_length] at inside
    exact inside
  have hHome := homeOfASlot data number face planes homesAre j below
  have hBelow := takeOfASlotIsBelow data number face planes levels ownBound keyBound j below
  have hGet : home.getD j default = home[j] := by simp [Array.getD, inside]
  rw [Array.getElem?_eq_getElem inside] at hHome
  have hSlot := Option.some.inj hHome
  rw [hGet, hSlot]
  have hPosition : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).length := by
    rw [unrolledLengthIsTheSlots face planes]
    exact below
  unfold maskOf
  rw [Nat.sub_zero]
  cases hFlag : (slotOwner face j == indexMaskRun) with
  | true =>
    have hOwner : (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).getD j "" = indexMaskRun := by
      simpa using hFlag
    rw [hFlag] at hBelow
    have hTake : takeOfSlot data number face j = (takenBeforeLookup data number).2 +
        ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count indexMaskRun := by
      unfold takeOfSlot
      rw [hFlag]
      show _ + ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count
        ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).getD j "") = _
      rw [hOwner]
      rfl
    rw [if_pos rfl, readsKey, keyCoin _ hBelow, hOwner, keyBookHomeOfTheSecondOwner, hTake,
      ← Nat.add_assoc]
    rfl
  | false =>
    have hOwner : (ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).getD j "" = K3.multRun :=
      slotOwnerIsOneOfTwo face j hPosition hFlag
    rw [hFlag] at hBelow
    have hTake : takeOfSlot data number face j = (takenBeforeLookup data number).1 +
        ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count K3.multRun := by
      unfold takeOfSlot
      rw [hFlag]
      show _ + ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).take j).count
        ((ProofFile.Honest.K3.Parts.unroll (keyOwners face) face).getD j "") = _
      rw [hOwner]
      rfl
    rw [if_neg (by simp), readsOwn, ownCoin _ hBelow, hOwner, keyBookHomeOfTheFirstOwner, hTake,
      ← Nat.add_assoc]
    rfl

/-! ## 2 At the key file's thread -/

section Top
open ProofFile.Honest.K3.Parts.Key (faceK)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)

/-- The first written lookup. -/
abbrev firstWrittenLookup : Lookup := OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk0Full
/-- The second. -/
abbrev secondWrittenLookup : Lookup := OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk1Full

theorem everyPartHasALevelAtTheWrittenLookups :
    (∀ v ∈ (faceOfLkp firstWrittenLookup).parts, 1 ≤ v) ∧
      ∀ v ∈ (faceOfLkp secondWrittenLookup).parts, 1 ≤ v := by
  have hParts : (OnBytes.Wf.lookupsOf keyFull.ranges.x (OnBytes.Wf.matrixOf keyFull.once.shape)).map (fun y => y.parts) =
      [List.replicate 12 36, List.replicate 12 35] := AtPublicFiles.KeyFaces.parts_full
  rw [AtPublicFiles.Key.faces_written] at hParts
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hParts
  constructor
  · intro v hv
    have hv' : v ∈ firstWrittenLookup.parts := hv
    rw [hParts.1] at hv'
    have := List.eq_of_mem_replicate hv'
    omega
  · intro v hv
    have hv' : v ∈ secondWrittenLookup.parts := hv
    rw [hParts.2] at hv'
    have := List.eq_of_mem_replicate hv'
    omega

theorem planesAtTheWrittenBook {data : KeyPub} (written : fullPub = some data) :
    2 ≤ (faceOfLkp firstWrittenLookup).planes ∧ 2 ≤ (faceOfLkp secondWrittenLookup).planes := by
  have hFaces : data.faces = [faceOfLkp firstWrittenLookup, faceOfLkp secondWrittenLookup] :=
    keyBookFacesAreTheWrittenFaces written
  have hStand := lookupsStandAtTheWrittenSizes data written
  constructor
  · obtain ⟨face, hFace, hp, -⟩ := hStand.2 0 (by decide)
    rw [hFaces] at hFace
    obtain rfl : faceOfLkp firstWrittenLookup = face := Option.some.inj hFace
    exact hp
  · obtain ⟨face, hFace, hp, -⟩ := hStand.2 1 (by decide)
    rw [hFaces] at hFace
    obtain rfl : faceOfLkp secondWrittenLookup = face := Option.some.inj hFace
    exact hp

theorem takesOfBothLookupsAtTwoFaces {data : KeyPub} {first second : Face}
    (faces : data.faces = [first, second]) (levelsFirst : ∀ v ∈ first.parts, 1 ≤ v)
    (levelsSecond : ∀ v ∈ second.parts, 1 ≤ v) :
    takesOfBothLookups data =
      (first.slots - 2 * first.parts.length + (second.slots - 2 * second.parts.length),
        2 * first.parts.length + 2 * second.parts.length) := by
  have a := spansTakeTheSlotsOfTheTwoOwners first levelsFirst
  have b := spansTakeTheSlotsOfTheTwoOwners second levelsSecond
  simp [takesOfBothLookups, takenBeforeLookup, faces, a.1, a.2, b.1, b.2]

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles}

/-- **The homes at border 4 or 10, as a list**: by the deal behind the takes of the lookups in front. -/
theorem homesByTheDealAtTheKey (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (data : KeyPub) (written : fullPub = some data)
    (number : Nat) (below : number < 2) :
    ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables)
        (if number = 0 then 4 else 10) k s m E →
      s.base.home.toList =
        (deal (fromKeys (faceK 1 ⟨kRef, 3076096⟩ (if number = 0 then lk0Full else lk1Full)))
          (takenBeforeLookup data number).1 (takenBeforeLookup data number).2).map
          (homeOfCoin (one₀ source).ranges.messageId s.idx (one₀ source).ranges.message.shape.maskRows
            (one₀ source).indexMasks.shape.maskRows 0 0) := by
  intro k s m E thread
  obtain ⟨public₀, made, fromFiles, maker, madeSource, -, -⟩ := sourced.source
  have reading := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO fromFiles
  have five := Johnson.RunOne.Law.KeyInScope.five_in_scope scope reading maker madeSource
    sourced.named.plan
  have two : lookupsOf (one₀ source) = [firstWrittenLookup, secondWrittenLookup] :=
    sourceLookupsAreTheWrittenLookups sourced scope
  obtain ⟨levels₀, levels₁⟩ := everyPartHasALevelAtTheWrittenLookups
  obtain ⟨a₁, a₂, a₃, a₄⟩ := writtenMessagesHaveAnswersAndMaskRows
  have indexAnswers : (one₀ source).indexMasks.shape.answers ≠ 0 := by
    show source.Y.k.oneTime.indexMasks.shape.answers ≠ 0
    rw [five.2.2.2.1]
    exact a₁
  have indexRows : 0 < (one₀ source).indexMasks.shape.maskRows := by
    show 0 < source.Y.k.oneTime.indexMasks.shape.maskRows
    rw [five.2.2.2.1]
    exact a₂
  have ownAnswers : (one₀ source).ranges.message.shape.answers ≠ 0 := by
    show source.Y.k.oneTime.ranges.message.shape.answers ≠ 0
    rw [five.2.1]
    exact a₃
  have ownRows : 0 < (one₀ source).ranges.message.shape.maskRows := by
    show 0 < source.Y.k.oneTime.ranges.message.shape.maskRows
    rw [five.2.1]
    exact a₄
  have hFaces : data.faces = [faceOfLkp firstWrittenLookup, faceOfLkp secondWrittenLookup] :=
    keyBookFacesAreTheWrittenFaces written
  have hTaken := takesInFrontOfALookupAreTheBooks data _ _ hFaces levels₀
  have hMade := thread.2.2.2.2.1
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · have reached := reach_made₁ source numbers later filling w₀ rc x
      (by rw [(AtPublicFiles.KeyThread.lengths scope sourced.named).1]; decide) hMade
    have hBehind := (standBehindTheFirstCaller (one := one₀ source) (D := source.Y.D.1)
      (told := source.Y.told.1) (set := source.set) (N := numbers) two indexAnswers indexRows ownAnswers
      ownRows levels₀ reached).2
    rw [hTaken.1]
    exact hBehind
  · have reached := reach_made₁ source numbers later filling w₀ rc x
      (by rw [(AtPublicFiles.KeyThread.lengths scope sourced.named).1]; decide) hMade
    have hBehind := homesBehindTheSecondCaller (one := one₀ source) (D := source.Y.D.1)
      (told := source.Y.told.1) (set := source.set) (N := numbers) two indexAnswers indexRows ownAnswers
      ownRows levels₀ levels₁ reached
    rw [hTaken.2]
    exact hBehind

end Top

section TheTwoDebts
open ProofFile.Honest.K3.Parts.Key (faceK)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)
open Johnson.RunOne.KeyRows23 (readE)
open VerifiableInference.Desc.Key (mkOf)

/-- **THE MASK ENTRIES UNDER A LOOKUP's SLOTS READ AS THE COINS THAT `maskOf` NAMES, AT THE BORDER OF THE LOOKUP**, from the two debts
that are not the ledger's: each owner's sender lays its coins in the order of taking (`ownLays`, `keyLays`), and the thread's
witness reads those two messages (`witnessReads`). Conditional besides: the description is sourced from the files in scope; the
book is at the written sizes. -/
theorem maskEntriesReadAsTheCoinsOfTheTwoDebts {W₀ Rc Cells M Smp Rec X' : Type} (data : KeyPub) (source : Source)
    (numbers : H2U.PlaceNums) (later : LaterPlaces) (filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec)
    (w₀ : W₀) (rc : Rc) (x : Xi)
    {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
    {tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table}
    {files : VerifierAndGoals.PublicFiles} (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (written : fullPub = some data) (number : Nat)
    (below : number < 2)
    (ownEntry keyEntry : Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Nat → OnBytes.E)
    (ownLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨msgPlace, 0⟩
      (one₀ source).ranges.message.shape.maskRows (tableAt data.sMsg 0) (takesOfBothLookups data).1 ownEntry)
    (keyLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨idxPlace, 0⟩
      (one₀ source).indexMasks.shape.maskRows (tableAt data.sIdx 0) (takesOfBothLookups data).2 keyEntry)
    (witnessReads : ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables)
        (if number = 0 then 4 else 10) k s m E → ∀ more ν,
        readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
            ⟨(one₀ source).ranges.messageId, ν⟩) =
          readE (ownEntry k m.st.input (m.st.heard ++ more) ν) ∧
        readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) ⟨s.idx, ν⟩) =
          readE (keyEntry k m.st.input (m.st.heard ++ more) ν)) :
    ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables)
        (if number = 0 then 4 else 10) k s m E → ∀ more j, j < s.base.home.size →
      readE (mkOf (plan₁ (one₀ source)) filling.R
          (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
          (s.base.home.getD j default)) =
        maskOf (keyOwners (faceK 1 ⟨kRef, 3076096⟩ (if number = 0 then lk0Full else lk1Full)))
          (faceK 1 ⟨kRef, 3076096⟩ (if number = 0 then lk0Full else lk1Full))
          (keyBookHomes data number) (k.look 0) 0 j := by
  intro k s m E thread more j inside
  have hHomes := homesByTheDealAtTheKey source numbers later filling w₀ rc x sourced scope data written
    number below k s m E thread
  have hFaces : data.faces = [faceOfLkp firstWrittenLookup, faceOfLkp secondWrittenLookup] :=
    keyBookFacesAreTheWrittenFaces written
  obtain ⟨levels₀, levels₁⟩ := everyPartHasALevelAtTheWrittenLookups
  obtain ⟨planes₀, planes₁⟩ := planesAtTheWrittenBook written
  have hTaken := takesInFrontOfALookupAreTheBooks data _ _ hFaces levels₀
  have hBoth := takesOfBothLookupsAtTwoFaces hFaces levels₀ levels₁
  have reads := witnessReads k s m E thread more
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · exact maskEntryReadsAsItsCoin data 0 (faceOfLkp firstWrittenLookup) planes₀ levels₀
      (by rw [hTaken.1, hBoth]; show 0 + _ ≤ _ + _; omega)
      (by rw [hTaken.1, hBoth]; show 0 + _ ≤ _ + _; omega)
      hHomes (k.look 0)
      (fun slot => readE (mkOf (plan₁ (one₀ source)) filling.R
        (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) slot))
      (ownEntry k m.st.input (m.st.heard ++ more)) (keyEntry k m.st.input (m.st.heard ++ more))
      (fun ν => (reads ν).1) (fun ν => (reads ν).2)
      (fun n hn => ownLays k _ _ n hn) (fun n hn => keyLays k _ _ n hn) j inside
  · exact maskEntryReadsAsItsCoin data 1 (faceOfLkp secondWrittenLookup) planes₁ levels₁
      (by rw [hTaken.2, hBoth] <;> exact Nat.le_refl _)
      (by rw [hTaken.2, hBoth] <;> exact Nat.le_refl _)
      hHomes (k.look 0)
      (fun slot => readE (mkOf (plan₁ (one₀ source)) filling.R
        (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) slot))
      (ownEntry k m.st.input (m.st.heard ++ more)) (keyEntry k m.st.input (m.st.heard ++ more))
      (fun ν => (reads ν).1) (fun ν => (reads ν).2)
      (fun n hn => ownLays k _ _ n hn) (fun n hn => keyLays k _ _ n hn) j inside

end TheTwoDebts

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.homeOfASlot
#print axioms AtPublicFiles.Lookup.Key.takeOfASlotIsBelow
#print axioms AtPublicFiles.Lookup.Key.maskEntryReadsAsItsCoin
#print axioms AtPublicFiles.Lookup.Key.everyPartHasALevelAtTheWrittenLookups
#print axioms AtPublicFiles.Lookup.Key.planesAtTheWrittenBook
#print axioms AtPublicFiles.Lookup.Key.takesOfBothLookupsAtTwoFaces
#print axioms AtPublicFiles.Lookup.Key.homesByTheDealAtTheKey
#print axioms AtPublicFiles.Lookup.Key.maskEntriesReadAsTheCoinsOfTheTwoDebts
