-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: of the three debts under the mask entries at a lookup's border the sender's is paid at the two owners'
  sendings (`msgOwner_lays_in_order`, `idxOwner_lays_in_order`, AtFullSide/K1/KeyOwnersLayInOrder.lean). What is left is that the
  thread's witness reads the rows that those senders lay: `WitnessReadsTheSendersRows`, a premise here, by name.

AtFullSide/Honest/K3/Key/MaskEntriesReadAsTheCoinsAtTheSendersRows.lean. Theorems with proofs.

  `takesOfBothLookupsFitTheMaskRows`   the two lookups' takes fit each owner's mask rows, in the form of that file's premise
  `takesDoNotFitTheOtherOwner`         THE CONTROL: the own message's takes do not fit the index-mask message's rows
  `oneTimeIsTheWrittenOneInScope`      `OneFull` of the source's one-time chain
  `ownSendersEntry`, `keySendersEntry`   the entries that those theorems name, at the two jobs
  `ANumberThatTheBitsRead`              a number of the main table that a lookup's bits read
  `maskEntryReadsAsItsCoinAtTheTakes`, `maskEntriesReadAsTheCoinsAtTheTakes`   the law of E2E/Lookup/Key/MaskEntriesReadAsTheCoins.lean,
                                        the witness asked at the numbers of the takes alone
  `WitnessReadsTheSendersRows`         the debt that is left: at those numbers, and at the numbers that the bits read
  `maskEntriesReadAsTheCoinsAtTheSendersRows`   **the join**

Limits. `WitnessReadsTheSendersRows` is a premise. The coins of the two senders are had by "there are", each with its `OwnIs`. The
written sizes alone. Nothing on any property of a protocol.
-/
import AtFullSide.K1.KeyOwnersLayInOrder
import E2E.Lookup.Key.MaskEntriesReadAsTheCoins
import E2E.KeyLookups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Lookup.Key
open ProofFile.Honest
open ProofFile.Honest.K1 (maskWordE maskEntriesW msgOwner_lays_in_order idxOwner_lays_in_order dueR)
open ProofFile.Honest.K3 (keyOwners)
open ProofFile.Honest.K3.Parts (maskOf)
open ProofFile.Honest.K3.Parts.Key (faceK)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyThread
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyValues (multiplicitiesSending indexMaskSending multiplicitiesGroups matrixEntryOf oneOf)
open AtPublicFiles.KeyFile (In1)
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi pieces mkOf)
open Johnson.Pack (lk0Full lk1Full)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23 (readE)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)
open OnBytes (E Slot takenNo)
open VerifiableInference.Desc.K3 (Face fromKeys)

/-- **At the written sizes the two lookups' takes fit each owner's mask rows.** By Lean's kernel. -/
theorem writtenTakesFitTheMaskRows :
    ((faceK 1 ⟨kRef, 3076096⟩ lk0Full).slots - 2 * (faceK 1 ⟨kRef, 3076096⟩ lk0Full).parts.length +
        ((faceK 1 ⟨kRef, 3076096⟩ lk1Full).slots - 2 * (faceK 1 ⟨kRef, 3076096⟩ lk1Full).parts.length)) ≤
      maskEntriesW (OnBytes.Wf.messageOf keyFull.ranges.x) ∧
    2 * (faceK 1 ⟨kRef, 3076096⟩ lk0Full).parts.length + 2 * (faceK 1 ⟨kRef, 3076096⟩ lk1Full).parts.length ≤
      maskEntriesW #[keyFull.once.input] := by
  decide +kernel

/-- **The control: the own message's takes do not fit the index-mask message's rows.** So the test can fail. By Lean's kernel. -/
theorem takesDoNotFitTheOtherOwner :
    ¬ ((faceK 1 ⟨kRef, 3076096⟩ lk0Full).slots - 2 * (faceK 1 ⟨kRef, 3076096⟩ lk0Full).parts.length +
        ((faceK 1 ⟨kRef, 3076096⟩ lk1Full).slots - 2 * (faceK 1 ⟨kRef, 3076096⟩ lk1Full).parts.length)) ≤
      maskEntriesW #[keyFull.once.input] := by
  decide +kernel

/-- **The two lookups' takes fit each owner's mask rows**, in the form of the premise of `msgOwner_lays_in_order` and
`idxOwner_lays_in_order`. -/
theorem takesOfBothLookupsFitTheMaskRows {data : KeyPub} (written : fullPub = some data) :
    (takesOfBothLookups data).1 ≤ maskEntriesW (OnBytes.Wf.messageOf keyFull.ranges.x) ∧
      (takesOfBothLookups data).2 ≤ maskEntriesW #[keyFull.once.input] := by
  have hFaces : data.faces = [faceOfLkp firstWrittenLookup, faceOfLkp secondWrittenLookup] :=
    keyBookFacesAreTheWrittenFaces written
  obtain ⟨levels₀, levels₁⟩ := everyPartHasALevelAtTheWrittenLookups
  rw [takesOfBothLookupsAtTwoFaces hFaces levels₀ levels₁]
  exact writtenTakesFitTheMaskRows

section
variable {files : VerifierAndGoals.PublicFiles} {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}

/-- **In scope the source's one-time chain is the written one.** -/
theorem oneTimeIsTheWrittenOneInScope (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) : OneFull (one₀ source) := by
  obtain ⟨_, _, read, made, fromMade, -, -⟩ := sourced.source
  obtain ⟨-, ranges, shape, index, codes⟩ := Johnson.RunOne.Law.KeyInScope.five_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO read) made fromMade sourced.named.plan
  exact ⟨codes, index, ranges, shape⟩

/-- The first message of the multiplicities' sending has the shape of the ranges' message. -/
theorem ownMaskRowsAreTheSentShapes (full : OneFull (one₀ source)) :
    ((OnBytes.Wf.messageOf keyFull.ranges.x).getD 0 default).shape.maskRows =
      (one₀ source).ranges.message.shape.maskRows := by
  obtain ⟨positive, first⟩ := AtPublicFiles.KeyLookup.messageOf_head keyFull.ranges.x
  have hGet : (OnBytes.Wf.messageOf keyFull.ranges.x).getD 0 default = keyFull.ranges.x.message := by
    simp [Array.getD, positive, first]
  rw [hGet, full.ranges]

end

section Senders
variable {W₀ Rc X : Type} (data : KeyPub) (f : W₀ → Weights) (source : Source) (own₀ : X)

/-- **The entry of the multiplicities' sender**: the word of its mask table, of the rows that its part lays of its own coins. -/
def ownSendersEntry (coins : Coins (keyBook data) →
      Cs (dueR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg)) :
    Coins (keyBook data) → In1 W₀ Rc → List Fmt.Drawn → Nat → E :=
  fun c w heard i => maskWordE (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg
    ((multiplicitiesSending (Rc := Rc) (X := X) f source).data w { heard := heard, own := own₀, seen := .bare [] }) 0 (coins c) i

/-- **The entry of the index masks' sender.** -/
def keySendersEntry (coins : Coins (keyBook data) →
      Cs (dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) source).P fun _ => none)) :
    Coins (keyBook data) → In1 W₀ Rc → List Fmt.Drawn → Nat → E :=
  fun c w heard i => maskWordE (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) source).P (fun _ => none)
    ((indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) source).data w { heard := heard, own := own₀, seen := .bare [] }) 0
    (coins c) i

end Senders

/-- **A number of the multiplicities' main table that the bits of lookup `number` read**: the place, in a block of that lookup that holds
the plane, of an entry that `bitVec` asks. -/
def ANumberThatTheBitsRead (number place : Nat) : Prop :=
  ∃ b ∈ AtPublicFiles.Key.sixBlocks, b.lookup = number ∧ ∃ front table,
    front < 2 ^ b.logPlanes ∧ table < 2 ^ ([lk0Full, lk1Full].getD b.lookup default).d ∧ place =
      VerifiableInference.Desc.Key.blockPlace 1 18 b (front + 2 ^ b.logPlanes * table)

/-- **Under a slot the reader reads the coin that `maskOf` names**, where the reader is asked at the numbers of the takes alone. -/
theorem maskEntryReadsAsItsCoinAtTheTakes {home : Array Slot} {ownMessage keyMessage ownMaskRows keyMaskRows : Nat}
    (data : KeyPub) (number : Nat) (face : Face) (planes : 2 ≤ face.planes)
    (levels : ∀ v ∈ face.parts, 1 ≤ v)
    (ownBound : (takenBeforeLookup data number).1 + (face.slots - 2 * face.parts.length) ≤
      (takesOfBothLookups data).1)
    (keyBound : (takenBeforeLookup data number).2 + 2 * face.parts.length ≤ (takesOfBothLookups data).2)
    (homesAre : home.toList =
      (deal (fromKeys face) (takenBeforeLookup data number).1 (takenBeforeLookup data number).2).map
        (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows 0 0))
    (look : Addr → (d : Due) × Cs d) (reader : Slot → OnBytes.Slice.GE) (own key : Nat → OnBytes.E)
    (readsOwn : ∀ n, n < (takesOfBothLookups data).1 → reader ⟨ownMessage, takenNo ownMaskRows n⟩ =
      readE (own (takenNo ownMaskRows n)))
    (readsKey : ∀ n, n < (takesOfBothLookups data).2 → reader ⟨keyMessage, takenNo keyMaskRows n⟩ =
      readE (key (takenNo keyMaskRows n)))
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
    rw [if_pos rfl, readsKey _ hBelow, keyCoin _ hBelow, hOwner, keyBookHomeOfTheSecondOwner, hTake,
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
    rw [if_neg (by simp), readsOwn _ hBelow, ownCoin _ hBelow, hOwner, keyBookHomeOfTheFirstOwner, hTake,
      ← Nat.add_assoc]
    rfl

section TheTwoDebts
variable {W₀ Rc Cells M Smp Rec X X' : Type} (data : KeyPub) (f : W₀ → Weights) (source : Source)
  (numbers : H2U.PlaceNums) (later : LaterPlaces)
  (filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table) (own₀ : X)

/-- **The theorem of the two debts, with the witness asked at the numbers of the takes alone**: the sister of
`maskEntriesReadAsTheCoinsOfTheTwoDebts`, whose premise asks every number. -/
theorem maskEntriesReadAsTheCoinsAtTheTakes {files : VerifierAndGoals.PublicFiles}
    (sourced : KeySourced files source numbers later) (scope : VerifierAndGoals.InScope files = true)
    (written : fullPub = some data) (number : Nat) (below : number < 2)
    (ownEntry keyEntry : Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Nat → E)
    (ownLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨msgPlace, 0⟩
      (one₀ source).ranges.message.shape.maskRows (tableAt data.sMsg 0) (takesOfBothLookups data).1 ownEntry)
    (keyLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨idxPlace, 0⟩
      (one₀ source).indexMasks.shape.maskRows (tableAt data.sIdx 0) (takesOfBothLookups data).2 keyEntry)
    (witnessReads : ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables)
        (if number = 0 then 4 else 10) k s m E → ∀ more n,
        (n < (takesOfBothLookups data).1 → readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
            ⟨(one₀ source).ranges.messageId, takenNo (one₀ source).ranges.message.shape.maskRows n⟩) =
          readE (ownEntry k m.st.input (m.st.heard ++ more)
            (takenNo (one₀ source).ranges.message.shape.maskRows n))) ∧
        (n < (takesOfBothLookups data).2 → readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
            ⟨s.idx, takenNo (one₀ source).indexMasks.shape.maskRows n⟩) =
          readE (keyEntry k m.st.input (m.st.heard ++ more)
            (takenNo (one₀ source).indexMasks.shape.maskRows n)))) :
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
  have hHomes := homesByTheDealAtTheKey source numbers later filling w₀ rc x (halves := halves)
    (tables := tables) sourced scope data written number below k s m E thread
  have hFaces : data.faces = [faceOfLkp firstWrittenLookup, faceOfLkp secondWrittenLookup] :=
    keyBookFacesAreTheWrittenFaces written
  obtain ⟨levels₀, levels₁⟩ := everyPartHasALevelAtTheWrittenLookups
  obtain ⟨planes₀, planes₁⟩ := planesAtTheWrittenBook written
  have hTaken := takesInFrontOfALookupAreTheBooks data _ _ hFaces levels₀
  have hBoth := takesOfBothLookupsAtTwoFaces hFaces levels₀ levels₁
  have reads := witnessReads k s m E thread more
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · exact maskEntryReadsAsItsCoinAtTheTakes data 0 (faceOfLkp firstWrittenLookup) planes₀ levels₀
      (by rw [hTaken.1, hBoth]; show 0 + _ ≤ _ + _; omega)
      (by rw [hTaken.1, hBoth]; show 0 + _ ≤ _ + _; omega)
      hHomes (k.look 0)
      (fun slot => readE (mkOf (plan₁ (one₀ source)) filling.R
        (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) slot))
      (ownEntry k m.st.input (m.st.heard ++ more)) (keyEntry k m.st.input (m.st.heard ++ more))
      (fun n hn => (reads n).1 hn) (fun n hn => (reads n).2 hn)
      (fun n hn => ownLays k _ _ n hn) (fun n hn => keyLays k _ _ n hn) j inside
  · exact maskEntryReadsAsItsCoinAtTheTakes data 1 (faceOfLkp secondWrittenLookup) planes₁ levels₁
      (by rw [hTaken.2, hBoth] <;> exact Nat.le_refl _)
      (by rw [hTaken.2, hBoth] <;> exact Nat.le_refl _)
      hHomes (k.look 0)
      (fun slot => readE (mkOf (plan₁ (one₀ source)) filling.R
        (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) slot))
      (ownEntry k m.st.input (m.st.heard ++ more)) (keyEntry k m.st.input (m.st.heard ++ more))
      (fun n hn => (reads n).1 hn) (fun n hn => (reads n).2 hn)
      (fun n hn => ownLays k _ _ n hn) (fun n hn => keyLays k _ _ n hn) j inside

/-- **THE DEBT THAT IS LEFT**: the thread's witness reads the rows that the two senders lay: their mask tables at the lookup's border,
at the numbers of the takes; and the multiplicities' main table behind the challenges in front of the lookup, at the numbers that the
bits read. -/
structure WitnessReadsTheSendersRows (number inFront : Nat)
    (ownCoins : Coins (keyBook data) → Cs (dueR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg))
    (keyCoins : Coins (keyBook data) →
      Cs (dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) source).P fun _ => none)) : Prop where
  /-- the two mask tables, at the numbers of the takes -/
  masks : ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
    Thr (laid₁ source numbers later filling w₀ rc x halves tables)
      (if number = 0 then 4 else 10) k s m E → ∀ more n,
      (n < (takesOfBothLookups data).1 → readE (mkOf (plan₁ (one₀ source)) filling.R
          (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
          ⟨(one₀ source).ranges.messageId, takenNo (one₀ source).ranges.message.shape.maskRows n⟩) =
        readE (ownSendersEntry data f source own₀ ownCoins k m.st.input (m.st.heard ++ more)
          (takenNo (one₀ source).ranges.message.shape.maskRows n))) ∧
      (n < (takesOfBothLookups data).2 → readE (mkOf (plan₁ (one₀ source)) filling.R
          (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
          ⟨s.idx, takenNo (one₀ source).indexMasks.shape.maskRows n⟩) =
        readE (keySendersEntry data source own₀ keyCoins k m.st.input (m.st.heard ++ more)
          (takenNo (one₀ source).indexMasks.shape.maskRows n)))
  /-- the multiplicities' main table, at the numbers that the bits read -/
  main : ∀ (k : Coins (keyBook data)) (input : Local W₀ Rc Xi Unit) (heard : List Fmt.Drawn),
    inFront ≤ heard.length → ∀ place, ANumberThatTheBitsRead number place →
      OnBytes.Slice.readE (filling.R.val (filling.R.of (filling.wit k input.w₀ input.rc heard []) 1) .main place) =
        OnBytes.Slice.readE (E.ofTriple (OnBytes.Slice.ofE
          ((ProofFile.Honest.K1.rowsR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg
            ((multiplicitiesSending (Rc := Rc) (X := X) f source).data input
              { heard := heard, own := own₀, seen := .bare [] })
            (ownCoins k) 0).word (Johnson.Prover.Send.shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0)
            .main place)))

/-- **THE MASK ENTRIES AT A LOOKUP's BORDER READ AS THE COINS, WITH ONE DEBT LEFT**: there are coins of the two senders, each the
book's at its address, such that wherever the witness reads those senders' rows, the mask entry at each home reads as the coin that
`maskOf` names. Conditional: the description is sourced from the files in scope; the book is at the written sizes. -/
theorem maskEntriesReadAsTheCoinsAtTheSendersRows {files : VerifierAndGoals.PublicFiles}
    (sourced : KeySourced files source numbers later) (scope : VerifierAndGoals.InScope files = true)
    (written : fullPub = some data) (number inFront : Nat) (below : number < 2) :
    ∃ ownCoins keyCoins,
      OwnIs (keyBook data) 0 ⟨msgPlace, 0⟩ (dueR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg) ownCoins ∧
      OwnIs (keyBook data) 0 ⟨idxPlace, 0⟩
        (dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) source).P fun _ => none) keyCoins ∧
      (WitnessReadsTheSendersRows data f source numbers later filling w₀ rc x halves tables own₀ number inFront
          ownCoins keyCoins →
        ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
          Thr (laid₁ source numbers later filling w₀ rc x halves tables)
            (if number = 0 then 4 else 10) k s m E → ∀ more j, j < s.base.home.size →
          readE (mkOf (plan₁ (one₀ source)) filling.R
              (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
              (s.base.home.getD j default)) =
            maskOf (keyOwners (faceK 1 ⟨kRef, 3076096⟩ (if number = 0 then lk0Full else lk1Full)))
              (faceK 1 ⟨kRef, 3076096⟩ (if number = 0 then lk0Full else lk1Full))
              (keyBookHomes data number) (k.look 0) 0 j) := by
  have full := oneTimeIsTheWrittenOneInScope sourced scope
  obtain ⟨fitsOwn, fitsKey⟩ := takesOfBothLookupsFitTheMaskRows written
  obtain ⟨ownCoins, ownIs, ownLays⟩ := msgOwner_lays_in_order (W := In1 W₀ Rc) (X := X) data written
    (one₀ source) full pieces (multiplicitiesGroups source) 1 own₀ (matrixEntryOf f) rideMsg rides_full.2.1 rfl
    (takesOfBothLookups data).1 fitsOwn
  obtain ⟨keyCoins, keyIs, keyLays⟩ := idxOwner_lays_in_order (W := In1 W₀ Rc) (X := X) data written
    (one₀ source) full pieces (VerifiableInference.Desc.Key.groupsTold source.Y.told.1 0
      (VerifiableInference.Desc.Key.rootsAt source.Y.D.1 0)) 0 own₀ (takesOfBothLookups data).2 fitsKey
  rw [ownMaskRowsAreTheSentShapes full] at ownLays
  refine ⟨ownCoins, keyCoins, ownIs, keyIs, fun reads => ?_⟩
  have keyRows : keyFull.once.input.shape.maskRows = (one₀ source).indexMasks.shape.maskRows := by
    rw [full.idx]
  rw [keyRows] at keyLays
  exact maskEntriesReadAsTheCoinsAtTheTakes data source numbers later filling w₀ rc x halves tables sourced
    scope written number below (ownSendersEntry data f source own₀ ownCoins)
    (keySendersEntry data source own₀ keyCoins) ownLays keyLays reads.masks

end TheTwoDebts

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.writtenTakesFitTheMaskRows
#print axioms AtPublicFiles.Lookup.Key.takesDoNotFitTheOtherOwner
#print axioms AtPublicFiles.Lookup.Key.takesOfBothLookupsFitTheMaskRows
#print axioms AtPublicFiles.Lookup.Key.oneTimeIsTheWrittenOneInScope
#print axioms AtPublicFiles.Lookup.Key.ownMaskRowsAreTheSentShapes
#print axioms AtPublicFiles.Lookup.Key.maskEntryReadsAsItsCoinAtTheTakes
#print axioms AtPublicFiles.Lookup.Key.maskEntriesReadAsTheCoinsAtTheTakes
#print axioms AtPublicFiles.Lookup.Key.maskEntriesReadAsTheCoinsAtTheSendersRows
