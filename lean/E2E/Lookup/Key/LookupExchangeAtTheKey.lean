-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: (K-P2), THE THIRD OF THE FIVE, WHOLE: `ExchangeS` (Honest/Thread/PaysS.lean) AT NUMBERS 4 AND 10 OF THE KEY FILE's
  FIRST THREAD, at the key's book, from what the offline prover's letters are said to be.

E2E/Lookup/Key/LookupExchangeAtTheKey.lean. Definitions of premises, and theorems with their proofs.

  `writtenLookup`, `writtenFace`, `borderOfLookup`: the two lookups of the written key, by number
  `LookupIsSeatedAtTheKey`: the thread's half at the lookup's place is the owned row at the written face, with one record a run
  `LookupValuesMeetTheRelation`: that record meets `KeyMidHyp`, and its bits read 0 at the planes that are not real
  `WitnessReadsAsTheProver`: in range the thread's witness reads as that record, and `same` holds of what reads alike
  `MaskEntriesReadAsTheCoins`: A NAMED DEBT: the mask entries at the homes in front of the lookup read as the owners' coins
  `lookupNewItemsHoldAtOneBorder`: behind a step the three new items hold
  **`lookupExchangeAtTheKey`**: `ExchangeS` at 4 and 10

By what. `ledgerInFrontOfTheLookupAtTheKey`, `lookupPlaysAtOwnersAtTheKey`, `ownedLookupBehindTheMove` and
`lookupStepLaysTheHearingAtTheKey` give what stands behind the step. `lookupIsLawfulAtTheKeyRecord` gives `Lawful`;
`lookupMasksAreTheOwnersCoinsAtTheKeyBook` gives `MasksAre`, the book's lending being the one that the move has made.
`lookupTruthBehindTheHearing` gives the three sentences, which are then read at the thread's witness.

Limits. The four premises are premises: this file does not show that the offline prover's value meets them. `readE` here is
`OnBytes.Slice.readE`; `Johnson.RunOne.KeyRows23.readE` is another constant of the same text. It is true also where the thread
stands at nothing.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.Key.LookupStepLaysTheHearingAtTheKey
import E2E.Lookup.Key.OneFaceUnderThreeNames
import E2E.Lookup.Key.LedgerIsTheKeyBook
import E2E.Lookup.Key.LookupDataMeetTheRelationAtTheWrittenKey
import Johnson.Desc.ProofFile.Honest.K3.Key.LookupTruthBehindTheHearing
import Johnson.Desc.ProofFile.Honest.K3.Key.LookupIsLawfulAtTheKeyRecord
import Johnson.Desc.ProofFile.Honest.K3.Key.LookupRecordReadsAsTheSentences
import Johnson.Desc.ProofFile.Honest.K3.Key.OwnedLookupBehindTheMove

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open OnBytes (E Slot Tensor mulE subE)
open OnBytes.Slice (readE)
open OnBytes.Params (WfLookup)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (HeardG toHeardG faceOfLkp hearV)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces Lookup lookupSeat lookupsOf lkpOf
  FormsObjects WorthPlanes WorthKeys keyVec bitVec mkOf matOf planeSum sumE closedAt)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)
open Johnson.RunOne.KeyRows1 (plan₁)
open ProofFile.Honest
open ProofFile.Honest.K3 (At Ask LFace fastJobs keyOwners proverSideOfLookupInChain ptsOf pointsAt LookJobs Stage)
open ProofFile.Honest.K3.Law (Stands courseAt LedgerIn)
open ProofFile.Honest.K3.Parts (dataP keysOfP plainOf)
open ProofFile.Honest.K3.Parts.Key (faceK rowK hidK KeyMidHyp numsK okK)
open ProofFile.Honest.K3.Law.Spec (planesOf)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace)
open AtPublicFiles.KeyThread

/-! ## 1 The two written lookups -/

/-- The structure of a written lookup, by its number. -/
def writtenLookup (number : Nat) : WfLookup := if number = 0 then lk0Full else lk1Full

/-- Its face. -/
abbrev writtenFace (number : Nat) : LFace := faceK 1 ⟨kRef, 3076096⟩ (writtenLookup number)

/-- The number of the sub-protocol of the first chain at which a lookup stands. -/
def borderOfLookup (number : Nat) : Nat := if number = 0 then 4 else 10

/-! ## 2 The premises -/

/-- **The lookup's half stands at the thread**: the owned row at the written face, reading one record a run. -/
structure LookupIsSeatedAtTheKey {W₀ Rc X' : Type}
    (halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (blocks : List (Block FirstState Claim)) (number : Nat) (lookup : At)
    (wit : Local W₀ Rc Xi Unit → Ask) (keyReader : Local W₀ Rc Xi Unit → Nat → Nat → E)
    (bitReader : Local W₀ Rc Xi Unit → Nat → E) : Prop where
  half : halves.find? (fun h => h.place == lookPlace number) =
    some (proverSideOfLookupInChain (keyOwners lookup.face) ⟨ptsOf, pointsAt⟩
      (fastJobs (writtenFace number) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup number))).asked wit lookup)
  place : lookup.place = lookPlace number
  face : lookup.face = writtenFace number
  base : lookup.base = roundsTo blocks (borderOfLookup number)
  constant : ∀ input heard, wit input heard =
    hidK (writtenLookup number) (keyReader input) (bitReader input)

/-- **The record meets the relation.** -/
structure LookupValuesMeetTheRelation {W₀ Rc : Type} (valid : Local W₀ Rc Xi Unit → Prop) (number : Nat)
    (keyReader : Local W₀ Rc Xi Unit → Nat → Nat → E) (bitReader : Local W₀ Rc Xi Unit → Nat → E) : Prop where
  relation : ∀ input, valid input → ∀ theta alpha,
    KeyMidHyp 1 ⟨kRef, 3076096⟩ (writtenLookup number) (keyReader input) (bitReader input) theta alpha
  idle : ∀ input, valid input → ∀ u, u < 2 ^ (writtenLookup number).d → ∀ j,
    (writtenFace number).planes ≤ j → j < 2 ^ (writtenLookup number).mu →
      readE (bitReader input (j + 2 ^ (writtenLookup number).mu * u)) = 0

/-- **The thread's witness reads as the record**, once the challenges in front of the lookup have been heard: key by key and bit
by bit, in range, under `readE`: just what the sentences spend. -/
structure WitnessReadsAsTheProver {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec : Type}
    (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (source : Source) (number inFront : Nat)
    (keyReader : Local W₀ Rc Xi Unit → Nat → Nat → E) (bitReader : Local W₀ Rc Xi Unit → Nat → E) : Prop where
  same : ∀ a b, readE a = readE b → filling.R.same a b
  keys : ∀ (k : Coins Bk) (input : Local W₀ Rc Xi Unit) heard, inFront ≤ heard.length →
    ∀ part, part < (writtenFace number).parts.length → ∀ i, i < 2 ^ (writtenFace number).parts.getD part 0 →
      readE (keyVec (plan₁ (one₀ source)).m (writtenLookup number)
        (matOf (plan₁ (one₀ source)) filling.R (filling.wit k input.w₀ input.rc heard [])) part i) =
      readE (keyReader input part i)
  bits : ∀ (k : Coins Bk) (input : Local W₀ Rc Xi Unit) heard, inFront ≤ heard.length →
    ∀ i, i < 2 ^ ((writtenFace number).mu + (writtenFace number).d) →
      readE (bitVec (one₀ source).ranges (one₀ source).codes number
        (fun i => filling.R.val (filling.R.of (filling.wit k input.w₀ input.rc heard []) 1) .main i) i) =
      readE (bitReader input i)

section
variable {W₀ Rc Cells M Smp Rec X' : Type} (data : KeyPub) (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)

/-- **A NAMED DEBT**: at the border in front of a lookup the mask entry at each home reads as the owners' coin under that slot. -/
def MaskEntriesReadAsTheCoins (number : Nat) : Prop :=
  ∀ k s m E, Thr (laid₁ source numbers later filling w₀ rc x halves tables) (borderOfLookup number) k s m E →
    ∀ more j, j < s.base.home.size →
      readE (mkOf (plan₁ (one₀ source)) filling.R
          (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) (s.base.home.getD j default)) =
        ProofFile.Honest.K3.Parts.maskOf (keyOwners (writtenFace number)) (writtenFace number)
          (keyBookHomes data number) (k.look 0) 0 j

end

/-! ## 3 The sentences under a weaker `same` -/

section
variable {same same' : E → E → Prop} (weaker : ∀ a b, same a b → same' a b)
  {face : VerifiableInference.Desc.K3.Face} {heard : HeardG} {ledger : Fork} {home : Array Slot}
  {maskEntry : Slot → E}
include weaker

theorem formsObjectsUnderAWeakerSame (forms : FormsObjects same face heard ledger home maskEntry) :
    FormsObjects same' face heard ledger home maskEntry := by
  obtain ⟨claims, closed, closes, zero⟩ := forms
  exact ⟨claims, closed, closes, fun a member =>
    ⟨(zero a member).1, (zero a member).2.1, weaker _ _ (zero a member).2.2⟩⟩

theorem worthPlanesUnderAWeakerSame {bit : Nat → E}
    (worth : WorthPlanes same face heard ledger home maskEntry bit) :
    WorthPlanes same' face heard ledger home maskEntry bit := by
  obtain ⟨claims, closed, closes, three, zero⟩ := worth
  exact ⟨claims, closed, closes, three, fun c member =>
    ⟨(zero c member).1, (zero c member).2.1, weaker _ _ (zero c member).2.2⟩⟩

theorem worthKeysUnderAWeakerSame {key : Nat → Nat → E}
    (worth : WorthKeys same face heard ledger home maskEntry key) :
    WorthKeys same' face heard ledger home maskEntry key := by
  obtain ⟨asMany, claims, closed, closes, zero⟩ := worth
  exact ⟨asMany, claims, closed, closes, fun y member =>
    ⟨(zero y member).1, (zero y member).2.1, weaker _ _ (zero y member).2.2⟩⟩

end

/-! ## 3b The sentences at other readers, where these read alike in range -/

section
open OnBytes.Slice (readE_zero readE_add readE_mul readE_sub)
variable {face : VerifiableInference.Desc.K3.Face} {heard : HeardG} {ledger : Fork} {home : Array Slot}
  {maskEntry : Slot → E}

/-- Two bit readers that read alike in range have sums that read alike. -/
theorem planeSumsReadAlike (pairs : List (E × E)) {bit bit' : Nat → E}
    (alike : ∀ i, i < 2 ^ (face.mu + face.d) → readE (bit' i) = readE (bit i)) :
    readE (planeSum face pairs bit') = readE (planeSum face pairs bit) := by
  unfold planeSum
  rw [VerifiableInference.Desc.Key.sumE_read readE readE_zero readE_add,
    VerifiableInference.Desc.Key.sumE_read readE readE_zero readE_add]
  refine Finset.sum_congr rfl fun i below => ?_
  rw [readE_mul, readE_mul, alike i (Finset.mem_range.1 below)]

/-- **`WorthPlanes` at another reader of the bits**, where the two read alike in range. -/
theorem worthPlanesAtBitsThatReadAlike {bit bit' : Nat → E}
    (worth : WorthPlanes ProofFile.Honest.K3.Key.ReadAlike face heard ledger home maskEntry bit)
    (alike : ∀ i, i < 2 ^ (face.mu + face.d) → readE (bit' i) = readE (bit i)) :
    WorthPlanes ProofFile.Honest.K3.Key.ReadAlike face heard ledger home maskEntry bit' := by
  obtain ⟨claims, closed, closes, three, zero⟩ := worth
  refine ⟨claims, closed, closes, three, fun c member =>
    ⟨(zero c member).1, (zero c member).2.1, ?_⟩⟩
  have before : readE _ = readE _ := (zero c member).2.2
  show readE _ = readE _
  rw [readE_add, readE_mul] at before ⊢
  rw [planeSumsReadAlike c.pairs alike]
  exact before

/-- **`WorthKeys` at another reader of the keys**, where the two read alike in range. -/
theorem worthKeysAtKeysThatReadAlike {key key' : Nat → Nat → E}
    (worth : WorthKeys ProofFile.Honest.K3.Key.ReadAlike face heard ledger home maskEntry key)
    (alike : ∀ part, part < face.parts.length → ∀ i, i < 2 ^ face.parts.getD part 0 →
      readE (key' part i) = readE (key part i)) :
    WorthKeys ProofFile.Honest.K3.Key.ReadAlike face heard ledger home maskEntry key' := by
  obtain ⟨asMany, claims, closed, closes, zero⟩ := worth
  refine ⟨asMany, claims, closed, closes, fun y member =>
    ⟨(zero y member).1, (zero y member).2.1, ?_⟩⟩
  have before : readE _ = readE _ := (zero y member).2.2
  have part : y.2 < face.parts.length := by
    have found : heard.keys[y.2]? = some y.1 := List.mem_zipIdx_iff_getElem?.1 member
    have below := (List.getElem?_eq_some_iff.1 found).1
    rw [asMany] at below
    exact below
  show readE _ = readE _
  rw [before, VerifiableInference.Desc.Key.sumE_read readE readE_zero readE_add,
    VerifiableInference.Desc.Key.sumE_read readE readE_zero readE_add]
  refine Finset.sum_congr rfl fun i below => ?_
  rw [readE_mul, readE_mul, readE_sub, readE_sub, alike y.2 part i (Finset.mem_range.1 below)]

end

/-! ## 4 The two ties at a seated face -/

/-- The planes at a seated lookup's face. -/
theorem planesAtASeatedFace {number : Nat} {lookup : At} (face : lookup.face = writtenFace number)
    (planes : 2 ≤ lookup.face.planes) (keyReader : Nat → Nat → E) (bitReader : Nat → E)
    (idle : ∀ u, u < 2 ^ (writtenLookup number).d → ∀ j, (writtenFace number).planes ≤ j →
      j < 2 ^ (writtenLookup number).mu → readE (bitReader (j + 2 ^ (writtenLookup number).mu * u)) = 0)
    (points : ProofFile.Honest.K3.Pts) (pairs : List (E × E)) :
    planesOf (ProofFile.Honest.K3.dataAt (numsK 1 ⟨kRef, 3076096⟩ (writtenLookup number))
        (hidK (writtenLookup number) keyReader bitReader) points) pairs =
      readE (planeSum lookup.face pairs bitReader) := by
  rw [face] at planes ⊢
  exact ProofFile.Honest.K3.Key.planesOfTheKeyRecordAreThePlaneSum 1 ⟨kRef, 3076096⟩ (writtenLookup number) keyReader
    bitReader points pairs planes idle

/-- The keys at a seated lookup's face. -/
theorem keysAtASeatedFace {number : Nat} {lookup : At} (face : lookup.face = writtenFace number)
    (ok : lookup.face.ok = true) (keyReader : Nat → Nat → E) (bitReader : Nat → E)
    (points : ProofFile.Honest.K3.Pts) (sizes : ∀ part levels, (points.keyPt part levels).size = levels)
    (alpha : E) (part : Nat) (below : part < lookup.face.parts.length) :
    readE alpha - keysOfP (dataP (numsK 1 ⟨kRef, 3076096⟩ (writtenLookup number)) lookup.face.parts
        lookup.face.orders (hidK (writtenLookup number) keyReader bitReader) points) part
        (points.keyPt part (lookup.face.parts.getD part 0)) =
      readE (sumE (2 ^ lookup.face.parts.getD part 0) fun k =>
        mulE ((Tensor.eq (points.keyPt part (lookup.face.parts.getD part 0)).toList.reverse).entry k)
          (subE alpha (keyReader part k))) := by
  have positive : 1 ≤ lookup.face.parts.getD part 0 := by
    refine (ProofFile.Honest.K3.Parts.facts_of_ok ok).1 _ ?_
    rw [List.getD_eq_getElem _ _ below]
    exact List.getElem_mem _
  rw [face] at positive ⊢
  exact ProofFile.Honest.K3.Key.keysOfTheKeyRecordAreTheKeySum 1 ⟨kRef, 3076096⟩ (writtenLookup number) keyReader
    bitReader points part positive _ (sizes _ _) alpha

/-! ## 5 Behind the step -/

section
variable {W₀ Rc Cells M Smp Rec X' : Type} {data : KeyPub} {source : Source} {numbers : H2U.PlaceNums}
  {later : LaterPlaces} {filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec} {w₀ : W₀} {rc : Rc} {x : Xi}
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles} {first second : Lookup}

/-- **Behind the step of the thread at one lookup the three new items hold.** -/
theorem lookupNewItemsHoldAtOneBorder (written : fullPub = some data)
    (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (two : lookupsOf (one₀ source) = [first, second]) {number b : Nat} (atLookup : b ∈ [4, 10])
    (border : borderOfLookup number = b) (numberAt : lookupNumberAtBorder b = number)
    (lookupIs : lookupAtBorder first second b = OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ (writtenLookup number))
    (record : lkpOf (plan₁ (one₀ source)) (one₀ source).ranges number =
      some (OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ (writtenLookup number)))
    (planned : (plan₁ (one₀ source)).lookups[number]? = some (writtenLookup number))
    (accepted : okK 1 ⟨kRef, 3076096⟩ (writtenLookup number) = true)
    (bookFace : data.faces[number]? = some (writtenFace number))
    (lookup : At) (wit : Local W₀ Rc Xi Unit → Ask) (keyReader : Local W₀ Rc Xi Unit → Nat → Nat → E)
    (bitReader : Local W₀ Rc Xi Unit → Nat → E)
    (seated : LookupIsSeatedAtTheKey halves (laid₁ source numbers later filling w₀ rc x halves tables).bs number
      lookup wit keyReader bitReader)
    (values : LookupValuesMeetTheRelation (laid₁ source numbers later filling w₀ rc x halves tables).valid number
      keyReader bitReader)
    (witness : WitnessReadsAsTheProver filling source number lookup.base keyReader bitReader)
    (masks : MaskEntriesReadAsTheCoins data source numbers later filling w₀ rc x halves tables number)
    (said : Nat → Coins (keyBook data) → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ blk, (laid₁ source numbers later filling w₀ rc x halves tables).bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (laid₁ source numbers later filling w₀ rc x halves tables) said b k s m E →
      drawsFit blk.rounds ds = true →
      (laid₁ source numbers later filling w₀ rc x halves tables).Stepped blk k s m E ds y cols s' →
      (laid₁ source numbers later filling w₀ rc x halves tables).Items (lookupNewItems number) k s' y.2
        (E.add y.1) := by
  intro blk found k s m E ds y cols s' threadSaid drawn stepped
  have thread := threadSaid.1
  have faceIs : lookup.face = faceOfLkp (lookupAtBorder first second b) := by
    rw [seated.face, lookupIs]
    rfl
  obtain ⟨front, forkIs, freshLedger, homeSize⟩ := ledgerInFrontOfTheLookupAtTheKey source numbers later filling
    w₀ rc x (halves := halves) (tables := tables) two b atLookup k s m E thread
  rw [← faceIs] at freshLedger homeSize
  obtain ⟨entries, seven⟩ := lookupPlaysAtOwnersAtTheKey source numbers later filling w₀ rc x
    (halves := halves) (tables := tables) sourced two (keyOwners lookup.face) lookup
    (fastJobs (writtenFace number) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup number))).asked wit b atLookup
    (by rw [numberAt]; exact seated.half) (by rw [numberAt]; exact seated.place) faceIs
    (by rw [seated.base, border]; rfl)
  obtain ⟨noColumns, coins, lent, heard, behind, hearing, behindYes⟩ :=
    ProofFile.Honest.K3.Key.ownedLookupBehindTheMove seven found thread drawn stepped.1 0 front freshLedger
  have hearing' : hearV (faceOfLkp (lookupAtBorder first second b)) front (roundsOf y.1) =
      some (heard, behind) := by
    rw [← faceIs]
    exact hearing
  have behindState : s' = lookupSeat.put s (toHeardG heard) behind :=
    lookupStepLaysTheHearingAtTheKey source numbers later filling w₀ rc x sourced two b atLookup blk found k s m
      E ds y cols s' drawn stepped front heard behind forkIs hearing'
  subst behindState
  have moved := stepped.1
  unfold Thread.Moved at moved
  obtain ⟨⟨steps, -, played⟩, -⟩ := moved
  have sameInput : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ played).1
  have sameHeard : y.2.st.heard = m.st.heard ++ ds := play_heard _ _ _ _ _ played
  have stands : Stands lookup entries m ds :=
    ⟨seven.ok, (Thread.heard_length _ thread.2.1).trans seven.base.symm, seven.entries, by
      rw [← seven.rounds blk found]
      exact drawn⟩
  have valid : (laid₁ source numbers later filling w₀ rc x halves tables).valid m.st.input :=
    thread.2.2.2.2.2.2
  have lawful := fun stageCoins => ProofFile.Honest.K3.Key.lookupIsLawfulAtTheKeyRecord 1 ⟨kRef, 3076096⟩
    (writtenLookup number) (keyReader m.st.input) (bitReader m.st.input) lookup seated.face wit entries m ds
    (fun heard => seated.constant m.st.input heard) stands accepted
    (fun theta alpha => values.relation m.st.input valid theta alpha) stageCoins
  have twoPlanes : 2 ≤ lookup.face.planes := ProofFile.Honest.K3.two_le_planes_of_ok _ seven.ok
  have standsAtBook : LookupStandsAtTheKeyBook data number lookup :=
    { place := seated.place
      face := by rw [seated.face]; exact bookFace
      twoFaces := (lookupsStandAtTheWrittenSizes data written).1
      planes := twoPlanes }
  obtain ⟨lentAgain, lends, spentList⟩ := ProofFile.Honest.K3.Key.bookLendsTheOwnedSeatInTheFirstChain
    (V₁ := Local W₀ Rc Xi Unit) (X₁ := X') (keyOwners lookup.face) ⟨ptsOf, pointsAt⟩
    (fastJobs (writtenFace number) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup number))).asked wit lookup
    (keyBook data) (keyBookFitsTheOwnedRow data written number lookup standsAtBook) k
  have sameCoins : coins = lentAgain := by
    rw [seven.place blk found] at lent
    exact Except.ok.inj (lent.symm.trans lends)
  subst sameCoins
  have masksAre := fun stageCoins coinsAre => lookupMasksAreTheOwnersCoinsAtTheKeyBook
    (courseAt lookup (fastJobs (writtenFace number) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup number))).asked 0 wit
      m ds stageCoins) data written number standsAtBook k _
    ((ProofFile.Honest.K3.Law.rowSpent_unlift _ _ _ _).trans
      ((ProofFile.Honest.K3.Parts.spent_owned _ _ _ _ _ coins).trans spentList)) coinsAre
  refine (lookupNewItemsUnfoldedAtTheKey source numbers later filling w₀ rc x number k
    (lookupSeat.put s (toHeardG heard) behind) y.2 (E.add y.1)).2 fun more => ?_
  rw [sameHeard, sameInput, List.append_assoc]
  have long : lookup.base ≤ (m.st.heard ++ (ds ++ more)).length := by
    rw [List.length_append, stands.base]
    exact Nat.le_add_right _ _
  have atBorder : Thr (laid₁ source numbers later filling w₀ rc x halves tables) (borderOfLookup number) k s m E := by
    rw [border]
    exact thread
  obtain ⟨forms, planesWorth, keysWorth⟩ := ProofFile.Honest.K3.Key.lookupTruthBehindTheHearing lookup _ wit m ds
    (plainOf (keyOwners lookup.face) ⟨ptsOf, pointsAt⟩
      (fastJobs (writtenFace number) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup number))).asked wit lookup coins)
    freshLedger hearing behindYes _ _ lawful
    (ProofFile.Honest.K3.Parts.maskOf (keyOwners lookup.face) lookup.face (keyBookHomes data number) (k.look 0) 0)
    masksAre s.base.home
    (mkOf (plan₁ (one₀ source)) filling.R
      (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ (ds ++ more)) []))
    homeSize
    (fun j below => by
      have entry := masks k s m E atBorder (ds ++ more) j below
      rw [← seated.face] at entry
      exact entry)
    (bitReader m.st.input)
    (planesAtASeatedFace seated.face twoPlanes (keyReader m.st.input) (bitReader m.st.input)
      (values.idle m.st.input valid) _)
    (keyReader m.st.input)
    (keysAtASeatedFace seated.face seven.ok (keyReader m.st.input) (bitReader m.st.input) _
      (ProofFile.Honest.K3.Law.Spec.size_keyPt _ _ _) heard.alpha)
  rw [seated.face] at forms planesWorth keysWorth
  have planesAtWitness := worthPlanesAtBitsThatReadAlike planesWorth (witness.bits k m.st.input _ long)
  have keysAtWitness := worthKeysAtKeysThatReadAlike keysWorth (witness.keys k m.st.input _ long)
  refine ⟨?_, ?_, ?_⟩
  · show VerifiableInference.Desc.Key.formsAt (plan₁ (one₀ source)) filling.R Johnson.RunOne.KeyRows1.k3At₁
      (one₀ source).ranges number "objects" _ (Env.strs filling.item (srcAt 0 6 11) (E.add y.1)) _
    exact ⟨rfl, _, toHeardG heard, behind, record, rfl, rfl,
      formsObjectsUnderAWeakerSame witness.same forms⟩
  · show VerifiableInference.Desc.Key.worthAt (plan₁ (one₀ source)) filling.R Johnson.RunOne.KeyRows1.k3At₁
      (one₀ source).ranges (one₀ source).codes number "planes" _ (Env.strs filling.item (srcAt 0 6 11) (E.add y.1)) _
    exact ⟨_, _, toHeardG heard, behind, record, planned, rfl, rfl,
      Or.inl ⟨rfl, worthPlanesUnderAWeakerSame witness.same planesAtWitness⟩⟩
  · show VerifiableInference.Desc.Key.worthAt (plan₁ (one₀ source)) filling.R Johnson.RunOne.KeyRows1.k3At₁
      (one₀ source).ranges (one₀ source).codes number "keys" _ (Env.strs filling.item (srcAt 0 6 11) (E.add y.1)) _
    exact ⟨_, _, toHeardG heard, behind, record, planned, rfl, rfl,
      Or.inr ⟨rfl, worthKeysUnderAWeakerSame witness.same keysAtWitness⟩⟩

end

/-! ## 6 The exchange, whole -/

/-- **`ExchangeS` AT THE TWO LOOKUPS OF THE KEY FILE's FIRST THREAD, WHOLE.** -/
theorem lookupExchangeAtTheKey {W₀ Rc Cells M Smp Rec X' : Type} (data : KeyPub) (written : fullPub = some data)
    {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}
    {filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec} {w₀ : W₀} {rc : Rc} {x : Xi}
    {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
    {tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table}
    {files : VerifierAndGoals.PublicFiles} (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁)
    (said : Nat → Coins (keyBook data) → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (lookup : Nat → At) (wit : Nat → Local W₀ Rc Xi Unit → Ask)
    (keyReader : Nat → Local W₀ Rc Xi Unit → Nat → Nat → E) (bitReader : Nat → Local W₀ Rc Xi Unit → Nat → E)
    (seated : ∀ number, number < 2 → LookupIsSeatedAtTheKey halves
      (laid₁ source numbers later filling w₀ rc x halves tables).bs number (lookup number) (wit number)
      (keyReader number) (bitReader number))
    (values : ∀ number, number < 2 → LookupValuesMeetTheRelation
      (laid₁ source numbers later filling w₀ rc x halves tables).valid number (keyReader number) (bitReader number))
    (witness : ∀ number, number < 2 → WitnessReadsAsTheProver filling source number (lookup number).base
      (keyReader number) (bitReader number))
    (masks : ∀ number, number < 2 →
      MaskEntriesReadAsTheCoins data source numbers later filling w₀ rc x halves tables number) :
    ∀ b ∈ [4, 10], ExchangeS (laid₁ source numbers later filling w₀ rc x halves tables) said b := by
  have two := sourceLookupsAreTheWrittenLookups sourced scope
  obtain ⟨recordFirst, recordSecond⟩ := tableRecordIsTheWrittenLookup sourced scope
  obtain ⟨_, _, read, made, fromMade, -, -⟩ := sourced.source
  obtain ⟨-, ranges, -⟩ := Johnson.RunOne.Law.KeyInScope.five_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO read) made fromMade sourced.named.plan
  have lookupsAre : (plan₁ (one₀ source)).lookups = [lk0Full, lk1Full] := by
    show (one₀ source).ranges.lookups = _
    rw [ranges]
    exact AtPublicFiles.Key.item_written.1
  have faces := keyBookFacesAreTheWrittenFaces written
  have planes := planesAtTheWrittenLookups
  intro b atLookup
  refine lookupExchangeOfTheNewItemsAtTheKey source numbers later filling w₀ rc x sourced scope reads said b
    atLookup ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · exact lookupNewItemsHoldAtOneBorder (number := 0) written sourced two (by decide) rfl rfl rfl recordFirst
      (by rw [lookupsAre]; rfl) planes.2.2.2.2.1 (by rw [faces]; rfl) (lookup 0) (wit 0) (keyReader 0)
      (bitReader 0) (seated 0 (by decide)) (values 0 (by decide)) (witness 0 (by decide))
      (masks 0 (by decide)) said
  · exact lookupNewItemsHoldAtOneBorder (number := 1) written sourced two (by decide) rfl rfl rfl recordSecond
      (by rw [lookupsAre]; rfl) planes.2.2.2.2.2 (by rw [faces]; rfl) (lookup 1) (wit 1) (keyReader 1)
      (bitReader 1) (seated 1 (by decide)) (values 1 (by decide)) (witness 1 (by decide))
      (masks 1 (by decide)) said

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.lookupNewItemsHoldAtOneBorder
#print axioms AtPublicFiles.Lookup.Key.lookupExchangeAtTheKey
