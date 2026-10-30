-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: the bits that a lookup's record reads must be what the multiplicities' message holds. As at the masks the work is in
  two: what the sender lays in its main rows is the prover's own reckoning of the planes (`keyMessageLaysThePlanesInItsMainRows`,
  proved here); that the thread's witness reads those rows is the thread's (the field `main` of `WitnessReadsTheSendersRows`).

AtFullSide/Honest/K3/Key/BitsReadAsTheSendersMainRows.lean. Theorems with proofs.

  `mainEntryOfRowsWithoutACoin`, `mainEntryBehindTheRow`   a main entry of a message over the base field that has no coin there
  `writtenOwnMessageShape`, `writtenBlocksFit`   closed facts at the written sizes
  `keyMessageLaysThePlanesAtEveryFront`, `keyMessageLaysThePlanesInItsMainRows`   **the sender's side**, at every number; at every
                                        front and at the front that the witness's debt names
  `foldOfBlocksReadsAlike`              `bitVec` reads alike what reads alike
  `bitsReadAsTheSendersMainRows`       **the join**: the premise `bits`, pointwise

Limits. The written sizes alone. `WitnessReadsTheSendersRows` is a premise. Nothing on any property of a protocol.
-/
import E2E.KeyLookups
import E2E.KeyPlanesAtFull
import E2E.Lookup.Key.LookupValuesAtTheNamedParts
import AtFullSide.Honest.K3.Key.MaskEntriesReadAsTheCoinsAtTheSendersRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Lookup.Key
open OnBytes
open OnBytes.Slice (GF GE readE ofE toE)
open ProofFile.Honest
open ProofFile.Honest.K1 (rowsR stepsOf dueR Steps)
open Johnson.Prover.Send (shapeAt Rows)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyThread
open AtPublicFiles.Key (planesVal planesData msgData)
open AtPublicFiles.KeyValues (multiplicitiesSending multiplicitiesGroups matrixEntryOf oneOf)
open AtPublicFiles.KeyFile (In1)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi bitVec blockPlace)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)

/-! ## 1 A main entry without a coin -/

/-- **Inside the rows a main entry over the base field, at a message that lays no coin there, is what the data has.** -/
theorem mainEntryOfRowsWithoutACoin (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)) (k r j : Nat)
    (noWord : (stepsOf P.codes (shapeAt P k) (ride k)).word = 0)
    (noPad : (stepsOf P.codes (shapeAt P k) (ride k)).pad = 0)
    (overBase : ((shapeAt P k).mainDeg == 3) = false) (rowIn : r < (shapeAt P k).mainRows)
    (placeIn : j < (P.codes.base.getD (shapeAt P k).code default).ell) :
    (rowsR P ride data c k).mainF r j =
      match data k r j with
      | some (.inl x) => x
      | _ => 0 := by
  have hInside : ((shapeAt P k).mainDeg == 3 || decide ((shapeAt P k).mainRows ≤ r) ||
      decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j)) = false := by
    rw [overBase, decide_eq_false (Nat.not_le.2 rowIn), decide_eq_false (Nat.not_le.2 placeIn)]
    rfl
  unfold rowsR
  dsimp only
  simp only [hInside, noWord, noPad, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false,
    Option.map_none]
  cases data k r j with
  | none => rfl
  | some value => cases value <;> rfl

/-- **Behind the row's end a main entry is 0.** -/
theorem mainEntryBehindTheRow (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)) (k r j : Nat)
    (placeOut : (P.codes.base.getD (shapeAt P k).code default).ell ≤ j) :
    (rowsR P ride data c k).mainF r j = 0 := by
  have hOut : ((shapeAt P k).mainDeg == 3 || decide ((shapeAt P k).mainRows ≤ r) ||
      decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j)) = true :=
    Bool.or_eq_true_iff.2 (Or.inr (decide_eq_true placeOut))
  unfold rowsR
  dsimp only
  rw [if_pos hOut]

/-! ## 2 Closed facts -/

/-- **The own message at the written sizes**: two main rows over the base field, mask rows, an answer. By Lean's kernel. -/
theorem writtenOwnMessageShape :
    keyFull.ranges.x.message.shape.mainRows = 2 ∧ keyFull.ranges.x.message.shape.maskRows ≠ 0 ∧
      keyFull.ranges.x.message.shape.answers ≠ 0 ∧ (keyFull.ranges.x.message.shape.mainDeg == 3) = false := by
  decide +kernel

/-- Every block of the written layout fits. -/
theorem writtenBlocksFit : ∀ b ∈ AtPublicFiles.Key.sixBlocks,
    AtPublicFiles.Key.fitB [lk0Full, lk1Full] 1 18 b = true := by
  have h := AtPublicFiles.Key.good_full
  unfold AtPublicFiles.Key.Good at h
  exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1

theorem readOfTheSendersWord (z : GE) : readE (E.ofTriple (ofE z)) = z := by
  show toE (E.ofTriple (ofE z)).triple = z
  rw [E.triple_ofTriple, OnBytes.Slice.toE_ofE]

/-- Behind the row's end the planes hold nothing. -/
theorem planesEndWithTheRow (entry : Nat → Nat → GF) (row place : Nat) (out : 2 ^ 18 ≤ place) :
    planesData entry kRef [lk0Full, lk1Full] (2 ^ 18) row place = none := by
  unfold planesData
  rw [AtPublicFiles.Key.layout_full]
  have hNone : AtPublicFiles.Key.sixBlocks.find? (fun b => b.row == row && decide (b.firstPlace ≤ place) &&
                decide (place < b.firstPlace + 2 ^ b.bits)) = none := by
    rw [List.find?_eq_none]
    intro b hb
    have hFit := writtenBlocksFit b hb
    unfold AtPublicFiles.Key.fitB at hFit
    simp only [decide_eq_true_eq, Bool.and_eq_true] at hFit
    obtain ⟨⟨⟨-, -⟩, hEnd⟩, -⟩ := hFit
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro _
    omega
  rw [hNone]
  rfl

/-! ## 3 The sender's side -/

section
variable {W₀ Rc X : Type} (f : W₀ → Weights) {source : Source}

/-- **WHAT THE MULTIPLICITIES' SENDER LAYS IN THE MAIN ROWS OF ITS FIRST MESSAGE IS THE PLANES**, at every number of the table, at all
coins and at every front that its part is handed: its data reads no front. -/
theorem keyMessageLaysThePlanesAtEveryFront (full : OneFull (one₀ source)) (input : In1 W₀ Rc)
    (front : Front X) (coins : Cs (dueR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg))
    (i : Nat) :
    readE (E.ofTriple (ofE ((rowsR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg
        ((multiplicitiesSending (Rc := Rc) (X := X) f source).data input front)
        coins 0).word (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0) .main i))) =
      readE (planesVal (matrixEntryOf f input) kRef [lk0Full, lk1Full] (2 ^ 18) 1 i) := by
  obtain ⟨items, rows, ell, -, matrix⟩ := AtPublicFiles.Key.item_written
  obtain ⟨twoRows, maskRows, answers, overBase⟩ := writtenOwnMessageShape
  have hSent : (multiplicitiesSending (Rc := Rc) (X := X) f source).P.sent = Wf.messageOf keyFull.ranges.x := by
    rw [← full.ranges]
    exact sendingPar_sent _ _ _ _ _
  have hCodes : (multiplicitiesSending (Rc := Rc) (X := X) f source).P.codes = keyFull.codes := full.codes
  have hShape : shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0 = keyFull.ranges.x.message.shape := by
    obtain ⟨positive, firstIs⟩ := AtPublicFiles.KeyLookup.messageOf_head keyFull.ranges.x
    unfold shapeAt
    rw [hSent]
    simp [Array.getD, positive, firstIs]
  have hData : ∀ r j, (multiplicitiesSending (Rc := Rc) (X := X) f source).data input front 0 r j =
      (planesData (matrixEntryOf f input) kRef [lk0Full, lk1Full] (2 ^ 18) r j).map Sum.inl := by
    intro r j
    show msgData (matrixEntryOf f input) (Wf.matrixOf (oneOf source).lin).kCol (oneOf source).ranges.lookups
      ((oneOf source).codes.base.getD (oneOf source).ranges.message.shape.code default).ell 0 r j = _
    have hLin : (oneOf source).lin = keyFull.once.shape := full.lin
    have hRanges : (oneOf source).ranges = keyFull.ranges.x := full.ranges
    have hCodes' : (oneOf source).codes = keyFull.codes := full.codes
    rw [hLin, hRanges, hCodes', matrix, items, ell]
    rfl
  have hRowBits : VerifiableInference.Desc.K1.clog keyFull.ranges.x.message.shape.mainRows = 1 := by
    rw [twoRows]
    rfl
  have hRow : i % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [readOfTheSendersWord, AtPublicFiles.Key.planesVal_read]
  show (if i % 2 ^ VerifiableInference.Desc.K1.clog
        (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0).mainRows <
        (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0).mainRows then
      Rows.main _ ((shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0).mainDeg == 3)
        (i % 2 ^ VerifiableInference.Desc.K1.clog
          (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0).mainRows)
        (i / 2 ^ VerifiableInference.Desc.K1.clog
          (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0).mainRows) else 0) = _
  have hEll : ((multiplicitiesSending (Rc := Rc) (X := X) f source).P.codes.base.getD
      (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0).code default).ell = 2 ^ 18 := by
    rw [hCodes, hShape]
    exact ell
  rw [hShape, hRowBits, twoRows, overBase, if_pos (by simpa using hRow)]
  show algebraMap GF GE (Rows.mainF _ (i % 2 ^ 1) (i / 2 ^ 1)) = _
  by_cases inside : i / 2 ^ 1 < 2 ^ 18
  · rw [mainEntryOfRowsWithoutACoin _ _ _ _ 0 _ _ ?_ ?_ ?_ ?_ ?_]
    · rw [hData]
      cases planesData (matrixEntryOf f input) kRef [lk0Full, lk1Full] (2 ^ 18) (i % 2 ^ 1) (i / 2 ^ 1) <;> rfl
    · rw [hShape]
      simp [stepsOf, answers]
    · rw [hShape]
      simp [stepsOf, maskRows]
    · rw [hShape]
      exact overBase
    · rw [hShape, twoRows]
      simpa using hRow
    · rw [hEll]
      exact inside
  · rw [mainEntryBehindTheRow _ _ _ _ 0 _ _ (by rw [hEll]; omega),
      planesEndWithTheRow _ _ _ (by omega)]
    simp

/-- The same at the front of the form that `WitnessReadsTheSendersRows` names. -/
theorem keyMessageLaysThePlanesInItsMainRows (full : OneFull (one₀ source)) (input : In1 W₀ Rc)
    (heard : List Fmt.Drawn) (own₀ : X) (coins : Cs (dueR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg))
    (i : Nat) :
    readE (E.ofTriple (ofE ((rowsR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg
        ((multiplicitiesSending (Rc := Rc) (X := X) f source).data input { heard := heard, own := own₀, seen := .bare [] })
        coins 0).word (shapeAt (multiplicitiesSending (Rc := Rc) (X := X) f source).P 0) .main i))) =
      readE (planesVal (matrixEntryOf f input) kRef [lk0Full, lk1Full] (2 ^ 18) 1 i) :=
  keyMessageLaysThePlanesAtEveryFront f full input _ coins i

end

/-! ## 4 `bitVec` reads alike what reads alike -/

theorem foldOfBlocksReadsAlike (keep : Wf.Block → Prop) [DecidablePred keep] (place : Wf.Block → Nat)
    (first second : Nat → E) : ∀ (blocks : List Wf.Block) (a b : E), readE a = readE b →
    (∀ block ∈ blocks, keep block → readE (first (place block)) = readE (second (place block))) →
    readE (blocks.foldl (fun s block => if keep block then addE s (first (place block)) else s) a) =
      readE (blocks.foldl (fun s block => if keep block then addE s (second (place block)) else s) b)
  | [], _, _, same, _ => same
  | block :: blocks, a, b, same, alike => by
    simp only [List.foldl_cons]
    refine foldOfBlocksReadsAlike keep place first second blocks _ _ ?_
      fun c hc => alike c (List.mem_cons_of_mem _ hc)
    split
    · rename_i kept
      rw [OnBytes.Slice.readE_add, OnBytes.Slice.readE_add, same,
        alike block List.mem_cons_self kept]
    · exact same

/-! ## 5 The join -/

section
variable {W₀ Rc Cells M Smp Rec X X' : Type} (data : KeyPub) (f : W₀ → Weights) (source : Source)
  (numbers : H2U.PlaceNums) (later : LaterPlaces)
  (filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table) (own₀ : X)

/-- **THE BITS THAT THE THREAD's WITNESS HOLDS READ AS THE PROVER's BITS**, pointwise, inside the lookup's table: from the sender's side,
proved above, and the thread's debt. Conditional: the description is sourced from the files in scope. -/
theorem bitsReadAsTheSendersMainRows {files : VerifierAndGoals.PublicFiles} (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number inFront : Nat) (below : number < 2)
    (ownCoins : Coins (keyBook data) → Cs (dueR (multiplicitiesSending (Rc := Rc) (X := X) f source).P rideMsg))
    (keyCoins : Coins (keyBook data) →
      Cs (dueR (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) source).P fun _ => none))
    (reads : WitnessReadsTheSendersRows data f source numbers later filling w₀ rc x halves tables own₀ number
      inFront ownCoins keyCoins) :
    ∀ (k : Coins (keyBook data)) (input : Local W₀ Rc Xi Unit) (heard : List Fmt.Drawn),
      inFront ≤ heard.length → ∀ i, i < 2 ^ ((writtenStructure number).mu + (writtenStructure number).d) →
      readE (bitVec (one₀ source).ranges (one₀ source).codes number
          (fun i => filling.R.val (filling.R.of (filling.wit k input.w₀ input.rc heard []) 1) .main i) i) =
        readE (bitReaderAt f number input i) := by
  intro k input heard enough i inside
  have full := oneTimeIsTheWrittenOneInScope sourced scope
  obtain ⟨items, rows, ell, -, -⟩ := AtPublicFiles.Key.item_written
  have hLayout : Wf.layout keyFull.ranges.x.lookups
      (keyFull.codes.base.getD keyFull.ranges.x.message.shape.code default).ell = AtPublicFiles.Key.sixBlocks := by
    rw [items, ell]
    exact AtPublicFiles.Key.layout_full
  have hLog : (keyFull.codes.base.getD keyFull.ranges.x.message.shape.code default).logEll = 18 := by
    unfold OnBytes.Code.logEll
    rw [ell]
    decide
  have hRowBits : ceilLog2 keyFull.ranges.x.message.shape.mainRows = 1 := by
    rw [rows]
    decide
  have hWritten : [lk0Full, lk1Full].getD number default = writtenStructure number := by
    have isLookup : number = 0 ∨ number = 1 := by omega
    rcases isLookup with rfl | rfl <;> rfl
  have hStructure : keyFull.ranges.x.lookups.getD number default = writtenStructure number := by
    rw [items]
    exact hWritten
  unfold bitReaderAt
  rw [full.ranges, full.codes]
  refine foldOfBlocksReadsAlike
    (fun b => b.first ≤ i % 2 ^ (keyFull.ranges.x.lookups.getD number default).mu ∧
      i % 2 ^ (keyFull.ranges.x.lookups.getD number default).mu < b.first + 2 ^ b.logPlanes)
    (fun b => blockPlace (ceilLog2 keyFull.ranges.x.message.shape.mainRows)
      (keyFull.codes.base.getD keyFull.ranges.x.message.shape.code default).logEll b
      (i % 2 ^ (keyFull.ranges.x.lookups.getD number default).mu - b.first +
        2 ^ b.logPlanes * (i / 2 ^ (keyFull.ranges.x.lookups.getD number default).mu)))
    _ _ _ _ _ rfl ?_
  intro b member kept
  rw [hLayout] at member
  obtain ⟨inBlocks, isLookup⟩ := List.mem_filter.1 member
  have hLookup : b.lookup = number := by simpa using isLookup
  rw [hRowBits, hLog]
  rw [hStructure] at kept ⊢
  have hTable : i / 2 ^ (writtenStructure number).mu <
      2 ^ ([lk0Full, lk1Full].getD b.lookup default).d := by
    have hDepth : ([lk0Full, lk1Full].getD b.lookup default).d = (writtenStructure number).d := by
      rw [hLookup, hWritten]
    rw [hDepth]
    rw [Nat.pow_add] at inside
    exact Nat.div_lt_of_lt_mul inside
  have hFront : i % 2 ^ (writtenStructure number).mu - b.first < 2 ^ b.logPlanes := by
    have := kept.1
    have := kept.2
    omega
  have hThread := reads.main k input heard enough _
    ⟨b, inBlocks, hLookup, _, _, hFront, hTable, rfl⟩
  rw [hThread]
  exact keyMessageLaysThePlanesInItsMainRows f full input heard own₀ (ownCoins k) _

end

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.mainEntryOfRowsWithoutACoin
#print axioms AtPublicFiles.Lookup.Key.mainEntryBehindTheRow
#print axioms AtPublicFiles.Lookup.Key.writtenOwnMessageShape
#print axioms AtPublicFiles.Lookup.Key.writtenBlocksFit
#print axioms AtPublicFiles.Lookup.Key.planesEndWithTheRow
#print axioms AtPublicFiles.Lookup.Key.keyMessageLaysThePlanesAtEveryFront
#print axioms AtPublicFiles.Lookup.Key.keyMessageLaysThePlanesInItsMainRows
#print axioms AtPublicFiles.Lookup.Key.foldOfBlocksReadsAlike
#print axioms AtPublicFiles.Lookup.Key.bitsReadAsTheSendersMainRows
