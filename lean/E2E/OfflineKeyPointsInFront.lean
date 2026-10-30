-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineKeyPointsInFront.lean: THE POINTS OF THE CLAIMS ON THE LOOKUPS' KEYS (`keyPoints`, E2E/KeyFirstSends.lean) READ, OF THE
CHALLENGES HEARD, THE FIRST 18,848 ALONE: those in front of the sending of W. In scope, at the written sizes. With the
batching's three numbers (`battAt_full`, E2E/KeyWReadsFront.lean) so does the data of W's sending.

  `elemAt_front`, `varChals_front`, `keyPt_front`   what a lookup's key point reads of the list: general in the face
  `belowB`, `below_of_B`     a test with code: every key point of a face reads below N; what it gives
  `writtenBase`            the rounds in front of lookup number i, off the written rows
  `below_written`          the test at the two written faces: kernel lines that can say no
  `no_third_lookup`        from number 2 on the written face has no part
  `baseAt_written`         in scope the description's number is the written one
  `keyPoints_in_front`     the statement on the points
  `keyW_data_in_front`     the statement on the data of W's sending

Limits. In scope (`KeySourced`, `InScope`). On which challenges are read: nothing on what is made of them. Nothing on
completeness, on soundness or on what is hidden.
-/
import E2E.OfflineLookupCounts
import E2E.KeyWReadsFront
import E2E.OfflineRowsAtValue
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowWData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K3 (LFace Stage elemsAt elemAt varChals roundAt ptsOf behind)
open ProofFile.Honest.K12.Sim2 (wJob_data_reads)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyBook (OneFull fullFirst startIn places_named roundsInFront_rows battAt_full)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.KeyValues (faceAt baseAt placeAt blocksOf keyPoints battAt batchedRowsSending oneOf)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)

/-! ## 1 What a key point reads -/

theorem elemAt_front (h h' : List Fmt.Drawn) (n i : Nat) (e : h.take n = h'.take n) (hi : i < n) :
    elemAt h i = elemAt h' i := by
  unfold elemAt elemsAt
  have g : h[i]? = h'[i]? := by
    rw [← List.getElem?_take_of_lt hi (l := h), e, List.getElem?_take_of_lt hi]
  rw [g]

theorem varChals_front (f : LFace) (base : Nat) (h h' : List Fmt.Drawn) (n : Nat)
    (e : h.take n = h'.take n) (s : Stage) (k : Nat) (hk : roundAt f base s + 1 + k ≤ n) :
    varChals f base h s k = varChals f base h' s k := by
  unfold varChals
  refine List.map_congr_left fun l hl => ?_
  have := List.mem_range.1 hl
  exact elemAt_front h h' n _ e (by omega)

/-- **A key point reads the rounds of its level and of the line behind it.** -/
theorem keyPt_front (f : LFace) (base : Nat) (h h' : List Fmt.Drawn) (n : Nat)
    (e : h.take n = h'.take n) (p v : Nat)
    (hb : ∀ m, v = m + 1 → roundAt f base (.key p m) + 1 + m ≤ n ∧ roundAt f base (.keyLine p m) < n) :
    (ptsOf f base h).keyPt p v = (ptsOf f base h').keyPt p v := by
  cases v with
  | zero => rfl
  | succ m =>
    obtain ⟨b1, b2⟩ := hb m rfl
    show behind m (f.orders p m) (varChals f base h (.key p m) m)
        (elemAt h (roundAt f base (.keyLine p m))) =
      behind m (f.orders p m) (varChals f base h' (.key p m) m)
        (elemAt h' (roundAt f base (.keyLine p m)))
    rw [varChals_front f base h h' n e _ _ b1, elemAt_front h h' n _ e b2]

/-! ## 2 The test -/

/-- **Every key point of the face reads below n.** A test with code. -/
def belowB (f : LFace) (base n : Nat) : Bool :=
  (List.range f.parts.length).all fun p =>
    match f.parts.getD p 0 with
    | 0 => true
    | m + 1 => decide (roundAt f base (.key p m) + 1 + m ≤ n) &&
        decide (roundAt f base (.keyLine p m) < n)

theorem below_of_B {f : LFace} {base n : Nat} (h : belowB f base n = true) (p m : Nat)
    (hv : f.parts.getD p 0 = m + 1) :
    roundAt f base (.key p m) + 1 + m ≤ n ∧ roundAt f base (.keyLine p m) < n := by
  have hp : p < f.parts.length := by
    rcases Nat.lt_or_ge p f.parts.length with q | q
    · exact q
    · rw [List.getD_eq_default _ _ q] at hv
      cases hv
  have q := List.all_eq_true.1 h p (List.mem_range.2 hp)
  rw [hv] at q
  simp only [Bool.and_eq_true, decide_eq_true_eq] at q
  exact q

/-! ## 3 At the written sizes -/

/-- The rounds in front of lookup number i, off the written rows. -/
def writtenBase (i : Nat) : Nat := (startIn fullFirst (placeAt i)).getD 0

theorem below_written : belowB (writtenLookupFace 0) (writtenBase 0) 18848 = true ∧
    belowB (writtenLookupFace 1) (writtenBase 1) 18848 = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The test can say no: one round fewer is too few for the second lookup. -/
theorem below_written_bites : belowB (writtenLookupFace 1) (writtenBase 1) 18000 = false := by
  decide +kernel

theorem two_lookups : (OnBytes.Wf.lookupsOf keyFull.ranges.x
    (OnBytes.Wf.matrixOf keyFull.once.shape)).length = 2 := by decide +kernel

/-- From number 2 on the written face has no part. -/
theorem no_third_lookup (i : Nat) (hi : 2 ≤ i) : (writtenLookupFace i).parts = [] := by
  unfold writtenLookupFace
  rw [List.getD_eq_default _ _ (by rw [two_lookups]; exact hi)]
  rfl

theorem below_all (i : Nat) : belowB (writtenLookupFace i) (writtenBase i) 18848 = true := by
  match i with
  | 0 => exact below_written.1
  | 1 => exact below_written.2
  | j + 2 =>
    unfold belowB
    rw [no_third_lookup (j + 2) (by omega)]
    rfl

section Scope
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- In scope the description's number of rounds in front of a lookup is the written one. -/
theorem baseAt_written (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (i : Nat) :
    baseAt Xs N i = writtenBase i := by
  obtain ⟨r1, -, -⟩ := places_named scope hs.named
  unfold baseAt writtenBase
  rw [roundsInFront_rows]
  show (startIn (rowsOf (keyFileDescription Xs N Pl).first.blocksInOrder) (placeAt i)).getD 0 = _
  rw [r1]

/-- **The points read the first 18,848 challenges alone.** -/
theorem keyPoints_in_front (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (h h' : List Fmt.Drawn) (e : h.take 18848 = h'.take 18848) :
    keyPoints Xs N h = keyPoints Xs N h' := by
  funext i p
  unfold keyPoints
  rw [faceAt_written hs scope i, baseAt_written hs scope i,
    keyPt_front (writtenLookupFace i) (writtenBase i) h h' 18848 e p _
      (fun m hm => below_of_B (below_all i) p m hm)]

theorem columns_written : (OnBytes.Wf.matrixOf keyFull.once.shape).kCol ≤ 18 := by decide +kernel

/-- **The data of W's sending reads of a front the first 18,848 challenges alone.** -/
theorem keyW_data_in_front {W₀ Rc : Type} (f : W₀ → Weights) (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (w : AtPublicFiles.KeyFile.In1 W₀ Rc) (fr fr' : Front Unit)
    (e : fr.heard.take 18848 = fr'.heard.take 18848) :
    (batchedRowsSending (Rc := Rc) (X := Unit) f Xs N).data w fr = (batchedRowsSending (Rc := Rc) (X := Unit) f Xs N).data w fr' := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  obtain ⟨msg, hm⟩ : ∃ msg, OnBytes.linMessageW (oneOf Xs).lin = some msg := by
    obtain ⟨J, -, -, -, -, -, gs, fi, pts, a, hJ⟩ := keyW_written (W₀ := W₀) (Rc := Rc) Xs N f one
    unfold AtPublicFiles.Key.wJob at hJ
    obtain ⟨msg, hm, -⟩ := Option.map_eq_some_iff.1 hJ
    exact ⟨msg, hm⟩
  have hb := battAt_full scope hs.named
  have hk : (OnBytes.Wf.matrixOf (oneOf Xs).lin).kCol ≤ 18 := by
    rw [one.lin]
    exact columns_written
  obtain ⟨J, hJ⟩ : ∃ J, AtPublicFiles.Key.wJob (W := AtPublicFiles.KeyFile.In1 W₀ Rc) (X := Unit) (AtPublicFiles.KeyValues.matrixEntryOf f)
      (oneOf Xs) VerifiableInference.Desc.Key.pieces
      (VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1
        (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1
          (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))
        (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1
          (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1)))
      (AtPublicFiles.KeyValues.firstW Xs) AtPublicFiles.KeyBook.rideW (keyPoints Xs N) (battAt Xs N) = some J := by
    unfold AtPublicFiles.Key.wJob
    rw [hm]
    exact ⟨_, rfl⟩
  have eW : batchedRowsSending (Rc := Rc) (X := Unit) f Xs N = J := by
    unfold batchedRowsSending
    rw [hJ]
    rfl
  rw [eW]
  exact wJob_data_reads _ _ _ _ _ _ _ _ J hJ 18848 (keyPoints_in_front hs scope)
    (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; show 18830 + _ ≤ 18848; omega) w fr fr' e

end Scope

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.keyPt_front
#print axioms AtPublicFiles.OfflineRows.below_of_B
#print axioms AtPublicFiles.OfflineRows.below_written
#print axioms AtPublicFiles.OfflineRows.below_written_bites
#print axioms AtPublicFiles.OfflineRows.no_third_lookup
#print axioms AtPublicFiles.OfflineRows.baseAt_written
#print axioms AtPublicFiles.OfflineRows.keyPoints_in_front
#print axioms AtPublicFiles.OfflineRows.keyW_data_in_front
