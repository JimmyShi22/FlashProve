-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKeyOwn/ReadsBelow.lean: THE KEY FILE's SENDING OF W READS NONE BUT THE FIRST n CHALLENGES, and of
what stands in front of it the challenges alone. For the own test: the test's member reads W's data at the test's own
front; the table at hand was laid at the challenges in front of W's sending: the two data are one.

  readsBelow   K14's form (SendJob.readsBelow, Honest/K14/SendingsPaid.lean) for a job of the kind K1: the data at the first
               n challenges, at whatever own state and whatever was seen, are the data at the whole front
  readsBelow_mono
  wJob_readsBelow   AtPublicFiles.Key.wJob's job, from: the letter points reads none but the first n · the batching's three numbers
               lie below n
  keyPoints_take    the key claims' points (AtPublicFiles.KeyValues.keyPoints) read none but the first n, from KeyPointsBelow
  keyW_readsBelow   THE END, at the value batchedRowsSending f Xs N
  idx_readsBelow    the index masks' job has no datum: it reads nothing

Omega's half lies on the trunk: K14.jobOmega_readsBelow (Honest/K14/SendingsPaid.lean): readsBelow (A.atPoint + 1).

Limits. KeyPointsBelow and the bound on the batching's numbers are PUBLIC premises, on numbers of rounds: nothing here
evaluates them at a description. This file proves nothing about completeness, soundness or hiding.
-/
import E2E.KeyFirstSends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKeyOwn
open OnBytes OnBytes.Params
open OnBytes.Slice (GF)
open ProofFile.Honest.K1 (SendJob Ride)
open VerifiableInference.Desc.Key (Source Pieces)
open AtPublicFiles.Key (wJob wWeights BattAt idxJob)
open AtPublicFiles.KeyValues (batchedRowsSending indexMaskSending keyPoints battAt baseAt faceAt oneOf)

variable {W X : Type}

/-- **The job's data reads none but the first n challenges, and of the front the challenges alone.** -/
def readsBelow (J : SendJob W X) (n : Nat) : Prop :=
  ∀ w (fr : Front X) (own' : X) (seen' : Seen),
    J.data w { heard := fr.heard.take n, own := own', seen := seen' } = J.data w fr

theorem readsBelow_mono {J : SendJob W X} {n n' : Nat} (h : readsBelow J n) (hn : n ≤ n') :
    readsBelow J n' := by
  intro w fr own' seen'
  rw [← h w { heard := fr.heard.take n', own := own', seen := seen' } own' seen']
  show J.data w { heard := (fr.heard.take n').take n, own := own', seen := seen' } = _
  rw [List.take_take, Nat.min_eq_left hn, h w fr own' seen']

/-- A challenge below the cut is the list's. -/
theorem elemAt_take (h : List Fmt.Drawn) {i n : Nat} (hi : i < n) :
    AtPublicFiles.Key.elemAt (h.take n) i = AtPublicFiles.Key.elemAt h i := by
  unfold AtPublicFiles.Key.elemAt
  rw [List.getElem?_take, if_pos hi]

/-- The batching's weights read none but the first n challenges. -/
theorem wWeights_take (one : OneTime) (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)
    (n : Nat) (hp : ∀ ds, points (ds.take n) = points ds) (h1 : a.sigma < n) (h2 : a.eps < n)
    (h3 : a.first + (Wf.matrixOf one.lin).kCol ≤ n) (h : List Fmt.Drawn) :
    wWeights one points a (h.take n) = wWeights one points a h := by
  unfold wWeights
  rw [hp h, elemAt_take h h1, elemAt_take h h2,
    List.map_congr_left fun i hi => elemAt_take h (i := a.first + i)
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (List.mem_range.1 hi) _) h3)]

/-- **W's job reads none but the first n challenges.** -/
theorem wJob_readsBelow (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
    (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
    (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt) (J : SendJob W X)
    (hJ : wJob entry one N groups first ride points a = some J) (n : Nat)
    (hp : ∀ ds, points (ds.take n) = points ds) (h1 : a.sigma < n) (h2 : a.eps < n)
    (h3 : a.first + (Wf.matrixOf one.lin).kCol ≤ n) : readsBelow J n := by
  unfold wJob at hJ
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hJ
  intro w fr own' seen'
  funext m r j
  dsimp only
  rw [wWeights_take one points a n hp h1 h2 h3]

/-- The index masks' job has no datum. -/
theorem idx_readsBelow (one : OneTime) (N : Pieces) (groups : List (List Nat)) (first n : Nat) :
    readsBelow (idxJob (W := W) (X := X) one N groups first) n :=
  fun _ _ _ _ => rfl

/-! ## The key claims' points -/

theorem k3_elemAt_take (h : List Fmt.Drawn) {i n : Nat} (hi : i < n) :
    K3.elemAt (h.take n) i = K3.elemAt h i := by
  unfold K3.elemAt K3.elemsAt
  rw [List.getElem?_take, if_pos hi]

/-- **A PUBLIC PREMISE's FORM**: at each part of each lookup that has a level, the rounds of the key tree's last level
and of its line lie below n. -/
def KeyPointsBelow (Xs : Source) (N : H2U.PlaceNums) (n : Nat) : Prop :=
  ∀ i p m, (faceAt Xs i).parts.getD p 0 = m + 1 →
    K3.roundAt (faceAt Xs i) (baseAt Xs N i) (.key p m) + 1 + m ≤ n ∧
      K3.roundAt (faceAt Xs i) (baseAt Xs N i) (.keyLine p m) < n

/-- **The key claims' points read none but the first n challenges.** -/
theorem keyPoints_take (Xs : Source) (N : H2U.PlaceNums) (n : Nat) (hB : KeyPointsBelow Xs N n)
    (ds : List Fmt.Drawn) : keyPoints Xs N (ds.take n) = keyPoints Xs N ds := by
  funext i p
  unfold keyPoints
  cases hm : (faceAt Xs i).parts.getD p 0 with
  | zero => rfl
  | succ m =>
    obtain ⟨b1, b2⟩ := hB i p m hm
    show (K3.behind m ((faceAt Xs i).orders p m)
        (K3.varChals (faceAt Xs i) (baseAt Xs N i) (ds.take n) (.key p m) m)
        (K3.elemAt (ds.take n) (K3.roundAt (faceAt Xs i) (baseAt Xs N i) (.keyLine p m)))).toList.reverse =
      (K3.behind m ((faceAt Xs i).orders p m)
        (K3.varChals (faceAt Xs i) (baseAt Xs N i) ds (.key p m) m)
        (K3.elemAt ds (K3.roundAt (faceAt Xs i) (baseAt Xs N i) (.keyLine p m)))).toList.reverse
    rw [k3_elemAt_take ds b2]
    unfold K3.varChals
    rw [List.map_congr_left fun l hl => k3_elemAt_take ds
      (i := K3.roundAt (faceAt Xs i) (baseAt Xs N i) (.key p m) + 1 + l)
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (List.mem_range.1 hl) _) b1)]

/-- **THE KEY FILE's SENDING OF W READS NONE BUT THE FIRST n CHALLENGES**, at the value batchedRowsSending. -/
theorem keyW_readsBelow {W₀ Rc : Type} (f : W₀ → Weights) (Xs : Source) (N : H2U.PlaceNums) (n : Nat)
    (hB : KeyPointsBelow Xs N n)
    (h3 : (battAt Xs N).first + (Wf.matrixOf (oneOf Xs).lin).kCol ≤ n) :
    readsBelow (batchedRowsSending (Rc := Rc) (X := X) f Xs N) n := by
  have e1 : (battAt Xs N).sigma + 2 = (battAt Xs N).first := rfl
  have e2 : (battAt Xs N).eps + 1 = (battAt Xs N).first := rfl
  unfold batchedRowsSending
  cases hJ : wJob (X := X) (AtPublicFiles.KeyValues.matrixEntryOf (Rc := Rc) f) (oneOf Xs)
      VerifiableInference.Desc.Key.pieces
      (VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1
        (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1
          (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))
        (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1
          (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1)))
      (AtPublicFiles.KeyValues.firstW Xs) AtPublicFiles.KeyBook.rideW (keyPoints Xs N) (battAt Xs N) with
  | none => exact fun _ _ _ _ => rfl
  | some J =>
    exact wJob_readsBelow _ _ _ _ _ _ _ _ J hJ n (keyPoints_take Xs N n hB) (by omega) (by omega) h3

end ProofFile.Honest.K12.AtKeyOwn

#print axioms ProofFile.Honest.K12.AtKeyOwn.readsBelow_mono
#print axioms ProofFile.Honest.K12.AtKeyOwn.wJob_readsBelow
#print axioms ProofFile.Honest.K12.AtKeyOwn.keyPoints_take
#print axioms ProofFile.Honest.K12.AtKeyOwn.keyW_readsBelow
#print axioms ProofFile.Honest.K12.AtKeyOwn.idx_readsBelow
