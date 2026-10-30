-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHSeats.lean: the record `SendSeat` (E2E/FirstHSeat.lean) at the key file's three sendings,
from one list of public facts.

  `FirstPublic`: what is public: K's senders are the sheet's; they stand at the first chain's places;
    the jobs fit; W's first number is the plan's. All are closed facts at the written sizes.
  `sizes_of_shape`: the statement's count of messages at a border, off the book-keeping.
  `seat_idx`, `seat_msg`, `seat_w`: the three records.

Limits. `FirstPublic` is a premise here. What pays its closed fields is another file's.
-/
import E2E.FirstHSeat
import E2E.FirstHMembers
import E2E.KeySendSeats
import E2E.KeySampledAt
import E2E.KeyTreesCount
import E2E.KeyFirstSends
import E2E.KeyWIs
import E2E.KeyLedgers

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces sendingPar sendW pieces
  groupsTold rootsAt rootsBefore lastSendRound shape₁_iff)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ counts₁ ties₁ sizesB)
open Johnson.RunOne.KeyRows23 (atSix)
open AtPublicFiles.KeyThread (D one₀ sampled_of_shape sentIn)
open AtPublicFiles.KeyFile (KeyParts keyProver In1)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription pubOf sendWAt sentAt groupsW)
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending keyBatt constraintRowsAtClaimPoints firstW oneOf matrixEntryOf battAt keyPoints multiplicitiesGroups)
open AtPublicFiles.Key (idxJob msgJob wJob idx_seat msg_seat w_seat w_sent)
open AtPublicFiles.KeyBook (rideMsg rideW)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob proverSideOfSending sendFits)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- **What is public at the three sendings and the batching.** -/
structure FirstPublic (Xs : Source) (N : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X' Wk)
    (f : W₀ → Weights) : Prop where
  places : K.AtPlaces
  idx : K.idx = indexMaskSending Xs
  msg : K.msg = multiplicitiesSending f Xs
  w : K.w = batchedRowsSending f Xs N
  batt : K.batt = keyBatt Xs
  pile : K.pile = constraintRowsAtClaimPoints Xs N
  weights : K.weights = f
  fitsIdx : sendFits K.idx.P K.idx.ride = true
  fitsMsg : sendFits K.msg.P K.msg.ride = true
  fitsW : sendFits K.w.P K.w.ride = true
  sentMsg : 0 < (Wf.messageOf (oneOf Xs).ranges).size
  firstIsPlans : firstW Xs = 1 + 2 * (oneOf Xs).ranges.stages.length
  stages : 1 ≤ (oneOf Xs).ranges.stages.length
  lookupsTwo : (oneOf Xs).ranges.lookups.length = 2
  toldThree : ((D Xs N Pl).oracleAt 0).isSome = true ∧ ((D Xs N Pl).oracleAt 1).isSome = true ∧
    ((D Xs N Pl).oracleAt 5).isSome = true
  treesIdx : K.idx.P.trees.length = 1
  treesMsg : K.msg.P.trees.length = 1
  treesW : K.w.P.trees.length = 1
  treesAt1 : treesTo (D Xs N Pl).first.blocksInOrder 1 = 1
  treesAt17 : treesTo (D Xs N Pl).first.blocksInOrder 17 = 5
  sentAt0 : sentIn ((D Xs N Pl).first.blocksInOrder.flatMap (·.rounds)) 0 = 0
  sentAt1 : sentIn ((D Xs N Pl).first.blocksInOrder.flatMap (·.rounds)) 1 =
    roundsTo (D Xs N Pl).first.blocksInOrder 1
  sentAt5 : sentIn ((D Xs N Pl).first.blocksInOrder.flatMap (·.rounds)) 5 =
    roundsTo (D Xs N Pl).first.blocksInOrder 17

/-- The statement's count of messages at a border. -/
theorem sizes_of_shape {b : Nat} {s : FirstState} (h : ShapeAt Xs b s = true) :
    s.d.st.oracles.size = (counts₁ (one₀ Xs) b).1 := by
  have e := ((shape₁_iff _ _ _ _ _ b s).1 h).1
  have e' : ties₁ (one₀ Xs) b s = true := e
  unfold ties₁ sizesB at e'
  simp only [Bool.and_eq_true, beq_iff_eq] at e'
  exact e'.2.1.1.1.1.1.1.1

theorem toldAt {j : Nat} (h : ((D Xs N Pl).oracleAt j).isSome = true) :
    ∃ o, (D Xs N Pl).oracleAt j = some o :=
  Option.isSome_iff_exists.1 h

/-- **The index masks' sending.** -/
theorem seat_idx (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) :
    SendSeat Xs N Pl K f Q w₀ rc x 0 0 K.idx := by
  obtain ⟨bw, hw⟩ := w_there hs scope
  refine
    { member := ⟨_, member0 hw, ?_, fun h => ?_⟩
      half := ?_, fits := hp.fitsIdx, data := ?_, sent := ?_, number := fun s h => ?_
      sampled := fun s h => ?_, orc := ?_, num := ?_, small := by decide, msg := fun _ _ => rfl
      fixed := rfl, told := toldAt hp.toldThree.1, seat := rfl
      table := fun τ hτ k w h => ?_, fixedTree := fun τ hτ => ?_ }
  · rw [hp.idx]
    exact idx_seat (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Claim) _ _ _ _
  · rw [hp.idx]
    exact idx_yes _ _ _ h
  · rw [hp.places.idx]
    exact find_idx K hp.places
  · intro w fr fr' _
    rw [hp.idx]
    rfl
  · rw [hp.idx]
    show 0 < (sendingPar (oneOf Xs) pieces.idx "the index masks" #[(oneOf Xs).indexMasks] _).sent.size
    rw [AtPublicFiles.KeyLookup.sent_par]
    simp
  · rw [sizes_of_shape h, hp.idx]
    rfl
  · exact sampled_of_shape (one₀ Xs) (by decide) s h 0 (Or.inl (by decide))
  · rw [hp.idx]
    rfl
  · rw [hp.idx]
    rfl
  · rw [hp.treesIdx] at hτ
    obtain rfl : τ = 0 := by omega
    rfl
  · rw [hp.treesIdx] at hτ
    obtain rfl : τ = 0 := by omega
    exact hp.sentAt0.trans (Nat.zero_add _).symm

/-- **The multiplicities' sending.** -/
theorem seat_msg (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) :
    SendSeat Xs N Pl K f Q w₀ rc x 1 1 K.msg := by
  obtain ⟨bw, hw⟩ := w_there hs scope
  refine
    { member := ⟨_, member1 hw, ?_, fun h => ?_⟩
      half := ?_, fits := hp.fitsMsg, data := ?_, sent := ?_, number := fun s h => ?_
      sampled := fun s h => ?_, orc := ?_, num := ?_, small := by decide, msg := fun _ _ => rfl
      fixed := rfl, told := toldAt hp.toldThree.2.1, seat := rfl
      table := fun τ hτ k w h => ?_, fixedTree := fun τ hτ => ?_ }
  · rw [hp.msg]
    exact msg_seat (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Claim) _ _ _ _ _ _
  · rw [hp.msg]
    exact msg_yes _ _ _ h
  · rw [hp.places.msg]
    exact find_msg K hp.places
  · intro w fr fr' _
    rw [hp.msg]
    rfl
  · rw [hp.msg]
    show 0 < (sendingPar (oneOf Xs) pieces.msg "the lookups' own message and what rides with it"
      (Wf.messageOf (oneOf Xs).ranges) _).sent.size
    rw [AtPublicFiles.KeyLookup.sent_par]
    exact hp.sentMsg
  · rw [sizes_of_shape h, hp.msg]
    rfl
  · exact sampled_of_shape (one₀ Xs) (by decide) s h 1 (Or.inl (by decide))
  · rw [hp.msg]
    rfl
  · rw [hp.msg]
    rfl
  · rw [hp.treesMsg] at hτ
    obtain rfl : τ = 0 := by omega
    show (tbH Xs N Pl K f Q) (.own (treesTo (D Xs N Pl).first.blocksInOrder 1 + 0)) k w h = _
    rw [hp.treesAt1]
    rfl
  · rw [hp.treesMsg] at hτ
    obtain rfl : τ = 0 := by omega
    show (Th Xs N Pl K f Q w₀ rc x).fixed (.own (treesTo (D Xs N Pl).first.blocksInOrder 1 + 0)) = _
    rw [hp.treesAt1]
    exact hp.sentAt1.trans (Nat.zero_add _).symm

/-- W's job is what the shape's message makes it. -/
theorem keyW_job {bw : Block FirstState Claim}
    (hw : sendWAt (pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 = some bw) :
    wJob (X := X') (W := In1 W₀ Rc) (matrixEntryOf f) (oneOf Xs) pieces (groupsW Xs.Y.D.1 Xs.Y.told.1)
        (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N) = some (batchedRowsSending f Xs N) ∧
      bw.place = (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P.place ∧
      bw.rounds = VerifiableInference.Desc.K1.rounds (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P ∧
      bw.oracles = VerifiableInference.Desc.K1.oracles (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P := by
  have hs := w_seat (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Claim) (W := In1 W₀ Rc)
    (X := X') (matrixEntryOf f) (oneOf Xs) pieces (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs) rideW
    (keyPoints Xs N) (battAt Xs N) (sentAt Xs.Y.D.1)
  have hw' : sendW (oneOf Xs) pieces (sentAt Xs.Y.D.1) (groupsW Xs.Y.D.1 Xs.Y.told.1) = some bw := hw
  rw [hw'] at hs
  cases hj : wJob (X := X') (W := In1 W₀ Rc) (matrixEntryOf f) (oneOf Xs) pieces
      (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N) with
  | none =>
    rw [hj] at hs
    exact hs.elim
  | some J =>
    rw [hj] at hs
    have e : batchedRowsSending (X := X') (Rc := Rc) f Xs N = J := by
      unfold batchedRowsSending
      show (wJob (X := X') (W := In1 W₀ Rc) (matrixEntryOf f) (oneOf Xs) pieces
        (groupsW Xs.Y.D.1 Xs.Y.told.1) (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N)).getD _ = J
      rw [hj]
      rfl
    rw [e]
    exact ⟨rfl, hs⟩

/-- **W's sending.** -/
theorem seat_w (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) :
    SendSeat Xs N Pl K f Q w₀ rc x 17 2 K.w := by
  obtain ⟨bw, hw⟩ := w_there hs scope
  obtain ⟨hj, hsh⟩ := keyW_job (X' := X') (W₀ := W₀) (Rc := Rc) (f := f) (N := N) hw
  have hw' : sendW (oneOf Xs) pieces (sentAt Xs.Y.D.1) (groupsW Xs.Y.D.1 Xs.Y.told.1) = some bw := hw
  obtain ⟨msg, hm, hyes⟩ := w_yes hw'
  obtain ⟨-, hsent, hfirst, -⟩ := w_sent _ _ _ _ _ _ _ _ _ hj
  have hP : (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P = sendingPar (oneOf Xs) pieces.w
      "W and what rides with it" msg (groupsW Xs.Y.D.1 Xs.Y.told.1) := by
    unfold wJob at hj
    rw [hm] at hj
    exact (congrArg SendJob.P (Option.some.inj hj)).symm
  refine
    { member := ⟨_, (member_back hs scope hw).2, ?_, fun h => ?_⟩
      half := ?_, fits := hp.fitsW, data := ?_, sent := ?_, number := fun s h => ?_
      sampled := fun s h => ?_, orc := ?_, num := ?_, small := by decide, msg := fun _ _ => rfl
      fixed := rfl, told := toldAt hp.toldThree.2.2, seat := rfl
      table := fun τ hτ k w h => ?_, fixedTree := fun τ hτ => ?_ }
  · rw [hp.w]
    exact hsh
  · rw [hp.w, hP]
    exact hyes h
  · rw [hp.places.w]
    exact find_w K hp.places
  · intro w fr fr' e
    rw [hp.w]
    unfold wJob at hj
    rw [hm] at hj
    rw [← Option.some.inj hj]
    simp only [e]
  · rw [hp.w]
    exact hsent
  · rw [sizes_of_shape h, hp.w, hfirst, hp.firstIsPlans]
    rfl
  · exact sampled_of_shape (one₀ Xs) (by decide) s h 2 (Or.inl (by decide))
  · rw [hp.w, hfirst, hp.firstIsPlans]
    rfl
  · rw [hp.w, hfirst, hp.firstIsPlans]
    have h1 := hp.stages
    show (if (1 + 2 * (oneOf Xs).ranges.stages.length == 0) = true then some 0
      else if (1 + 2 * (oneOf Xs).ranges.stages.length == 1) = true then some 1
      else if (1 + 2 * (oneOf Xs).ranges.stages.length ==
        1 + 2 * (oneOf Xs).ranges.stages.length) = true then some 2 else none) = some 2
    have e0 : ¬ (1 + 2 * (oneOf Xs).ranges.stages.length == 0) = true := by
      rw [beq_iff_eq]
      omega
    have e1 : ¬ (1 + 2 * (oneOf Xs).ranges.stages.length == 1) = true := by
      rw [beq_iff_eq]
      omega
    rw [if_neg e0, if_neg e1, if_pos (beq_self_eq_true _)]
  · rw [hp.treesW] at hτ
    obtain rfl : τ = 0 := by omega
    show (tbH Xs N Pl K f Q) (.own (treesTo (D Xs N Pl).first.blocksInOrder 17 + 0)) k w h = _
    rw [hp.treesAt17]
    rfl
  · rw [hp.treesW] at hτ
    obtain rfl : τ = 0 := by omega
    show (Th Xs N Pl K f Q w₀ rc x).fixed (.own (treesTo (D Xs N Pl).first.blocksInOrder 17 + 0)) = _
    rw [hp.treesAt17]
    exact hp.sentAt5.trans (Nat.zero_add _).symm

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.sizes_of_shape
#print axioms AtPublicFiles.FirstH.seat_idx
#print axioms AtPublicFiles.FirstH.seat_msg
#print axioms AtPublicFiles.FirstH.seat_w
