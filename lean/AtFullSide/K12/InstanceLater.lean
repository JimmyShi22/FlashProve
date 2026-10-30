-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/InstanceLater.lean: the five statements at members 9 and 10 of ProofFile's sharedThread at
laterBase (LaterDefs.lean), a value of LaterLetters at the base prover.

  seat_at_nine the member at 9 seats the test on G_u.
  lettersBase  the letters of which sharedThread is the thread.
  five_border_nine, five_border_ten   FiveAtBorder at 9 and 10 at sharedThread at that value.

Limits.
- At the base return alone: at the return read through, the side in the list is not proverSideOfProximityTest, and
  this theorem does not apply.
- NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The
  ground: each of the five starts from ThrS, a premise on the letters left (rest, Kp₁, Said, w), which
  may read the coins; no lemma here shows it at every value of the coins: there the bar is flat.
- Nothing on completeness, on soundness or on what is hidden.
-/
import AtFullSide.K12.InstanceShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FiveAtLaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OFiveAt
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest.K14 (mgWords form2 holds2 witL kp2 randNow tailLike_shared)
open ProofFile.Honest.K12 (TestJob SeatOf)
open ProofFile.Honest.K12.AtFile (keepsU keeps_of_step seat_of_like jobDoorU jobDoorO tableShared
  fixedShared five_at_sharedThread)
open ProofFile.Honest.K12.AtProof (fourOf placeU)
open ProofFile.Honest.FirstThread
open P2Law.ProofPlan (declProofFull)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

variable (h : HeadAtReturn files A) (parts : SharedThreadParts A WtShared)
  (w : Common FullSizeMatrix IndexCommitterCoins TableKey) {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {nO : H2U.PlaceNums}

/-- **The member at 9 of sharedThread seats the test on G_u.** -/
theorem seat_at_nine (J : TestJob (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit)
    (hJ : J.p = (fourOf h.places).U) (hO : h.places.O = some nO)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (reads : IndexReaders FullSizeMatrix IndexCommitterCoins) {blk : Block St ProofFile.Cl}
    (hblk : (sharedThread h reads parts w).bs[9]? = some blk) :
    SeatOf blk J (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave := by
  obtain ⟨x, hx, hl⟩ := (tailLike_shared A.Z h.places h.firstChain A.H h.sharedNumbers
    (fun v => mgWords parts.lens (K1.qAt A.Z h.places) h.sharedNumbers (parts.meaning v))
    (form2 (K1.qAt A.Z h.places) parts.shape) (fun d => (_root_.Desc.K14.ended d).isSome)
    (fun s => OnBytes.Means.InOrder s.st)
    (witL parts.lens (K1.qAt A.Z h.places) (sentFirstOf A.Z h.places)
      (holds2 (K1.qAt A.Z h.places) reads.weights reads.rand) parts.rest)
    parts.table parts.fixed h.description.t₁ h.description.t₂
    (fun v => A.H.inRange v.w₀ = true) parts.rides
    (kp2 (K1.qAt A.Z h.places) (sentFirstOf A.Z h.places) parts.keeps) w
    b1 b2 b3 b4 b5 b6 b7 b8 nO hO hb).nine
  obtain rfl : x = blk := Option.some.inj (hx.symm.trans hblk)
  refine seat_of_like ?_
  rw [hJ]
  exact hl

/-- **The five statements at member 9, at sharedThread at the value of LaterLetters.** -/
theorem five_border_nine
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (riders : List (RiderCl (Common FullSizeMatrix IndexCommitterCoins TableKey) St)) (Kp₁ : Place → St → St → Prop)
    (hr10 : ∀ v s, ridersOf riders 10 v s)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    FiveAtBorder (sharedThread h (readsBase h)
      (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w)
      Said fall 9 := by
  have hf := half_at_base h.head.toAtMg h.head b1 b2 b3 b4 b5 b6 b7 b8 hb base rfl
  obtain ⟨p, be, ex, ri, ac⟩ := five_at_sharedThread h (readsBase h)
    (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w
    b1 b2 b3 b4 b5 b6 b7 b8 hb
    (jobDoorO (X₀ := Unit) A.Z h.places pO [b1, b2, b3, b4, b5, b6, b7, b8] (readsBase h).weights
      (readsBase h).rand).toRun.toTest () rfl (fun _ => rfl) nO hO hf Said fall
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => hr10 _ _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (fun blk hblk _ _ _ _ _ _ _ s' _ hS => (keepsAtBase_U h.places Kp₁ _ s').2
      (keeps_of_step (seat_at_nine h _ w
        (jobDoorU (X₀ := Unit) A.Z h.places [b1, b2, b3, b4, b5, b6, b7, b8] A.H.storedWords
          (readsBase h).weights (readsBase h).rand).toRun.toTest rfl hO hb (readsBase h) hblk) hS.2))
    (fun _ _ _ _ _ _ hk => (keepsAtBase_U h.places Kp₁ _ _).1 hk)
  exact ⟨p, be, ex, ri, ac⟩

/-- **The shared thread's letters**, the value of which sharedThread is the thread. -/
abbrev lettersBase (parts : SharedThreadParts A WtShared) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (w : Common FullSizeMatrix IndexCommitterCoins TableKey) :=
  SharedThread.lettersShared A.Z h.places h.firstChain A.H h.sharedNumbers
    (fun v => mgWords parts.lens (K1.qAt A.Z h.places) h.sharedNumbers (parts.meaning v))
    (form2 (K1.qAt A.Z h.places) parts.shape) (fun d => (_root_.Desc.K14.ended d).isSome)
    (fun s => OnBytes.Means.InOrder s.st)
    (witL parts.lens (K1.qAt A.Z h.places) (sentFirstOf A.Z h.places)
      (holds2 (K1.qAt A.Z h.places) reads.weights reads.rand) parts.rest)
    parts.table parts.fixed h.description.t₁ h.description.t₂
    (fun v => A.H.inRange v.w₀ = true) parts.rides
    (kp2 (K1.qAt A.Z h.places) (sentFirstOf A.Z h.places) parts.keeps) w

/-- **The five statements at member 10, at sharedThread at the value of LaterLetters.** hfield: that
the field holds the columns: ProofFile's. -/
theorem five_border_ten
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pO : P12)
    (hO : (fourOf h.places).O = some pO)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (riders : List (RiderCl (Common FullSizeMatrix IndexCommitterCoins TableKey) St)) (Kp₁ : Place → St → St → Prop)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (hr11 : ∀ blk, (sharedThread h (readsBase h)
        (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w).bs[10]? =
          some blk → ∀ k s m E ds y cols s', ThrS (sharedThread h (readsBase h)
        (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w)
        Said 10 k s m E →
      (sharedThread h (readsBase h)
        (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w).Stepped
        blk k s m E ds y cols s' → ridersOf riders 11 y.2.st.input s')
    (hfield : ∀ k s m E, ThrS (sharedThread h (readsBase h)
        (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w)
        Said 10 k s m E → ∀ cols,
      (sharedThread h (readsBase h)
        (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w).colsTo
        10 m E = .ok cols → m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    FiveAtBorder (sharedThread h (readsBase h)
      (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁)) w)
      Said fall 10 := by
  have hW := ProofFile.Honest.K12.AtFile.book_written h
  have hB := ProofFile.Honest.K14.bookWhole_same_at_laid hW h.head.scope h.head.laid
  have e₁ : A.H.shared = ProofFile.Honest.K12.AtProof.sharedWithUO matrixInput A.Z :=
    congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A₀.H.shared) (eq_ofFill base)
  have hhalf := ProofFile.Honest.K12.AtFile.half_found_O h.head hO matrixInput b1 b2 b3 b4 b5 b6 b7 b8 hb
  rw [← e₁] at hhalf
  have f11 : ∀ s, form2 (K1.qAt A.Z h.places) (fun _ _ => true) 11 s = true := fun s => by
    unfold form2
    rw [if_neg (by decide)]
  have k10 : ∀ s s', kp2 (K1.qAt A.Z h.places) (sentFirstOf A.Z h.places)
      (keepsAtBase h.places Kp₁) ⟨2, none, 10, .K12⟩ s s' ↔
        VerifiableInference.Desc.Grows s.st s'.st ∧ VerifiableInference.Desc.K1.SmpStay s.st s'.st := by
    intro s s'
    unfold kp2
    rw [if_neg (by decide)]
    exact keepsAtBase_O h.places Kp₁ s s'
  have e10 : (VerifiableInference.Desc.Shared.sharedPlaces true)[10]? =
      some ⟨2, none, 10, .K12⟩ := rfl
  have K : ProofFile.Honest.K12.AtFile.LettersTen
      (lettersBase h (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest riders Kp₁))
        (readsBase h) w) Said :=
    { split := rfl
      order := fun _ => Iff.rfl
      form := fun _ _ _ _ _ _ _ _ _ s' _ _ => f11 s'
      rides := hr11
      keepsIn := fun _ _ _ s _ _ _ _ _ s' _ _ g₁ g₂ p hp => by
        obtain rfl := Option.some.inj (e10.symm.trans hp)
        exact (k10 s s').2 ⟨g₁, g₂⟩
      keepsOut := fun _ s _ _ s' _ g => (k10 s s').1 (g _ e10) }
  obtain ⟨p, be, ex, ri, ac⟩ := ProofFile.Honest.K12.AtFile.five_at_letters h.head hO hB b1 b2 b3 b4 b5 b6
    b7 b8 hb ⟨rfl, fun k v hd => ProofFile.Honest.K14.get_witL _ _ _ _ rest k v hd, rfl, rfl⟩ Said K hhalf
    hfield fall
  exact ⟨p, be, ex, ri, ac⟩

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.seat_at_nine
#print axioms ProofFile.Honest.Term.five_border_nine
#print axioms ProofFile.Honest.Term.five_border_ten
