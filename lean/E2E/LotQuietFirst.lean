-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotQuietFirst.lean: THE FIVE DEBTS AT THE QUIET MEMBERS OF THE KEY FILE's FIRST CHAIN, at the thread laid₁
(E2E/KeyRest.lean), general in the filling, the halves and the tables, and at the thread Th (E2E/FirstHSeat.lean).
The road of E2E/LotMemberFourteenGrows.lean (member 14), at the members where the row owes nothing.

  `acceptedQuiet`: a member of the first chain without a round is accepted, at every fall.
  **`fiveQuiet`**: PlaysS, BehindS, ExchangeS, RidesPastS, AcceptedS at members 2, 3, 6, 7, 8, 9, 12, 13
    ("laid", "caller", "behind the batching", "cleared" of both lookups), at every letter Said and every fall.
  **`fourLayer`**: the same but for ExchangeS at members 5 and 11 (the two layers of rows): THE EXCHANGE THERE IS
    NOT HERE.
  `fiveQuiet_Th`, `fourLayer_Th`: at Th.

All by calls of the library: plays_quiet₁ (E2E/KeyPlaysQuiet.lean), behind₁ (E2E/KeyBehind.lean), exchange_of_nil
(E2E/KeyExchangeEmpty.lean), ridesPast₁ (E2E/KeyRides.lean), accepted_quiet₁ (E2E/KeyQuietFirst.lean) at
first_of_sourced (E2E/KeyShapeFullSourced.lean). No new content.

Limits. ThrS at the border in front, the premise inside every debt, is met by nothing here: where the thread
stands nowhere all are empty. SaidNext is not among the five. The written sizes alone: in scope, at a sourced
description. No member here has a round: nothing is said of what any half sends. Nothing on soundness,
completeness, hiding or binding.
-/
import E2E.FirstHSeat
import E2E.KeyRowsLater
import E2E.KeyShapeFullSourced
import E2E.KeyExchangeEmpty

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows1 (ReadsL)
open AtPublicFiles.KeyThread (KeyFill laid₁ behind₁ ridesPast₁ plays_quiet₁ exchange_of_nil rowsFirst)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : PublicFiles}

/-- **A member of the first chain without a round is accepted**, at every fall. -/
theorem acceptedQuiet (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) (b : Nat) (hb : b < 19)
    (hq : (AtPublicFiles.KeyBook.fullFirst[b]?).map (·.2) = some 0) :
    Accepted (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) fall b := by
  obtain ⟨-, -, -, hlen, hT0, -, hyes, -⟩ :=
    AtPublicFiles.AtFiles.Full.first_of_sourced hs scope (fun _ _ _ _ => true)
  obtain ⟨blk, hblk, hr, -⟩ := AtPublicFiles.KeyThread.quiet_of_rows (keyFileDescription Xs N Pl).first.blocksInOrder
    AtPublicFiles.KeyBook.fullFirst (AtPublicFiles.KeyBook.places_named scope hs.named).1
    (fun b hb => ((planOk_all hs.named.plan).1 b hb).2) (b := b) hq
  exact AtPublicFiles.AtFiles.accepted_quiet₁ Xs N Pl AtPublicFiles.AtFiles.CF (fun _ _ _ _ => true)
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) rfl (AtPublicFiles.AtFiles.Full.public_first_sourced hs scope)
    (n := 19) (Nat.le_of_eq hlen.symm) (by rw [hT0]; exact hyes)
    (fun _ w _ s₀ _ hb => ⟨_, hb⟩) (fun _ _ _ _ _ _ _ => rfl) b hb blk hblk hr

/-- **The five at the eight quiet members whose row owes nothing.** -/
theorem fiveQuiet (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hG : ReadsL L.base.h₁)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13],
      PlaysS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        BehindS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        ExchangeS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        RidesPastS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        AcceptedS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said fall b := by
  intro b hb
  have h1 : b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14] :=
    (by decide : ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13], b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14]) b hb
  have h2 : b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18] :=
    (by decide : ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13],
      b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18]) b hb
  have h3 : (rowsFirst b).owes = [] :=
    (by decide : ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13], (rowsFirst b).owes = []) b hb
  have h4 : b < 19 ∧ (AtPublicFiles.KeyBook.fullFirst[b]?).map (·.2) = some 0 :=
    (by decide : ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13],
      b < 19 ∧ (AtPublicFiles.KeyBook.fullFirst[b]?).map (·.2) = some 0) b hb
  exact ⟨playsS_of _ _ (plays_quiet₁ scope hs.named (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) rfl b h1),
    behindS_of _ _ (behind₁ Xs N Pl L w₀ rc x hs scope b h2),
    exchangeS_of _ _ (exchange_of_nil _ h3),
    ridesPastS_of _ _ (ridesPast₁ Xs N Pl L w₀ rc x hG b h2),
    acceptedS_of _ _ (acceptedQuiet Xs N Pl L w₀ rc x hs scope fall b h4.1 h4.2)⟩

/-- **Four of the five at the two layers of rows**: all but the exchange. -/
theorem fourLayer (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hG : ReadsL L.base.h₁)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [5, 11],
      PlaysS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        BehindS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        RidesPastS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said b ∧
        AcceptedS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said fall b := by
  intro b hb
  have h1 : b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14] :=
    (by decide : ∀ b ∈ [5, 11], b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14]) b hb
  have h2 : b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18] :=
    (by decide : ∀ b ∈ [5, 11], b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18]) b hb
  have h4 : b < 19 ∧ (AtPublicFiles.KeyBook.fullFirst[b]?).map (·.2) = some 0 :=
    (by decide : ∀ b ∈ [5, 11], b < 19 ∧ (AtPublicFiles.KeyBook.fullFirst[b]?).map (·.2) = some 0) b hb
  exact ⟨playsS_of _ _ (plays_quiet₁ scope hs.named (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) rfl b h1),
    behindS_of _ _ (behind₁ Xs N Pl L w₀ rc x hs scope b h2),
    ridesPastS_of _ _ (ridesPast₁ Xs N Pl L w₀ rc x hG b h2),
    acceptedS_of _ _ (acceptedQuiet Xs N Pl L w₀ rc x hs scope fall b h4.1 h4.2)⟩

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi) {Z : PublicFiles}

/-- The filling's reading reads no ledger of a message. -/
theorem readsL_fillH : ReadsL (fillH Xs N Pl K f Q x).base.h₁ :=
  Johnson.RunOne.KeyRows1.readsL_h₁ (baseH (AtPublicFiles.KeyThread.one₀ Xs)) fun _ _ _ _ => rfl

/-- The five at the eight quiet members, at Th. -/
theorem fiveQuiet_Th (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13],
      PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
        ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b ∧ RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
        AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall b :=
  fiveQuiet Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope (readsL_fillH Xs N Pl K f Q x) Said fall

/-- Four of the five at the two layers, at Th. -/
theorem fourLayer_Th (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [5, 11],
      PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
        RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
        AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall b :=
  fourLayer Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope (readsL_fillH Xs N Pl K f Q x) Said fall

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.acceptedQuiet
#print axioms AtPublicFiles.FirstH.Lots.fiveQuiet
#print axioms AtPublicFiles.FirstH.Lots.fourLayer
#print axioms AtPublicFiles.FirstH.Lots.fiveQuiet_Th
#print axioms AtPublicFiles.FirstH.Lots.fourLayer_Th
