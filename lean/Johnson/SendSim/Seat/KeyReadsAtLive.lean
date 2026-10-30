-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/KeyReadsAtLive.lean: in the goals' scope, wherever the key file's makers
return, the public test on queried positions accepts at the three sub-protocols of the kind K1 in
the key file's first chain; and where also the library's gate accepts, the makers return, the
description passes its tests on the plan and the three jobs fit.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". There the description is the proof
file's; here it is the key file's Key.descriptionFromSource. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. P is any public files with VerifierAndGoals.InScope P = true.
  Spec.keyReadsAt P  The statement on the test. For every hash function o: if publicOfO, Key.madeAt
                     at the constant Key.fixedDigest, Key.sourceOf, Key.rangesNumbers and
                     Key.laterPlaces return X₀, m, X, N and Q at P's files, then keyReadsB (Key.descriptionFromSource
                     X N Q) (keyPars X) = true (KeyReadsAtWritten.lean).
  keyReads_in_scope  Spec.keyReadsAt P holds.
  Spec.keyAt P       The statement at files at which the gate accepts. publicOfO, Key.madeAt and
                     Key.descAt return at OnBytes.secondHashFunction; what Key.descAt returns is Key.descriptionFromSource X N Q,
                     and its run is the one that the library's verifier asks; it passes its tests on
                     the plan; keyPars X has three entries, at the three places; each fits its place
                     (sendFits); and keyReadsB accepts. It does not hold the returns of
                     Key.sourceOf, Key.rangesNumbers and Key.laterPlaces; keyMakers_of_live does.
  keyAt_of_live      Spec.keyAt P holds if also FlashProve.protocolDataWellFormed (asDescriptionFiles P) = true.
                     keyMakers_of_live: where the gate accepts, all five makers return, with the
                     description, its run and its tests on the plan; a caller takes the returns from
                     it.
  bud_of_keyReads    At any source and numbers: where keyReadsB accepts, our clause of the rule's
                     premise on queried positions (BudClause, Bud.lean) holds at every job with the
                     description's public numbers at one of the three places.
  keyPins_in_scope   In scope, where the makers return, the source and the numbers have the
                     library's written full-size values (Pins, Johnson/HB/LLHARD/KB4/Pins.lean). Its
                     proof is that of the library's key_planOk_in_scope (RowInScope.lean there) as
                     far as Pins.

How it fits. With fieldsAtKey_all (AtKey.lean), which holds at every source and numbers, these give
at the verifier's own key file's description: the three jobs fit, the sides have fits and exact, the
positions read are within the bound that is a premise inside exact and fresh, and fresh holds at
every book that is clear (BookClearAny). keyMakers_of_live follows the library's kseat_name
(Johnson/Goal/Description/KeySeat.lean) and keeps three returns that kseat_name drops; keyAt_of_live
is proved through it. The side library proves that the gate accepts at named files
(AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean). Statements on public data: no distribution is
named. Meant as steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder
derives index privacy from them. Not one of the release's goal statements.

Limits. The premise on the book is not touched. Among the files that this folder imports there is no
honest prover of a key file in the framework of Johnson/Desc/ProofFile/Honest/ (parts at the
description's places). Three of the key file's sendings. The count is of one execution of the key
file's description. At a constant in the place of the public files' digest (Key.fixedDigest). That
the makers return, or that the gate accepts, at given files is not shown here. All limits of
AtKey.lean and KeyReadsAtWritten.lean.
-/
import Johnson.SendSim.Seat.KeyReadsAtWritten
import Johnson.SendSim.Seat.AtKeyStands
import Johnson.SendSim.Seat.FitsAtKey
import Johnson.SendSim.Seat.LotsTestTie
import Johnson.SendSim.Seat.ReadsTestTie
import Johnson.HB.LLHARD.KB4.RowInScope
import Johnson.Goal.Description.KeySeat

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference
open VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.G.OfPlan (Made)
open OnBytes.Model.Verify (Public chainsOf chainsOf_parts)
open Johnson.KB4 (Pins pins_of_made chainPins_of decl_of_source toldKeyFull)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

/-- In the goals' scope, where the key file's makers return, the source and the numbers have the
library's written full-size values. -/
theorem keyPins_in_scope {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {m : Made}
    {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces} (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) (r1 : Key.sourceOf m = .ok X)
    (r2 : Key.rangesNumbers m = .ok N) (r3 : Key.laterPlaces m = .ok P) : Pins X N P := by
  obtain ⟨-, hch, ⟨e, hse⟩, -, hz, c1, c2, c3, hY⟩ := IM.keyPins_at_made hZ hX hm
  obtain ⟨hs, pk, p1, p2, p3, hread⟩ := IM.keyPlans_at_made hZ hX hm
  obtain ⟨links, shapes, -, hcf, -, -⟩ := chainsOf_parts hch
  obtain ⟨b1, b2, -⟩ := _root_.AtFull.KeyBack.four_at_scope hZ hX hm Key.fixedDigest_size
  have hb₁ : m.p.chains.made.keyOneTime.size < 2 ^ 64 := Nat.lt_trans b1 (by norm_num)
  have hb₂ : m.p.chains.made.keyShared.size < 2 ^ 64 := Nat.lt_trans b2 (by norm_num)
  obtain ⟨i1, i2, i3, -, i4, i5, i6, i7⟩ :=
    Johnson.KB9.items_at_made hcf Key.fixedDigest_size hb₁ hb₂ hread hz
  have hD : X.Y.D = declKeyFull := Johnson.AtFull.KeyBack.decl_at_return hZ hX hm r1
  have hT : Key.toldOfMade m = .ok toldKeyFull :=
    Johnson.AtFull.KeyBack.toldOfMade_in_scope hZ hX hm
  have hN : N = rangesNumsFull :=
    Except.ok.inj (r2.symm.trans (Johnson.AtFull.KeyBack.rangesNumbers_in_scope hZ hX hm))
  have hP : P = laterPlacesFull :=
    Except.ok.inj (r3.symm.trans (Johnson.AtFull.KeyBack.laterPlaces_in_scope hZ hX hm))
  exact pins_of_made r1 ((decl_of_source r1).trans (congrArg Except.ok hD)) hT hz hs c1 c2 c3 i1 i2
    i3 i4 i5 i6 i7 p1 p2 p3 pk hN hP

/-- The statement at public files P. Statement only; proved as keyReads_in_scope below, for P in the
goals' scope. Wherever the key file's makers return at P, the public test on queried positions
accepts at the three sub-protocols of the kind K1 in the first chain of the key file's description.
-/
def Spec.keyReadsAt (P : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (o : ℕ → ByteArray → ByteArray) (X₀ : Public) (m : Made) (X : Key.Source)
    (N : H2U.PlaceNums) (Q : Key.LaterPlaces),
    PlanWritten.publicOfO o P.pol P.KL (some P.lay) = .ok X₀ →
    Key.madeAt X₀ P.lay Key.fixedDigest = .ok m → Key.sourceOf m = .ok X →
    Key.rangesNumbers m = .ok N → Key.laterPlaces m = .ok Q →
    keyReadsB (Key.descriptionFromSource X N Q) (keyPars X) = true

/-- **Spec.keyReadsAt P holds at all public files P in the goals' scope.** -/
theorem keyReads_in_scope {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true) : Spec.keyReadsAt P :=
  fun _ _ _ _ _ _ hX hm r1 r2 r3 =>
    keyReads_of_pins (chainPins_of (keyPins_in_scope hS hX hm r1 r2 r3))

/-- Where the test accepts, our clause of the rule's premise on queried positions holds at every job
with the description's public numbers at one of the three places. -/
theorem bud_of_keyReads {V W X Pb : Type} (Xs : Key.Source) (N : H2U.PlaceNums)
    (Q : Key.LaterPlaces) (h : keyReadsB (Key.descriptionFromSource Xs N Q) (keyPars Xs) = true)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) (J : SendJob W X) (hP : J.P = x.1) :
    BudClause (V := V) (Pb := Pb) (Key.descriptionFromSource Xs N Q) J.P.place J :=
  budClause_of_light _ _ J fun pre b t hF hb => by
    have h1 : readsWithinB (Key.descriptionFromSource Xs N Q) J.P (treesOf (Key.descriptionFromSource Xs N Q).first.blocksInOrder
                         ((Key.descriptionFromSource Xs N Q).first.blocksInOrder.takeWhile (·.place != J.P.place))) = true := by
      rw [hP]
      exact List.all_eq_true.1 h x hx
    have hn := key_places_apart Xs N Q
    have h2 : (Key.descriptionFromSource Xs N Q).first.blocksInOrder.takeWhile (·.place != J.P.place) = pre := by
      rw [hF] at hn ⊢
      rw [← hb]
      exact takeWhile_split (·.place) pre b t hn
    rw [h2] at h1
    exact h1

/-- The statement at public files P. Statement only; proved as keyAt_of_live below, under two tests
on P. Three of the key file's makers return (publicOfO, Key.madeAt, Key.descAt); the description
Key.descriptionFromSource X N Q that they give is the one whose run the library's verifier asks; it passes its tests
on the plan; keyPars X has its three entries, at the three places; each of the three fits its place;
and the public test on queried positions accepts at the three. -/
def Spec.keyAt (P : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (X₀ : Public) (m : Made) (X : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces),
    PlanWritten.publicOfO OnBytes.secondHashFunction P.pol P.KL (some P.lay) = .ok X₀ ∧
    Key.madeAt X₀ P.lay Key.fixedDigest = .ok m ∧
    Key.descAt X₀ P.lay Key.fixedDigest = .ok (Key.descriptionFromSource X N Q) ∧
    FlashProve.theKeyRun (VerifierAndGoals.asDescriptionFiles P) = ((Key.descriptionFromSource X N Q).pull Key.keyInstanceOfOutOfDomainSample).run ∧
    (Key.descriptionFromSource X N Q).planOk = true ∧
    (keyPars X).map (·.1.place) = [⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, none, 14, .K1⟩] ∧
    (∀ x ∈ keyPars X, sendFits x.1 x.2 = true) ∧
    keyReadsB (Key.descriptionFromSource X N Q) (keyPars X) = true

/-- Where the library's gate accepts, all five makers of the key file return at the earlier hash
function; Key.descriptionFromSource X N Q is what Key.descAt returns; its run is the one that the library's verifier
asks; and it passes its tests on the plan. It follows the library's kseat_name and keeps the three
returns that kseat_name drops, so that a caller can reach keyPins_in_scope. -/
theorem keyMakers_of_live {P : VerifierAndGoals.PublicFiles} (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) :
    ∃ (X₀ : Public) (m : Made) (X : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces),
      PlanWritten.publicOfO OnBytes.secondHashFunction P.pol P.KL (some P.lay) = .ok X₀ ∧
      Key.madeAt X₀ P.lay Key.fixedDigest = .ok m ∧ Key.sourceOf m = .ok X ∧
      Key.rangesNumbers m = .ok N ∧ Key.laterPlaces m = .ok Q ∧
      Key.descAt X₀ P.lay Key.fixedDigest = .ok (Key.descriptionFromSource X N Q) ∧
      FlashProve.theKeyRun (VerifierAndGoals.asDescriptionFiles P) = ((Key.descriptionFromSource X N Q).pull Key.keyInstanceOfOutOfDomainSample).run ∧
      (Key.descriptionFromSource X N Q).planOk = true := by
  obtain ⟨K, _, _, hK, _, _⟩ := FlashProve.theLive_made (VerifierAndGoals.asDescriptionFiles P) hL
  obtain ⟨D, r⟩ := K
  have hK' : (PlanWritten.publicOfO OnBytes.secondHashFunction P.pol P.KL (some P.lay)).bind
      (fun X => Key.keyDataAndDecisionAtFixedDigest X P.lay) = .ok (D, r) := hK
  cases hX : PlanWritten.publicOfO OnBytes.secondHashFunction P.pol P.KL (some P.lay) with
  | error e => rw [hX] at hK'; cases hK'
  | ok X₀ =>
    rw [hX] at hK'
    obtain ⟨m, X, N, Q, hm, r1, r2, r3, h0, h1, -, -, -, -, h6⟩ :=
      Key.laidFixed_is X₀ P.lay D r hK'
    refine ⟨X₀, m, X, N, Q, rfl, hm, r1, r2, r3, h0, ?_, h1⟩
    rw [FlashProve.theKeyRun_ok hK]
    exact h6

/-- **Spec.keyAt P holds at all public files P that are in the goals' scope and at which the
library's gate accepts.** -/
theorem keyAt_of_live {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) : Spec.keyAt P := by
  obtain ⟨X₀, m, X, N, Q, hX, hm, r1, r2, r3, h0, h6, h1⟩ := keyMakers_of_live hL
  have hp := chainPins_of (keyPins_in_scope hS hX hm r1 r2 r3)
  refine ⟨X₀, m, X, N, Q, hX, hm, h0, h6, h1, ?_, fits_at_key X N Q h1, keyReads_of_pins hp⟩
  rw [keyPars_written hp]
  exact keyParsW_places

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.keyPins_in_scope
#print axioms OnBytes.SendSim.Seat.keyReads_in_scope
#print axioms OnBytes.SendSim.Seat.bud_of_keyReads
#print axioms OnBytes.SendSim.Seat.keyMakers_of_live
#print axioms OnBytes.SendSim.Seat.keyAt_of_live
