-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinRun.lean: THE JOIN's FIELD «run» (TheLots, E2E/OfflineJoin.lean): what a run owes (AtRunS,
E2E/KeyAcceptPairs.lean) at the offline prover's own senders and the written book, at every tied input
and every coin, FROM WHAT IS LEFT. This file does not import the join: «an input is tied» stands as a
letter Tied, of which two facts are premises.

AtRunS has ten clauses under one ∃ R. FOUR ARE PAID HERE:
  (2) ready returns           lotReadyReturnsWhole (E2E/LotReadyWhole.lean)
  (3) the plan serves         lotPlanServes (E2E/LotPlanServes.lean)
  (4) the first chain begins  entersFirst_atTerm (E2E/LotEntersFirstAtTerm.lean)
  (6) the first chain's letter at the start   lotBegunFirstAtValue (E2E/LotBegunFirst.lean)
SIX ARE LEFT, the fields of LeftRun, each in AtRunS's own words; where a clause reads R it is asked
at every R that ready returns:
  (1) okStart · (5) Enters₂ · (7) S₂ at 0 · (8) DoorBehindS · (9) DoorYesS · (10) FinYesS

  LeftRun       what is left, at one input and coin: a premise's form
  runFromLeft   THE FIELD: AtRunS at every tied input and coin

The letters. U₁ := Th … (E2E/FirstHSeat.lean) and S₁ := walkedFirst … (E2E/LotBegunFirst.lean) at the
description's three parts, the offline prover's own senders, the index's reader, the input's matrix
w.1 and committer's coins w.2.1: the bodies of joinThread and joinSaid (E2E/LotJoinFirst.lean), spelled
out so that this file need not stand over that one. U₂, S₂, U₃, S₃: letters of the join's types.
Q : LaterFill stays a letter.
Premises. The test on the public files says yes; offlineDescription returns d; scope; fullPub = some K₀.
On Tied: rel (a tied input meets Q.Rel) and range (a tied input's matrix is in range).
Limits. AN IMPLICATION. runFromDoor (E2E/LotJoinRunStruck.lean) builds a member of LeftRun inside its proof, from LeftDoor; no theorem states it. The two facts on Tied are premises:
at the join's TiedAt, with ok := inRange, they are meant to follow from Tied.rel (ok_of_tied,
E2E/LotReadyAtRunCore.lean; Q.Rel laid as the committer's relation): no theorem here says so. All that
the head of E2E/LotReadyWhole.lean says goes with clause (2). Nothing on soundness, completeness, hiding
or binding.
-/
import E2E.LotReadyWhole
import E2E.LotPlanServes
import E2E.LotEntersFirstAtTerm
import E2E.LotBegunFirst
import E2E.KeyAcceptPairs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open OnBytes (TableKey)
open AtPublicFiles.KeyLink (CoinOne AtRunS)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open ProofFile.Honest.Term (matrixInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest

variable {Z : PublicFiles} {K₀ : KeyPub} {R₂ R₃ : Type} (d : OfflineDescription)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (U₂ : Thread (keyBook K₀) (keyFileDescription d.source d.numbers d.later).S₂
    (keyFileDescription d.source d.numbers d.later).Cl Empty (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit TableKey)
  (U₃ : Thread (keyBook K₀) (keyFileDescription d.source d.numbers d.later).S₃
    (keyFileDescription d.source d.numbers d.later).Cl (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit)
    Unit Xi)
  (S₂ : Nat → Coins (keyBook K₀) → Mid (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit → Prop)
  (S₃ : Nat → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **WHAT IS LEFT OF A RUN's DEBTS**, at one input and coin: six clauses of AtRunS, in its own words. A
premise's form. -/
structure LeftRun (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) (c : CoinOne (keyBook K₀) R₂ R₃) :
    Prop where
  /-- (1) the description's test on the instance -/
  okStart : (keyFileDescription d.source d.numbers d.later).okStart x = true
  /-- (5) the shared chain begins -/
  entersShared : ∀ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
      (keyProver (offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
    Enters₂ (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d)) U₂ w.1
      w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R
  /-- (7) the shared chain's letter at the start -/
  begunShared : ∀ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
      (keyProver (offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
    S₂ 0 ⟨c.2.1.1, c.1.1, c.2.1.2⟩
      { R.start₂ (keyProver (offlineValue (files := Z) d)) with opened := some [] }
  /-- (8) behind the door -/
  doorBehind : ∀ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
      (keyProver (offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
    DoorBehindS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
      (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x) U₂ U₃
      (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
      S₂ S₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R
  /-- (9) the door says yes -/
  doorYes : DoorYesS (keyFileDescription d.source d.numbers d.later)
    (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x) U₂
    (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
    S₂ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
  /-- (10) the end says yes -/
  finYes : FinYesS (keyFileDescription d.source d.numbers d.later)
    (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x) U₂ U₃
    (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
    S₂ S₃ x ⟨c.2.1.1, c.1.1, c.2.1.2⟩

end AtPublicFiles.FirstH.Lots

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open OnBytes (TableKey)
open AtPublicFiles.KeyLink (CoinOne AtRunS)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open ProofFile.Honest.Term (matrixInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest

variable {Z : PublicFiles} {K₀ : KeyPub} {R₂ R₃ : Type} {d : OfflineDescription}
  {Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness}
  (Tied : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Prop)
  (U₂ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₂ (keyFileDescription d.source d.numbers d.later).Cl Empty
    (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit TableKey)
  (U₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₃ (keyFileDescription d.source d.numbers d.later).Cl
    (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
  (S₂ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit → Prop)
  (S₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **THE FIELD run**: what a run owes, at every tied input and every coin, from what is left. -/
theorem runFromLeft (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (hK : fullPub = some K₀)
    (rel : ∀ w x, Tied w x → Q.Rel w.1 w.2.1 x)
    (range : ∀ w x, Tied w x → matrixInput.inRange w.1 = true)
    (left : ∀ w x (c : CoinOne (keyBook K₀) R₂ R₃), Tied w x →
      LeftRun d Q (U₂ w x) (U₃ w x) (S₂ w x) (S₃ w x) w x c) :
    ∀ w x (c : CoinOne (keyBook K₀) R₂ R₃), Tied w x →
      AtRunS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
        (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
        (U₂ w x) (U₃ w x)
        (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1
          x)
        (S₂ w x) (S₃ w x) w x c := by
  intro w x c ht
  obtain ⟨R, hR⟩ := AtPublicFiles.OfflineRows.Lots.lotReadyReturnsWhole live hd scope hK w.1 w.2.1 x
    ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (range w x ht)
  have hs : KeySourced Z d.source d.numbers d.later :=
    AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok live hd
  have L := left w x c ht
  exact ⟨L.okStart, R, hR, AtPublicFiles.AtFiles.HonestTerm.Lots.lotPlanServes hd scope _ _ _ _ _ hR,
    entersFirst_atTerm d hs scope Q w.1 w.2.1 x (rel w x ht) _ R hR, L.entersShared R hR,
    lotBegunFirstAtValue (files := Z) d Q w.1 w.2.1 x _ R hR, L.begunShared R hR,
    L.doorBehind R hR, L.doorYes, L.finYes⟩

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.runFromLeft
