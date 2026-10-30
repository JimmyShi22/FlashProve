-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinRunStruck.lean: THE JOIN's FIELD «run» (TheLots, E2E/OfflineJoin.lean) WITH SEVEN OF ITS TEN CLAUSES PAID: what
a run owes (AtRunS, E2E/KeyAcceptPairs.lean) at the offline prover's own senders and the written book, at every input
that is tied (TiedOffline itself, ok := inRange) and every coin, FROM THE DOOR's THREE CLAUSES.

PAID: (1) okStart: okStart_of_tied (E2E/KeyOkStart.lean) · (2) ready returns · (3) the plan serves · (4) the
first chain begins · (6) its letter at the start: runFromLeft (E2E/LotJoinRun.lean) · (5) the shared chain begins ·
(7) its letter at the start: shared_at_start (E2E/KeySharedDebts.lean), which speaks of this prover because the
offline prover's senders ARE keyOf at every public part (prover_is_keyOf, E2E/KeyArgumentsAt.lean: by unfolding).
LEFT, the fields of LeftDoor, in AtRunS's own words: (8) DoorBehindS, at every R that ready returns · (9) DoorYesS ·
(10) FinYesS.

  LeftDoor      what is left, at one input and coin: a premise's form
  runFromDoor   THE FIELD

The letters. U₁, S₁: as in E2E/LotJoinRun.lean. U₂ := threadAt …, S₂ := walkedLetter … (E2E/KeyStandWalked.lean) at the
offline prover's own senders, the index's reader and the table's coins: the bodies of the join's sharedThread and
sharedSaid. ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀, U₃, S₃ and Q stay letters.
Premises. The test on the public files says yes; offlineDescription returns d; scope; fullPub = some K₀ · hQ: Q.Rel is
the committer's relation at the range · hV: Vd holds at a tied input's shared input · hPin: the meaning's pinT holds
everywhere (as shared_at_start asks it).
[Inhabited Q₃] IS DATA, not a side condition: the frame's Tied reads «default» in its clause on the seam. The join lays
«Inhabited RunValue := ⟨fun _ => 0⟩»: a caller must lay the same term (E2E/LotJoinRunFits.lean does).
Limits. AN IMPLICATION. runFromBehind (E2E/LotJoinRunDoor.lean) builds a member of LeftDoor inside its proof, from the clause «behind the door»; no theorem states it. hV and hPin are premises on letters: at
Vd := fun _ => True and at a meaning whose pinT is True they hold by their text; what else the shared thread reads of
Mg₀ is not said here. All that
the heads of E2E/LotJoinRun.lean and E2E/LotReadyWhole.lean say goes with it. Nothing on soundness, completeness,
hiding or binding.
-/
import E2E.LotJoinRun
import E2E.LotTiedIsTied
import E2E.KeyOkStart
import E2E.KeySharedDebts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open OnBytes (TableKey)
open AtPublicFiles.KeyLink (CoinOne AtRunS)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles TiedOffline relKeyZ)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue threadAt walkedLetter)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open ProofFile.Honest.Term (matrixInput tableCoins)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens)

variable {Z : PublicFiles} {K₀ : KeyPub} {Q₂ Q₃ : Type} (d : OfflineDescription)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (U₂ : Thread (keyBook K₀) (keyFileDescription d.source d.numbers d.later).S₂
    (keyFileDescription d.source d.numbers d.later).Cl Empty (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit TableKey)
  (U₃ : Thread (keyBook K₀) (keyFileDescription d.source d.numbers d.later).S₃
    (keyFileDescription d.source d.numbers d.later).Cl (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit)
    Unit Xi)
  (S₂ : Nat → Coins (keyBook K₀) → Mid (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit → Prop)
  (S₃ : Nat → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **WHAT IS LEFT OF A RUN's DEBTS: THE DOOR's THREE CLAUSES**, at one input and coin, in AtRunS's own words. A premise's
form. -/
structure LeftDoor (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) (c : CoinOne (keyBook K₀) Q₂ Q₃) :
    Prop where
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
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open OnBytes (TableKey)
open AtPublicFiles.KeyLink (CoinOne AtRunS)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles TiedOffline relKeyZ)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue threadAt walkedLetter)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open ProofFile.Honest.Term (matrixInput tableCoins)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens)

variable {Z : PublicFiles} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃] {d : OfflineDescription}
  {Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness} (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray)
  {P₁ Wt : Type} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (U₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₃ (keyFileDescription d.source d.numbers d.later).Cl
    (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
  (S₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **THE FIELD run, from the door's three clauses.** -/
theorem runFromDoor (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hQ : Q.Rel = relKeyZ Z AtPublicFiles.AtFiles.inRange)
    (hV : ∀ w x, TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
      AtPublicFiles.AtFiles.inRange w x → Vd (inK w.1 w.2.1 x))
    (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (left : ∀ w x (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
        AtPublicFiles.AtFiles.inRange w x →
      LeftDoor d Q
        (threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd
          matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (U₃ w x)
        (walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
          Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (S₃ w x) w x c) :
    ∀ w x (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
        AtPublicFiles.AtFiles.inRange w x →
      AtRunS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
        (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
        (threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd
          matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (U₃ w x)
        (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1
          x)
        (walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
          Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (S₃ w x) w x c := by
  have hs : KeySourced Z d.source d.numbers d.later :=
    AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok live hd
  refine runFromLeft
    (fun w x => TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
      AtPublicFiles.AtFiles.inRange w x)
    (fun w x => threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest
      Kp Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) U₃
    (fun w x => walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt
      rest Kp Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) S₃ live hd scope hK ?_ ?_ ?_
  · intro w x t
    rw [hQ]
    exact t.rel
  · intro w x t
    exact AtPublicFiles.OfflineRows.Lots.inRange_of_tied t
  · intro w x c t
    have L := left w x c t
    refine ⟨AtPublicFiles.AtFiles.okStart_of_tied hs.named scope t, fun R hR => ?_, fun R hR => ?_,
      L.doorBehind, L.doorYes, L.finYes⟩
    · exact (AtPublicFiles.KeySharedDebts.shared_at_start d.source d.numbers d.later K₀
        (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1
        x hR (hV w x t) hPin).1
    · exact (AtPublicFiles.KeySharedDebts.shared_at_start d.source d.numbers d.later K₀
        (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1
        x hR (hV w x t) hPin).2

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.runFromDoor
