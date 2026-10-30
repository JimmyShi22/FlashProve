-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
Johnson/Desc/ProofFile/Honest/K3/Key/SeatedWalkAtAnyNumberOfParts.lean: what the verifier's hearing does on what the lookup's
seated row plays, AT ANY NUMBER OF PARTS OF KEYS. Honest/K3/Law/Top.lean has it at a face with one part (`seated_walk`,
`HeardInner`, `LeftInner`); a key file's lookup has twelve. Here the same sentences with no premise on the parts, over
Honest/K3/Parts/LookHeard.lean and LookLeft.lean, and then AT THE ROW WITH A LETTER FOR THE OWNERS (`proverSideOfLookupInChain`,
Honest/K3/RowOwned.lean), which is what the key file's prover lays. Theorems with proofs.

  `seatedWalkAtAnyNumberOfParts`    where the seated row's play returns, from a ledger with room in front: there is a course
                                    with the row's coins; the hearing returns on what was played; what it heard is the
                                    run's, with its points; the invariant holds behind the last stage; and, if the
                                    summands are `Lawful` at that course, `Left`
  `behindYesAtAnyNumberOfParts`     so `BehindYes` (Honest/K3/Law/Joined.lean) wherever the hearing has returned
  `ownedSeatedWalk`                 the first at the owned row's steps, at the coins `plainOf` (Honest/K3/Parts/OwnedPlays.lean)

By what. `rowPlaysSeated` (Honest/K3/Law/RowSeated.lean), which is general in the face; `lookHeardP`, `lookLeft_ofP`; `hb`
(Honest/K3/Law/HBPaid.lean); `steps_owned`.

Limits. The verifier's side is the kind's own texts `hearV` and `planesV`, not the step of a seated sub-protocol. `Left` is
conditional on `Lawful`. That a book lends the row its coins is another file's.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.LookLeft
import Johnson.Desc.ProofFile.Honest.K3.Parts.OwnedPlays
import Johnson.Desc.ProofFile.Honest.K3.Law.HBPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.Joined

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Key
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.K3 (HeardV hearV)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (lookHeardP lookLeft_ofP plainOf steps_owned)

variable {W W₁ X₁ V₁ : Type}

/-- **What the verifier's hearing does on what the seated row plays, at any number of parts of keys.** -/
theorem seatedWalkAtAnyNumberOfParts (lookup : At) (jobs : LookJobs W) (wit : W₁ → W) (name : String)
    (view : Option V₁) (entries : List Fmt.Entry) (mid : Mid W₁ X₁) (draws : List Fmt.Drawn)
    (coins : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts)
    (first : Nat) (front : Fork) (played : List Played × Mid W₁ X₁) (stands : Stands lookup entries mid draws)
    (ledger : LedgerIn lookup.face first front)
    (plays : play (seatSteps lookup jobs wit name view entries coins) draws [] mid = .ok played) :
    ∃ stageCoins : (s : Stage) → StageCoins lookup s,
      CoinsAre (V := Unit) (courseAt lookup jobs first wit mid draws stageCoins)
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ jobs lookup) coins) ∧
      ∃ heard behind, hearV lookup.face front (roundsOf played.1) = some (heard, behind) ∧
        HeardIs (courseAt lookup jobs first wit mid draws stageCoins) heard ∧
        PointsAgree lookup.face heard lookup.base (mid.st.heard ++ draws) ∧
        Inv (courseAt lookup jobs first wit mid draws stageCoins) (stages lookup.face).length behind ∧
        ∀ (planes : List (E × E) → GE) (keys : Nat → Array E → GE),
          Lawful (courseAt lookup jobs first wit mid draws stageCoins) planes keys →
          Left (courseAt lookup jobs first wit mid draws stageCoins) planes keys heard behind := by
  obtain ⟨c', hc, hplay⟩ := rowPlaysSeated V₁ W₁ X₁ W
    (courseAt lookup jobs first wit mid draws (courseCoins lookup fun _ _ _ => 0)) wit mid.st name view entries
    mid.loc coins rfl
  obtain ⟨y', x, hy', hx, hyx, _, _⟩ := hplay (fit_of_stands stands jobs first wit _) stands.entries []
  have e : y' = played := Except.ok.inj (hy'.symm.trans plays)
  subst e
  subst hyx
  have hF := fit_of_stands stands jobs first wit c'
  have hx' : (courseAt lookup jobs first wit mid draws c').rounds = some (roundsOf y'.1) := hx
  obtain ⟨g, G, hh, hH, hI, _, h1, h2, P⟩ := lookHeardP (stageStep hb) (leavesStep hb)
    (courseAt lookup jobs first wit mid draws c') front (roundsOf y'.1) hF (inv0_of ledger) hx'
  exact ⟨c', hc, g, G, hh, hH, P, hI, fun planes keys hLaw =>
    lookLeft_ofP _ planes keys G g hF hH hI h1 h2 P hLaw⟩

/-- **`BehindYes` at any number of parts of keys**, wherever the hearing has returned on what was played. -/
theorem behindYesAtAnyNumberOfParts (lookup : At) (jobs : LookJobs W) (wit : W₁ → W) (name : String)
    (view : Option V₁) (entries : List Fmt.Entry) (mid : Mid W₁ X₁) (draws : List Fmt.Drawn)
    (coins : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts)
    (first : Nat) (front behind : Fork) (played : List Played × Mid W₁ X₁) (heard : HeardV)
    (stands : Stands lookup entries mid draws) (ledger : LedgerIn lookup.face first front)
    (plays : play (seatSteps lookup jobs wit name view entries coins) draws [] mid = .ok played)
    (hearing : hearV lookup.face front (roundsOf played.1) = some (heard, behind)) :
    BehindYes lookup jobs first wit mid draws coins heard behind := by
  obtain ⟨c', hc, g', G', hh', hH, P, hI, hLeft⟩ := seatedWalkAtAnyNumberOfParts lookup jobs wit name view entries
    mid draws coins first front played stands ledger plays
  rw [hearing] at hh'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh')
  exact ⟨c', hc, hH, P, hI, hLeft⟩

/-- **The same at the row with a letter for the owners**: its steps are the elder row's at the coins `plainOf`. -/
theorem ownedSeatedWalk (owners : Owners) (lookup : At) (jobs : LookJobs W) (wit : W₁ → W) (name : String)
    (view : Option V₁) (entries : List Fmt.Entry) (mid : Mid W₁ X₁) (draws : List Fmt.Drawn)
    (coins : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts)
    (first : Nat) (front : Fork) (played : List Played × Mid W₁ X₁) (stands : Stands lookup entries mid draws)
    (ledger : LedgerIn lookup.face first front)
    (plays : play (rowSteps name lookup.place view
      (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts 0
      (entries.map fun e => (declOf e, ([] : List Oracle))) coins) draws [] mid = .ok played) :
    ∃ heard behind, hearV lookup.face front (roundsOf played.1) = some (heard, behind) ∧
      BehindYes lookup jobs first wit mid draws (plainOf owners ⟨ptsOf, pointsAt⟩ jobs wit lookup coins) heard
        behind := by
  rw [steps_owned] at plays
  obtain ⟨c', hc, g, G, hh, hH, P, hI, hLeft⟩ := seatedWalkAtAnyNumberOfParts lookup jobs wit name view entries mid
    draws (plainOf owners ⟨ptsOf, pointsAt⟩ jobs wit lookup coins) first front played stands ledger plays
  exact ⟨g, G, hh, c', hc, hH, P, hI, hLeft⟩

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.seatedWalkAtAnyNumberOfParts
#print axioms ProofFile.Honest.K3.Key.behindYesAtAnyNumberOfParts
#print axioms ProofFile.Honest.K3.Key.ownedSeatedWalk
