-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
Johnson/Desc/ProofFile/Honest/K3/Key/OwnedLookupBehindTheMove.lean: AT ANY THREAD, ANY TYPE OF STATE AND ANY NUMBER OF PARTS OF
KEYS: what stands behind the prover's side of a step at a lookup whose half is the row with a letter for the owners
(`proverSideOfLookupInChain`). From the seven under which that row plays (`K3PlaysAtO`, E2E/KeyLookupOwned.lean), the thread's sentence
in front and the move (`Thread.Moved`, Honest/Thread/Pays.lean), from any ledger with room in front: the book has lent the
row its coins; no column is read; the verifier's hearing `hearV` returns on what was played; and `BehindYes`
(Honest/K3/Law/Joined.lean) holds at the coins `plainOf`: what was heard is the run's, with its points, and `Left` under
`Lawful`. One lemma, one theorem, with proofs.

  `ownedStepsAtTheEntries`      the owned seat's steps at a member whose place is the lookup's and whose rounds and oracle
                                messages are those of the planner's entries
  `ownedLookupBehindTheMove`    **the theorem**

Limits. The verifier's side is the kind's own text `hearV`: that a seated sub-protocol's own step lays what `hearV` heard is
said for the key file in E2E/Lookup/Key/LookupStepLaysTheHearingAtTheKey.lean. The count `first` and the ledger `front` are free
letters: no state is read. `Left` is conditional on `Lawful`. It holds also where the thread stands at nothing.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Key.SeatedWalkAtAnyNumberOfParts
import E2E.KeyLookupOwned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Key
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Oracle OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr
open ProofFile.Honest.K3.Parts (plainOf)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb Wj : Type}

/-- The owned seat's steps at a member whose place is the lookup's and whose rounds and oracle messages are those of the
planner's entries. -/
theorem ownedStepsAtTheEntries (owners : Owners) (lookup : At) (jobs : LookJobs Wj) (wit : W → Wj)
    (view : Option V) (entries : List Fmt.Entry) (block : Block S Cl) (place : block.place = lookup.place)
    (rounds : block.rounds = entries.map declOf) (oracles : block.oracles = entries.map fun _ => [])
    (coins : RowCoins (proverSideOfLookupInChain (V₁ := V) (X₁ := X) owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts) :
    (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).steps block view coins =
      rowSteps block.name lookup.place view (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts 0
        (entries.map fun e => (declOf e, ([] : List Oracle))) coins := by
  show rowSteps block.name block.place view _ 0 (block.rounds.zip block.oracles) coins =
    rowSteps block.name lookup.place view _ 0 (entries.map fun e => (declOf e, ([] : List Oracle))) coins
  rw [place, rounds, oracles, List.zip_map']

/-- **BEHIND THE PROVER's SIDE OF A STEP AT A LOOKUP, AT ANY THREAD**: the lending, the hearing's return and `BehindYes`. -/
theorem ownedLookupBehindTheMove {T : Thread Bk S Cl V W X Pb} {owners : Owners} {b : Nat} {lookup : At}
    {jobs : LookJobs Wj} {wit : W → Wj} {entries : List Fmt.Entry}
    (seven : K3PlaysAtO T owners b lookup jobs wit entries) {block : Block S Cl} (member : T.bs[b]? = some block)
    {k : Coins Bk} {s : S} {mid : Mid W X} {env : Env} {draws : List Fmt.Drawn} {played : List Played × Mid W X}
    {columns : List OpenedColumn} (stands : Thr T b k s mid env) (drawn : drawsFit block.rounds draws = true)
    (moved : T.Moved block k mid env draws played columns) (first : Nat) (front : Fork)
    (ledger : LedgerIn lookup.face first front) :
    columns = [] ∧
      ∃ coins : RowCoins (proverSideOfLookupInChain (V₁ := V) (X₁ := X) owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts,
        lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) block.place
          (proverSideOfLookupInChain (V₁ := V) (X₁ := X) owners ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts 0 = .ok coins ∧
        ∃ heard behind, hearV lookup.face front (roundsOf played.1) = some (heard, behind) ∧
          BehindYes lookup jobs first wit mid draws (plainOf owners ⟨ptsOf, pointsAt⟩ jobs wit lookup coins) heard
            behind := by
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := moved
  obtain ⟨_, _, c, hlend, rfl⟩ := chainSteps_one Bk _ _ _ block T.hs _ (seven.half block member) l hl
  have hSt : Stands lookup entries mid draws :=
    ⟨seven.ok, (Thread.heard_length T stands.2.1).trans seven.base.symm, seven.entries,
      by rw [← seven.rounds block member]; exact drawn⟩
  have hc0 : columns = [] := by
    rw [seven.rounds block member, readsOf_plain] at hc
    exact (Except.ok.inj hc).symm
  rw [ownedStepsAtTheEntries owners lookup jobs wit _ entries block (seven.place block member)
    (seven.rounds block member) (seven.oracles block member) c] at hy
  obtain ⟨heard, behind, hh, hB⟩ := ownedSeatedWalk owners lookup jobs wit block.name _ entries mid draws c first
    front played hSt ledger hy
  exact ⟨hc0, c, hlend, heard, behind, hh, hB⟩

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.ownedStepsAtTheEntries
#print axioms ProofFile.Honest.K3.Key.ownedLookupBehindTheMove
