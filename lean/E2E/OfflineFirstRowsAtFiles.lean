-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFirstRowsAtFiles.lean: what E2E/OfflineFirstRowsGood.lean and E2E/OfflineOwedSix.lean prove of six rows
of the offline prover's first chain, said in the terms in which the fields good and owed of OwedRest
(E2E/OfflineClauses.lean) ask it: at the public files, a description d, the value's senders
(senderValue d), the offline file's book (offlineProverCoinCounts) and the rows offlineRowsAt d offlineProverCoinCounts S c
(E2E/OfflineRowsAtFiles.lean).

  GoodFirst d S c               the first conjunct of the field good, its text to the letter.
  GoodFirstButRanges d S c      the same with one premise laid in: L.place ≠ rngPlace.
  goodFirst_of                  the second, and the clause at the row of the test on the ranges, give
                                the first.
  first_rows_at_files           GoodFirstButRanges at S := laidSimulators (senderValue d) T, whatever the
                                ten lists T, under SendingPositions, where d's three parts are sourced
                                (KeySourced) at SOME public files Z in scope: Z is a letter of its own,
                                as in owns_at (E2E/OfflineClauses.lean), beside the letter files of
                                senderValue, offlineRowsAt and the committer's coins.
  first_rows_where_live         the same under the premises of offline_clauses: the public files' test
                                says yes, scope, d is the files' description, KeySourced at the files.
  lookup_members_at_files       A TEST OF EMPTINESS: the two lookups' sides have 935 and 920 members.
  owed_first_six_at_files       the first conjunct of what the field owed concludes, with the same premise
                                on the place, at every S, under SixLetters, at a run that has returned.

Calls alone, of first_share, lookup_members_at_value and owed_first_six_at_value: senderValue d is
offlineValue …, which is valueAt … at the two places of the shared tests, by abbreviations; the book
is carried by offlineBook_eq.

Limits. Those of the called files. NOT the row of the test on the ranges, nor the conjuncts on the shared
and the last chain, nor the field runs: OwedRest is not shown here. This file does not import
E2E/OfflineClauses.lean: that GoodFirst is that field's first conjunct, and that owed_first_six_at_files
concludes owed's first conjunct but for the place, is seen by holding the texts side by side, not by
Lean. SendingPositions and SixLetters are premises on the letters c. Nothing on any property.
-/
import E2E.OfflineFirstRowsGood
import E2E.OfflineOwedSix
import E2E.OfflineLookupMembers
import E2E.OfflineRowsAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace rngPlace)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {files : PublicFiles}

/-! ## The field good -/

/-- **The first conjunct of OwedRest.good.** -/
def GoodFirst (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ L ∈ G.first, (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
      F.first.blocksInOrder (orderOf F) 0 0 G.falls₁

/-- **The same but for the test on the ranges.** -/
def GoodFirstButRanges (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ L ∈ G.first, L.place ≠ rngPlace → (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
      F.first.blocksInOrder (orderOf F) 0 0 G.falls₁

/-- The six rows and the seventh give the conjunct. -/
theorem goodFirst_of {d : OfflineDescription} {S : OfflineSimulators}
    {c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit}
    (six : GoodFirstButRanges (files := files) d S c)
    (ranges : ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.first, L.place = rngPlace →
      (L.withField 0 0 (keyFileDescription d.source d.numbers d.later).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription d.source d.numbers d.later) 0) .own
        (keyFileDescription d.source d.numbers d.later).first.blocksInOrder
        (orderOf (keyFileDescription d.source d.numbers d.later)) 0 0
        (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.falls₁) :
    GoodFirst (files := files) d S c := fun L hL =>
  if h : L.place = rngPlace then ranges L hL h else six L hL h

/-- **It holds at the laid simulators.** -/
theorem first_rows_at_files {Z : PublicFiles} (d : OfflineDescription)
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (hc : SendingPositions (senderValue (files := files) d) c) :
    GoodFirstButRanges (files := files) d (laidSimulators (senderValue (files := files) d) T) c := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact first_share _ d.source d.numbers d.later _ _ _ _ _ _ _ _ 0 hs scope hK (offlineBook_eq hK) T c hc

/-- **Under the premises of offline_clauses.** -/
theorem first_rows_where_live (_live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (scope : InScope files = true) (d : OfflineDescription)
    (_hd : offlineDescription files = .ok d) (hs : KeySourced files d.source d.numbers d.later)
    (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (hc : SendingPositions (senderValue (files := files) d) c) :
    GoodFirstButRanges (files := files) d (laidSimulators (senderValue (files := files) d) T) c :=
  first_rows_at_files d hs scope T c hc

/-- **A TEST OF EMPTINESS: the two lookups' sides have 935 and 920 members.** -/
theorem lookup_members_at_files (d : OfflineDescription)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.first, ∀ σ,
      (L.withField 0 0 (keyFileDescription d.source d.numbers d.later).first.blocksInOrder [] 0).side
        (keyFileDescription d.source d.numbers d.later).first.blocksInOrder [] = some σ →
      (L.place = lookPlace 0 → σ.members.length = 935) ∧
        (L.place = lookPlace 1 → σ.members.length = 920) :=
  lookup_members_at_value _ _ _ _ _ _ _ _ _ _ _ _ _ hs scope S c

/-! ## The field owed -/

/-- **owedAt at every row of the first chain but the test on the ranges**, at a run that has
returned. -/
theorem owed_first_six_at_files (d : OfflineDescription)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    {S : OfflineSimulators}
    {c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit}
    (hc : SixLetters (senderValue (files := files) d) c)
    {H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit} {w₀ : FullSizeMatrix}
    {rc : (protocolAtFiles files).EncodingRandomness} {x : AtPublicFiles.KeyFile.KeyInst} {k : Coins offlineProverCoinCounts} {ρ : Draws}
    {r : RunC (keyFileDescription d.source d.numbers d.later)}
    (hρ : ρ.due (keyFileDescription d.source d.numbers d.later) = true)
    (h : runC (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
      ((offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H) w₀ rc x k ρ = .ok r) :
    ∀ L ∈ (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.first, L.place ≠ rngPlace →
      L.owedAt (keyFileDescription d.source d.numbers d.later).first.blocksInOrder k 0
        (fun a => orRefused (midAtW (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts
          ((offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact owed_first_six_at_value _ _ _ _ _ _ _ _ _ _ _ _ _ hs scope hK (offlineBook_eq hK) hc hρ h _

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.goodFirst_of
#print axioms AtPublicFiles.OfflineRows.first_rows_at_files
#print axioms AtPublicFiles.OfflineRows.first_rows_where_live
#print axioms AtPublicFiles.OfflineRows.lookup_members_at_files
#print axioms AtPublicFiles.OfflineRows.owed_first_six_at_files
