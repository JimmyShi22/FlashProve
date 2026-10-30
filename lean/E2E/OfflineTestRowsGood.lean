-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineTestRowsGood.lean: the field `good` of `OwedRest` (E2E/OfflineClauses.lean) AT THE FOUR PROXIMITY TESTS' ROWS of the
offline file: the test on the ranges (first chain), the tests on the folded row's group and on Omega's (shared
chain), the own test (last chain). A JOIN: `Good` at these rows is `key_k12_pays_offline`
(Johnson/Desc/ProofFile/Honest/K12/Sim2/RowsOffline.lean); here it is laid in the three clauses' own text, at the muted
rows with the field beside them, place by place. Nothing is proved anew of `exact` or `fresh`.

  `ranges_test_good`, `folded_test_good`, `omega_test_good`, `own_test_good`   `goodAt` at the muted row at the place, in the form
                       of the field's first, second, second and third clause

What is laid at the four places is that file's `K12Laid`: the four lists of simulators are the rows' own, and c's letters
there are On := `OnEntry`, `OnEntry`, `OnOmegaKey`, `OnOwnTestEntry` at the row's two jobs, bud := `budBoth`.

ALL FOUR ARE CONDITIONAL ON THEIR On AT A RUN: On is not True. Whoever lays these letters takes them on at every called part
of a run (the field `owed`), of which nothing is paid here.

Premises that stay. In scope (`KeySourced`, `InScope`), at the written book (`fullPub = some Kp`, Bk = `keyBook Kp`); the senders are
`withTests Sd …` at the description's own two places and bear the sixteen places (`AtAll`); `K12Laid`.

Limits. A and B are false at a muted row, so `plays` and `acc` are vacuous. The state on entry is each job's own, not shown to be
the verifier's. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowsOffline
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyLay (withTests)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ X Wk : Type}
  (scope : InScope Z = true) (hS : KeySourced Z Xs N Pl) {Kp : KeyPub} (hKp : fullPub = some Kp)
  {Bk : ProverCoinCounts} (hB : Bk = keyBook Kp) (Sd : KeyParts W₀ Rc X₀ X Wk)
  (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF) (grp : List (List Nat)) (fst : Nat)
  (hK : (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst).AtAll) (T : TheirSimulators)
  (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X)
  (hL : K12Laid Sd ent grp fst T c)
include scope hS hKp hB hK hL

/-- **The row of the test on the ranges**, in the form of the field's first clause. -/
theorem ranges_test_good :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).mute.first,
      L.place = rngPlace →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt (earlierOf (keyFileDescription Xs N Pl) 0) .own
        (keyFileDescription Xs N Pl).first.blocksInOrder (orderOf (keyFileDescription Xs N Pl)) 0 0 [] := by
  intro L hL' hp
  obtain ⟨L', hm, rfl⟩ := List.mem_map.1 hL'
  have hp' : L'.place = rngPlace := hp
  exact goodAt_mute fun σ hσ => (key_k12_pays_offline scope hS hKp Sd ent grp fst hK T hB c hL).1 L' hm
    (by rw [hp']; rfl) σ hσ

/-- **The row of the test on the folded row's group**, in the form of the field's second clause. -/
theorem folded_test_good :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).mute.shared,
      L.place = foldedTestPlace →
      (L.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).goodAt (earlierOf (keyFileDescription Xs N Pl) 1)
        .shared (keyFileDescription Xs N Pl).shared.blocksInOrder (orderOf (keyFileDescription Xs N Pl)) 1 0 [] := by
  intro L hL' hp
  obtain ⟨L', hm, rfl⟩ := List.mem_map.1 hL'
  have hp' : L'.place = foldedTestPlace := hp
  exact goodAt_mute fun σ hσ => (key_k12_pays_offline scope hS hKp Sd ent grp fst hK T hB c hL).2.1 L'
    hm (by rw [hp']; rfl) σ hσ

/-- **The row of the test on Omega's group**, in the form of the field's second clause. -/
theorem omega_test_good :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).mute.shared,
      L.place = omegaTestPlace →
      (L.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).goodAt (earlierOf (keyFileDescription Xs N Pl) 1)
        .shared (keyFileDescription Xs N Pl).shared.blocksInOrder (orderOf (keyFileDescription Xs N Pl)) 1 0 [] := by
  intro L hL' hp
  obtain ⟨L', hm, rfl⟩ := List.mem_map.1 hL'
  have hp' : L'.place = omegaTestPlace := hp
  exact goodAt_mute fun σ hσ => (key_k12_pays_offline scope hS hKp Sd ent grp fst hK T hB c hL).2.1 L'
    hm (by rw [hp']; rfl) σ hσ

/-- **The row of the own test**, in the form of the field's third clause. -/
theorem own_test_good :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).mute.second,
      L.place = ownTestPlace → ∀ base skip,
      (L.withField 2 (keyFileDescription Xs N Pl).lastChainFirstTreeNumber (keyFileDescription Xs N Pl).second.blocksInOrder base skip).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 2) .own (keyFileDescription Xs N Pl).second.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 2 (keyFileDescription Xs N Pl).lastChainFirstTreeNumber [] := by
  intro L hL' hp base skip
  obtain ⟨L', hm, rfl⟩ := List.mem_map.1 hL'
  have hp' : L'.place = ownTestPlace := hp
  exact goodAt_mute fun σ hσ => (key_k12_pays_offline scope hS hKp Sd ent grp fst hK T hB c hL).2.2 L'
    hm (by rw [hp']; rfl) σ hσ

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.ranges_test_good
#print axioms AtPublicFiles.OfflineRows.folded_test_good
#print axioms AtPublicFiles.OfflineRows.omega_test_good
#print axioms AtPublicFiles.OfflineRows.own_test_good
