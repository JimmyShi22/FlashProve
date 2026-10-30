-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotPlanServesValue.lean: the three premises of the library's planServes (Honest/Law/PlanGives.lean) at the offline
prover of a description of the public files, in the goals' scope, off the five returns (E2E/LotPlanServesGround.lean).
For E2E/LotPlanServes.lean.

Main names.
  made5_of: where offlineDescription returns, its three fields are what the reader, the maker and the three functions
    return.
  rootedAll_of_rows: rootedAll_key (E2E/KeyValueHolds.lean) with the three equations on the rows in KeyNamed's place: that
    proof, from its second line on.
  storedColumn_some, stored_offline: at the written sizes the stored column at the item 0 is there below 2^32, with 2048
    entries; so at the offline prover's value.
  atAll_offline: KeyParts.AtAll at the offline prover's value, by atAll_value.

Nothing on soundness, completeness, hiding or binding. No law over coins: the index and the committer's coins are letters.
-/
import E2E.LotPlanServesGround
import E2E.KeyValueHolds
import E2E.KeyStandWalked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.LotPlanGround
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput tableCoins)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open Johnson.RunOne.Sound (rowsOf)
open Lk6.AtPlan (keyFull)
open Bind.ForProver (shapeOfIndex rowsFit)
open AtPublicFiles.KeyFile (KeyParts keyProver first_places keyProver_shared)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyValueHolds (rooted_of_rows rooted_sealed atAll_value place_p12At)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyValues (WitK matrixEntryOf multiplicitiesGroups faceAt keyBatt oneOf)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles keyFileDescription)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription offlineTestParametersOnU offlineTestOnOmega
  matrixReader storedColumn idleRecord)

/-- **Where offlineDescription returns, its fields are the five returns'.** -/
theorem made5_of {Z : VerifierAndGoals.PublicFiles} {D : OfflineDescription} (h : offlineDescription Z = .ok D) :
    Made5 Z D.source D.numbers D.later := by
  unfold offlineDescription at h
  obtain ⟨X₀, h0, h⟩ := exBind_ok h
  obtain ⟨m, hm, h⟩ := exBind_ok h
  obtain ⟨X, r1, h⟩ := exBind_ok h
  obtain ⟨N, r2, h⟩ := exBind_ok h
  obtain ⟨P, r3, h⟩ := exBind_ok h
  obtain rfl : (⟨X, N, P⟩ : OfflineDescription) = D := Except.ok.inj h
  exact ⟨X₀, m, h0, hm, r1, r2, r3⟩

section Rooted
variable {W₀ Rc X₀ X Wk : Type}

/-- **A half of keyProver K stands at every sub-protocol that sends a root**, where the three chains' rows are the written
lists. -/
theorem rootedAll_of_rows {Xs : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (r1 : rowsOf (keyFileDescription Xs N P).first.blocksInOrder = AtPublicFiles.KeyBook.fullFirst)
    (r2 : rowsOf (keyFileDescription Xs N P).shared.blocksInOrder = AtPublicFiles.KeyBook.fullShared)
    (r3 : rowsOf (keyFileDescription Xs N P).second.blocksInOrder = AtPublicFiles.KeyBook.fullSecond)
    (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll) :
    rootedAll (keyFileDescription Xs N P) (keyProver K) = true := by
  have e1 : AtPublicFiles.KeyBook.fullFirst = ([(AtPublicFiles.KeyBook.idxPlace, 2), (AtPublicFiles.KeyBook.msgPlace, 2)] ++
                AtPublicFiles.KeyBook.linkRows 0 9581 ++ AtPublicFiles.KeyBook.linkRows 1 9220 ++
                [(AtPublicFiles.KeyBook.rowsPlace, 0), (AtPublicFiles.KeyBook.rngPlace, 23), (AtPublicFiles.KeyBook.battPlace, 20),
                  (AtPublicFiles.KeyBook.wPlace, 2)]) ++ [(AtPublicFiles.KeyBook.sealPlace, 1)] := by
    decide
  have e2 : AtPublicFiles.KeyBook.fullShared = [(AtPublicFiles.KeyBook.frontPlace, 0), (AtPublicFiles.KeyBook.pointPlace, 1),
                (AtPublicFiles.KeyBook.foldedPlace, 2), (AtPublicFiles.KeyBook.gammaPlace, 0), (AtPublicFiles.KeyBook.locPlace, 1),
                (AtPublicFiles.KeyBook.omegaPlace, 2), (AtPublicFiles.KeyBook.joinsPlace, 0), (AtPublicFiles.KeyBook.zetaPlace, 1),
                (AtPublicFiles.KeyBook.splitPlace, 1), (foldedTestPlace, 35), (omegaTestPlace, 24)] ++
      [(AtPublicFiles.KeyBook.sharedSealPlace, 1)] := by decide
  have a1 : rooted (keyFileDescription Xs N P).first.blocksInOrder (keyProver K).first = true :=
    rooted_sealed _ _ _ _ (r1.trans e1) rfl (by
      rw [first_places K hK.first]
      decide)
  have a2 : rooted (keyFileDescription Xs N P).shared.blocksInOrder (keyProver K).shared = true :=
    rooted_sealed _ _ _ _ (r2.trans e2) rfl (by
      rw [keyProver_shared K hK.splits, hK.onU, hK.onOmega]
      decide)
  have a3 : rooted (keyFileDescription Xs N P).second.blocksInOrder (keyProver K).second = true :=
    rooted_of_rows _ _ _ r3 (by
      show ∀ r ∈ AtPublicFiles.KeyBook.fullSecond, r.2 = 0 ∨ (([K.own].map (·.place)).any (· == r.1)) = true
      rw [List.map_cons, List.map_nil, hK.own]
      decide)
  unfold rootedAll
  rw [a1, a2, a3]
  rfl

end Rooted

/-- **At the written sizes the stored column at the item 0 is there below 2^32, with 2048 entries.** -/
theorem storedColumn_some (chains : OnBytes.Model.Verify.Chains)
    (hk : chains.made.sized.key = keyFull) (weights : Weights) (coins : Nat → TableRand) (y : Nat)
    (hy : y < 2 ^ 32) : ∃ c, storedColumn chains weights coins 0 y = some c ∧ c.length = 2048 := by
  have hfit : rowsFit (shapeOfIndex chains.made.sized.key.once.shape.fold.index)
      chains.made.sized.key.once.shape.kLo chains.made.sized.key.once.shape.matrixRows = true := by
    rw [hk]
    exact rows_written
  unfold storedColumn
  rw [if_pos ⟨rfl, hfit⟩]
  exact column_some _ (by rw [hk]; exact a_written) (by rw [hk]; exact v_written) _ _ y hy

variable {Z : VerifierAndGoals.PublicFiles} (D : OfflineDescription)

/-- **So at the offline prover's value.** -/
theorem stored_offline (hk : D.source.chains.made.sized.key = keyFull) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness)
    (y : Nat) (hy : y < 2 ^ 32) :
    ∃ c, (keyProver (offlineValue (files := Z) D)).stored w₀ rc 0 y = some c ∧ c.length = 2048 :=
  storedColumn_some D.source.chains hk (matrixReader w₀) (tableCoins Z rc) y hy

/-- **The offline prover's value bears the sixteen places.** hW: the shape has a message W. hsp: the shape splits. -/
theorem atAll_offline (hW : (OnBytes.linMessageW (oneOf D.source).lin).isSome = true)
    (hsp : (ProofFile.Honest.K14.planData
      (AtPublicFiles.KeySharedThread.parKey D.source D.later)).S.sharedSplitNeeded = true) :
    (offlineValue (files := Z) D).AtAll :=
  atAll_value
    (fixedKeyParts (faceAt D.source 0) (keyBatt D.source) matrixInput.dummy () () idleRecord)
    D.source D.numbers D.later matrixReader (tableCoins Z) matrixInput.inRange matrixInput.dummy
    (offlineTestParametersOnU D.later) (offlineTestOnOmega D.later) (matrixEntryOf matrixReader)
    (multiplicitiesGroups D.source) 0 hW hsp (place_p12At _ _) (place_p12At _ _)

end AtPublicFiles.LotPlanGround

#print axioms AtPublicFiles.LotPlanGround.made5_of
#print axioms AtPublicFiles.LotPlanGround.rootedAll_of_rows
#print axioms AtPublicFiles.LotPlanGround.storedColumn_some
#print axioms AtPublicFiles.LotPlanGround.stored_offline
#print axioms AtPublicFiles.LotPlanGround.atAll_offline
