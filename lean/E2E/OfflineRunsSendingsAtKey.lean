-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRunsSendingsAtKey.lean: three of the thirteen fields of `KeyOthersPlay` (E2E/OfflineRunsKey.lean), in
the fields' own type: `indexMasks`, `multiplicities`, `messageW`: `PlaysAtFirst` at the places of the three
sendings of the key file's first chain.

  `sendings_plays_at_first`            at letters K that bear the first chain's places and whose three jobs are
                                       the key file's own; every book, every input of the run
  `sendings_plays_at_first_at_value`   at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean)

By E2E/OfflineRunsSendings.lean's `sendings_blockPlays`. Limits: those of that file: the lending is
`BlockPlays`' own premise and is not shown here. Nothing on any property.
-/
import E2E.OfflineRunsKey
import E2E.OfflineRunsSendings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (idxPlace msgPlace wPlace)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-- **The three sendings' fields of `KeyOthersPlay`.** -/
theorem sendings_plays_at_first {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums}
    {Pl : LaterPlaces} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (f : W₀ → Weights) (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs) (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs)
    (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N) (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own idxPlace ∧
      PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own msgPlace ∧
      PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own wPlace :=
  ⟨fun _ b hj hp => sendings_blockPlays hs scope Bk f K hA hi hm hw b (List.mem_of_getElem? hj)
      (Or.inl hp) _,
    fun _ b hj hp => sendings_blockPlays hs scope Bk f K hA hi hm hw b (List.mem_of_getElem? hj)
      (Or.inr (Or.inl hp)) _,
    fun _ b hj hp => sendings_blockPlays hs scope Bk f K hA hi hm hw b (List.mem_of_getElem? hj)
      (Or.inr (Or.inr hp)) _⟩

/-- **The same at the offline prover's own senders.** -/
theorem sendings_plays_at_first_at_value {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK)
    (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (f : W₀ → Weights)
    (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀) (pU pO : P12)
    (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
    {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtFirst (keyFileDescription Xs N Pl) Bk
        (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) own idxPlace ∧
      PlaysAtFirst (keyFileDescription Xs N Pl) Bk
        (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) own msgPlace ∧
      PlaysAtFirst (keyFileDescription Xs N Pl) Bk
        (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) own wPlace :=
  sendings_plays_at_first hs scope Bk f _
    (value_bears_places K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl rfl rfl own

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.sendings_plays_at_first
#print axioms AtPublicFiles.OfflineRows.sendings_plays_at_first_at_value
