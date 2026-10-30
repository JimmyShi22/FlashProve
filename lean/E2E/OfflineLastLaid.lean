-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/OfflineLastLaid.lean: the last chain's row is laid at `keyOf` of the value: `keyOf` lays the stored
table, the readers, `lin` and `send`, and leaves `own`, so the row of `offline_second_laid` is the same.

  `second_laid_keyOf`   for `last_laid`, `hrow`: at K := keyOf … (the offline value)

Conditional on `KeySourced`, scope and `fullPub`; no premise on the lookups. Nothing on any property.
-/
import E2E.OfflineRowsAtValue
import E2E.KeyStandMember

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.AtFiles (KeySourced)
open VerifierAndGoals (PublicFiles InScope)

variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The last chain's row at `keyOf` of the value is laid.** -/
theorem second_laid_keyOf {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (Zp : ProofFile.Pub) (f' : W₀ → Weights)
    (g' : Rc → Nat → TableRand) :
    ∀ h ∈ (keyProver (AtPublicFiles.KeyStandMember.keyOf Zp Xs Pl
        (offlineValue K' Xs N Pl f g inR d ent groups first) f' g')).second,
      RowLaid (keyBook K₀) 2 h :=
  offline_second_laid K' Xs N Pl f g inR d ent groups first hs scope hK

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.second_laid_keyOf
