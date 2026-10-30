-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHPile.lean: what the batching at number 16 of the key file's first chain and W's row (Eval)
lean on, as two named sentences.

  `HeardAtKeys`: the claims on the keys that the verifier's state holds are at the points that the
    prover makes of the challenges heard.
  `CoinsAtSlots`: the mask entries that the verifier's ledger hands the batching are the coins that
    the book lends the batching's sum.

Limits. Definitions. That either holds at any value is not said here.
-/
import E2E.FirstHSeats
import Johnson.Desc.ProofFile.Honest.K13.Plays

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open VerifiableInference.Desc.Ground (takeMasksP)
open AtPublicFiles.KeyThread (D)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyValues (keyPoints oneOf)
open ProofFile.Honest
open ProofFile.Honest.K13 (proverSideOfClaimCombination)

/-- **The points of the claims on the keys.** heard: the challenges heard. s: the verifier's state. -/
def HeardAtKeys (Xs : Source) (N : H2U.PlaceNums) (heard : List Fmt.Drawn) (s : FirstState) : Prop :=
  ∀ i p, i < (oneOf Xs).ranges.lookups.length →
    p < ((oneOf Xs).ranges.lookups.getD i default).parts.length →
    keyPoints Xs N heard i p = ((s.base.keys.getD i []).getD p default).point

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **The coins of the batching's sum.** At a stand of the thread in front of the batching, at the
coins c that the book lends the batching's half, at a state whose rows the sub-protocol lays, and at
the entries t that the verifier's ledger hands out there: coin number j of the sum is the mask entry of the index masks' message under
entry number j, that message as the thread's witness holds it. -/
def CoinsAtSlots : Prop :=
  ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[16]? = some blk → ∀ k s m E,
    Thr (Th Xs N Pl K f Q w₀ rc x) 16 k s m E →
    ∀ laid, VerifiableInference.Desc.Key.layPile AtPublicFiles.AtFiles.keysAt (oneOf Xs) s = .ok laid →
    ∀ c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Unit) (X := X') K.weights K.pile K.batt).parts,
      lendRow Bk (Bk.rowsOf 0) (k.look 0) blk.place
        (proverSideOfClaimCombination (Rc := Rc) (Tr := Unit) (X := X') K.weights K.pile K.batt).parts 0 = .ok c →
      ∀ t, takeMasksP s.d s.idx (Batt.masksOf K.batt.lin.kCol) = some t →
        ∀ j, j < Batt.masksOf K.batt.lin.kCol →
          rdE.val ((coinsE c.2.1.2.1.1).getD j zeroE) =
            (Fl Xs N Pl K f Q x).msg 0 k w₀ rc [] .mask (t.1.getD j 0)

end

end AtPublicFiles.FirstH
