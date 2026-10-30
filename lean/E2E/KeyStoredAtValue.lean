-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStoredAtValue.lean: the stored table of the offline prover at the written value is the committer's columns at
the item 0, where the key's sizes are the written ones. `stored_key` (E2E/KeyStoredTie.lean), at `storedColumn` and
`partsOfDescription` (E2E/KeyArgumentsAt.lean).

Main names.
  `storedColumn_key`: `storedColumn` at the two readers is the format's encoder at the item 0, nothing at another.
  `stored_at_description`: the offline prover at a description has these columns.
  `stored_at_parts`: the same at `thePartsAt`, where the public files make that description.
  `encZ_is_cmKey`: these are the columns of the key file's committer.

What stays open. The premise `hk`: the description's key sizes are the written ones: `sized_sourced` in scope. Nothing
here says that any other field of the prover is the committer's.

No statement here is a law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStoredTie
import E2E.KeyArgumentsAt
import E2E.KeyTied

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyStoredTie
open OnBytes.Slice (frS)
open VerifiableInference.OnPublicFiles (numsRef)
open Lk6.AtPlan (keyFull)
open Bind.Column (shFull agree_full)
open Bind.ForProver (shapeOfIndex)
open AtPublicFiles.Key (stored_written)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.Committed (AZ PadZ holdZ Coin pads_nonempty)
open AtPublicFiles.KeyFiveFields (rows_full)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription partsOfDescription thePartsAt
  thePartsAt_of storedColumn Parts)

local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/-- **`storedColumn` at the two readers is the format's encoder at the item 0.** -/
theorem storedColumn_key (Z : VerifierAndGoals.PublicFiles) (c : OnBytes.Model.Verify.Chains)
    (hk : c.made.sized.key = keyFull) (i : FullSizeMatrix) (r : Coin (AZ Z) PadZ (holdZ Z)) (it x : ℕ) :
    storedColumn c (readF i) (readG r) it x = if it == 0 then encZ Z i r x else none := by
  have hfit : Bind.ForProver.rowsFit (shapeOfIndex keyFull.once.shape.fold.index)
      keyFull.once.shape.kLo keyFull.once.shape.matrixRows = true := rows_full
  have e₁ : keyFull.once.shape.kLo = numsRef.kLo := by
    rw [stored_written.2.1]
    rfl
  have e₂ : keyFull.once.shape.matrixRows = numsRef.rows := by
    rw [stored_written.1]
    rfl
  have e₃ : shFull.v = frS.P.v := by decide +kernel
  unfold storedColumn
  rw [hk]
  by_cases h0 : it = 0
  · subst h0
    rw [if_pos ⟨rfl, hfit⟩, index_written, e₁, e₂, e₃, if_pos (by decide)]
    unfold encZ
    by_cases h : x < 2 ^ frS.P.T.a
    · rw [dif_pos h]
      exact encAt_readers Z i r x h
    · rw [dif_neg h]
      exact if_neg (by rw [agree_full.a]; exact h)
  · rw [if_neg (by simp [h0]), if_neg (by simpa using h0)]

/-- The format's encoder at the item 0 is the key file's committer's columns: one text. -/
theorem encZ_is_cmKey (Z : VerifierAndGoals.PublicFiles) (i : FullSizeMatrix) (r : Coin (AZ Z) PadZ (holdZ Z)) (x : ℕ) :
    encZ Z i r x = (AtPublicFiles.AtFiles.cmKeyZ Z).enc i r x := rfl

/-- **The offline prover's stored columns at a description.** -/
theorem stored_at_description {files : VerifierAndGoals.PublicFiles} (description : OfflineDescription)
    (hk : description.source.chains.made.sized.key = keyFull) (i : FullSizeMatrix)
    (r : Coin (AZ files) PadZ (holdZ files)) (it x : ℕ) :
    ((partsOfDescription (files := files) description).prover description).stored i r it x =
      if it == 0 then encZ files i r x else none :=
  storedColumn_key files description.source.chains hk i r it x

/-- **The same at `thePartsAt`.** -/
theorem stored_at_parts {files : VerifierAndGoals.PublicFiles} {description : OfflineDescription}
    (h : offlineDescription files = .ok description)
    (hk : description.source.chains.made.sized.key = keyFull) (i : FullSizeMatrix)
    (r : Coin (AZ files) PadZ (holdZ files)) (it x : ℕ) :
    ((thePartsAt files).prover description).stored i r it x =
      if it == 0 then encZ files i r x else none := by
  rw [thePartsAt_of h]
  exact stored_at_description description hk i r it x

end AtPublicFiles.KeyStoredTie

#print axioms AtPublicFiles.KeyStoredTie.storedColumn_key
#print axioms AtPublicFiles.KeyStoredTie.stored_at_description
#print axioms AtPublicFiles.KeyStoredTie.stored_at_parts
#print axioms AtPublicFiles.KeyStoredTie.encZ_is_cmKey
