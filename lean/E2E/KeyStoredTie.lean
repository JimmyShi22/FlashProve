-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStoredTie.lean: the stored table of the key file's prover, as `keyOf` lays it, is the format's encoder at
the item 0, at the two readers of the index and of the committer's coins, where the key's sizes are the written
ones. It is a conditional on that one equation of sizes.

Why. `keyOf` (E2E/KeyStandMember.lean) lays `encW`, the column of the stand-in committer at two letters f, g.
The index committer of the key file's object reads the format's encoder at a matrix of cells, pads and tails
(`cmAt`, E2E/TiedAtFiles.lean). A prover that is to stand beside that committer must lay the same columns. So the
letters have to be the plain readers of the committer's own input: `readF`, `readG`.

Main names.
  `readF`, `readG`: the index's reader and the coins' reader: `cellsReader`, `padReader`, `tailReader`
    (E2E/KeyReaders.lean) at the matrix, the pads and the tails.
  `encZ`: the field `enc` of `cmAt`, written out; `enc_is_cmAt` says that it is that field.
  `index_written`: the committer's shape at the key's written index is `Bind.Column.shFull`: a closed question
    put to Lean's kernel.
  `encAt_readers`: below 2^a the column of `Bind.ForProver.encAt` at the readers is `colF`.
  `encW_key`: `encW` at `pubKey` and the readers is `encZ` at the item 0, and nothing at another item.
  `stored_key`: so `keyProver` at `keyOf` and the readers has these stored columns, at every `K'`.

What stays open. The premise `hk`: the key's sizes at the chains are the written ones: in scope that is
`sized_sourced` (E2E/KeyPublic.lean). Of a cell the first coordinate alone is read, on both sides. Nothing says
that any other field of the prover is the committer's; the key, the rows that a sending reads and the tails of
`rowsOf` are not spoken of here. Nothing says that the pads or tails are drawn as a law over coins asks.

No premise here ties a letter to a coin: `hk` is on public values. The statements hold at every matrix and all
coins. No law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandMember
import E2E.KeyStoredRows
import E2E.TiedAtFiles
import Johnson.Bind.ColumnSizes
import Johnson.Bind.ForProver.ExtIsStrAt
import Johnson.Bind.ForProver.SevenReaders
import Johnson.Flat.ClaimsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyStoredTie
open ProofFile.Honest (Weights TableRand)
open OnBytes.Slice (frS frZ GF ofF toF_ofF)
open OnBytes.Flat (PadsOf)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open Lk6.AtPlan (keyFull)
open Bind.Column (shFull agree_full)
open Bind.ForProver (encW entryAtF shapeOf shapeOfIndex linOf strAt strAt_apply strAt_readers)
open AtPublicFiles.Key (cellsReader padReader tailReader stored_written)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.Committed (AZ PadZ holdZ Coin colF enc_col cmAt pads_nonempty)
open AtPublicFiles.KeyFiveFields (pubKey linOf_pubKey rows_full)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyStandMember (keyOf)

/- The search for this instance runs out of its budget among these imports, as at E2E/BridgeExact.lean. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/-- The index's reader: the matrix of cells, read by plain numbers. -/
def readF (i : FullSizeMatrix) : Weights := ⟨cellsReader i⟩

/-- The coins' reader at every item: the pads and the tails, read by plain numbers. -/
def readG (r : PadZ × (Fin (2 ^ frS.P.v) → Fin frS.P.T.r → GF)) (_ : ℕ) : TableRand :=
  ⟨padReader (S := frS) (cut := 402653181) r.1, tailReader (S := frS) r.2⟩

/-- The field `enc` of the index committer at the format's encoder, written out. -/
def encZ (Z : VerifierAndGoals.PublicFiles) (i : FullSizeMatrix) (r : Coin (AZ Z) PadZ (holdZ Z)) (p : ℕ) : Option (List GF) :=
  if h : p < 2 ^ frS.P.T.a then some (colF (AZ Z) PadZ (holdZ Z) i r ⟨p, h⟩) else none

/-- It is that field, at every builder of the explicit input. -/
theorem enc_is_cmAt {Xi Ky : Type} (Z : VerifierAndGoals.PublicFiles) (wr : LPFD.Full.XF × OnBytes.Flat.RecFull → Xi)
    (key : Xi → Ky) (kp : OnBytes.Flat.RecFull → Ky) (hr : ∀ a, key (wr a) = kp a.2) :
    (cmAt (AZ Z) PadZ (holdZ Z) wr key kp hr).enc = encZ Z := rfl

/-- **The committer's shape at the key's written index is the full size's.** A closed question to Lean's kernel:
each of the six numbers can say no. -/
theorem index_written : shapeOfIndex keyFull.once.shape.fold.index = shFull := by
  decide +kernel

/-- **Below 2^a the stand-in committer's column at the readers is the format's.** -/
theorem encAt_readers (Z : VerifierAndGoals.PublicFiles) (i : FullSizeMatrix) (r : Coin (AZ Z) PadZ (holdZ Z)) (p : ℕ)
    (h : p < 2 ^ frS.P.T.a) :
    Bind.ForProver.encAt shFull (entryAtF numsRef.kLo numsRef.rows frS.P.v (readF i).entry)
        (readG r 0) p =
      some (colF (AZ Z) PadZ (holdZ Z) i r ⟨p, h⟩) := by
  have hA : p < 2 ^ shFull.a := by
    rw [agree_full.a]
    exact h
  obtain ⟨L, hL⟩ : ∃ L, Bind.ForProver.encAt shFull
      (entryAtF numsRef.kLo numsRef.rows frS.P.v (readF i).entry) (readG r 0) p = some L :=
    ⟨_, if_pos hA⟩
  have k : strAt frS shFull (entryAtF numsRef.kLo numsRef.rows frS.P.v (cellsReader i))
      ⟨padReader (S := frS) (cut := 402653181) r.1, tailReader (S := frS) r.2⟩ =
      AtPublicFiles.Committed.encAt (AZ Z) PadZ (holdZ Z) i r :=
    strAt_readers (Zs := frZ) (cut := 402653181) (N := numsRef) agree_full
      (OnBytes.Flat.full_fits.1 : numsRef.rows * 2 ^ numsRef.kLo ≤ 402653181) i r
  have k₂ := congrFun k ⟨p, h⟩
  rw [strAt_apply, enc_col] at k₂
  have k₃ : ((Bind.ForProver.encAt shFull
      (entryAtF numsRef.kLo numsRef.rows frS.P.v (readF i).entry) (readG r 0) p).getD []).map ofF =
      (colF (AZ Z) PadZ (holdZ Z) i r ⟨p, h⟩).map ofF := congrArg Prod.snd k₂
  rw [hL, Option.getD_some] at k₃
  rw [hL, List.map_injective_iff.2 (Function.LeftInverse.injective toF_ofF) k₃]

/-- **`encW` at the key's chains and the readers is the format's encoder at the item 0.** Where the key's sizes
are the written ones. -/
theorem encW_key (Z : VerifierAndGoals.PublicFiles) (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains)
    (hk : c.made.sized.key = keyFull) (i : FullSizeMatrix) (r : Coin (AZ Z) PadZ (holdZ Z)) (it x : ℕ) :
    encW (pubKey Z₀ c) (readF i) (readG r) it x = if it == 0 then encZ Z i r x else none := by
  have hs : shapeOf (pubKey Z₀ c) = shFull := by
    show shapeOfIndex c.made.sized.key.once.shape.fold.index = _
    rw [hk]
    exact index_written
  have hfit : Bind.ForProver.rowsFit (shapeOf (pubKey Z₀ c)) (linOf (pubKey Z₀ c)).kLo
      (linOf (pubKey Z₀ c)).matrixRows = true := by
    show Bind.ForProver.rowsFit (shapeOfIndex c.made.sized.key.once.shape.fold.index)
      c.made.sized.key.once.shape.kLo c.made.sized.key.once.shape.matrixRows = true
    rw [hk]
    exact rows_full
  have e₁ : (linOf (pubKey Z₀ c)).kLo = numsRef.kLo := by
    rw [linOf_pubKey, hk, stored_written.2.1]
    rfl
  have e₂ : (linOf (pubKey Z₀ c)).matrixRows = numsRef.rows := by
    rw [linOf_pubKey, hk, stored_written.1]
    rfl
  have e₃ : shFull.v = frS.P.v := by decide +kernel
  unfold encW
  by_cases h0 : it = 0
  · subst h0
    rw [if_pos ⟨rfl, hfit⟩, e₁, e₂, hs, e₃]
    rw [if_pos (by decide)]
    unfold encZ
    by_cases h : x < 2 ^ frS.P.T.a
    · rw [dif_pos h]
      exact encAt_readers Z i r x h
    · rw [dif_neg h]
      exact if_neg (by rw [agree_full.a]; exact h)
  · rw [if_neg (by simp [h0]), if_neg (by simpa using h0)]

/-- **The stored columns of the key file's prover at `keyOf` and the readers, at every `K'`.** -/
theorem stored_key {X₀ X Wk : Type} (Z : VerifierAndGoals.PublicFiles) (Z₀ : ProofFile.Pub) (Xs : Source) (Pl : LaterPlaces)
    (K' : KeyParts FullSizeMatrix (Coin (AZ Z) PadZ (holdZ Z)) X₀ X Wk) (hk : Xs.chains.made.sized.key = keyFull)
    (i : FullSizeMatrix) (r : Coin (AZ Z) PadZ (holdZ Z)) (it x : ℕ) :
    (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' readF readG)).stored i r it x =
      if it == 0 then encZ Z i r x else none :=
  encW_key Z Z₀ Xs.chains hk i r it x

end AtPublicFiles.KeyStoredTie

#print axioms AtPublicFiles.KeyStoredTie.enc_is_cmAt
#print axioms AtPublicFiles.KeyStoredTie.index_written
#print axioms AtPublicFiles.KeyStoredTie.encAt_readers
#print axioms AtPublicFiles.KeyStoredTie.encW_key
#print axioms AtPublicFiles.KeyStoredTie.stored_key
