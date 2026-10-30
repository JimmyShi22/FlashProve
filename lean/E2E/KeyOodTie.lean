-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyOodTie.lean: the key of a tied input of the offline prover is the key that the committer makes of the index,
the coins and a seed at the written sizes: so a tied input is valid in the sense of `validAt`, at which `five_made`
speaks. This is the tie from `Tied` to the shared thread's letter `Vd`.

Why. The five facts on the committed table and the key (`FiveFields`) are debts under `valid`; they may not be laid
into it. `valid` only says which instance: the key is the committer's, at a seed. `Tied` gives that of the library's
sample; the library's `keys_seed` says that this sample's key is `oodAt`.

Main names.
  `seedBack`: the library's seed, typed at the written shape. `seedAs_back`: `seedAs` undoes it.
  `key_of_sample`: the key of the sample at the two readers is `oodAt` at the written shape.
  `validAt_of_sample`: that key is valid at the key's public part, where the sizes are the written ones.
  `validAt_of_tied`: so is the key of a tied input.

What stays open. `hk`: the key sizes are the written ones: `sized_sourced` in scope. The index and the coins are read by
`readF`, `readG`, which are the written value's. That the thread's `Vd` is this sentence is for the caller to lay.

No law over coins: the seed is a letter.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStoredTie
import E2E.OfflineAtParts
import Johnson.Bind.ForProver.SeedAtFull
import Johnson.Bind.ForProver.SevenReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyOodTie
open OnBytes (TableKey)
open OnBytes.Slice (frS frZ keyOf NZ)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.Desc.Key (Source LaterPlaces keyInstanceOfOutOfDomainSample)
open Lk6.AtPlan (keyFull)
open Bind.Column (shFull agree_full)
open Bind.ForProver (Seed seedAs cube_full keys_seed spell oodAt oodSh validAt shapeOf
  shapeOfIndex entryOfPub entryAtF linOf recAt_readers)
open AtPublicFiles.Key (cellsReader stored_written)
open AtPublicFiles.KeyStoredTie (readF readG index_written)
open AtPublicFiles.KeyFiveFields (pubKey linOf_pubKey)
open AtPublicFiles.AtFiles (FullSizeMatrix Cz TiedOffline)
open AtPublicFiles.Committed (AZ PadZ holdZ keyAt)
open AtPublicFiles.Committed (pads_nonempty)
open AtPublicFiles.KeyFile (KeyParts keyProver)

local instance (priority := high) instNonemptyPadZKeyOodTie : Nonempty PadZ := pads_nonempty frS 402653181

/-- The library's seed, typed at the written shape. -/
def seedBack (e : frZ.D) : Seed shFull :=
  fun a => (fun t => (e a).1 (Fin.cast cube_full t), (e a).2)

/-- `seedAs` undoes it. -/
theorem seedAs_back (e : frZ.D) : seedAs cube_full (seedBack e) = e := by
  funext a
  apply Prod.ext
  · funext t
    simp [seedAs, seedBack]
  · rfl

variable (Z : VerifierAndGoals.PublicFiles) (i : FullSizeMatrix) (r : (Cz Z).Pad × (Cz Z).Rnd) (e : (Cz Z).Seed)

set_option maxHeartbeats 4000000 in
/-- **The key of the sample at the two readers is `oodAt` at the written shape.** -/
theorem key_of_sample :
    keyAt (AtPublicFiles.Committed.recAt (AZ Z) PadZ (holdZ Z) i r e) =
      oodAt shFull (entryAtF numsRef.kLo numsRef.rows frS.P.v (cellsReader i)) (readG r 0)
        (spell shFull (seedBack e)) := by
  have k := congrArg Prod.fst (keys_seed (entryAtF numsRef.kLo numsRef.rows frS.P.v (cellsReader i))
    (readG r 0) (readG r 0) (seedBack e) (seedBack e))
  rw [seedAs_back] at k
  have s := Bind.ForProver.recOf_readers (Zs := frZ) (cut := 402653181) (N := numsRef)
    (VerifiableInference.OnPublicFiles.ppAtFiles (VerifierAndGoals.asDescriptionFiles Z).pol (VerifierAndGoals.asDescriptionFiles Z).KL) Subtype.val
    (AtPublicFiles.AtFiles.filesAt Z) (FlashProve.dataAtFiles FlashProve.flashProveData Z).P agree_full
    (OnBytes.Flat.full_fits.1 : numsRef.rows * 2 ^ numsRef.kLo ≤ 402653181) i r e
  have q : (AtPublicFiles.AtFiles.protocolAtFiles Z).recOf i r e = (e, AtPublicFiles.Committed.ansAt (AZ Z) PadZ (holdZ Z) i r e) := by
    rw [AtPublicFiles.Committed.ansAt_eq]
    exact AtPublicFiles.AtFiles.validT_obj (AtPublicFiles.Committed.Cf (AZ Z) PadZ (holdZ Z)) (AtPublicFiles.AtFiles.filesAt Z)
      (FlashProve.dataAtFiles FlashProve.flashProveData Z).P (i, r, e) _
      (AtPublicFiles.AtFiles.valid_has (AtPublicFiles.AtFiles.protocolAtFiles Z) (i, r, e))
  refine Eq.trans ?_ k
  have step : keyAt (AtPublicFiles.Committed.recAt (AZ Z) PadZ (holdZ Z) i r e) =
      keyAt ((AtPublicFiles.AtFiles.protocolAtFiles Z).recOf i r e) := congrArg keyAt q.symm
  refine step.trans ?_
  show keyOf (fun β : NZ => β.val) _ = keyOf (fun β : NZ => β.val) _
  exact congrArg (keyOf (fun β : NZ => β.val)) s.symm

/-- **That key is valid at the key's public part, at the written sizes.** -/
theorem validAt_of_sample (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains)
    (hk : c.made.sized.key = keyFull) :
    validAt (shapeOf (pubKey Z₀ c)) (pubKey Z₀ c)
      ⟨readF i, readG r, keyAt (AtPublicFiles.Committed.recAt (AZ Z) PadZ (holdZ Z) i r e)⟩ := by
  have hs : shapeOf (pubKey Z₀ c) = shFull := by
    show shapeOfIndex c.made.sized.key.once.shape.fold.index = shFull
    rw [hk]
    exact index_written
  have e₁ : (linOf (pubKey Z₀ c)).kLo = numsRef.kLo := by
    rw [linOf_pubKey, hk, stored_written.2.1]
    rfl
  have e₂ : (linOf (pubKey Z₀ c)).matrixRows = numsRef.rows := by
    rw [linOf_pubKey, hk, stored_written.1]
    rfl
  have e₃ : shFull.v = frS.P.v := by decide +kernel
  have he : entryOfPub (pubKey Z₀ c) (readF i) =
      entryAtF numsRef.kLo numsRef.rows frS.P.v (cellsReader i) := by
    unfold entryOfPub
    rw [e₁, e₂, hs, e₃]
    rfl
  have main : ∀ sh, sh = shFull → validAt sh (pubKey Z₀ c)
      ⟨readF i, readG r, keyAt (AtPublicFiles.Committed.recAt (AZ Z) PadZ (holdZ Z) i r e)⟩ := by
    rintro _ rfl
    refine ⟨(seedBack e, 0), ?_⟩
    show _ = oodAt shFull (entryOfPub (pubKey Z₀ c) (readF i)) (readG r 0)
      (spell shFull (seedBack e))
    rw [he]
    exact key_of_sample Z i r e
  exact main _ hs

/-- **The key of a tied input is valid.** -/
theorem validAt_of_tied {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {Q₂ Q₃ X₀ Xh Wk : Type}
    [Nonempty Q₂] [Inhabited Q₃] {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray}
    {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk} {ok : FullSizeMatrix → Prop}
    {w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed} {x : AtPublicFiles.AtFiles.KeyInst}
    (hKey : (keyProver K).key = fun y => y.key)
    (ht : TiedOffline Z X N P val₂ val₃ K ok w x) (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains)
    (hk : c.made.sized.key = keyFull) :
    validAt (shapeOf (pubKey Z₀ c)) (pubKey Z₀ c) ⟨readF w.1, readG w.2.1, x.key⟩ := by
  have key := ht.key (Classical.arbitrary Q₂) default
  rw [hKey] at key
  have hv := validAt_of_sample Z w.1 w.2.1 w.2.2 Z₀ c hk
  have e' : keyAt (AtPublicFiles.Committed.recAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 w.2.2) = x.key := key
  rw [e'] at hv
  exact hv

end AtPublicFiles.KeyOodTie

#print axioms AtPublicFiles.KeyOodTie.seedAs_back
#print axioms AtPublicFiles.KeyOodTie.key_of_sample
#print axioms AtPublicFiles.KeyOodTie.validAt_of_sample
#print axioms AtPublicFiles.KeyOodTie.validAt_of_tied
