-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/TiedAtTheCommittersSample.lean   (in the side library: "TiedAtRun" lies there)

No property of the protocol is claimed. Theorems alone, by calls of the library's laws on the committer's key.

THE FIELD "tied : TiedAtRun reads R.own R.common" OF "ThreadFields" (AtFullSide/Honest/ThreadsAtTheTerm.lean), AT A RUN WHOSE INSTANCE HOLDS THE
COMMITTER's OWN OUT-OF-DOMAIN SAMPLE. "TiedAtRun" has two clauses: (typed) the instance's public part is a typed instance's; (key) where the index
is in range, the run's key is one that the committer makes of the index and the coins at some seed ("Bind.ForProver.validAt").
BY READING, NOT BY A THEOREM: the second clause cannot be expected at every record and all coins: it ties the record in the instance to the run's own index
and coins (the run's key is what "instanceAsPlainRecord" writes of the record). So it is stated where the instance is "instanceAsPlainRecord (x', recAt frS frZ shFull ‹the matrix's plain entries› (rc 0) e)": the form in which a tied instance of the
completeness statement is told in the base prover's terms ("tiedYes_plain", AtFullSide/Honest/InstanceTie.lean).

* "key_of_the_committers_sample": under "ShapeAtFull Zp": the key that "instanceAsPlainRecord" writes of that sample is "oodSh (shapeOf Zp) Zp" at the matrix's reader,
  the coins and the seed typed back: "validAt". By "keyOf_recAt" (KeyOfRecAt.lean), "oodAt_atFull", "seedBack" (SeedBack.lean).
* "tied_at_the_committers_sample": the field, at every return of the maker over the matrices with coins IndexCommitterCoins, every head at it, every readers whose
  weights are the matrix's reader, where "ready" returns.
* "tied_at_the_online_coins": the same at rc := tableCoins files ρ and the sample at the plain coins of ρ: the letters of "tiedYes_plain".

Limits. That "ready" returns is a premise. The seed e is a letter: that it is sampled, or of what, is not said. THE LIBRARY's OWN LIMIT ON THE COINS
GOES WITH IT (Johnson/Bind/ForProver/FiveAt.lean, "validAt"; FiveFieldsAt.lean, "A limit on the coins"): under "validAt", at a fixed index and key,
the pads that the answers read are no coins: NOT TO BE LAID IN FRONT OF A LAW OVER COINS: nothing on hiding follows from this file.
Everything here stands at a return of the maker with coins of the type IndexCommitterCoins, the base filling's.
The online prover of E2E/TheHonestProver.lean is made at that filling read through a map of the
coins: another type of coins and another return. Nothing here crosses to it.
-/
import AtFullSide.Honest.ThreadsAtTheTerm
import Johnson.Bind.ForProver.KeyOfRecAt
import Johnson.Bind.ForProver.SeedBack
import Johnson.Bind.ForProver.InScope
import Johnson.Bind.ForProver.FiveAt
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open OnBytes.Slice (frS frZ)
open VerifiableInference.OnPublicFiles (numsRef)
open Bind.ForProver (validAt shapeOf recAt entryAtF ShapeAtFull seedBack cube_full)
open Bind.Column (shFull)
open AtPublicFiles.Key (cellsReader padReader tailReader)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open LPFD.Full (XF instanceAsPlainRecord)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (tableCoins)
open AtFullSide.Honest (TiedAtRun)

/-- The plain entries of a matrix, at the full size. -/
abbrev plainEntries (M : FullSizeMatrix) : ℕ → ℕ → UInt64 :=
  entryAtF numsRef.kLo numsRef.rows frS.P.v (cellsReader M)

/-- **The key that "instanceAsPlainRecord" writes of the committer's own sample is the committer's key**, at the matrix's reader, the coins and the seed. -/
theorem key_of_the_committers_sample (Zp : ProofFile.Pub) (full : ShapeAtFull Zp) (M : FullSizeMatrix) (rc : IndexCommitterCoins)
    (e : frZ.D) (x' : XF) :
    validAt (shapeOf Zp) Zp
      ⟨⟨cellsReader M⟩, rc, (instanceAsPlainRecord (x', recAt frS frZ shFull (plainEntries M) (rc 0) e)).pub.key⟩ := by
  rw [full.1]
  refine ⟨(seedBack cube_full e, 0), ?_⟩
  show OnBytes.Slice.keyOf (fun β : OnBytes.Slice.NZ => β.val)
      (recAt frS frZ shFull (plainEntries M) (rc 0) e) =
    Bind.ForProver.oodAt shFull (Bind.ForProver.entryOfPub Zp ⟨cellsReader M⟩) (rc 0)
      (Bind.ForProver.spell shFull (seedBack cube_full e))
  rw [Bind.ForProver.oodAt_atFull Zp full (cellsReader M) (rc 0) cube_full e]
  exact congrArg Prod.fst (Bind.ForProver.keys_ours (plainEntries M) (rc 0) (rc 0) e e)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The field "tied" where the instance holds the committer's own sample.** -/
theorem tied_at_the_committers_sample (H : HeadAtReturn files A) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (weightsAre : ∀ M : FullSizeMatrix, reads.weights M = ⟨cellsReader M⟩) {M : FullSizeMatrix} {rc : IndexCommitterCoins} {e : frZ.D}
    {x' : XF} {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H M rc
      (instanceAsPlainRecord (x', recAt frS frZ shFull (plainEntries M) (rc 0) e)) k = .ok R) :
    TiedAtRun (A := A) reads R.own R.common := by
  obtain ⟨-, tr, -, own, common, -⟩ := ready_ok returns
  refine ⟨⟨(x', recAt frS frZ shFull (plainEntries M) (rc 0) e), by rw [own]⟩, fun _ => ?_⟩
  rw [common]
  show validAt (shapeOf A.Z) A.Z ⟨reads.weights M, rc, A.H.key _⟩
  rw [key_at_return H, weightsAre]
  exact key_of_the_committers_sample A.Z
    (Bind.ForProver.shapeAtFull_inScope H.head.scope H.head.laid.pub) M rc e x'

/-- **The same at the online prover's map of the coins**: the letters in which a tied instance is told in the base prover's terms. -/
theorem tied_at_the_online_coins (H : HeadAtReturn files A) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (weightsAre : ∀ M : FullSizeMatrix, reads.weights M = ⟨cellsReader M⟩) {M : FullSizeMatrix} {ρ : (protocolAtFiles files).EncodingRandomness}
    {e : frZ.D} {x' : XF} {k : Coins A.B}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H M (tableCoins files ρ)
      (instanceAsPlainRecord (x', recAt frS frZ shFull (plainEntries M)
                       ⟨padReader (S := frS) (cut := 402653181) ρ.1, tailReader (S := frS) ρ.2⟩ e)) k = .ok R) :
    TiedAtRun (A := A) reads R.own R.common :=
  tied_at_the_committers_sample H reads weightsAre (rc := tableCoins files ρ) returns

end HonestTraceRun.Meets

#check @HonestTraceRun.Meets.tied_at_the_committers_sample
#print axioms HonestTraceRun.Meets.key_of_the_committers_sample
#print axioms HonestTraceRun.Meets.tied_at_the_committers_sample
#print axioms HonestTraceRun.Meets.tied_at_the_online_coins
