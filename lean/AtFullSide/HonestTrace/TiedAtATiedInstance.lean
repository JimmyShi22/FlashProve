-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/TiedAtATiedInstance.lean

No property of the protocol is claimed. One theorem, two calls.

THE FIELD "tied" OF "ThreadFields" AT AN INSTANCE THAT THE COMPLETENESS STATEMENT's RELATION TIES. "TiedYes … n w x" (E2E/BridgeJoinAtFiles.lean) says
that x is what "instanceAsPlainRecord" writes for a request of Yes at the index w.1 with the out-of-domain sample of the private input w. By "tiedYes_plain"
(AtFullSide/Honest/InstanceTie.lean) that sample is "recAt" at the plain readers of w.1 and w.2.1; by "tied_at_the_online_coins"
(TiedAtTheCommittersSample.lean) the run of the BASE prover at the index w.1 and the coins "tableCoins files w.2.1" is tied. These are the letters at which
the base road reads "ready": g := id, rd := tableCoins files.

Limits: those of TiedAtTheCommittersSample.lean, the library's bar on "validAt" among them: nothing on hiding follows. That "ready" returns is a premise. The
outer prover Hp, its sides G and the book B of "TiedYes" are letters: of the relation the first clause alone is read.
Everything here stands at a return of the maker with coins of the type IndexCommitterCoins, the base filling's.
The online prover of E2E/TheHonestProver.lean is made at that filling read through a map of the
coins: another type of coins and another return. Nothing here crosses to it.
-/
import AtFullSide.HonestTrace.TiedAtTheCommittersSample
import AtFullSide.Honest.InstanceTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open AtPublicFiles.Key (cellsReader)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles WZ TiedYes descZ tiedYes_plain)
open LPFD.Full (XF)
open VerifiableInference.Desc (Chain)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (tableCoins)
open AtFullSide.Honest (TiedAtRun)

/-- **The field "tied" at a tied instance**, at the base prover's run at the index and the online map of the coins. -/
theorem tied_at_a_tied_instance {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (H : HeadAtReturn files A) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (weightsAre : ∀ M : FullSizeMatrix, reads.weights M = ⟨cellsReader M⟩)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
    (run₃ : R₃ → ByteArray) {Tr X₀ X' : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles files).EncodingRandomness OnBytes.TableKey Tr X₀ X')
    (Hp : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst OnBytes.TableKey Tr X₀ X')
    {Yes : FullSizeMatrix → XF → Prop} {n : ℕ} {w : WZ files} {x : ProofFile.Inst}
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp Yes n w x) {k : Coins A.B}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H w.1 (tableCoins files w.2.1) x k = .ok R) :
    TiedAtRun (A := A) reads R.own R.common := by
  obtain ⟨x', -, rfl⟩ := tiedYes_plain files Zp Np cF run₂ run₃ B G Hp tied
  exact tied_at_the_online_coins H reads weightsAre returns

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.tied_at_a_tied_instance
