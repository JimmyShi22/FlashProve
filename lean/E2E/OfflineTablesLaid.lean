-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/OfflineTablesLaid.lean: the step from a stand of the last thread at border 2 to lot P3's premise
TablesAreLaid: (H) at the own test's three sources, with the thread's tables written out: `tableLast`,
`fixedLast`, `tbH`, `tbKey`.

  `tables_of_hand`   the step

Conditional on `KeySourced`, scope, `parKey = QK` by them. It holds that each table at hand is the
thread's: nothing on what the thread's tables hold. Nothing on any property.
-/
import E2E.OfflineWidthsOfTreesSentBeforeTestAt
import E2E.KeyLastAll
import E2E.KeyAsksKey
import E2E.FirstHFill
import E2E.KeyStandWalked
import E2E.LotTreesSentBeforeOwnTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens jobOmega sendPlace sendTable witOf)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState)
open _root_.Desc.K14 (St P14)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.KeyTreesKey (treesOf5)
open ProofFile.Honest.K14 (treesU)
open AtPublicFiles.KeyLastChain (seat_own place_own)
open AtPublicFiles.KeyLastChain.Lots (TablesAreLaid)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.FirstH (LaterFill)
open ProofFile.Honest.Term (tableCoins)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} {Cells M Smp Rec P₂ Wt₂ : Type} {K₀ : KeyPub} (Z₀ : ProofFile.Pub)
  (description : OfflineDescription)
  (Q : LaterFill (keyBook K₀) AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness)
  (L : KeyFill (keyBook K₀) AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₂ Wt₂)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (w₂ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey) (w₀ : AtPublicFiles.AtFiles.FullSizeMatrix)
  (rc : (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness) (x : Xi)
  (hs₁ : List (Placed (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit)
    (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit))
  (Said₁ : Nat → Coins (keyBook K₀) → Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
  (Said₂ : Nat → Coins (keyBook K₀) → Mid (Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey) Unit → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit →
    MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit → Prop)
  (w : Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit)
  (dT : Place × Table) (dM : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit)

/-- The key's parts at the value, as the last thread reads them. -/
abbrev partsAtValue :=
  AtPublicFiles.KeyStandMember.keyOf (AtPublicFiles.KeyFiveFields.pubKey Z₀ description.source.chains) description.source
    description.later (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description) matrixReader (tableCoins Z)

/-- The last thread at the value's tables, every other letter free: `lastThread` is an instance. -/
abbrev ownThread :=
  AtPublicFiles.KeyLastChain.threadOwn description.source description.numbers description.later
    (partsAtValue (Z := Z) Z₀ description) L ℓ₂ Nm Mg₂
    (AtPublicFiles.KeyAsksKey.tableKey description.source description.later K₀
      (partsAtValue (Z := Z) Z₀ description) tk tt)
    rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁
    (AtPublicFiles.FirstH.tbH description.source description.numbers description.later
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description) matrixReader Q)
    Said₁ Said₂ d Dt (AtPublicFiles.KeyLastChain.mlKey (AtPublicFiles.KeyLastChain.val₁Key description.source L))
    n₁ n₂ Vd w dT dM

set_option maxHeartbeats 4000000 in
/-- **From (H) at border 2 to `TablesAreLaid`.** -/
theorem tables_of_hand
    (hs : KeySourced Z description.source description.numbers description.later)
    (scope : InScope Z = true) (k : Coins (keyBook K₀))
    (m : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit) (E : Env)
    (hH : (ownThread Z₀ description Q L ℓ₂ Nm Mg₂ tk tt rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ Said₁ Said₂ d Dt
      n₁ n₂ Vd w dT dM).Hand 2 k m E) :
    TablesAreLaid Z description k m.st.input m.st.heard E := by
  obtain ⟨blk, hb, hseat⟩ := seat_own description.source description.numbers description.later
    (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description).idx (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description).w
    (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description).send id
    (ProofFile.Honest.K12.Light.askOf (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description).send
      (fun w => (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description).weights w.w₀)
      (fun w => AtPublicFiles.KeyFile.randK14 ((AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description).rand w.rc)))
  have hp := place_own hs scope
  have hr : blk.rounds =
      (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts H2K.Member.piKWFull :
        VerifiableInference.Desc.Block VerifiableInference.Desc.K12.T12 Unit).rounds := by
    rw [hseat.rounds]
    show (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (AtPublicFiles.KeyLay.pWK description.later) :
        VerifiableInference.Desc.Block VerifiableInference.Desc.K12.T12 Unit).rounds = _
    rw [hp]
  obtain ⟨a0, a5, a1⟩ := old_opens_there
  have hand : ∀ c j, ((VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      H2K.Member.piKWFull : VerifiableInference.Desc.Block VerifiableInference.Desc.K12.T12 Unit).rounds.flatMap
        (·.opens)).any (fun o => o.2 == .taken c j) = true →
      Fmt.TreeSource.taken c j ∈
        (ownThread Z₀ description Q L ℓ₂ Nm Mg₂ tk tt rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ Said₁ Said₂ d Dt
          n₁ n₂ Vd w dT dM).hand 2 :=
    fun c j h => List.mem_append_left _ (source_taken _ blk hb hr h)
  obtain ⟨p0, e0, -, s0⟩ := Thread.handAt_elim _ (hH.2 _ (hand 0 0 a0))
  obtain ⟨p5, e5, -, s5⟩ := Thread.handAt_elim _ (hH.2 _ (hand 0 5 a5))
  obtain ⟨p1, e1, -, s1⟩ := Thread.handAt_elim _ (hH.2 _ (hand 1 1 a1))
  have hpar : AtPublicFiles.KeySharedThread.parKey description.source description.later = QK :=
    par_sourced hs scope
  have hU : treesU (AtPublicFiles.KeySharedThread.parKey description.source description.later) = 1 := by
    rw [hpar]
    exact omega_tree_full.2.2.2.1
  have hO : 0 < treesOf5 (AtPublicFiles.KeySharedThread.parKey description.source description.later) := by
    rw [hpar]
    exact omega_tree_full.2.2.2.2
  refine ⟨⟨p0, e0, s0⟩, ⟨p5, e5, s5⟩, ⟨p1, e1, ?_⟩⟩
  refine (congrArg (fun t => p1.2.same t.2 = true) (tbKey_one _ hU hO _ _ tk tt k _ _)).mp ?_
  exact s1

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.tables_of_hand
