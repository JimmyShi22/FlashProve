-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLastLetters.lean: the last chain's thread and letter as terms at the letters of E2E/OfflineJoin.lean: U₃, S₃ of `TheLots`.

  `keyAtValue`: the key's parts at the value: the term that `threadAt` reads.
  `fillAtValue`: the filling at the value.
  `lastThread`, `lastSaid`: U₃, S₃.

6 and 11 are the two earlier chains' counts of trees, as in `rest₃`'s `srcAt 2 6 11` (E2E/KeyRest.lean); they reach the thread's strings alone.
The letter that stays: S₁, the first chain's, as the join has it. Q is `laterValue`, a parameter here.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineLetters
import E2E.KeyLastLaid
import E2E.KeyLastEvOwn
import E2E.FirstHSeat
import E2E.KeyDotItem

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Coins Common Local Mid Table)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyLastChain (threadOwn saidOwn mlKey val₁Key)
open AtPublicFiles.FirstH (LaterFill HCells HTab fillH tbH)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyStandMember (keyOf)
open VerifierAndGoals (PublicFiles)
open AtPublicFiles.KeyStandWalked (offlineValue)
open ProofFile.Honest.Term (tableCoins)

variable {Z : PublicFiles} {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub) (description : OfflineDescription) (Q : LaterFill (keyBook K₀) AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness)

/-- The key's parts at the value. -/
abbrev keyAtValue :=
  keyOf (pubKey Z₀ description.source.chains) description.source description.later
    (offlineValue (files := Z) description) matrixReader (tableCoins Z)

/-- The filling at the value. -/
abbrev fillAtValue (x : Xi) :=
  fillH description.source description.numbers description.later (offlineValue (files := Z) description) matrixReader Q x

/-- A meaning that says nothing, but for what `dtValue` lays in. -/
def idleDot : MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words Cb.Gl.E) :=
  ⟨fun _ _ _ _ _ => True, fun _ _ _ => True, fun _ _ _ _ _ => True,
    fun _ _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ _ => True, fun _ _ _ => True,
    fun _ _ _ _ => True, fun _ _ _ => True, fun _ => True⟩

/-- **The one (Dot)**: `hDt` of `last_done`, and what `door_dot` lays. -/
abbrev dtValue (x : Xi) (_ : Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) :
    MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words Cb.Gl.E) :=
  AtPublicFiles.KeyDotItem.dotFill (VerifiableInference.Desc.Key.thirdPar description.source.chains).S AtPublicFiles.KeyLastChain.gKey
    (fun _ => AtPublicFiles.KeyLastChain.wvK (val₁Key description.source (fillAtValue description Q x))
      (VerifiableInference.Desc.Key.thirdPar description.source.chains).S AtPublicFiles.AtFiles.CF AtPublicFiles.AtFiles.Full.A0.2.w) idleDot

/-- What `ends` reads where no pair stands: the chains' first states, whose field lin is none. -/
abbrev dValue (x : Xi) : (Xi × FirstState) × St :=
  ((x, (VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers description.later).start₁
      ((VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers description.later).pub x)),
    (VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers description.later).start₂
      ((VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers description.later).pub x))

/-- A run state with a field: read where no door state exists. -/
abbrev dMValue (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :
    Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit :=
  ⟨⟨⟨w.1, w.2.1, x, ()⟩, [], ()⟩, [], [], some []⟩

/-- A table of no word. -/
abbrev dTValue : Place × Table := (⟨0, none, 0, .frame⟩, ⟨0, 0, fun _ i => i.elim0⟩)

variable
  (S₁ : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
  (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)

/-- **U₃.** -/
abbrev lastThread :=
  threadOwn description.source description.numbers description.later
    (keyAtValue (Z := Z) Z₀ description) (fillAtValue description Q x) ℓ Nm Mg₀
    (AtPublicFiles.KeyAsksKey.tableKey description.source description.later K₀ (keyAtValue (Z := Z) Z₀ description) tk tt) rest Kp Vd
    (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x) w.1 w.2.1 x (keyProver (keyAtValue (Z := Z) Z₀ description)).first
    (tbH description.source description.numbers description.later (offlineValue (files := Z) description) matrixReader Q)
    (S₁ w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (dValue description x) (dtValue description Q x)
    (mlKey (val₁Key description.source (fillAtValue description Q x))) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x)

/-- **S₃.** -/
abbrev lastSaid :=
  saidOwn description.source description.numbers description.later
    (keyAtValue (Z := Z) Z₀ description) (fillAtValue description Q x) ℓ Nm Mg₀
    (AtPublicFiles.KeyAsksKey.tableKey description.source description.later K₀ (keyAtValue (Z := Z) Z₀ description) tk tt) rest Kp Vd
    (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x) w.1 w.2.1 x (keyProver (keyAtValue (Z := Z) Z₀ description)).first
    (tbH description.source description.numbers description.later (offlineValue (files := Z) description) matrixReader Q)
    (S₁ w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (dValue description x) (dtValue description Q x)
    (mlKey (val₁Key description.source (fillAtValue description Q x))) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x)

end AtPublicFiles.AtFiles.HonestTerm
