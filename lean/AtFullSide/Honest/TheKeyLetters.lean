-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheKeyLetters.lean: the letters of the key file's offline prover, as definitions: the twin of TheLetters at the
proof file. For each of the three chains: thread, Said, keeps, riders, falls.

Why. Each house that pays a member of the key file must pay it at the same value. Here Lean is to hold the fit, by one term for each letter.

How a value turns. At one named minute, on a word (the fifty-second sheet).

The six points of the check sheet.
  the last chain's letter: `lastSaid`: `saidOwn`, at the first chain's `firstSaid` and the shared chain's `sharedSaid`.
  riders: at the last chain `fun _ _ _ => True`, in `threadOwn`; at the first and the shared chain, the threads' own texts.
  keeps: `keeps` at the shared chain: `keepsKey`. The first chain's is `kindFirst` inside `later`. The last chain's is `keptOwn`.
  the last chain's members 0 to 3: one value: `lastThread`.
  gathering at the first chain: a named hole: not settled here.
  names that mean two objects: `offlineValue` here is AtPublicFiles.KeyStandWalked's, of a description.

Holes, each named with its holder.
  `idle` letters: `numbers`, `meaning`, `rest`, `tableUnused` say nothing by design; that they serve at 9 and 10 is not shown here.


The falls are empty: `firstFalls`, `sharedFalls`, `lastFalls`.

`TheKeyLots`: `TheLots` at these values: its fields are what the houses pay. Definitions alone: the last line at them is in
E2E/OfflineAtTheLetters.lean.

Nothing on soundness, completeness, hiding or binding: a conditional in `TheKeyLots`.

-/
import E2E.OfflineLetters
import E2E.OfflineLastLetters
import E2E.LotLetters
import E2E.KeyStandFull
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UKeeps

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.Honest.TheKeyLetters
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Common Coins Table Fall)
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.AtKey (keepsKey)
open AtPublicFiles.KeyStandFull (idleNm idleMg pub_exists)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.FirstH.Lots (laterValue joinThread joinSaid)
open AtPublicFiles.KeyStandWalked.Lots (ttValue)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZTheKeyLetters : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueTheKeyLetters : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueTheKeyLetters : Inhabited RunValue := ⟨fun _ => 0⟩

variable (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- The witness's lens at the shared chain. -/
abbrev lens : WitLens (Words Cb.Gl.E) := WitLens.words

/-- The table's numbers at the shared chain. -/
abbrev numbers : NumbersS := idleNm

/-- The shared chain's own meaning: `mgWords` lays the rest. -/
abbrev meaning : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St Unit (Words Cb.Gl.E) := fun _ => idleMg

/-- The shared chain's `keeps` off the members 1 to 8. -/
abbrev keeps : Nat → St → St → Prop := keepsKey

/-- No further test on the shared chain's input. -/
abbrev validShared : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop := fun _ => True

/-- No table at the first tests' letter that the thread reads. -/
def tableUnused : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table :=
  fun _ _ _ _ _ => (⟨2, none, 0, .K14⟩, ⟨0, 0, fun _ i => i.elim0⟩)

/-- The words that the last rows read at no run. -/
def rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Words Cb.Gl.E :=
  fun _ _ _ _ _ _ => 0

/-- The public part that `pubKey` is handed: by trial, no shared thread or letter reads it: a change of it is `rfl` there. -/
def publicPart : ProofFile.Pub := Classical.choice AtPublicFiles.KeyStandFull.pub_exists

/-- The value of the first chain's later letters. -/
abbrev later := laterValue Z d K₀

/-- The tests' tables at the shared chain. -/
abbrev tests := ttValue Z d K₀

/-- **The first chain.** -/
abbrev firstThread := joinThread d (later Z d K₀)

abbrev firstSaid := joinSaid d (later Z d K₀)

/-- **The shared chain.** -/
abbrev sharedThreadAt := sharedThread (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀)
  keeps (validShared Z) publicPart d

abbrev sharedSaidAt := sharedSaid (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀)
  keeps (validShared Z) publicPart d

/-- **The last chain.** -/
abbrev lastThreadAt := lastThread (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀)
  keeps (validShared Z) publicPart d (later Z d K₀) (firstSaid Z d K₀)

abbrev lastSaidAt := lastSaid (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀)
  keeps (validShared Z) publicPart d (later Z d K₀) (firstSaid Z d K₀)

/-- No fall at any chain. -/
abbrev firstFalls : List (Fall (descOf d).S₁) := []

abbrev sharedFalls : List (Fall (descOf d).S₂) := []

abbrev lastFalls : List (Fall (descOf d).S₃) := []

/-- **`TheLots` at these values, no letter left.** -/
abbrev TheKeyLots : Prop :=
  TheLots (Z := Z) lens numbers (meaning Z) (tableUnused Z K₀) (tests Z d K₀) (rest Z K₀) keeps (validShared Z) publicPart d
    (firstThread Z d K₀) (lastThreadAt Z d K₀) (firstSaid Z d K₀) (lastSaidAt Z d K₀)

end AtFullSide.Honest.TheKeyLetters

