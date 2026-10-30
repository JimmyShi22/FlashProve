-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSayAtStand.lean: THE PREMISE OF TRUTH AT A PROXIMITY TEST, AT A THREAD's OWN STANDS: definitions, and one theorem on the
borders. Nothing is shown of any premise.

  `SayAtStand`        general in the job: at every stand of an invariant A in front of a proximity test, where the book lends
                      the test's two parts their coins, the rows that the test takes in hold at the job's plain rows
                      (`SaysInFront`, E2E/OfflineSayAtRun.lean). It is the premise hA of `says_of_inside`
                      (E2E/OfflineSayOfInside.lean), at every coin
  `rangesJobAtFiles`, `foldedJobAtFiles`, `omegaJobAtFiles`, `ownJobAtFiles`   the four tests' jobs at the offline
                      prover's own senders (`offlineSenders d`, E2E/KeyArgumentsAt.lean) and its two places of the shared tests
                      (`offlineTestParametersOnU`, `offlineTestOnOmega`, E2E/TheHonestProver.lean)
  `FourSayAtStands`   THE FOUR PREMISES: `SayAtStand` at each test, at the invariant `ThrS` of the thread and the letter of
                      `TheLots` (E2E/OfflineJoin.lean), at the test's border, at every tied input (`TiedAt`)
  `borders_are_the_tests`   in scope the sub-protocols number 15 of the first chain, 9 and 10 of the shared chain and 2
                      of the last chain stand at the four tests' places

What the four premises speak of, by reading; no theorem here says it. Ranges: the multiplicities' words. Folded row's
group and Omega's group: the committed table's columns and the folded rows. Own group: the evaluation claim on W and
the dot product.

Limits. No member of `FourSayAtStands` is known. The premises read the input and the coins: no later law may take one as a
hypothesis on a run and then speak of the coins as sampled anew. Nothing on any property.
-/
import E2E.OfflineJoin
import E2E.OfflineRowsAtFiles
import E2E.OfflineSayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (ManyJob plainMany askOf)
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile AtPublicFiles.KeyLay
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.KeyThread (rangesTestJob sentRanges)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope)

local instance (priority := high) sayAtStandPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) sayAtStandValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) sayAtStandDefault : Inhabited RunValue := ⟨fun _ => 0⟩

/-- **At every stand of the invariant A in front of a proximity test, where the book lends the test's two parts their
coins, the rows that the test takes in hold at the job's plain rows.** V: the type of what a second stop may read. chain, a:
the test's chain, from 0, and its place. -/
def SayAtStand (V : Type) {S W X : Type} (J : TestJob W X)
    (rows : W → Front X → TestCoins → PlainRows) {Bk : ProverCoinCounts} (chain : ℕ) (a : Place)
    (A : Coins Bk → S → Mid W X → Env → Prop) : Prop :=
  ∀ k st m₀ E₀ (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m₀ E₀ →
    lendRow Bk (Bk.rowsOf chain) (k.look chain) a [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))

variable {Z : PublicFiles}

/-- The job of the test on the ranges, at the offline prover's own senders. -/
abbrev rangesJobAtFiles (d : OfflineDescription) :
    TestJob (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) Unit :=
  rangesTestJob d.source d.numbers d.later (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0

/-- The job of the test on the folded row's group. -/
abbrev foldedJobAtFiles (d : OfflineDescription) : ManyJob (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit :=
  jobKU (offlineSenders (files := Z) d).send (offlineTestParametersOnU d.later) (bsOf (offlineSenders (files := Z) d))
    (stOf (offlineSenders (files := Z) d)) (wtOf (offlineSenders (files := Z) d))
    (rdOf (offlineSenders (files := Z) d))

/-- The job of the test on Omega's group. -/
abbrev omegaJobAtFiles (d : OfflineDescription) : ManyJob (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit :=
  jobKO (offlineSenders (files := Z) d).send (offlineTestParametersOnU d.later) (offlineTestOnOmega d.later)
    (bsOf (offlineSenders (files := Z) d)) (wtOf (offlineSenders (files := Z) d))
    (rdOf (offlineSenders (files := Z) d))

/-- The job of the own test. -/
abbrev ownJobAtFiles (d : OfflineDescription) :
    ManyJob (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) Unit :=
  jobKWAt d.source d.numbers d.later (offlineSenders (files := Z) d).idx
    (offlineSenders (files := Z) d).w (offlineSenders (files := Z) d).send id
    (askOf (offlineSenders (files := Z) d).send
      (fun w => (offlineSenders (files := Z) d).weights w.w₀)
      fun w => randK14 ((offlineSenders (files := Z) d).rand w.rc))

section Letters
variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **THE FOUR PREMISES OF TRUTH, AT THE THREADS' OWN STANDS.** NAMED PREMISES: no member is known. -/
structure FourSayAtStands (d : OfflineDescription) (U₁ : FirstFamily Z d (keyBook K₀))
    (U₃ : LastFamily Z d (keyBook K₀)) (S₁ S₃ : OwnLetter Z (keyBook K₀)) : Prop where
  /-- the test on the ranges: the first chain's sub-protocol number 15 -/
  ranges : ∀ w x, TiedAt Z d w x →
    SayAtStand (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) (rangesJobAtFiles (Z := Z) d)
      (fun v fr C => plainOne (sentRanges d.source (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0) v
        (C.mem 0) ((rangesJobAtFiles (Z := Z) d).first v fr C))
      0 rngPlace (ThrS (U₁ w x) (S₁ w x) 15)
  /-- the test on the folded row's group: the shared chain's sub-protocol number 9 -/
  folded : ∀ w x, TiedAt Z d w x →
    SayAtStand Empty (foldedJobAtFiles (Z := Z) d).toRun.toTest (plainMany (foldedJobAtFiles (Z := Z) d))
      1 foldedTestPlace (ThrS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) 9)
  /-- the test on Omega's group: the shared chain's sub-protocol number 10 -/
  omega : ∀ w x, TiedAt Z d w x →
    SayAtStand Empty (omegaJobAtFiles (Z := Z) d).toRun.toTest (plainMany (omegaJobAtFiles (Z := Z) d))
      1 omegaTestPlace (ThrS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) 10)
  /-- the own test: the last chain's sub-protocol number 2 -/
  own : ∀ w x, TiedAt Z d w x →
    SayAtStand (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness AtPublicFiles.AtFiles.KeyInst Unit) (ownJobAtFiles (Z := Z) d).toRun.toTest
      (plainMany (ownJobAtFiles (Z := Z) d)) 2 ownTestPlace (ThrS (U₃ w x) (S₃ w x) 2)

end Letters

/-- **The four borders are the four tests.** In scope. -/
theorem borders_are_the_tests {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) :
    ((descOf d).first.blocksInOrder[15]?).map (·.place) = some rngPlace ∧
      ((descOf d).shared.blocksInOrder[9]?).map (·.place) = some foldedTestPlace ∧
      ((descOf d).shared.blocksInOrder[10]?).map (·.place) = some omegaTestPlace ∧
      ((descOf d).second.blocksInOrder[2]?).map (·.place) = some ownTestPlace := by
  obtain ⟨r1, r2, r3⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  have a1 := places_of_rows r1
  have a2 := places_of_rows r2
  have a3 := places_of_rows r3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← List.getElem?_map, a1]
    decide
  · rw [← List.getElem?_map, a2]
    decide
  · rw [← List.getElem?_map, a2]
    decide
  · rw [← List.getElem?_map, a3]
    decide

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.SayAtStand
#print axioms AtPublicFiles.OfflineRows.FourSayAtStands
#print axioms AtPublicFiles.OfflineRows.borders_are_the_tests
