-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineJoin.lean: THE JOIN of the offline prover's debts: the members' statements, each a named field, give the clause
that the honest provers' theorem asks of the offline prover (`OfflineDebts`), with no fall, and with it `KeyAccepts`.

Why. One place holds all that the accept law at the key file still asks. Each field of `TheLots` is one lot.

Main names.
  `TheLots` (in E2E/OfflineLetters.lean): the fields.
  `offlineDebts_of_lots`: the value of `OfflineDebts` at `thePartsAt` and the served requests, at no fall, measures 0.
  `keyAccepts_of_lots`: these members give `KeyAccepts`: one third of what `offlineDebts_of_lots` gives, which is the one that
    the honest provers' theorem takes.

The two measures of `bad` and `hid` are 0 at no field of `TheLots`: `badSmall_key` and `hidSmall_key` come of the prover's quiet
halves and the book; the fall's is 0 because the fall is empty.

The letters, as meant at the term. U₁ := the first chain's thread `Th` through `joinThread`, S₁ := its
`joinSaid`; U₃ := `lastT`, S₃ := its `saidOwn`; these are parameters here, typed; the file that lays them imports this
one. Mg₀ := `fun _ => idleMg`, ℓ := `WitLens.words`, Nm := `idleNm`, Kp := `keepsKey` (K12/AtKey/UKeeps.lean: at 9 `keepsU`, which is meant to carry what rides past the test; not read here), Vd := `fun _ => True`: at these `hC`, `hN`,
`hKp`, `hE`, `hEnd` and `stand_nine`'s `hPin` are meant to hold: this is a reading, not shown here.

A stand is an existence and `testU`, `testOmega` speak of every state at 9 and 10: `walked_unique_shared` (E2E/KeySharedDebts.lean)
says that a state of the walk is one at its input and challenges, under opens and depths at the thread: IOP's `opens_key_all`,
`depths_key_all`, at its table.

What stays open. Every field of `TheLots`, and eight laws on the letters: five in the last line's premises (`hN`, `hKp`, `hE`, `hEnd`, `hC`), `hPin` and `Vd` at the input through `run`, and `Kp` at 9 through `testU`. That `TheLots` can be met at no fall is a reading: at a challenge where an honest item refuses, no
value of it exists, and a fall would be owed.

No law over coins. Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.OfflineFromChains

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Fall Thread Local Common Coins Mid Sits OwesS YesS SaidNext PlaysS BehindS ExchangeS
  RidesPastS AcceptedS Table fallsBy)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.Bridge (KeyAccepts)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open LPFD.Full (XF)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZOfflineJoin : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueOfflineJoin : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueOfflineJoin : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}
  {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub)

/-- **The clause that the honest provers' theorem asks of the offline prover, from the lots.** The fall is empty. -/
theorem offlineDebts_of_lots {U₁ : FirstFamily Z description (keyBook K₀)} {U₃ : LastFamily Z description (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hN : Function.Injective Nm.tenant)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (L : TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description U₁ U₃ S₁ S₃) :
    ∃ Tied TiedM, OfflineDebts Z (descOf description) (thePartsAt Z).book
      ((thePartsAt Z).prover description) runValueBytes runValueBytes
      (offlineStart description) (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ => ∅) Tied TiedM 0 0 0 :=
  offlineDebts_from_chains hr ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ hd scope live hK₀ hN hKp hE hEnd hC
    (U₁ := U₁) (U₃ := U₃) (S₁ := S₁) (S₃ := S₃)
    (fun w x ht hok => ⟨L.sits w x ht hok, L.firstOwes w x ht, L.lastOwes w x ht, L.firstNext w x ht,
      L.lastNext w x ht, L.firstYes w x ht, L.lastYes w x ht⟩)
    (fun w x ht => ⟨L.testU w x ht, L.testOmega w x ht, L.testYesU w x ht, L.testYesOmega w x ht⟩)
    L.run

/-- **THE LAST LINE: these members give `KeyAccepts`, at the empty fall.** -/
theorem keyAccepts_of_lots {U₁ : FirstFamily Z description (keyBook K₀)} {U₃ : LastFamily Z description (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hN : Function.Injective Nm.tenant)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (L : TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description U₁ U₃ S₁ S₃) :
    KeyAccepts (offlineProverWithEncodedTable Z (descOf description) (thePartsAt Z).book
        ((thePartsAt Z).prover description) runValueBytes runValueBytes (offlineStart description))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) := by
  obtain ⟨Tied, TiedM, off⟩ := offlineDebts_of_lots hr ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ hd scope live hK₀
    hN hKp hE hEnd hC L
  exact off.keyAccepts

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineDebts_of_lots
#print axioms AtPublicFiles.AtFiles.HonestTerm.keyAccepts_of_lots
