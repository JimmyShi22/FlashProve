-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineDebtsAtParts.lean: a value of `OfflineDebts` (E2E/CompleteAsIOPOffline.lean) at the key file's prover of
parts, from the debts at the pairs of the three chains. By calls.

Main names. `offlineDebts_at_parts`: at the fall of three lists, whose measure and clearing are premises.
  `offlineDebts_no_fall`: at no lists, where the three measures are 0.

What stays open. All that E2E/OfflineAtParts.lean leaves, and `hQuiet`: no part stops: `noStop_value`
(E2E/KeyValueHolds.lean) at the written value. `hOk`: the relation lies in `ok`.

Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.CompleteAsIOPOffline
import E2E.OfflineAtParts
import E2E.NoStop

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (relationsAndEncodingOfClaims front₀ join₀)
open _root_.Run (ckP)
open OnBytes.Slice (frS)
open VerifiableInference.Desc.Key (Source LaterPlaces keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (ProverCoinCounts Fall Thread Local Common Coins Mid halvedAll)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed allZeroDigest)
open LPFD.Full (XF)

local instance (priority := high) instNonemptyPadZOfflineDebtsAtParts : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyOfInhabitedOfflineDebtsAtParts {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {Q₂ Q₃ : Type} [Fintype Q₂]
  [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃] {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray}
  {X₀ Xh Wk : Type} {B : ProverCoinCounts} {K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk}

/-- The fall of three lists, at the key's prover, with the letters of the wire. -/
abbrev fallLists {Q₂ Q₃ : Type} [Fintype Q₂] [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
    {val₂ : Q₂ → ByteArray} {val₃ : Q₃ → ByteArray} (K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk)
    (f₁ : List (Fall (keyFileDescription X N P).S₁)) (f₂ : List (Fall (keyFileDescription X N P).S₂))
    (f₃ : List (Fall (keyFileDescription X N P).S₃)) :
    AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z (keyFileDescription X N P) B (keyProver K) val₂ val₃ (keyFirst X N P)) :=
  fun w a c => fallOne (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
    (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty
    (keyFileDescription X N P) B (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K) w
    (keyInstanceOfOutOfDomainSample a) c

/-- **The value of `OfflineDebts`, from the debts at the pairs.** -/
theorem offlineDebts_at_parts (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) {Relation : FullSizeMatrix → XF → Prop} (ok : FullSizeMatrix → Prop)
    (hOk : ∀ i x, Relation i x → ok i)
    (hStored : ∀ w rc it x, (keyProver K).stored w rc it x =
      if it == 0 then (cmKeyZ Z).enc w rc x else none)
    (hQuiet : AtPublicFiles.Stops.NoStopAll (keyProver K))
    (h4 : halvedAll (keyFileDescription X N P) (keyProver K) = true)
    (f₁ : List (Fall (keyFileDescription X N P).S₁)) (f₂ : List (Fall (keyFileDescription X N P).S₂))
    (f₃ : List (Fall (keyFileDescription X N P).S₃)) {pF : ℝ≥0∞}
    (hZero : AtPublicFiles.KeyBridge.FallZero (offlineProverWithEncodedTable Z (keyFileDescription X N P) B (keyProver K) val₂ val₃ (keyFirst X N P))
      (lettersZ Z allZeroDigest []).W (fallLists Z (val₂ := val₂) (val₃ := val₃) K f₁ f₂ f₃))
    (hFalls : AtPublicFiles.KeyBridge.FallSmall (offlineProverWithEncodedTable Z (keyFileDescription X N P) B (keyProver K) val₂ val₃ (keyFirst X N P))
      (fallLists Z (val₂ := val₂) (val₃ := val₃) K f₁ f₂ f₃)
      (fun w a => TiedOffline Z X N P val₂ val₃ K ok w (keyInstanceOfOutOfDomainSample a)) pF)
    {U₁ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit)
        (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh KeyInst}
    {U₂ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty
        (Common FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) TableKey) X₀ TableKey}
    {U₃ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit)
        (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh KeyInst}
    {S₁ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst → Nat → Coins B →
      Mid (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh → Prop}
    {S₂ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst → Nat → Coins B →
      Mid (Common FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) TableKey) X₀ → Prop}
    {S₃ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst → Nat → Coins B →
      Mid (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh → Prop}
    (hM : ∀ w x, TiedOffline Z X N P val₂ val₃ K ok w x → (keyFileDescription X N P).okStart x = true →
      MembersS (keyFileDescription X N P) (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K)
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B Q₂ Q₃), TiedOffline Z X N P val₂ val₃ K ok w x →
      AtRunS (keyFileDescription X N P) (keyProver K) (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x
        c) :
    OfflineDebts Z (keyFileDescription X N P) B (keyProver K) val₂ val₃ (keyFirst X N P) Relation
      (fallLists Z (val₂ := val₂) (val₃ := val₃) K f₁ f₂ f₃)
      (fun w a => TiedOffline Z X N P val₂ val₃ K ok w (keyInstanceOfOutOfDomainSample a)) (fun _ _ => True) 0 0 pF where
  tied := fun i x r e hy => tied_offline Z X N P val₂ val₃ K ok hn hStored i r e (hOk i x hy)
  tiedM := fun _ _ _ _ _ => trivial
  accepted := accepted_offline Z scope live hn ok h4 f₁ f₂ f₃ hM hat
  zero := hZero
  bad := badSmall_key (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (keyFileDescription X N P) (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).P hQuiet
  hid := hidSmall_key (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (keyFileDescription X N P) (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).P hQuiet _
  falls := hFalls

/-- **At no lists of falls the three measures are 0.** That the members' debts can be paid at no lists is a reading. -/
theorem offlineDebts_no_fall (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) {Relation : FullSizeMatrix → XF → Prop} (ok : FullSizeMatrix → Prop)
    (hOk : ∀ i x, Relation i x → ok i)
    (hStored : ∀ w rc it x, (keyProver K).stored w rc it x =
      if it == 0 then (cmKeyZ Z).enc w rc x else none)
    (hQuiet : AtPublicFiles.Stops.NoStopAll (keyProver K))
    (h4 : halvedAll (keyFileDescription X N P) (keyProver K) = true)
    {U₁ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit)
        (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh KeyInst}
    {U₂ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty
        (Common FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) TableKey) X₀ TableKey}
    {U₃ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst →
      Thread B (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit)
        (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh KeyInst}
    {S₁ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst → Nat → Coins B →
      Mid (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh → Prop}
    {S₂ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst → Nat → Coins B →
      Mid (Common FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) TableKey) X₀ → Prop}
    {S₃ : (FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → KeyInst → Nat → Coins B →
      Mid (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh → Prop}
    (hM : ∀ w x, TiedOffline Z X N P val₂ val₃ K ok w x → (keyFileDescription X N P).okStart x = true →
      MembersS (keyFileDescription X N P) (bareSides (keyFileDescription X N P) B (keyProver K) [] [] []) (keyProver K)
        (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x))
    (hat : ∀ w x (c : CoinOne B Q₂ Q₃), TiedOffline Z X N P val₂ val₃ K ok w x →
      AtRunS (keyFileDescription X N P) (keyProver K) (U₁ w x) (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x
        c) :
    OfflineDebts Z (keyFileDescription X N P) B (keyProver K) val₂ val₃ (keyFirst X N P) Relation
      (fun _ _ _ => ∅)
      (fun w a => TiedOffline Z X N P val₂ val₃ K ok w (keyInstanceOfOutOfDomainSample a)) (fun _ _ => True) 0 0 0 := by
  have e : fallLists Z (X := X) (N := N) (P := P) (B := B) (val₂ := val₂) (val₃ := val₃) K [] [] [] =
      fun _ _ _ => ∅ := by
    funext w a c
    exact fallOne_bare Z _ _ _ w _ c
  have core := offlineDebts_at_parts Z scope live hn ok hOk hStored hQuiet h4 [] [] []
    (by rw [e]; exact AtPublicFiles.KeyBridge.fallZero_none _ _) (by rw [e]; exact AtPublicFiles.KeyBridge.fallSmall_none _ _)
    hM hat
  rw [e] at core
  exact core

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.offlineDebts_at_parts
#print axioms AtPublicFiles.AtFiles.offlineDebts_no_fall
