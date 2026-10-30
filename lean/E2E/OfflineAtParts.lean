-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineAtParts.lean: the accept law at `offlineProverWithEncodedTable` and the tie of the samples, at the key file's prover of parts, from
the debts at the pairs of the three chains. By calls. It is a conditional: every member's debt stands as a premise.
E2E/OfflineDebtsAtParts.lean makes the value of `OfflineDebts` of them.

Why. T2's clause on the offline prover asks a value of `OfflineDebts` at `offlineProverWithEncodedTable`. The accept law from the pairs
(`accLaw_families_at`, E2E/KeyAcceptPairsLaid.lean) ends at `keyHonestAny`, which `offlineProverWithEncodedTable` is by unfolding. This file
makes that step and says which inputs are tied.

Main names.
  `chainFall_empty`, `viewsFall_empty`, `fallOne_bare`: with no lists of falls no fall speaks.
  `TiedOffline`: the frame's `Tied` at the key's prover, at the seat's letters and the committer's relation.
  `tied_offline`: the sample of every index with `ok` is tied, at a prover that has the committer's key and columns.
  `accepted_offline`: the accept law at tied inputs, at `offlineProverWithEncodedTable`, outside the fall of three lists, from the debts at
    the pairs.

What stays open. As premises: `hM`, `hat`: that the threads sit, and `OwesS`, `SaidNext`, `YesS` at each member, and
what is owed at a run: these are the members' debts. `hStored`: the prover
has the committer's columns at the item 0 alone: `stored_at_parts` (E2E/KeyStoredAtValue.lean) at the written value.
`h4`: `halved_value`. The lists of falls are letters; that they can be empty is a reading, not shown here.

No law over coins is stated here: `Tied` reads the
committer's coins as letters of each input.

Nothing on soundness, completeness, hiding or binding: a conditional.

-/
import E2E.BridgePremWKey
import Johnson.Goal.Conditions.BindsAtThe
import E2E.BridgeJoinAtFiles
import E2E.KeyAcceptAtFiles
import E2E.KeyAcceptPairsLaid
import E2E.KeyTied
import E2E.WrittenNonZero
import E2E.ItemsZero
import E2E.NoStop
import E2E.OfflineLetters

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

section
variable {S Cl : Type}

/-- With no list of falls no fall of a chain speaks. -/
theorem chainFall_empty (firstTree : Nat) (bs : List (Block S Cl)) (s : S) (v : Fmt.View) :
    chainFall ([] : List (Fall S)) firstTree bs s v = none := by
  unfold chainFall
  rw [List.findSome?_eq_none_iff]
  intro x _
  simp [fallOf]

end

section
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- With no lists of falls no fall speaks at three views. -/
theorem viewsFall_empty (F : FileDescription Xi) (x : Xi) (U : Views) :
    viewsFall F [] [] [] x U = none := by
  simp [viewsFall, chainFall_empty]

/-- At sides with no lists of falls an honest run meets none. -/
theorem fallAt_empty {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (h₁ : G.falls₁ = []) (h₂ : G.falls₂ = []) (h₃ : G.falls₃ = [])
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) (k : Coins Bk) (ρ : Draws) :
    fallAt G H w₀ rc x k ρ = none := by
  unfold fallAt
  rw [h₁, h₂, h₃]
  cases (runC F Bk (G.prover H) w₀ rc x k ρ).toOption with
  | none => rfl
  | some r => exact viewsFall_empty F x r.run.views

end

end ProofFile.Honest

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull front₀ join₀ codingHonest)
open OnBytes.Slice (frS frZ)
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Source LaterPlaces keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover ProverCoinCounts Sides Fall Thread Local Common Coins Mid Tied halvedAll tied_atItem)
open OnBytes.Prover (AccLaw)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed allZeroDigest)
open LPFD.Full (XF)

local instance (priority := high) instNonemptyPadZOfflineAtParts : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyOfInhabitedOfflineAtParts {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

section
variable (Z : PublicFiles) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) {Q₂ Q₃ : Type} [Fintype Q₂]
  [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃] (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray)
  {X₀ Xh Wk : Type} (B : ProverCoinCounts)
  (K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk)

/-- **The sample of every index with `ok` is tied**, at a prover with the committer's key and columns. -/
theorem tied_offline (ok : FullSizeMatrix → Prop) (hn : KeyNamed Z X N P)
    (hStored : ∀ w rc it x, (keyProver K).stored w rc it x =
      if it == 0 then (cmKeyZ Z).enc w rc x else none)
    (i : FullSizeMatrix) (r : (Cz Z).Pad × (Cz Z).Rnd) (e : (Cz Z).Seed) (hok : ok i) :
    TiedOffline Z X N P val₂ val₃ K ok (i, r, e) (keyInstanceOfOutOfDomainSample ((protocolAtFiles Z).recOf i r e)) := by
  have t := tied_atItem (Ryes := fun i (_ : Unit) => ok i)
    (tiedAtKeyFile (R₂ := Q₂) (R₃ := Q₃) (AZ Z) PadZ (holdZ Z) val₂ val₃ (dataAtFiles flashProveData Z).DK
      (keyFileDescription X N P) (keyFirst X N P) fun _ => rfl)
    (AtPublicFiles.AtZero.itemsZero_of_data hn.data_at) (keyProver K) (i, r, e) ((), (protocolAtFiles Z).recOf i r e)
    ⟨by
      rw [AtPublicFiles.Committed.ansAt_eq]
      exact validT_obj (AtPublicFiles.Committed.Cf (AZ Z) PadZ (holdZ Z)) (filesAt Z) (dataAtFiles flashProveData Z).P (i, r, e) _
        (valid_has (protocolAtFiles Z) (i, r, e)), hok⟩
  have eP : (keyCommitterTied (AZ Z) PadZ (holdZ Z)).proverAt 0 (keyProver K) = keyProver K :=
    ProofFile.Honest.Committer.proverAt_self (Cm := cmKeyZ Z) (H := keyProver K) rfl hStored
  have t₂ : Tied _ _ ((keyCommitterTied (AZ Z) PadZ (holdZ Z)).proverAt 0 (keyProver K)) _ _ _ _ _ _ _ := t
  rw [eP] at t₂
  unfold TiedOffline
  show Tied _ _ (keyProver K)
    (keySeam (AZ Z) (relationsAndEncodingOfClaims (AZ Z) (codingHonest frS frZ 402653181 (AZ Z) PadZ (holdZ Z))) val₂ val₃)
    (tableOf (AZ Z) (relationsAndEncodingOfClaims (AZ Z) (codingHonest frS frZ 402653181 (AZ Z) PadZ (holdZ Z)))
      (dataAtFiles flashProveData Z).DK) _ _ _ _ _
  rw [keySeam_eq_cm, tableOf_eq_cm]
  exact t₂

variable {X N P val₂ val₃ B K}

/-- **At sides with no fall the fall's set is empty.** -/
theorem fallOne_bare {TF TJ T3 Sd : Type} {C : _root_.Run.PQ.CK} {D : OnBytes.Maker.WholeD} {tF : TF}
    {tJ : TJ} {t3 : T3} (F : FileDescription KeyInst) (Bk : ProverCoinCounts)
    (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey Unit X₀ Xh) {R₂ R₃ : Type}
    (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × Sd) (x : KeyInst) (c : CoinOne Bk R₂ R₃) :
    fallOne C D tF tJ t3 F Bk (bareSides F Bk H [] [] []) H w x c = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro ρ hρ
  have h : (ProofFile.Honest.fallAt (bareSides F Bk H [] [] []) H w.1 w.2.1 x
      ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (ProofFile.Honest.drawsAt C D tF tJ t3 ρ)).isSome = true := hρ
  rw [ProofFile.Honest.fallAt_empty _ rfl rfl rfl] at h
  cases h

/-- `nzWritten`'s sentence, from the theorem on the written data: no run of the test. -/
theorem nzWritten_true : nzWritten = true := by
  unfold nzWritten
  rw [List.all_eq_true]
  intro d h
  exact decide_eq_true (AtPublicFiles.Written.nz_writtenK d h)

/-- **The accept law at `offlineProverWithEncodedTable`, outside the fall of three given lists, from the debts at the pairs.** -/
theorem accepted_offline (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) (ok : FullSizeMatrix → Prop)
    (h4 : halvedAll (keyFileDescription X N P) (keyProver K) = true)
    (f₁ : List (Fall (keyFileDescription X N P).S₁)) (f₂ : List (Fall (keyFileDescription X N P).S₂))
    (f₃ : List (Fall (keyFileDescription X N P).S₃))
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
    AtPublicFiles.KeyBridge.AccAtTied (offlineProverWithEncodedTable Z (keyFileDescription X N P) B (keyProver K) val₂ val₃ (keyFirst X N P))
      (lettersZ Z allZeroDigest []).W
      (fun w a c => fallOne (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
        (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty
        (keyFileDescription X N P) B (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K) w
        (keyInstanceOfOutOfDomainSample a) c)
      (fun w a => TiedOffline Z X N P val₂ val₃ K ok w (keyInstanceOfOutOfDomainSample a)) :=
  accLaw_families_at ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []) B (keyFileDescription X N P)
    (bareSides (keyFileDescription X N P) B (keyProver K) f₁ f₂ f₃) (keyProver K) (keyProver K)
    (bareSides_prover _ _ _ _ _ _)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (pubJ := pubAt val₂ val₃ keyAnswersTied 0) (Rel := relKeyZ Z ok) (full_key Z scope live)
    (carries_key Z) (dataFits_key hn) hn.plan (sealPlain_key X N P)
    (due_key hn (nz_key scope live hn nzWritten_true)) (run_key hn)
    (fun r2 r3 w a ht => keySeam_silentK_of_key (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E)
      val₂ val₃ r2 r3 default w.1 w.2.1 w.2.2 a (ht.key r2 r3).symm) h4 hM hat

end

end AtPublicFiles.AtFiles

#print axioms ProofFile.Honest.chainFall_empty
#print axioms ProofFile.Honest.viewsFall_empty
#print axioms ProofFile.Honest.fallAt_empty
#print axioms AtPublicFiles.AtFiles.tied_offline
#print axioms AtPublicFiles.AtFiles.fallOne_bare
#print axioms AtPublicFiles.AtFiles.accepted_offline
