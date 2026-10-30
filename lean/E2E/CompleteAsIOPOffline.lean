-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPOffline.lean: the offline clause of completeness as an IOP, from named statements on
the key file's prover, and completeness from two lists of named statements. It states no goal.

  OfflineDebts   what is left of the offline prover: the accept law at tied inputs, that every
                 request's own sample is tied, and the stops and falls with their measures.
  offlineClause_of_debts   the offline clause, at every coin and so over coins and challenges.
  OnlineDebts    what is left of the online prover: the field yes, and its measures.
  theProver_of_lists   completeness from the two lists.

Limits. A list that suffices, not what the last line alone needs: the fields are at every coin. It
is for every P, and meant at one named value. All fields are hypotheses; no value is shown to meet
them. The accept law at tied inputs is
the seam of the offline prover. That a payer's law at keyHonestAny is that law at offlineProverWithEncodedTable is by
keyHonestObj_eq, at a prover equal to the term's: that step is not typed here.
-/
import E2E.CompleteAsIOPAtHonestProversByYes

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed allZeroDigest)
open OnBytes.Prover (FailsRarelyAtEveryCoin everyCoinGivesFailsRarely everyCoinOfLaws)
open P5J

local instance (priority := high) nonemptyPadZ_offline : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) nonemptyOfInhabited_offline {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂]
  [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- **What is asked of the offline prover, by name.** Relation: the pairs of which something is said.
FT: the prover's falls. Tied, TiedM: the inputs at which the accept law and the fall's measure, and
the measure of the private stops, are stated. -/
structure OfflineDebts (Relation : FullSizeMatrix → XF → Prop)
    (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    (Tied TiedM : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z)) (zB z pF : ℝ≥0∞) : Prop where
  /-- every sample of an index of the relation is tied -/
  tied : ∀ i x r e, Relation i x → Tied (i, r, e) ((protocolAtFiles Z).recOf i r e)
  tiedM : ∀ i x r e, Relation i x → TiedM (i, r, e) ((protocolAtFiles Z).recOf i r e)
  /-- the accept law at tied inputs, outside the abort set and the fall at the coin -/
  accepted : AtPublicFiles.KeyBridge.AccAtTied (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z allZeroDigest []).W FT Tied
  /-- a fall at cleared challenges is a fall, or an abort, at the challenges -/
  zero : AtPublicFiles.KeyBridge.FallZero (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z allZeroDigest []).W FT
  bad : AtPublicFiles.KeyBridge.BadSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) zB
  hid : AtPublicFiles.KeyBridge.HidSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) TiedM z
  falls : AtPublicFiles.KeyBridge.FallSmall (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) FT Tied pF

variable {Z Fx BT HT val₂ val₃ shT}

/-- The fields of HonDebts on the key file's prover, from OfflineDebts. -/
theorem OfflineDebts.keyZero {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {Tied TiedM} {zB z pF : ℝ≥0∞}
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation FT Tied TiedM zB z pF) :
    KeyZeroAt (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z allZeroDigest []).W FT :=
  keyZeroAt_of_fallZero allZeroDigest [] Z Fx BT HT val₂ val₃ shT FT d.zero

theorem OfflineDebts.keyAccepts {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {Tied TiedM} {zB z pF : ℝ≥0∞}
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation FT Tied TiedM zB z pF) :
    KeyAccepts (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z allZeroDigest []).W FT (fun _ _ => ∅) Relation :=
  fun i x r e c hy _ => d.accepted (i, r, e) ((protocolAtFiles Z).recOf i r e) c (d.tied i x r e hy)

theorem OfflineDebts.keyMeasure {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {Tied TiedM} {zB z pF : ℝ≥0∞}
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation FT Tied TiedM zB z pF) :
    KeyMeasure (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) FT Relation (zB + z + pF) := by
  intro i x r e c hy
  exact (pr_union_le _ _ _).trans (add_le_add ((pr_union_le _ _ _).trans (add_le_add d.bad
    (d.hid (i, r, e) ((protocolAtFiles Z).recOf i r e) (d.tiedM i x r e hy))))
    (d.falls (i, r, e) ((protocolAtFiles Z).recOf i r e) c (d.tied i x r e hy)))

/-- **The offline clause, at every coin.** -/
theorem offlineEveryCoin_of_debts {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {Tied TiedM} {zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation FT Tied TiedM zB z pF) (i : FullSizeMatrix) (x : XF)
    (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (hy : Relation i x) :
    FailsRarelyAtEveryCoin (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (workAtFiles Z).offline ((protocolAtFiles Z).encodeIndex i r)
      (i, r, e) ((protocolAtFiles Z).recOf i r e) (zB + z + pF) := fun c =>
  everyCoinOfLaws hf.offline Set.subset_union_left (d.keyZero _ _ c)
    (fun τ hp hs hn => by
      have ha := d.accepted (i, r, e) ((protocolAtFiles Z).recOf i r e) c (d.tied i x r e hy) τ hp hs hn
      rw [extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT i r e] at ha
      exact ha)
    (d.keyMeasure i x r e c hy)

/-- **The offline clause**, over the prover's coins and the challenges together. -/
theorem offlineClause_of_debts {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)} {Tied TiedM} {zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : OfflineDebts Z Fx BT HT val₂ val₃ shT Relation FT Tied TiedM zB z pF) (i : FullSizeMatrix) (x : XF)
    (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (hy : Relation i x) :
    FailsRarely (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (workAtFiles Z).offline ((protocolAtFiles Z).encodeIndex i r)
      (i, r, e) ((protocolAtFiles Z).recOf i r e) (zB + z + pF) :=
  everyCoinGivesFailsRarely _ _ _ _ _ _ (offlineEveryCoin_of_debts hf d i x r e hy)

end AtPublicFiles.AtFiles

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (ProverCoinCounts Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open P5J

local instance (priority := high) nonemptyPadZ_offline : Nonempty PadZ := pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_offline : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_offline : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- **What is asked of the online prover, by name.** -/
structure OnlineDebts (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      _ _ _) (Relation : FullSizeMatrix → XF → Prop) (zB z pF : ℝ≥0∞) : Prop where
  scope : InScope Z = true
  live : protocolDataWellFormed (asDescriptionFiles Z) = true
  laid : ∃ (D : WholeD) (r : LPFD.Full.RunPF),
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r returned.Z places firstChain
  below : ∀ i x, Relation i x → RyesZ Z i x
  yes : YesZ allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
    returned.H
    (TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H
      Relation fun _ _ => ∅)
  bad : BadSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
    returned.H) zB
  hid : HidSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H)
    (fun n w a => TiedYes Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H Relation n w (instanceAsPlainRecord a)) z
  falls : FallSmall (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H)
    (fallG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H)
    (fun n w a => TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H Relation (fun _ _ => ∅) n w (instanceAsPlainRecord a)) pF

/-- **Completeness, from the two lists.** -/
theorem theProver_of_lists {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {Tied TiedM}
    {kB kH kF zB z pF : ℝ≥0∞}
    (hsum : (kB + kH + kF) + 0 + (zB + z + pF) ≤ completenessTarget)
    (hf : (workAtFiles Z).Faithful)
    (off : OfflineDebts Z (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT Tied TiedM kB kH kF)
    (on : OnlineDebts returned places firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z pF) :
    TheProverIsCompleteAsIOP Z P hr :=
  theProver_of_yesDebts P returned places firstChain description hr hM hP hC hD G hG hsum hf
    ⟨on.scope, on.live, on.laid, on.below, off.keyZero, off.keyAccepts, off.keyMeasure, on.yes,
      on.bad, on.hid, on.falls⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.offlineClause_of_debts
#print axioms AtPublicFiles.AtFiles.HonestTerm.theProver_of_lists
