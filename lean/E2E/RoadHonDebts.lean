-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/RoadHonDebts.lean: the hypotheses from which `honFit_atFiles` (E2E/BridgeJoinAtFiles.lean) gives
`OnBytes.Prover.HonFit` (Johnson/Prover/All/OfHonest.lean) at the three provers `proversOf (offlineProverWithEncodedTable …)
(linkProverAtFiles b Z) (famG …)`, as the fields of one structure, `HonDebts`, after the pattern of `PremWDebts`
(E2E/BridgeDebts.lean); and that theorem once more, with the structure as its only hypothesis, also
at the data of every value of the public reading. Toward completeness; nothing is claimed.

  `sealPlain_of_data`: where the description's `data` returns, its test `sealPlain` accepts: so the
    clause `plainSeal` of `PlainAt` is no field here; nor is its clause `width`: `width_atFiles`
    (E2E/RoadPublicRows.lean), in scope, under `laid`
  `SeedsAside`, `KeyZeroAt`, `KeyAccepts`, `KeyMeasure`: four of the five clauses of `KeyFive`
    (E2E/BridgeNineCut.lean), each under a name, in that structure's own words
  `keyFive_of_four`: the four and `ExtIsEnc` are the five
  `HonDebts`: a structure: the hypotheses by name, seventeen. On the public files: `scope`, `live`,
    `laid`, `start`. On the relation: `below`. On the OOD seeds that are set aside: `seeds`. On the
    key file's prover: `keyZero`, `keyAccepts`, `keyMeasure`. On the session's prover: `halved`,
    `rooted`, `ready₁`, `serves`, `threads`, `bad`, `hid`, `falls`
  `honFit_of_honDebts`: `HonDebts` gives `HonFit` at the parameters of `lettersZ Z c₀ m₀`
  `honFit_told_of_honDebts`: `HonDebts` at the pair (allZeroDigest, []) gives `HonFit` at the wiring of
    `homeR b Z` and the data `(homeT b Z).Sd dg`, at every value dg of the public reading

`HonDebts` occurs only as a hypothesis. It is none of the library's goals, and no theorem here has
it as its conclusion.

By what. `honFit_of_honDebts` is the first half of `both_of_debts` (E2E/BridgeBothOfDebts.lean):
`honFit_atFiles` at `nineFit_link` (E2E/BridgeNineLink.lean) and `num_letters`; the clause `extT` is
`extIsEnc_obj` (E2E/KeyBridgeFilled.lean), the clause `nonZero` of `PlainAt` is within
`plainAt_of_five` (E2E/BridgeNonZero.lean). `sealPlain_of_data` follows the proof of `seal_nz` (the
same file) and keeps two other conjuncts of `seal_of_fits`. `honFit_told_of_honDebts`:
`honFit_told_of_home` (E2E/LinkLaidAny.lean).

How the key file's fields can be reached. The session's fields (`threads`, `bad`, `hid`, `falls`)
are hypotheses of `honFit_atFiles`; the key file's three are clauses of `KeyFive`, in `HonFit`'s own
words. The library's road into them and `seeds`: `keyFive_of` (E2E/BridgeKeyFive.lean) takes the
structure `Sentences` whole, with two hypotheses more (Yes lies in the range ok; the seeds outside
Gs have measure at most δ, the ζ of its end), and ends at the fall `guardT … (asideOf Gs) FT` and at
Zs := `asideOf Gs`. `sentences_keyZ` (E2E/BridgeKeyEight.lean) makes `Sentences` at `offlineProverWithEncodedTable` from
eight hypotheses of E2E/KeyBridge.lean: `OneExact` (with a simulator), `ValidTied`, `FallZero`,
`HidSmall`, `BadSmall`, `FallSmall`, `AccAtTied`, and okT on the run values. It is at Gs := every
seed, where `asideOf Gs` is empty: over that theorem no seed is set aside, and, since `HonDebts` has
one Zs, `threads`, `falls` and `keyAccepts` are then owed at every seed. Without the simulator six
of the eight suffice, by `whT_of`, `accT_of` and `prT_of` (E2E/KeyBridge.lean).

What `threads` asks. `threads` is `ThreadsAt`, which names the structure `ThreadsC`
(Johnson/Desc/ProofFile/Honest/Law/ThreadStratC.lean). Whoever proves it builds a value of
`ThreadsC` by its fields: so the sense of this field moves with that structure's text.

Limits.
- The fields are hypotheses; none is proved here. No value is shown to meet `HonDebts`, not even an
  idle one.
- The fields are not of equal weight and are not to be counted: `threads` is the invariants of all
  sub-protocols of the proof file; `scope` is one Boolean test.
- Which fields can empty the whole list. What stands under Yes or under a bound can be made idle: at
  a Yes that holds of nothing, or at bounds of 1 or more, it asks nothing. These cannot: `scope`,
  `live`, `laid`, `start`, `keyZero`, `halved`, `rooted`, `ready₁`. Of them `start` reads the
  description alone, no prover: in scope it holds at every written instance or at none
  (E2E/StartInScope.lean), and it comes down to one public clause on the request's item
  (`start_of_item`, E2E/RoadPublicRows.lean). In general it is not known; if it is false at the
  description that `laid` ties to Z, every other field is paid for nothing. At the two written sets
  of files storedPublicFiles and zGap it is a theorem of the side library, and the four public fields hold
  together there (`okStart_zFull_whole`, AtFullSide/E2E/StartAtWrittenFiles.lean; `open_zFull`,
  AtFullSide/E2E/AtWrittenFiles.lean; at zGap `okStart_zGap_whole`, `open_zGap`).
- None of the fields reads the value of the public reading, the link's prover or the number b.
- Setting an OOD seed aside relieves `keyAccepts`, `threads` and `falls`. It relieves no abort set's
  measure: `hid` and `keyMeasure` are asked at every seed, because `HonFit` asks `prB` and `prT`
  there too; `bad` reads no input. In `keyMeasure` the fall FT stands unguarded, while the session's
  fall is guarded by Zs.
- `falls` and `keyMeasure` bound a measure at each fixed coin of the prover's: one coin at which the
  set is large forces the bound up.
- `falls` and `threads` share the letter G: the lists of falls outside which acceptance is owed are
  the lists whose measure is bounded.
- At a Yes that holds of nothing the conclusion keeps six clauses (`extT`, `extL`, `extB`, `whT`,
  `whL`, `whB`) and says nothing else; at bounds of 1 or more its clauses on measures say nothing.
- G, H, B, Fx, BT and HT are free letters: that they are the protocol's own prover is no field.
- Files over this one pay or bring down some fields in these letters: `seeds` and `keyZero`
  (E2E/RoadRowsPaid.lean); `keyMeasure`, under the hypothesis that no part of the key file's prover
  ever stops (E2E/RoadNoStop.lean); the cut into four public fields and thirteen others
  (E2E/RoadHonPublic.lean).
- All limits of E2E/BridgeJoinAtFiles.lean and E2E/BridgeBothOfDebts.lean hold here.
-/
import E2E.BridgeBothOfDebts
import E2E.BridgeDebtsTold
import E2E.BridgeNonZero
import E2E.RoadPublicRows
import E2E.LinkLaidAny

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Written
open VerifiableInference.Desc
open OnBytes OnBytes.Maker
open ProofFile.Honest (forall₂_last)

variable {Xi : Type}

/-- Where `F.data` returns for a value F of `FileDescription`, the test `sealPlain` accepts. -/
theorem sealPlain_of_data {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) : ProofFile.Honest.sealPlain F = true := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, -, -⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  obtain ⟨r, hr, -, qi, qr, -, -, -, -⟩ := ProofFile.Honest.seal_of_fits hf
  obtain ⟨d, hd, y, hy, rfl⟩ := forall₂_last w₁ r hr
  have e := round_ok hy
  have qi' : y.items = [] := qi
  have qr' : y.entry.roots = 0 := qr
  rw [e.2.1] at qi'
  rw [e.1] at qr'
  unfold ProofFile.Honest.sealPlain
  rw [hd]
  show ((d.items.filter (· != .root)).isEmpty && d.entry.roots == 0) = true
  rw [qi', qr']
  rfl

end AtPublicFiles.Written

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}
  (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
  (FT : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → hT.Coin → Set (Rho L.offline.shape))
  (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed)

/-- The clause `prZ` of `KeyFive`: the OOD seeds that are set aside have measure at most ζ, under
the wire's map from uniform digests. It reads no prover. -/
def SeedsAside (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (Yes : I → X → Prop) (ζ : ℝ≥0∞) : Prop :=
  ∀ i x r, Yes i x → pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Z i r} ≤ ζ

/-- The clause `whT` of `KeyFive`: if verifier randomness with its proof-of-work test bits set to 0
lies in the abort set or the fall, so does the verifier randomness itself. -/
def KeyZeroAt : Prop :=
  ∀ w x c ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ hT.withheld w x ∪ FT w x c →
    ρ ∈ hT.withheld w x ∪ FT w x c

/-- The clause `accT` of `KeyFive`: at an index that has a request of Yes and at an OOD seed that is
not set aside, `AccLaw` (Johnson/Prover/Law/Defs.lean: the interactive verifier of the key file
accepts the strategy's own run, whatever the nonces, where all proof-of-work tests are passed)
outside the abort set and the fall at the coin. -/
def KeyAccepts (Yes : I → X → Prop) : Prop :=
  ∀ i x r e c, Yes i x → e ∉ Z i r →
    AccLaw (batTC L aT) (wTC W) (L.recOf i r e) (hT.ext (i, r, e))
      (hT.strat (i, r, e) (L.recOf i r e) c)
      (hT.withheld (i, r, e) (L.recOf i r e) ∪ FT (i, r, e) (L.recOf i r e) c)

/-- The clause `prT` of `KeyFive`: abort set and fall together have measure at most pT, at each
fixed coin, at every OOD seed. -/
def KeyMeasure (Yes : I → X → Prop) (pT : ℝ≥0∞) : Prop :=
  ∀ i x r e c, Yes i x →
    prRho (hT.withheld (i, r, e) (L.recOf i r e) ∪ FT (i, r, e) (L.recOf i r e) c) ≤ pT

variable {hT W FT Z}

/-- The four, and that the external string is the encoded index, are the five. -/
theorem keyFive_of_four {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {Yes : I → X → Prop} {ζ pT : ℝ≥0∞}
    (he : ∀ i r e, hT.ext (i, r, e) = L.encodeIndex i r) (hz : KeyZeroAt hT W FT)
    (ha : KeyAccepts hT W FT Z Yes) (hs : SeedsAside W Z S Yes ζ) (hm : KeyMeasure hT FT Yes pT) :
    KeyFive hT W FT Z S Yes ζ pT :=
  ⟨he, hz, ha, hs, hm⟩

end AtPublicFiles.Bridge

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Premises
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀ relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse halvedAll rootedAll ready)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed homeR homeT allZeroDigest)
open OnBytes.K.Arm.Pub (D8)
open OnBytes.Prover (HonFit ThreeProvers Falls)
open OnBytes.WholeKey (CoinNums)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- **What is left to show for `HonFit` at the three provers, by name.** Yes: the relation of which
something is to be said. FT: the falls of the key file's prover. Zs: the OOD seeds that are set
aside. ζ, pT, zB, z, pF: five bounds that stay free parameters. -/
structure HonDebts (Yes : FullSizeMatrix → XF → Prop)
    (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed) (ζ pT zB z pF : ℝ≥0∞) : Prop where
  /-- On the public files: they are in scope: a Boolean test. Also a field of `PremWDebts` -/
  scope : InScope Z = true
  /-- On the public files: the IOP's own test on the public head accepts: a Boolean test. Also a
  field of `PremWDebts` -/
  live : protocolDataWellFormed (asDescriptionFiles Z) = true
  /-- On the public files: the description `descZ Zp Np cF` is what the library's own functions
  return for the files (`LaidAt`, Johnson/P5J/LaidOpens.lean). Also a field of `PremWDebts` -/
  laid : ∃ (D : WholeD) (r : LPFD.Full.RunPF),
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF
  /-- On the public files: the description's first test accepts one written instance -/
  start : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true
  /-- On the relation: Yes implies the library's object's relation `RyesZ Z`. Also a field of
  `PremWDebts` -/
  below : ∀ i x, Yes i x → RyesZ Z i x
  /-- On the OOD seeds that are set aside: their measure is at most ζ. It reads no prover -/
  seeds : SeedsAside (L := protocolAtFiles Z) (aT := (filesAt Z).annT) (aL := (filesAt Z).annL)
    (lettersZ Z c₀ m₀).W Zs (lettersZ Z c₀ m₀).letters.Sd Yes ζ
  /-- On the key file's prover: abort set and fall together hold verifier randomness whenever they
  hold it with the proof-of-work test bits set to 0 -/
  keyZero : KeyZeroAt (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT
  /-- On the key file's prover: the interactive verifier accepts its run, outside the abort set and
  the fall, at OOD seeds that are not set aside -/
  keyAccepts : KeyAccepts (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT Zs Yes
  /-- On the key file's prover: abort set and fall together have measure at most pT, at each fixed
  coin, at every OOD seed, also at those that are set aside -/
  keyMeasure : KeyMeasure (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) FT Yes pT
  /-- On the session's prover: it has a part (`Placed`) for each sub-protocol that states an item
  that is no root: a Boolean test -/
  halved : halvedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true
  /-- On the session's prover: it has a part for each sub-protocol that sends a root: a Boolean test
  -/
  rooted : rootedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true
  /-- On the session's prover: `ready` returns once, at some input and purses -/
  ready₁ : ∃ w₀ rc x k R, ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R
  /-- On the session's prover: at the requests of Yes its test on the index accepts, and it has a
  trace at what is written, at every OOD sample -/
  serves : ServesAt Z H Yes
  /-- On the session's prover: a value of `ThreadsC` (the invariants of all sub-protocols) with the
  rows' own lists of falls, wherever `ready` returns, at tied inputs whose OOD seed is not set aside
  -/
  threads : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H
    (TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs)
  /-- On the session's prover: the public abort set `Bad` has measure at most zB -/
  bad : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB
  /-- On the session's prover: the abort set `Hid`, which may depend on the private input, has
  measure at most z at tied inputs, at every OOD seed -/
  hid : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
    (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (instanceAsPlainRecord a)) z
  /-- On the session's prover: the rows' falls have measure at most pF, at each fixed coin, at tied
  inputs whose OOD seed is not set aside -/
  falls : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H)
    (fun n w a => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF

/-- **`HonFit` at the three provers, from the hypotheses by name.** This file's head has the limits.
-/
theorem honFit_of_honDebts {Yes : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)}
    {Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed} {ζ pT zB z pF : ℝ≥0∞}
    (d : HonDebts c₀ m₀ Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Yes FT Zs ζ pT zB z pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
      (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _ FT (fun _ _ _ => ∅)
        (guardFall Zs (fallG Z Zp Np cF run₂ run₃ B G H)))
      (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes Zs ζ pT 0 (zB + z + pF) := by
  obtain ⟨D, r, L⟩ := d.laid
  exact honFit_atFiles Z Zp Np cF run₂ run₃ B G H d.scope d.live L c₀ m₀
    (lettersZ Z c₀ m₀).letters.Sd (num_letters Z c₀ m₀) d.below
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) FT (fun _ _ _ => ∅) Zs
    (nineFit_link c₀ m₀ b Z d.scope d.live (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)
      (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) FT Zs
      (keyFive_of_four (extIsEnc_obj Z Fx BT (dataAtFiles flashProveData Z).P HT _ shT) d.keyZero d.keyAccepts
        d.seeds d.keyMeasure))
    d.start
    (plainAt_of_five Z Zp Np cF B G H d.scope L (AtPublicFiles.Written.sealPlain_of_data L.data) d.halved
      d.rooted (width_atFiles Z Zp Np cF d.scope L) d.ready₁)
    d.serves d.threads d.bad d.hid d.falls

/-- The wiring and the OOD-seed wire of `lettersZ Z allZeroDigest []` are the fields `queryLayout` and `seedQueries` of `homeR
b Z`, by unfolding (as in `premW_home_of_letters`, E2E/BridgeDebtsTold.lean). -/
theorem honFit_home_of_letters {Hs : ThreeProvers (protocolAtFiles Z)} {F : Falls Hs} {Yes : FullSizeMatrix → XF → Prop}
    {Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (h : HonFit Hs F (lettersZ Z allZeroDigest []).W (lettersZ Z allZeroDigest []).letters.Sd Yes Zs ζ pT pL pO) :
    HonFit Hs F (homeR b Z).queryLayout (homeR b Z).seedQueries Yes Zs ζ pT pL pO := h

/-- **`honFit_of_honDebts` with its conclusion at `(homeT b Z).Sd dg`**: from `HonDebts` at the pair
(allZeroDigest, []); its conclusion at every value dg of the public reading. -/
theorem honFit_told_of_honDebts (dg : D8) {Yes : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)}
    {Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed} {ζ pT zB z pF : ℝ≥0∞}
    (d : HonDebts allZeroDigest [] Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT Yes FT Zs ζ pT zB z
      pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
      (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _ FT (fun _ _ _ => ∅)
        (guardFall Zs (fallG Z Zp Np cF run₂ run₃ B G H)))
      (homeR b Z).queryLayout ((homeT b Z).Sd dg) Yes Zs ζ pT 0 (zB + z + pF) :=
  AtPublicFiles.LinkLaid.Any.honFit_told_of_home b Z dg
    (honFit_home_of_letters b Z
      (honFit_of_honDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT d))

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Written.sealPlain_of_data
#print axioms AtPublicFiles.Bridge.SeedsAside
#print axioms AtPublicFiles.Bridge.KeyZeroAt
#print axioms AtPublicFiles.Bridge.KeyAccepts
#print axioms AtPublicFiles.Bridge.KeyMeasure
#print axioms AtPublicFiles.Bridge.keyFive_of_four
#print axioms AtPublicFiles.AtFiles.HonDebts
#print axioms AtPublicFiles.AtFiles.honFit_of_honDebts
#print axioms AtPublicFiles.AtFiles.honFit_home_of_letters
#print axioms AtPublicFiles.AtFiles.honFit_told_of_honDebts
