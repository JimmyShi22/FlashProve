-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeAlong.lean: `OneExact` and `HidZero`, two hypotheses of E2E/BridgePrivacy.lean, for the
family of one request's honest provers of `ProofFile.Honest.honestBatchProverOfFile`, read along a writing map.
`honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) is the honest side of the proof file's
protocol, stated at a description's own instance type Xi. The instances of the library's object are
pairs of a request and an out-of-domain (OOD) sample, and wr : (request, OOD sample) → Xi writes
such a pair as an instance of the description. Here the family at Xi is read along wr as a family of
the object's own protocol for one request. For that family `OneExact` follows from the same
statement at Xi (`ExactAt`), and `HidZero` is proved with no hypothesis. It is for files that have
to show `Sims.Good` and `StopsSmall`, the fields `good` and `stops` of `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean: the hypotheses of the statement of index privacy). General in the
description, the writing map and the prover: first at the library's three protocols of the full size
at any parameters (`threeProtocolsAtFullSize`), then at three public files Z, at the parameters from which the
verifier is compiled. At Z nothing is asked of Z: neither `InScope Z`, nor that the IOP's own test
on the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`), nor an equation of protocols.

  `oneExact_along`: `OneExact` of `famAlong`, from `ExactAt` of `fam₀` at a simulator simOne and a
    relation Tied. The simulator at the number n and the instance a is `simOne n (wr a)`, with each
    disclosed view read in the object's type (`viewRe`: the same data); tied: `Tied n w (wr a)`
  `hidZero_along`: `HidZero` of `famAlong` at the library's wiring `wireOfFullD`: the abort set
    `Hid`, which may depend on the private input, does not depend on the proof-of-work test bits.
    Proved for every description F, writing map wr, book of coins B (`ProverCoinCounts`), prover structure H
    (`ProofFile.Honest.Prover`) and seam J (`KeyAndJoiningRoundMessages`)
  `oneExact_atFiles`, `hidZero_atFiles`: the same two for `onlineProversAlongInstanceMap`: the first at the object
    `(filesAt Z).withProvers P`, for any provers P; the second at P := `(dataAtFiles flashProveData Z).P`, the provers in
    the parameters from which the verifier is compiled, and at these parameters' wiring
    `((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W`, at every digest c₀ and list of digests m₀
  `good_atFiles`: `Sims.Good` at that object and wiring, at the provers
    `proversOf hT hL (onlineProversAlongInstanceMap …)` and the session's simulator of `oneExact_atFiles`, with the
    clause on the session's prover (the field `B`) at error 0. The clauses on the key file's prover
    and on the link's (`T`, `Lk`) are taken over from a hypothesis
  `stops_atFiles`: `StopsSmall` at the same object, wiring and provers, with the field `B` at z; `T`
    and `Lk` are taken over likewise
  `ExactAt Fm sim Tied`: a definition: at tied inputs, at every verifier randomness outside `Hid`,
    the honest output is the named simulator's. For a family Fm of any protocol; `OneExact` is this
    at an object's protocol for one request
  `ExactAt.re`: `ExactAt` of Fm gives `ExactAt` of `Fm.re f acc g`, at the simulator `sim n (f x)`
    with its views read by `viewRe f acc`, and at the relation `Tied n (g w) (f x)`
  `Family.re Fm f acc g`: a definition: the family Fm with instances read through f and private
    inputs through g, at the protocol `reAcc Q f acc`, acc any decision. `re_at`: at each number n
    it is `honestRe` of `Fm.at n`, by unfolding
  `honestProversByCopyNumber`: a definition: the family of `(honestBatchProverOfFile … (J n) …).one` by the copy's number n, in all
    parameters of `honestBatchProverOfFile`; only the seam depends on n. `famBC_at`: at n it is that prover, by
    unfolding
  `fam₀`, `onlineProversAtOwnInstances`: abbreviations: `honestProversByCopyNumber` at Xi, at the proof file's rounds' data and fixed plain
    parts: for `fam₀` those of `threeProtocolsAtFullSize`, for `onlineProversAtOwnInstances` those at Z
  `famAlong`, `onlineProversAlongInstanceMap`: definitions: `fam₀` and `onlineProversAtOwnInstances` under `Family.re`, at f := wr, g := id
    and acc := the object's own decision; the type is `Family (….withProvers P).onlineBatch.loc (I × EncodingRandomness × OutOfDomainSeed)`, in
    the object's types

By what. The honest side is not stated anew at the object's types and is not pulled back part by
part; no equation of protocols and no cast is used. Output, abort sets and answers do not read a
protocol's decision (E2E/OneAlong.lean), and but for the decision the object's protocol for one
request is the description's along wr, by unfolding: it is `reAcc Q wr acc` (same file), Q the
description's protocol and acc the object's decision. So the object's decision on the proof file
(runP) and the description's test on the three rounds without a challenge (silent) are free
parameters in section 2. At Z silent still is one, and nothing is asked of `(dataAtFiles flashProveData Z).runP`.
That runP is the description's decision along wr matters for acceptance only. At Z, where the IOP's
own test on the public files accepts, `protocol_along` (E2E/TiedAlong.lean) has the equation of the
two batch protocols, decisions included, at a description of which `LaidAt` holds, at wr :=
`LPFD.Full.instanceAsPlainRecord` and silent := `silInst`. What is stated on acceptance at Z is in
E2E/BridgeLinkAtFiles.lean and E2E/BridgeJoinAtFiles.lean, at such a description. Called: `exact_re`
(E2E/OneAlong.lean) for `ExactAt.re`; `AtPublicFiles.Reads.hid_zero` (E2E/DrawsBlind.lean) for `hidZero_along`
and `hidZero_atFiles`; `good_of_exact` and `stops_of_small` (E2E/BridgePrivacy.lean) for
`good_atFiles` and `stops_atFiles`. Definitions: `Family` (E2E/HonestFamily.lean); `OneExact`,
`HidZero`, `HidSmall`, `ValidTied`, `ExtIsEnc`, `proversOf` (E2E/BridgePrivacy.lean); `batchOf`
(Johnson/Desc/ProofFile/Honest/Record.lean); `threeProtocolsAtFullSize`, `wireOfFullD`
(Johnson/Flat/Dec/WiresAtSizes.lean); `Cz`, `filesAt` (E2E/ObjectAtFiles.lean); `dataAtFiles`
(Johnson/Goal/Tie/DescriptionOfData.lean); `DescriptionDataAtFiles.inputFieldsAtReadings` (Johnson/Goal/Tie/DescriptionOnDecodedProof.lean).

Hypotheses of `good_atFiles`. g: `Sims.Good` with the same three simulators, wiring, ok, Gs and
Ryes, at `proversOf hT hL Fm'` for any family Fm' and any error zO; only its fields `T` and `Lk` are
read. h: `ExactAt` of `onlineProversAtOwnInstances` at simOne and Tied. h2: `ValidTied`: wherever `ok i`, `Gs e` and
`Ryes i x` hold, Tied holds at every number n and committer's randomness r, at (i, r, e) and at what
wr writes for the request x with the OOD sample of (i, r, e). he: `ExtIsEnc`: the family's external
strings are the encoded index. Of `stops_atFiles`. s: `StopsSmall` at any family Fm' and any pO,
read as g is. hz: `HidSmall`: at tied inputs the measure of `Hid` is at most z; here Tied is a
relation at the object's own instances. h2: `ValidTied` at that Tied. In both, hT and hL are free
parameters: any honest provers of the key file's protocol and of the link.

Limits.
- Those of E2E/BridgePrivacy.lean, "error 0 is no result by itself" among them.
- At Z the object and the wiring are those from which the verifier is compiled; the prover is
  arbitrary: the description F, the writing map, the book of coins, the prover structure H and the
  seam are free parameters. Nothing ties them to Z but the proof file's rounds' data and fixed plain
  parts at which `honestProversByCopyNumber` is taken, and the configuration `Cz Z` in the types of H, J and ext. At a
  description that is not the verifier's the statements hold and speak of a prover whose proofs the
  verifier may reject.
- "At every Z" is nominal where the IOP's own test on the public files rejects: there the rounds'
  data are empty and all decisions reject (E2E/ObjectAtFiles.lean's Limits, read off the library's
  definitions: no theorem there states it), so the statements speak of a protocol that accepts
  nothing.
- Nothing on acceptance in this file: acceptance reads the decision (E2E/BridgeLinkAtFiles.lean).
- `ExactAt (honestProversByCopyNumber …) …` is a hypothesis. E2E/BridgeExact.lean proves it at Z from hypotheses of its
  own on Z, the description and the rows G (`Sides`); the lemma that it calls
  (`ProofFile.Honest.one_exact_atItem_mute`, Johnson/Desc/ProofFile/Honest/Law/Rule/TiedAtItem.lean) has
  hypotheses on the description, the rows and the rounds' data.
- In `oneExact_along`, `oneExact_atFiles` and `good_atFiles` the simulator is bound next to the free
  parameter Tied (in `good_atFiles` next to ok, Gs and Ryes too), not before it: at a parameter that
  holds at one index only the simulator may lean on that index, and `Sims.Good` then says nothing on
  hiding the index (E2E/BridgeJoinAtFiles.lean's Limits).
- No value is shown here to meet the hypotheses of `good_atFiles` or of `stops_atFiles` together,
  and the statement of index privacy is not called.
-/
import E2E.OneAlong
import E2E.ObjectAtFiles
import E2E.BridgePrivacy
import E2E.DrawsBlind

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along

/-! ## 1. General -/

section Fam
variable {Y Y' : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt Wt' : Type}

/-- The family Fm with instances read through f and private inputs through g, at the protocol
`reAcc Q f acc` (E2E/OneAlong.lean), whose decision is acc. -/
def Family.re (Fm : Family Q Wt) (f : Y' → Y) (acc : Y' → E.Str → Tr Q.shape → Bool)
    (g : Wt' → Wt) : Family (reAcc Q f acc) Wt' where
  Coin := Fm.Coin
  ext := fun n w => Fm.ext n (g w)
  strat := fun n w x c => Fm.strat n (g w) (f x) c
  Bad := Fm.Bad
  Hid := fun n w x => Fm.Hid n (g w) (f x)

theorem re_at (Fm : Family Q Wt) (f : Y' → Y) (acc : Y' → E.Str → Tr Q.shape → Bool)
    (g : Wt' → Wt) (n : ℕ) : (Fm.re f acc g).at n = honestRe (Fm.at n) f acc g := rfl

/-- At tied inputs, at every verifier randomness outside `Hid`, the honest output is the named
simulator's. -/
def ExactAt (Fm : Family Q Wt)
    (sim : ℕ → Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q)))
    (Tied : ℕ → Wt → Y → Prop) : Prop :=
  ∀ n w x, Tied n w x → ∀ ρ, ρ ∉ (Fm.at n).Hid w x →
    (Fm.at n).output w x ρ = sim n x ρ (Q.extAns x ρ ((Fm.at n).ext w))

/-- **`ExactAt` goes over to the family `Fm.re f acc g`**: the simulator at x is `sim n (f x)`, with
each disclosed view read by `viewRe f acc`; tied: `Tied n (g w) (f x)`. -/
theorem ExactAt.re {Fm : Family Q Wt}
    {sim : ℕ → Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))}
    {Tied : ℕ → Wt → Y → Prop} (h : ExactAt Fm sim Tied) (f : Y' → Y)
    (acc : Y' → E.Str → Tr Q.shape → Bool) (g : Wt' → Wt) :
    ExactAt (Fm.re f acc g)
      (fun n x ρ a => (sim n (f x) ρ a).map (Option.map (viewRe f acc)))
      (fun n w x => Tied n (g w) (f x)) :=
  fun n w x ht ρ hρ => exact_re (Fm.at n) f acc g (sim n) w x ρ (h n (g w) (f x) ht ρ hρ)

end Fam

section BC
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts)
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
  (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃]
  [Inhabited R₃] (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- The family of one request's honest provers of `honestBatchProverOfFile`, by the copy's number n: the seam is
`J n`. The coins and the public abort set `Bad` are written at `J 0`; they do not read the seam
(`famBC_at`). -/
def honestProversByCopyNumber : Family (batchOf C D tF tJ t3 F silent).loc (W₀ × Rc × Sd) where
  Coin := (honestBatchProverOfFile C D tF tJ t3 F silent B H (J 0) sh ext).one.Coin
  finCoin := (honestBatchProverOfFile C D tF tJ t3 F silent B H (J 0) sh ext).one.finCoin
  neCoin := (honestBatchProverOfFile C D tF tJ t3 F silent B H (J 0) sh ext).one.neCoin
  ext := fun _ => ext
  strat := fun n => (honestBatchProverOfFile C D tF tJ t3 F silent B H (J n) sh ext).one.strat
  Bad := (honestBatchProverOfFile C D tF tJ t3 F silent B H (J 0) sh ext).one.Bad
  Hid := fun n => (honestBatchProverOfFile C D tF tJ t3 F silent B H (J n) sh ext).one.Hid

theorem famBC_at (n : ℕ) :
    (honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).at n =
      (honestBatchProverOfFile C D tF tJ t3 F silent B H (J n) sh ext).one := rfl

end BC

end AtPublicFiles.Bridge

/-! ## 2. At the library's object -/

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (batchOf Prover KeyAndJoiningRoundMessages ProverCoinCounts)

section General
variable {X Xi : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool)
  (runP : X × RecFull → View → View → View → Bool) (F : FileDescription Xi) (wr : X × RecFull → Xi)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  (silent : Xi → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) Xi Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed Xi Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → F.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- `honestProversByCopyNumber` at the description's own instances, at the proof file's rounds' data and fixed plain
parts of `threeProtocolsAtFullSize`. -/
abbrev fam₀ :=
  honestProversByCopyNumber (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP)
    ByteArray.empty F silent B H J sh ext

/-- `fam₀` read along the writing map wr, as a family of the object's protocol for one request. The
decision is the object's own. -/
def famAlong :
    Family ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).onlineBatch.loc
      ((DecR.configurationOfStoredTable A R).I ×
        ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).EncodingRandomness ×
        ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).OutOfDomainSeed) :=
  (fam₀ A R DP F rP silent B H J sh ext).re wr
    ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).onlineBatch.loc.accept
    id

/-- **`OneExact` of `famAlong`**, from `ExactAt` of `fam₀`: the same statement at the description's
own instances. -/
theorem oneExact_along
    {simOne : ℕ → Xi → (ρ : Rho (batchOf (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
        (OnBytes.Flat.join₀ rP) ByteArray.empty F silent).loc.shape) →
      ((Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Pos →
        Option (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Sym) →
      PMF (Option (DView (batchOf (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
        (OnBytes.Flat.join₀ rP) ByteArray.empty F silent).loc))}
    {Tied : ℕ → (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) ×
      (DecR.configurationOfStoredTable A R).Seed → Xi → Prop}
    (h : ExactAt (fam₀ A R DP F rP silent B H J sh ext) simOne Tied) :
    OneExact
      (famAlong A R DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B H J sh ext P)
      (fun n a ρ ans => (simOne n (wr a) ρ ans).map (Option.map (viewRe wr _)))
      (fun n w a => Tied n w (wr a)) :=
  h.re wr _ id

/-- **`HidZero` of `famAlong`, at the library's wiring `wireOfFullD`**, with no hypothesis. -/
theorem hidZero_along (K depthReqT : ℕ) :
    HidZero
      (famAlong A R DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B H J sh ext P)
      (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) :=
  fun n w a ρ => AtPublicFiles.Reads.hid_zero (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty K (chalP .two K) F silent B H (J n) sh ext w (wr a) ρ

end General

/-! ## 3. At three public files Z -/

section AtZ
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open OnBytes.WholeKey (sessionAt)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open TypedOracleCompiler.Compile.Batch.Cms (wBC)

variable (Z : PublicFiles) {Xi : Type} (F : FileDescription Xi) (wr : XF × RecFull → Xi)
  (silent : Xi → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) Xi Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed Xi Ky
    (OnBytes.Maker.FrontMsg (List OnBytes.E)) (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (sh : Ky → F.S₂)
  (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (P : (filesAt Z).Provers)

/-- `honestProversByCopyNumber` at the description's own instances, at the proof file's rounds' data and fixed plain
parts at Z. -/
abbrev onlineProversAtOwnInstances :=
  honestProversByCopyNumber (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty F silent B H J sh ext

/-- `onlineProversAtOwnInstances` read along the writing map wr, as a family of the protocol for one request of the object
at Z. The decision is the object's own. -/
def onlineProversAlongInstanceMap :
    Family ((filesAt Z).withProvers P).onlineBatch.loc
      ((Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) :=
  (onlineProversAtOwnInstances Z F silent B H J sh ext).re wr ((filesAt Z).withProvers P).onlineBatch.loc.accept id

theorem oneExact_atFiles {simOne} {Tied}
    (h : ExactAt (onlineProversAtOwnInstances Z F silent B H J sh ext) simOne Tied) :
    OneExact (onlineProversAlongInstanceMap Z F wr silent B H J sh ext P)
      (fun n a ρ ans => (simOne n (wr a) ρ ans).map (Option.map (viewRe wr _)))
      (fun n w a => Tied n w (wr a)) :=
  h.re wr _ id

/-- **`HidZero` of `onlineProversAlongInstanceMap`, at the wiring of the parameters from which the verifier is
compiled**: proved, at every Z, digest c₀ and list of digests m₀. -/
theorem hidZero_atFiles (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) :
    HidZero (onlineProversAlongInstanceMap Z F wr silent B H J sh ext (dataAtFiles flashProveData Z).P)
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W :=
  fun n w a ρ => AtPublicFiles.Reads.hid_zero (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty _ (chalP .two _) F silent B H (J n) sh ext w (wr a) ρ

variable (hT : Honest ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).offline
    ((Cz Z).I × ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness ×
      ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).OutOfDomainSeed))
  (hL : Honest ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).link
    ((Cz Z).I × (((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness ×
        ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).OutOfDomainSeed) ×
      (((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness × ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).OutOfDomainSeed)))

/-- **`Sims.Good` at Z, with the clause on the session's prover at error 0.** It is the structure
that the statement of index privacy takes as a hypothesis; the clauses on the key file's prover and
on the link's are taken over from g. "Error 0" is no result by itself: E2E/BridgePrivacy.lean's
Limits. -/
theorem good_atFiles (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) {simOne} {Tied}
    {sT sL} {ok Gs Ryes} {zT zL zO : ℝ≥0∞} {Fm'}
    (g : OnBytes.WholeKey.Sims.Good
      ⟨sT, sL, fun n a ρ ans => (simOne n (wr a) ρ ans).map (Option.map (viewRe wr _))⟩
      (proversOf hT hL Fm') ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ok Gs Ryes zT zL zO)
    (h : ExactAt (onlineProversAtOwnInstances Z F silent B H J sh ext) simOne Tied)
    (h2 : ValidTied (fun n w a => Tied n w (wr a)) ok Gs Ryes)
    (he : ExtIsEnc (onlineProversAlongInstanceMap Z F wr silent B H J sh ext (dataAtFiles flashProveData Z).P)) :
    OnBytes.WholeKey.Sims.Good
      ⟨sT, sL, fun n a ρ ans => (simOne n (wr a) ρ ans).map (Option.map (viewRe wr _))⟩
      (proversOf hT hL (onlineProversAlongInstanceMap Z F wr silent B H J sh ext (dataAtFiles flashProveData Z).P))
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ok Gs Ryes zT zL 0 :=
  good_of_exact hT hL _ _ g
    (oneExact_atFiles Z F wr silent B H J sh ext (dataAtFiles flashProveData Z).P h) h2 he

/-- **`StopsSmall` at Z, with the clause on the session's prover at z.** The clauses on the key
file's prover and on the link's are taken over from s. -/
theorem stops_atFiles (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) {Tied}
    {ok Gs Ryes} {pT pL pO z : ℝ≥0∞} {Fm'}
    (s : OnBytes.WholeKey.StopsSmall (proversOf hT hL Fm') ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ok Gs
      Ryes
      pT pL pO)
    (hz : HidSmall (onlineProversAlongInstanceMap Z F wr silent B H J sh ext (dataAtFiles flashProveData Z).P) Tied z)
    (h2 : ValidTied Tied ok Gs Ryes) :
    OnBytes.WholeKey.StopsSmall
      (proversOf hT hL (onlineProversAlongInstanceMap Z F wr silent B H J sh ext (dataAtFiles flashProveData Z).P))
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ok Gs Ryes pT pL z :=
  stops_of_small hT hL _ _ s hz h2 (hidZero_atFiles Z F wr silent B H J sh ext c₀ m₀)

end AtZ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Bridge.re_at
#print axioms AtPublicFiles.Bridge.ExactAt.re
#print axioms AtPublicFiles.Bridge.famBC_at
#print axioms AtPublicFiles.AtFiles.oneExact_along
#print axioms AtPublicFiles.AtFiles.hidZero_along
#print axioms AtPublicFiles.AtFiles.oneExact_atFiles
#print axioms AtPublicFiles.AtFiles.hidZero_atFiles
#print axioms AtPublicFiles.AtFiles.good_atFiles
#print axioms AtPublicFiles.AtFiles.stops_atFiles
#print axioms AtPublicFiles.Bridge.Family.re
#print axioms AtPublicFiles.Bridge.ExactAt
#print axioms AtPublicFiles.Bridge.honestProversByCopyNumber
#print axioms AtPublicFiles.AtFiles.fam₀
#print axioms AtPublicFiles.AtFiles.famAlong
#print axioms AtPublicFiles.AtFiles.onlineProversAtOwnInstances
#print axioms AtPublicFiles.AtFiles.onlineProversAlongInstanceMap
