-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeLawB.lean: two statements on the session's honest prover, the family of one request's
honest provers `honestProversByCopyNumber` (E2E/BridgeAlong.lean: the provers of `ProofFile.Honest.honestBatchProverOfFile`, by the copy's
number n). First, its strategy meets `StratLaw` (Johnson/Prover/Print/StratLaw.lean), the condition
that the printer of a file asks of a strategy's own run. Second, four run values of 32 bytes each
are read back off the coins of the key file's prover and of the session's prover into which they
were put. Both are stated in the form of a clause of `LastFits`, the list of named hypotheses on
completeness of Johnson/Goal/Conditions/HomeLast.lean: the first as its clause `lawB`, the second as
its clause `tie`, for all four run values. E2E/KeyHonestLaw.lean has the same for the key file's
prover: the clause `lawT`, and `tie` for two of the four. General in the description, the book of
coins B (`ProverCoinCounts`), the rows G (`Sides`: for each sub-protocol the prover's part and its simulator)
and the prover structure H (`ProofFile.Honest.Prover`). The proofs are calls of lemmas of other files.

`StratLaw C D tF tJ t3 s run2 run3` says of the run of the strategy s, at every verifier randomness:
the joining round's plain part holds the run value run2; the plain part of the seam (the last of the
three rounds without a challenge) is run3; the words of the field elements in the plain part of
every round of the three chains, and the words of every symbol of every oracle message, are below
the prime. A coin κ of the family (`CoinG B R₂ R₃`, E2E/BridgeJoinAtFiles.lean) is ((the shared
chain's coins, r₂), ((the two other chains' coins), r₃)); `Purse` is the type of a chain's coins.

  `famBC_stratLaw`: at all parameters of `honestProversByCopyNumber`, for every number n, private input w, instance x
    and coin κ, the family's strategy meets `StratLaw`. The run values are the field `run` of
    `(J n r₂ default).join` at w, and `(J n r₂ r₃).seam` at w and x
  `famAtFiles_stratLaw`: the same for `onlineProversAlongInstanceMap` (E2E/BridgeAlong.lean): the family read along a
    writing map wr, in the types of the object `(filesAt Z).withProvers P` at three public files Z, for any
    provers P. The instance is a pair a of a request and an OOD sample, and the seam is taken at
    `wr a`
  `lawB_at`: the clause `lawB` at Z, at that object and at the three honest provers
    `proversOf hT hL (onlineProversAlongInstanceMap …)` (E2E/BridgePrivacy.lean); the key file's prover hT and the
    link's prover hL are free parameters. For every index i, committer's coins r, OOD seed e₂,
    request x, number n and coins κ of the three provers, the session's strategy
    `strats.B i r e₂ x n κ` meets `StratLaw`, at the library's own five arguments of the proof
    file's protocol at Z and at the run values `run₂ r₂` and `run₃ r₃`, where r₂ and r₃ are those of
    the third coin in κ. Under two hypotheses on J
  `lawB_famG`: the same at `proversOf hT hL (famG …)` and the object `protocolAtFiles Z` (`famG`, `protocolAtFiles`:
    E2E/BridgeJoinAtFiles.lean). By unfolding, `famG` is `onlineProversAlongInstanceMap` at the description
    `descZ Zp Np cF`, the library's writing map `instanceAsPlainRecord`, the seam `seamZ Z run₂ run₃` and the
    prover structure `provG`: H with the committer's key, with the committer's stored table at the
    item 0 and none at any other item (`Committer.proverAt`,
    Johnson/Desc/ProofFile/Honest/CommitterAt.lean), and with the parts of the rows G. At that seam
    the two hypotheses on J hold by unfolding. Nothing is asked of Zp, Np or cF
  `tie_both`: the clause `tie` for all four run values: `runsBoth (kapBoth (k, r)) = r`, for four
    run values r that meet `Runs4.Fit` (Johnson/Prover/Print/DrawOwes.lean) and any further coins k
  `laws_at`: the clauses `lawT`, `lawB` and `tie` as one conjunction, at one value of the three
    honest provers, `proversLast`, with `runsBoth` and `kapBoth`, at run values of 256 bits
  `proversLast`: an abbreviation: three honest provers at `protocolAtFiles Z`. The first is `offlineProverInThreeProtocols`
    (E2E/KeyHonest.lean), a prover structure for the key file's protocol that is built by `honestBatchProverOfFile`
    from parameters that nothing here fixes (below: the shell `offlineProverInThreeProtocols`), with `keySeamZ Z` for
    J; the second, hL, is a free parameter; the third is `famG` with `digToBytes` for run₂ and for
    run₃
  `KapMore BT B CL`: an abbreviation: the type of the further coins k: the three chains' coins of
    the key file's prover, the link's prover's coin (of type CL), the three chains' coins of the
    session's prover
  `kapBoth`, `runsBoth`: definitions, at run values of 256 bits: the three provers' coins, from the
    further coins and four run values as bytes (`coinKey` twice); the four run values, as bytes, of
    the three provers' coins (`runsKey` twice; both E2E/KeyHonestLaw.lean)

By what. `meets_stratLawC` (Johnson/Desc/ProofFile/Honest/Law/MeetsStratLawC.lean): the two
strategies of the honest side (`sharedPartStrategyTrackingVerifier`, `requestStrategyTrackingVerifier`, Johnson/Desc/ProofFile/Honest/StratC.lean),
zipped, meet `StratLaw`, with no hypothesis. The family's strategy is that zip, by unfolding. For
`tie_both`: `tie_key`, once for each of the two provers. For the first clause of `laws_at`:
`lawT_at` (both E2E/KeyHonestLaw.lean).

Hypotheses of `lawB_at`. hJ: at every n, r₂ and private input, the field `run` of
`(J n r₂ default).join` is `run₂ r₂`. h3: at every n, r₂, r₃, private input and instance,
`(J n r₂ r₃).seam` is `run₃ r₃`.

Compared with the clauses `lawB` and `tie` of `LastFits`, term by term. A is that file's structure
of open parameters (`LastArgs`).
  the kit, the rounds' data, the three fixed plain parts: the same five terms
  the strategy: `(A.Hs Z).strats.B` at i, r, e₂, x, n and κ: the same field of the same structure.
    There i is one index for each value of the weights (`backB`); here it is any
  the run values: there `(A.runs Z κ).2.1` and `(A.runs Z κ).2.2`, where `A.runs` is a field of the
    open parameters; here, in `laws_at`, `(runsBoth κ).2.1` and `(runsBoth κ).2.2`
  `tie`: there `A.runs Z (A.κOf Z (k, r)) = r` under `Runs4.Fit r`; here the same with `runsBoth`
    and `kapBoth`. The further coins k, there of the open type `A.Kap₀ Z`, are here of the type
    `KapMore`
  the object: there `(homeR b Z).protocol`; here `(filesAt Z).withProvers P` in `lawB_at`, and in `lawB_famG` and
    `laws_at` `protocolAtFiles Z`, which is `(filesAt Z).withProvers (dataAtFiles flashProveData Z).P`. That the object there and the
    object here are the same is not shown here. (`linkFour_any`, E2E/BridgeNineLink.lean, gives
    three provers of the type `ThreeProvers (protocolAtFiles Z)` to `homeSide_accepted`,
    Johnson/LinkSim/AtHome/HomeAccepted.lean, which takes them at the type `ThreeProvers (homeR b Z).protocol`: by
    unfolding.)

Limits. The statements hold at every description, book of coins, rows G and prover structure H, also
at an H that has no part for any sub-protocol and at a description that rejects everything. They say
nothing on acceptance. In `famBC_stratLaw` the joining round's run value is that of the shared
part's strategy, which is given r₂ only: it is taken at the default value of the type of r₃, not at
r₃. At `seamZ` the joining round does not read r₃. `tie_both` uses the four sizes in `Runs4.Fit`
only, not the format's test on a run value. What the Limits of E2E/KeyHonestLaw.lean say of the run
value of 256 bits with all bits 0 holds of the first and of the third prover of `proversLast`.
Nothing is shown of any part of a prover: no completeness, and nothing on what a view shows. No
property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyHonestLaw
import E2E.BridgeJoinAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Bridge
open Iop
open OnBytes.Maker (WholeD chainsOf FrontMsg)
open Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)
open Johnson.Prover.Print (StratLaw)

variable {Xi W₀ Rc Ky Tr X₀ X Sd R₂ R₃ : Type} (C : CK) (D : WholeD)
  (tF : FrontMsg (List OnBytes.E)) (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray)
  (F : VerifiableInference.Desc.FileDescription Xi)
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃]
  [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky (FrontMsg (List OnBytes.E))
    (JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **The strategy of the family `honestProversByCopyNumber` meets `StratLaw`**, at every number, private input,
instance and coin. -/
theorem famBC_stratLaw (n : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (κ : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) :
    StratLaw C D tF tJ t3 ((honestProversByCopyNumber C D tF tJ t3 F silent B H J sh ext).strat n w x κ)
      ((J n κ.1.2 default).join w.1 w.2.1 w.2.2).run
      ((J n κ.1.2 κ.2.2).seam w.1 w.2.1 w.2.2 x) :=
  ProofFile.Honest.meets_stratLawC C D tF tJ t3 F B H (J n κ.1.2 default) (J n κ.1.2 κ.2.2) sh w κ.1.1 x
    κ.2.1

end AtPublicFiles.Bridge

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull front₀ join₀)
open OnBytes.Slice (frS)
open _root_.Run (ckP digToBytes)
open VerifiableInference.Desc (FileDescription Chain)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides)
open Johnson.Prover.Print (StratLaw Runs4)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J

/-! ## The clause `lawB` -/

section AtZ
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

/-- The same for `onlineProversAlongInstanceMap`: along the writing map, in the types of the object at Z. -/
theorem famAtFiles_stratLaw (n : ℕ)
    (w : (Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) (a : XF × RecFull)
    (κ : CoinG B R₂ R₃) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      ((onlineProversAlongInstanceMap Z F wr silent B H J sh ext P).strat n w a κ)
      ((J n κ.1.2 default).join w.1 w.2.1 w.2.2).run
      ((J n κ.1.2 κ.2.2).seam w.1 w.2.1 w.2.2 (wr a)) :=
  famBC_stratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty F silent B H J sh ext n w (wr a) κ

/-- **The clause `lawB`**, at any key file's prover hT and any link's prover hL, under two
hypotheses on J. That this object is the one of `LastFits`, `(homeR b Z).protocol`, is not shown here. -/
theorem lawB_at (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray)
    (hJ : ∀ n r2 w₀ rc sd, ((J n r2 default).join w₀ rc sd).run = run₂ r2)
    (h3 : ∀ n r2 r3 w₀ rc sd x, (J n r2 r3).seam w₀ rc sd x = run₃ r3)
    (hT : Honest ((filesAt Z).withProvers P).offline
      ((Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed))
    (hL : Honest ((filesAt Z).withProvers P).link ((Cz Z).I ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed)))
    (i : (Cz Z).I) (r : ((filesAt Z).withProvers P).EncodingRandomness) (e₂ : ((filesAt Z).withProvers P).OutOfDomainSeed) (x : XF) (n : ℕ)
    (κ : hT.Coin × hL.Coin × CoinG B R₂ R₃) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      ((proversOf hT hL (onlineProversAlongInstanceMap Z F wr silent B H J sh ext P)).strats.B i r e₂ x n κ)
      (run₂ κ.2.2.1.2) (run₃ κ.2.2.2.2) := by
  have h := famAtFiles_stratLaw Z F wr silent B H J sh ext P n (i, r, e₂)
    (x, ((filesAt Z).withProvers P).recOf i r e₂) κ.2.2
  rw [hJ, h3] at h
  exact h

end AtZ

section AtG
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **The clause `lawB` at `famG`**, the family of E2E/BridgeJoinAtFiles.lean: there the two
hypotheses on J hold by unfolding. -/
theorem lawB_famG (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e₂ : (protocolAtFiles Z).OutOfDomainSeed) (x : XF) (n : ℕ)
    (κ : hT.Coin × hL.Coin × CoinG B R₂ R₃) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      ((proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)).strats.B i r e₂ x n κ)
      (run₂ κ.2.2.1.2) (run₃ κ.2.2.2.2) :=
  lawB_at Z (descZ Zp Np cF) LPFD.Full.instanceAsPlainRecord silInst B (provG Z Zp Np cF B G H)
    (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) (dataAtFiles flashProveData Z).P run₂ run₃
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) hT hL i r e₂ x n κ

end AtG

/-! ## The clause `tie`, for all four run values -/

/-- The further coins: the three chains' coins of the key file's prover, the link's prover's coin,
the three chains' coins of the session's prover. -/
abbrev KapMore (BT B : ProverCoinCounts) (CL : Type) : Type :=
  (Purse BT.shared × Purse BT.first × Purse BT.second) × CL ×
    (Purse B.shared × Purse B.first × Purse B.second)

/-- The three provers' coins, from the further coins and four run values as bytes. -/
def kapBoth {BT B : ProverCoinCounts} {CL : Type} (z : KapMore BT B CL × Runs4) :
    KeyCoin BT × CL × KeyCoin B :=
  (coinKey z.1.1 z.2.1, z.1.2.1, coinKey z.1.2.2 z.2.2)

/-- The four run values, as bytes, of the three provers' coins. -/
def runsBoth {BT B : ProverCoinCounts} {CL : Type} (κ : KeyCoin BT × CL × KeyCoin B) : Runs4 :=
  (runsKey κ.1, runsKey κ.2.2)

/-- **The clause `tie`, for all four run values**: four run values that meet `Runs4.Fit` are read
back off the coins into which they were put. -/
theorem tie_both {BT B : ProverCoinCounts} {CL : Type} (k : KapMore BT B CL) (r : Runs4) (h : Runs4.Fit r) :
    runsBoth (kapBoth (k, r)) = r :=
  Prod.ext (tie_key k.1 r.1 h.sizeT2 h.sizeT3) (tie_key k.2.2 r.2 h.sizeB2 h.sizeB3)

/-! ## The three clauses at one value of the three provers -/

/- The two instances at run values of 256 bits, by name (E2E/KeyHonestLaw.lean): `proversLast`
contains these terms. -/
attribute [local instance] digInhabited digNonempty

section One
variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {TrT X₀T XT : Type} (BT : ProverCoinCounts)
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey TrT X₀T XT)
  (shT : OnBytes.TableKey → Fx.S₂)
  (extT : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))

/-- The three honest provers: the shell `offlineProverInThreeProtocols` for the key file; any prover hL for the link;
the family `famG` for the session. -/
abbrev proversLast : OnBytes.Prover.ThreeProvers (protocolAtFiles Z) :=
  proversAt Z Fx BT HT (keySeamZ Z) shT extT (dataAtFiles flashProveData Z).P hL
    (famG Z Zp Np cF digToBytes digToBytes B G H)

/-- **The clauses `lawT`, `lawB` and `tie` at one value of the three provers.** That the object
`protocolAtFiles Z` is the one of `LastFits`, `(homeR b Z).protocol`, is not shown here. -/
theorem laws_at :
    (∀ i r e₁ (κ : KeyCoin BT × hL.Coin × KeyCoin B),
      StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
        (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty
        ((proversLast Z Fx BT HT shT extT Zp Np cF B G H hL).strats.T i r e₁ κ)
        (runsBoth κ).1.1 (runsBoth κ).1.2) ∧
    (∀ i r e₂ x n (κ : KeyCoin BT × hL.Coin × KeyCoin B),
      StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
        ((proversLast Z Fx BT HT shT extT Zp Np cF B G H hL).strats.B i r e₂ x n κ)
        (runsBoth κ).2.1 (runsBoth κ).2.2) ∧
    ∀ (k : KapMore BT B hL.Coin) (r : Runs4), Runs4.Fit r → runsBoth (kapBoth (k, r)) = r :=
  ⟨fun i r e₁ κ => lawT_at Z Fx BT HT shT extT (dataAtFiles flashProveData Z).P hL
      (famG Z Zp Np cF digToBytes digToBytes B G H) i r e₁ κ,
    fun i r e₂ x n κ => lawB_famG Z Zp Np cF digToBytes digToBytes B G H
      (offlineProverInThreeProtocols Z Fx BT HT (keySeamZ Z) shT extT (dataAtFiles flashProveData Z).P) hL i r e₂ x n κ,
    fun k r h => tie_both k r h⟩

end One

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Bridge.famBC_stratLaw
#print axioms AtPublicFiles.AtFiles.famAtFiles_stratLaw
#print axioms AtPublicFiles.AtFiles.lawB_at
#print axioms AtPublicFiles.AtFiles.lawB_famG
#print axioms AtPublicFiles.AtFiles.tie_both
#print axioms AtPublicFiles.AtFiles.laws_at
#print axioms AtPublicFiles.AtFiles.KapMore
#print axioms AtPublicFiles.AtFiles.kapBoth
#print axioms AtPublicFiles.AtFiles.runsBoth
#print axioms AtPublicFiles.AtFiles.proversLast
