-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyHonestLaw.lean: two statements on `keyHonestAny` (E2E/KeyHonest.lean), a prover structure for
the key file's protocol that is built by `honestBatchProverOfFile` from parameters that nothing here fixes (below:
the shell `keyHonestAny`). First, its strategy meets `StratLaw`
(Johnson/Prover/Print/StratLaw.lean), the condition that the printer of a file asks of a strategy's
own run. Second, two run values of 32 bytes each are read back off the shell's coin into which they
were put. Both are stated in the form of a clause of `LastFits`, the list of named hypotheses on
completeness of Johnson/Goal/Conditions/HomeLast.lean: the first as its clause `lawT`, the second as
its clause `tie`, for the key file's two run values out of the four. General in the description Fx,
the book of coins B (`ProverCoinCounts`) and the prover structure H (`ProofFile.Honest.Prover`). The proofs are calls
of lemmas of other files.

`StratLaw C D tF tJ t3 σ run2 run3` says of the run of the strategy σ, at every verifier randomness:
the joining round's plain part holds the run value run2; the plain part of the seam (the last of the
three rounds without a challenge) is run3; the words of the field elements in the plain part of
every round of the three chains, and the words of every symbol of every oracle message, are below
the prime. A coin c of the shell is ((the shared chain's coins, r₂), ((the two other chains' coins),
r₃)); `Purse` is the type of a chain's coins.

  `keyHonest_stratLaw`: at all parameters and any decision runK of the key file, for every private
    input w, instance x and coin c, the shell's strategy meets `StratLaw`. The run values are the
    field `run` of `(J r₂ default).join` at w, and `(J r₂ r₃).seam` at w and `keyInstanceOfOutOfDomainSample x`, the written
    key of x
  `keySeam_stratLaw`: the same at J := `keySeam val₂ val₃` (E2E/KeyHonest.lean): the run values are
    `val₂ r₂` and `val₃ r₃`, read off the coin only
  `lawT_cut`, `lawT_at`: the clause `lawT` at three public files Z, at this file's objects (see the
    comparison below): `objAt Z P`, whose index type is cut to the matrices in range, and
    `(filesAt Z).withProvers P`. The three honest provers are `proversCut` and `proversAt`
    (E2E/KeyWithSession.lean). Their first field is the shell at Z's parameters, with `keySeamZ Z`
    for J (`keyHonestCut`, which reads the index through the inclusion, and `offlineProverInThreeProtocols`); the
    link's prover hL and the session's family Fm are free parameters. For every index i, committer's
    coins r, OOD seed e₁ and coins κ of the three provers, the key file's strategy
    `strats.T i r e₁ κ` meets `StratLaw`, at the library's own five arguments of the key file's
    protocol at Z and at the run values `runsKey κ.1`
  `tie_key`: the clause `tie` for the key file's two run values: `runsKey (coinKey p r) = r`, where
    each of the two byte strings of r has 32 bytes
  `tie_key_fit`: the same under the hypothesis of the clause `tie`: for four run values r that meet
    `Runs4.Fit` (Johnson/Prover/Print/DrawOwes.lean), the equation holds of the first two, `r.1`
  `tie_key_no`: a negative test on the hypotheses of `tie_key`: `digToBytes (digS ByteArray.empty)`
    is not the empty byte string
  `KeyCoin B`: a definition: the type of the shell's coins where r₂ and r₃ are run values of 256
    bits (`Dig 256`)
  `runsKey`, `coinKey`: definitions, at run values of 256 bits: the two run values of a coin, as
    bytes; a coin, from the three chains' coins and two run values as bytes
  `keySeamZ Z`: a definition: `keySeam` at Z's parameters, with `digToBytes` for val₂ and for val₃
  `digInhabited`, `digNonempty`: the two instances for `Dig 256`, with names: the provers of
    `lawT_cut` and `lawT_at` contain these terms

By what. `meets_stratLawC` (Johnson/Desc/ProofFile/Honest/Law/MeetsStratLawC.lean): the two
strategies of the honest side (`sharedPartStrategyTrackingVerifier`, `requestStrategyTrackingVerifier`, Johnson/Desc/ProofFile/Honest/StratC.lean),
zipped, meet `StratLaw`, with no hypothesis. The shell's strategy is that zip, by unfolding. For
`tie_key`: `digToBytes_digS` (Run/ChainRow.lean). For `tie_key_no`: `size_digToBytes`
(Run/CodingPage160.lean).

Compared with the clause `lawT` of `LastFits`, term by term. A is that file's structure of open
parameters (`LastArgs`).
  the kit, the rounds' data, the three fixed plain parts: the same five terms
  the strategy: `(A.Hs Z).strats.T` at i, r, e₁ and κ: the same field of the same structure. There i
    and r are one index and one value of the committer's coins for each pair of weights and
    commitment randomness (`backB`, `A.endArgs.pads`); here they are any
  the run values: there `(A.runs Z κ).1.1` and `(A.runs Z κ).1.2`, where `A.runs` is a field of the
    open parameters; here the two components of `runsKey κ.1`. Whoever sets `A.runs` sets its first
    component so
  the object: there `(homeR b Z).protocol`; here `objAt Z P` or `(filesAt Z).withProvers P`. That the object there
    and the object here are the same is not shown here

Limits. The statements hold at every description, book of coins and prover structure H, also at an H
that has no part for any sub-protocol and at a description that rejects everything. They say nothing
on acceptance. In `keyHonest_stratLaw` the joining round's run value is that of the shared part's
strategy, which is given r₂ only: it is taken at the default value of the type of r₃, not at r₃
(E2E/KeyHonestPlain.lean). At `keySeam` the joining round does not read r₃. `tie_key` asks for 32
bytes and no more; the clause `tie` gives more (the format's test on a run value), which is not
used. The same for the proof file's two run values is not in this file. The type of run values of
256 bits has a value that the format refuses: all bits 0, the default value of `digInhabited`. As
bytes it is 32 zero bytes, at which the format's test on a run value rejects (`runOk`,
Fmt/Rules4.lean; read off the library's definitions, with no theorem here). `StratLaw` holds at a
coin with such a value too, and `tie` is asked only of run values that pass that test. So "each
coin's run values pass the format's test" does not hold of the shell at `keySeamZ`. Nothing is shown
of any part of a prover: no completeness, and nothing on what a view shows. No property of a
protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyHonestPlain
import E2E.KeyWithSession
import Johnson.Desc.ProofFile.Honest.Law.MeetsStratLawC
import Johnson.Prover.Print.DrawOwes
import Run.ChainRow

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run (ckP digToBytes digS)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)
open Johnson.Prover.Print (StratLaw Runs4)
open OnBytes.Prover (ThreeProvers)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

section General
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fx : FileDescription KeyInst)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed KeyInst Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (runK : RecFull → View → View → View → Bool)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- **The strategy of the shell `keyHonestAny` meets `StratLaw`**, at every private input, instance
and coin. -/
theorem keyHonest_stratLaw
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull) (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) :
    StratLaw (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
      ByteArray.empty
      ((keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
        P).strat w x c)
      ((J c.1.2 default).join w.1 w.2.1 w.2.2).run
      ((J c.1.2 c.2.2).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample x)) :=
  ProofFile.Honest.meets_stratLawC (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
    (OnBytes.Flat.join₀ rK) ByteArray.empty Fx B H (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1
    (keyInstanceOfOutOfDomainSample x) c.2.1

end General

section Filled
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fx : FileDescription KeyInst)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  {Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst
    OnBytes.TableKey Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray) (sh : OnBytes.TableKey → Fx.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (runK : RecFull → View → View → View → Bool)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- **At `keySeam` the two run values are read off the coin only.** -/
theorem keySeam_stratLaw
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull) (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) :
    StratLaw (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
      ByteArray.empty
      ((keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H
        (keySeam A R val₂ val₃) sh ext runK P).strat w x c)
      (val₂ c.1.2) (val₃ c.2.2) :=
  keyHonest_stratLaw A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H
    (keySeam A R val₂ val₃) sh ext runK P w x c

end Filled

/-! ## Run values of 256 bits -/

/-- **The default value of the type of run values of 256 bits**: all bits 0. It has a name, so that
a file that uses a statement of this file with another one on the same provers can give both the
same term: `attribute [local instance] AtPublicFiles.AtFiles.digInhabited AtPublicFiles.AtFiles.digNonempty`. (At the
literal 256 Lean's search for these two instances runs out of its budget.) -/
@[reducible] def digInhabited : Inhabited (Dig 256) := ⟨fun _ => false⟩

theorem digNonempty : Nonempty (Dig 256) := ⟨fun _ => false⟩

attribute [local instance] digInhabited digNonempty

/-- The coins of the shell `keyHonestAny` at run values of 256 bits. -/
abbrev KeyCoin (B : ProverCoinCounts) : Type :=
  (Purse B.shared × Dig 256) × ((Purse B.first × Purse B.second) × Dig 256)

/-- The two run values of a coin, as bytes. -/
def runsKey {B : ProverCoinCounts} (c : KeyCoin B) : ByteArray × ByteArray :=
  (digToBytes c.1.2, digToBytes c.2.2)

/-- A coin, from the three chains' coins and two run values as bytes. -/
def coinKey {B : ProverCoinCounts} (p : Purse B.shared × Purse B.first × Purse B.second)
    (r : ByteArray × ByteArray) : KeyCoin B :=
  ((p.1, digS r.1), (p.2, digS r.2))

/-- **The clause `tie` for the key file's two run values**: two run values of 32 bytes each are read
back off the coin into which they were put. -/
theorem tie_key {B : ProverCoinCounts} (p : Purse B.shared × Purse B.first × Purse B.second)
    (r : ByteArray × ByteArray) (h₂ : r.1.size = 32) (h₃ : r.2.size = 32) :
    runsKey (coinKey p r) = r :=
  Prod.ext (_root_.Run.digToBytes_digS r.1 h₂) (_root_.Run.digToBytes_digS r.2 h₃)

/-- The same under the hypothesis of the clause `tie`: of four run values that meet `Runs4.Fit`, the
first two. -/
theorem tie_key_fit {B : ProverCoinCounts} (p : Purse B.shared × Purse B.first × Purse B.second) (r : Runs4)
    (h : Runs4.Fit r) : runsKey (coinKey p r.1) = r.1 :=
  tie_key p r.1 h.sizeT2 h.sizeT3

/-- A negative test on the hypotheses of `tie_key`: what is read back at the empty byte string is
not that string. -/
theorem tie_key_no : digToBytes (digS ByteArray.empty) ≠ ByteArray.empty := fun h => by
  have := congrArg ByteArray.size h
  rw [_root_.Run.size_digToBytes] at this
  cases this

/-! ## The clause `lawT`, at three public files -/

section AtZ
variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {Tr X₀ X' : Type} (B : ProverCoinCounts)
  (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Tr X₀ X')
  (sh : OnBytes.TableKey → Fx.S₂)
  (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (P : (filesAt Z).Provers)

/-- A value for the parameter J at run values of 256 bits, at Z. -/
abbrev keySeamZ : Dig 256 → Dig 256 → KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed KeyInst
    OnBytes.TableKey (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray :=
  keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) digToBytes digToBytes

/-- **The clause `lawT` at the object of the three protocols at Z.** That this object is the one of
`LastFits`, `(homeR b Z).protocol`, is not shown here. -/
theorem lawT_at
    (hL : Honest ((filesAt Z).withProvers P).link ((Cz Z).I ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) ×
              (((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed)))
    (Fm : Family ((filesAt Z).withProvers P).onlineBatch.loc
      ((Cz Z).I × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed))
    (i : (Cz Z).I) (r : ((filesAt Z).withProvers P).EncodingRandomness) (e₁ : ((filesAt Z).withProvers P).OutOfDomainSeed)
    (κ : KeyCoin B × hL.Coin × Fm.glue.Coin) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
      (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀)
      ByteArray.empty
      ((proversAt Z Fx B H (keySeamZ Z) sh ext P hL Fm).strats.T i r e₁ κ)
      (runsKey κ.1).1 (runsKey κ.1).2 :=
  ProofFile.Honest.meets_stratLawC (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀)
    ByteArray.empty Fx B H (keySeamZ Z κ.1.1.2 default) (keySeamZ Z κ.1.1.2 κ.1.2.2) sh (i, r, e₁)
    κ.1.1.1 (keyInstanceOfOutOfDomainSample (((filesAt Z).withProvers P).recOf i r e₁)) κ.1.2.1

/-- **The clause `lawT` at the object whose index type is cut to the matrices in range.** That this
object is the one of `LastFits`, `(homeR b Z).protocol`, is not shown here. -/
theorem lawT_cut
    (hL : Honest (objAt Z P).link (Ix × ((objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed) ×
      ((objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed)))
    (Fm : Family (objAt Z P).onlineBatch.loc (Ix × (objAt Z P).EncodingRandomness × (objAt Z P).OutOfDomainSeed))
    (i : Ix) (r : (objAt Z P).EncodingRandomness) (e₁ : (objAt Z P).OutOfDomainSeed)
    (κ : KeyCoin B × hL.Coin × Fm.glue.Coin) :
    StratLaw (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
      (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀)
      ByteArray.empty
      ((proversCut Z Fx B H (keySeamZ Z) sh ext P hL Fm).strats.T i r e₁ κ)
      (runsKey κ.1).1 (runsKey κ.1).2 :=
  ProofFile.Honest.meets_stratLawC (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀)
    ByteArray.empty Fx B H (keySeamZ Z κ.1.1.2 default) (keySeamZ Z κ.1.1.2 κ.1.2.2) sh
    (i.val, r, e₁) κ.1.1.1 (keyInstanceOfOutOfDomainSample ((objAt Z P).recOf i r e₁)) κ.1.2.1

end AtZ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.digNonempty
#print axioms AtPublicFiles.AtFiles.keyHonest_stratLaw
#print axioms AtPublicFiles.AtFiles.keySeam_stratLaw
#print axioms AtPublicFiles.AtFiles.tie_key
#print axioms AtPublicFiles.AtFiles.tie_key_fit
#print axioms AtPublicFiles.AtFiles.tie_key_no
#print axioms AtPublicFiles.AtFiles.lawT_at
#print axioms AtPublicFiles.AtFiles.lawT_cut
#print axioms AtPublicFiles.AtFiles.digInhabited
#print axioms AtPublicFiles.AtFiles.KeyCoin
#print axioms AtPublicFiles.AtFiles.runsKey
#print axioms AtPublicFiles.AtFiles.coinKey
#print axioms AtPublicFiles.AtFiles.keySeamZ
