-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyHonestPlain.lean: what the three rounds without a challenge show in the transcript that the
strategy of `keyHonestAny` writes. `keyHonestAny` (E2E/KeyHonest.lean) has the type of the key
file's honest prover and is a prover structure built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes; below: the
shell `keyHonestAny`. The three rounds are the front round, the joining round and the seam: each
sends a plain part only and has one verifier message (`plainRound`, Compile/Joined/Types.lean). At
every private input, instance, coin and verifier randomness they show the values of the parameter J.
E2E/KeyBridgeFilled.lean, which imports this file, takes the two run values from `keySeam_plain`.
`keyHonest_plain` is general in every parameter of the shell, also in the key file's decision runK.
The theorems have no hypothesis but the instances that `honestBatchProverOfFile` asks for the types of r₂ and r₃.

In the list: w is the private input (index; pads with encoding randomness; OOD seed). x is the
instance, an OOD sample (`RecFull`), and `keyInstanceOfOutOfDomainSample x` is its written key: the stored table's key as the
program writes it. c is a coin, that is ((the shared chain's coins, r₂), ((the two other chains'
coins), r₃)); a chain's coins have the type `Purse`. ρ is the verifier randomness.

  `keyHonest_plain`: in the transcript that the strategy writes at (w, x, c, ρ): the front round's
    message is `(J r₂ r₃).front` at w and the written key of x; the joining round's is
    `(J r₂ default).join` at w; the seam's is `(J r₂ r₃).seam` at w and the written key of x. The
    joining round's is at `default`, the fixed value of the type of r₃, and not at r₃: of the two,
    the shared part's strategy is handed r₂ only
  `keySeam_plain`: at J := `keySeam val₂ val₃` (E2E/KeyHonest.lean): the front round shows the
    answers of the honest OOD sample (`sampleOf` at w) and the number 0; the joining round these
    answers and `val₂ r₂`; the seam `val₃ r₃`. So the two run values that are shown are read off
    the coin, at every verifier randomness, private input and instance
  `keySeam_plain_accepts`: so, where the instance is the honest OOD sample, the library's test on
    the three plain parts (`silK`, OnBytes/Flat/FilesAt.lean) accepts what the strategy shows, at
    every coin and verifier randomness. That is one test of the verifier's
  `keyChains DK rK`: a definition: the rounds of the key file's protocol: `chainsOf`
    (OnBytes/Maker/Whole.lean) at the arguments of the library's key file
  `keyTr`: a definition: the transcript that the strategy of the shell `keyHonestAny` writes at
    (w, x, c, ρ)

By what. `zip_partsC` (Johnson/Desc/ProofFile/Honest/Law/StratFormC.lean) gives the six parts of the
transcript that the two strategies of `honestBatchProverOfFile`, zipped, write at every verifier randomness.
`keyHonest_plain` calls it and keeps its three equations on the rounds without a challenge; that the
shell's strategy at x is this zip at the written key of x holds by unfolding. `keySeam_plain` is
`keyHonest_plain` at `keySeam`. `keySeam_plain_accepts` rewrites by `keySeam_plain` and calls
`keySeam_silentK` (E2E/KeyHonest.lean).

Limits. Nothing is shown of any part of a prover: no completeness, nothing on what a view shows. The
three theorems hold at every book of coins B (`ProverCoinCounts`) and prover structure H (`ProofFile.Honest.Prover`),
also at a prover structure H that has no part for any sub-protocol (`Placed`): the three rounds are
rounds of no sub-protocol, and their values are sent whatever happens in the other rounds.
`keySeam_plain_accepts` is no statement of completeness: it speaks of one test, which reads neither
run value. The theorems speak of these three rounds only: nothing on the other rounds. No property
of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyHonest
import Johnson.Desc.ProofFile.Honest.Law.StratFormC

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)

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

/-- The rounds of the key file's protocol: `chainsOf` at the arguments of the library's key file.
-/
abbrev keyChains : Compile.Joined.Chains :=
  chainsOf (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty

/-- The transcript that the strategy of `keyHonestAny` writes at the private input w, the instance
x, the coin c and the verifier randomness ρ. -/
abbrev keyTr
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull) (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (keyChains DK rK).sh) : Iop.Tr (keyChains DK rK).sh :=
  (((keyHonestAny A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK
    P).strat w x c).run ρ).1

/-- **The three rounds without a challenge show the values of J**, at every private input, instance,
coin and verifier randomness. The joining round's value is at `default`, not at the coin's r₃. -/
theorem keyHonest_plain
    (w : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)
    (x : RecFull) (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (keyChains DK rK).sh) :
    (keyChains DK rK).msgF
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P w x c ρ) =
      ((), (J c.1.2 c.2.2).front w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample x)) ∧
    (keyChains DK rK).msgJ
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P w x c ρ) =
      ((), (J c.1.2 default).join w.1 w.2.1 w.2.2) ∧
    (keyChains DK rK).msg3
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H J sh ext runK P w x c ρ) =
      ((), (J c.1.2 c.2.2).seam w.1 w.2.1 w.2.2 (keyInstanceOfOutOfDomainSample x)) :=
  have h := ProofFile.Honest.zip_partsC (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
    (OnBytes.Flat.join₀ rK) ByteArray.empty Fx B H (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1
    (keyInstanceOfOutOfDomainSample x) c.2.1 ρ
  ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩

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

/-- **At J := `keySeam val₂ val₃` they show the honest OOD sample's answers, the number 0, and the
two run values, which are read off the coin.** -/
theorem keySeam_plain (i : (DecR.configurationOfStoredTable A R).I) (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (e : (DecR.configurationOfStoredTable A R).Seed) (x : RecFull)
    (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (keyChains DK rK).sh) :
    (keyChains DK rK).msgF
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃) sh
          ext runK P (i, r, e) x c ρ) =
      ((), ⟨(keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key.record.toList, 0⟩) ∧
    (keyChains DK rK).msgJ
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃) sh
          ext runK P (i, r, e) x c ρ) =
      ((), ⟨(keyInstanceOfOutOfDomainSample (sampleOf A R i r e)).key.record.toList, val₂ c.1.2⟩) ∧
    (keyChains DK rK).msg3
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃) sh
          ext runK P (i, r, e) x c ρ) = ((), val₃ c.2.2) :=
  keyHonest_plain A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃)
    sh ext runK P (i, r, e) x c ρ

/-- **Where the instance is the honest OOD sample, the library's test on the three plain parts
accepts what the strategy shows.** That is one test of the verifier's. -/
theorem keySeam_plain_accepts (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed)
    (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (keyChains DK rK).sh) :
    OnBytes.Flat.silK (sampleOf A R i r e)
      ((keyChains DK rK).msgF
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃) sh
          ext runK P (i, r, e) (sampleOf A R i r e) c ρ)).2
      ((keyChains DK rK).msgJ
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃) sh
          ext runK P (i, r, e) (sampleOf A R i r e) c ρ)).2
      ((keyChains DK rK).msg3
        (keyTr A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H (keySeam A R val₂ val₃) sh
          ext runK P (i, r, e) (sampleOf A R i r e) c ρ)).2 = true := by
  obtain ⟨h1, h2, h3⟩ := keySeam_plain A R DK DP Fx runP ds xs dec rK rP depthReq early salt B H
    val₂ val₃ sh ext runK P i r e (sampleOf A R i r e) c ρ
  rw [h1, h2, h3]
  exact keySeam_silentK A R val₂ val₃ c.1.2 c.2.2 i r e

end Filled

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keyHonest_plain
#print axioms AtPublicFiles.AtFiles.keySeam_plain
#print axioms AtPublicFiles.AtFiles.keySeam_plain_accepts
#print axioms AtPublicFiles.AtFiles.keyChains
#print axioms AtPublicFiles.AtFiles.keyTr
