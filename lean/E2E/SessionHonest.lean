-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/SessionHonest.lean: `famC` is a family of honest provers of one request's protocol, one for each
number of a copy (`Family`, E2E/HonestFamily.lean). It is built by `ProofFile.Honest.honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean), the honest side of the proof file's protocol that is
written over a description Fd of the file (`FileDescription`, Johnson/Desc/Block.lean: the file's IOP as
written in Lean). Its type is stated at the library's object (`Files.withProvers`,
OnBytes/Flat/Object.lean). It is for files that import this one and need one request's honest
provers in that type. General in the claims, the rounds' data, the description and the decisions.
Definitions, and equations that hold by unfolding. Nothing is shown of any prover.

The copy's number is fixed before everything else: it is the first argument of the parameter J, and
nothing else of the honest side reads it. At a number and two coins, J gives a `KeyAndJoiningRoundMessages`
(Johnson/Desc/ProofFile/Honest/Strat.lean): the key for the shared chain, and what the three rounds
without a challenge send (the front round, the joining round and the seam).

  `famC … P`: a definition: the family. Its type of coins and its public abort set (`Bad`) are
    those of `(sideAt 0).one`. At the number n, its strategy and the rest of its abort set (`Hid`,
    which may depend on the private input) are those of `(sideAt n).one`. Its table is the
    parameter ext at every number. `.one` is `BatchHonestProver.one` (Iop/Batch.lean): one request's prover
    of an honest side. The type of `famC` is
    `Family (F'.withProvers P).onlineBatch.loc (I × (F'.withProvers P).EncodingRandomness × (F'.withProvers P).OutOfDomainSeed)`, for every P. F' is the
    library's three protocols whose proof file's decision is the description's (`filesWith`,
    E2E/ProtocolOverDescription.lean). The type of private inputs is the object's own, which unfolds to that of
    `sideAt`: no map on the private input, no cast
  `famC_at`: at the number n the family's prover (`Family.at`) is `(sideAt n).one`: by unfolding.
    So the type of coins and the public abort set of `(sideAt n).one` do not depend on n
  `famC_at_seat`: it is also `(seatB … (sideAt n)).one`: one request's prover of a value of the type
    that the third field of the library's provers asks (`Files.Provers.hB`; `seatB`,
    E2E/ProtocolOverDescription.lean): by unfolding
  `famC_coin`: its type of coins is
    `(Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)`: by unfolding. These are the
    three chains' coins and the two coins that J takes. R₂ and R₃ are free types, meant for the
    second and the third chain's run value
  `sideAt … n`: short for `honestBatchProverOfFile` at `J n`, at the protocol's parameters that
    `batch_eq_batchOf` (E2E/ProtocolOverDescription.lean) names, and at B, H, sh and ext. Of the type parameters
    of `honestBatchProverOfFile`, W₀ is the index type, Rc the pads with the encoding randomness, Sd the OOD seeds

By what. Every proof is `rfl`. `(F'.withProvers P).onlineBatch` unfolds to `F'.batch`, and that to `batchOf`
(Johnson/Desc/ProofFile/Honest/Record.lean) at the parameters of `sideAt`: the equation
`batch_eq_batchOf`, which is not called. `(F'.withProvers P).EncodingRandomness` unfolds to the pads with the encoding
randomness, `(F'.withProvers P).OutOfDomainSeed` to the OOD seeds. The fields `Coin0`, `Coin`, `Bad` and `stop0` of
`honestBatchProverOfFile` do not name J, and `BatchHonestProver.one` makes its coins and its `Bad` of these four.

Limits.
- This file is for a description that is stated at the object's own instances, or pulled back to
  them. E2E/BridgeAlong.lean, which reads the family along a writing map instead, does not call it.
- All parameters of the honest side stay free: the book of coins B (`ProverCoinCounts`), the prover structure H
  (`ProofFile.Honest.Prover`), J, the shared chain's first state sh, the table ext.
- That the front round's plain part holds the number n (the field `copy` of what `J n` sends there)
  is a statement on J. It is not a hypothesis here, and nothing here ties `J n` to n.
- P occurs in the type of `famC` only. No field reads it, and nothing says that `P.hB` is a
  `sideAt n`.
- The key file's prover is built by `honestBatchProverOfFile` too, at the key file's parameters (`keyHonest`,
  E2E/KeyHonest.lean). The link's honest prover is a term that is written out on its own
  (`OnBytes.LinkSim.AtHome.explicitLinkProver`, Johnson/LinkSim/AtHome/SpecHome.lean).
- At three public files Z the three protocols (`filesWithAt Z Fd`) are `filesAt Z` by a proved
  equation, not by unfolding: if `Fd.run` is the proof file's decision at Z (`filesWith_eq`). Where
  the IOP's own test on the files accepts and `theProofLaid` returns, that decision is the one
  returned (`run_eq_of_laid`; both E2E/ProtocolOverDescription.lean). Neither is called here.
- The description Fd is stated at the object's own instance type, `X × RecFull`. Of a description
  that is stated at another instance type and pulled back along a map, nothing is said here.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.ProtocolOverDescription
import E2E.HonestFamily
import Johnson.Desc.ProofFile.Honest.StratC

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
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)

section General
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool) (Fd : FileDescription (X × RecFull))
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (X × RecFull) Ky Tr X₀
    X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed (X × RecFull) Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → Fd.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- The honest side over the description Fd at the copy's number n: `honestBatchProverOfFile` at `J n`. -/
abbrev sideAt (n : ℕ) :=
  honestBatchProverOfFile (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP)
    ByteArray.empty Fd OnBytes.Flat.silP B H (J n) sh ext

/-- **The family of one request's honest provers, by the copy's number**, with its type stated at
the library's object at the three protocols `filesWith`. For every P; no field reads P. -/
def famC (P : (filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).Provers) :
    Family ((filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).withProvers P).onlineBatch.loc
      ((DecR.configurationOfStoredTable A R).I ×
        ((filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).withProvers P).EncodingRandomness ×
        ((filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).withProvers P).OutOfDomainSeed) where
  Coin := (sideAt A R DP Fd rP B H J sh ext 0).one.Coin
  finCoin := (sideAt A R DP Fd rP B H J sh ext 0).one.finCoin
  neCoin := (sideAt A R DP Fd rP B H J sh ext 0).one.neCoin
  ext := fun _ => ext
  strat := fun n => (sideAt A R DP Fd rP B H J sh ext n).one.strat
  Bad := (sideAt A R DP Fd rP B H J sh ext 0).one.Bad
  Hid := fun n => (sideAt A R DP Fd rP B H J sh ext n).one.Hid

variable (P : (filesWith A R DK DP runK Fd ds xs dec rK rP depthReq early salt).Provers)

/-- Its type of coins: the three chains' coins (`Purse`) and the two coins that J takes. -/
theorem famC_coin :
    (famC A R DK DP runK Fd ds xs dec rK rP depthReq early salt B H J sh ext P).Coin =
      ((Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) := rfl

/-- **At the number n it is one request's prover of the honest side at n**, `(sideAt n).one`. -/
theorem famC_at (n : ℕ) :
    (famC A R DK DP runK Fd ds xs dec rK rP depthReq early salt B H J sh ext P).at n =
      (sideAt A R DP Fd rP B H J sh ext n).one := rfl

/-- The same through `seatB`: the honest side at n has the type that the third field of the
library's provers (`Files.Provers.hB`) asks. -/
theorem famC_at_seat (n : ℕ) :
    (famC A R DK DP runK Fd ds xs dec rK rP depthReq early salt B H J sh ext P).at n =
      (seatB A R DK DP runK Fd ds xs dec rK rP depthReq early salt
        (sideAt A R DP Fd rP B H J sh ext n)).one := rfl

end General

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.famC_coin
#print axioms AtPublicFiles.AtFiles.famC_at
#print axioms AtPublicFiles.AtFiles.famC_at_seat
#print axioms AtPublicFiles.AtFiles.sideAt
#print axioms AtPublicFiles.AtFiles.famC
