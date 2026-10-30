-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbAccLawAtD.lean: E2E/ClimbFits.lean, E2E/ClimbUnif.lean and E2E/ClimbAccLaw.lean at the
wiring of the three files' protocols of the full size (`wireOfFullD`,
Johnson/Flat/Dec/WiresAtSizes.lean), and at the library's input at the full size's letters T
(`innerCompilerInputAtFullSize T`, Johnson/Flat/Dec/TwoSizesAt.lean). By definition the wiring `T.W` of that
input is `wireOfFullD` at the rest that belongs to T's coding (`InnerCompilerInputAndAnalysisFieldsAtFullSize.W`,
`InnerCompilerInputAndAnalysisFieldsAtFullSize.letters`).

Section 1, at ANY claims A, rest R, rounds' data DK, DP, ds, openings xs, three decisions, fixed
values rK, rP, depth of a request tree, early part, salt, provers P, number K and depth of the key
file's request tree; for each of the key file, the copy's file ("entry") and the proof file.
  `fits_key_fullD` and the like: the wiring's wire says, of proof of work, the words of the pair
    between the protocol at the same data with 0 bits of proof of work and the protocol itself
    (`filesPairFullD`, E2E/ClimbAtD.lean). Which wires these are stands in the three docstrings.
  `unif_key_fullD` and the like: that pair keeps probabilities (`Pair.Unif`).
  `accLaw_key_fullD` and the like: at one strategy and one set, `AccLaw`
    (Johnson/Prover/Law/Defs.lean) at the protocol and wire at which the compiled prover's accept
    laws are spent (`batTC` with `wTC`, `batLC` with `wLC`, the object's `onlineBatch` with `wBC`:
    Johnson/TypedOracleCompiler/RecCompile/) is `AccPassAt` (E2E/ClimbRun.lean) along that pair.
  `accLaw_key_fullD_up` and the like: the verifier at 0 bits accepts a strategy's runs outside B₀ if
    and only if the strategy carried up has `AccLaw` at the set pulled back.
  `accLaw_key_fullD_dn` and the like: `AccLaw` of any strategy at any set B holds if and only if the
    verifier at 0 bits accepts the runs of the strategy carried down, at verifier randomness whose
    image lies outside B.
  `prRho_zero_key_fullD` and the like: for every set B, what the compiled prover's law measures (B
    with the wire's test bits set to 0) is the probability, at 0 bits, of the set of verifier
    randomness whose image lies in B.

Section 2, at letters T: the pair is `pair0 T`, the protocols at 0 bits `files0 T`
(E2E/ClimbAtD.lean).
  `fits_key_at`, `fits_key_input`, `unif_key_at` and the like: the first two of section 1, at `T.W`
    and at the input's wiring.
  `accLaw_key_at`, `accLaw_key_at_up`, `accLaw_key_at_dn`, `prRho_zero_key_at` and the like: the
    other four, spelled at the input's own object, marks and wiring.
The letters of the IOP as written in Lean are a value of T
(`(FlashProve.dataAtFiles FlashProve.flashProveData Z).inputFieldsAtReadings c₀ m₀`: E2E/ClimbAtD.lean calls it so). No statement
here is spelled at that value.

Limits. Those of E2E/ClimbAccLaw.lean and E2E/ClimbRun.lean. Above all:
  * No strategy is shown to have `AccLaw`, and no verifier is shown to accept anything.
  * A STRATEGY CARRIED DOWN IS ANOTHER STRATEGY, OF ANOTHER PROTOCOL. It is the strategy where every
    test is passed, with the nonces dropped. It agrees with the strategy at hand, carried down and
    up again, only under `BlindUp` (E2E/ClimbRun.lean).
  * `AccLaw` at a set B says nothing in B. The number that goes beside it is that of
    `prRho_zero_key_fullD` and the like, never the probability of B alone: the set of all verifier
    randomness that passes gives `AccLaw` to every strategy; where rounds have bits of proof of work
    it is small, while with the test bits set to 0 it holds everything.
  * The statements hold at every data: no public file, no scope and no gate occurs in them. From
    which input, at which letters and data, the verifier is compiled is not said here.
  * Proved by unfolding from the general statements.
  * Johnson/Prover/Law/Defs.lean, which defines `AccLaw`, is not reviewed.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

-/
import E2E.ClimbAccLaw
import E2E.ClimbAtD
import Johnson.Flat.Dec.WiresAtSizes

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Climb
open OnBytes.Prover Prob TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (RecFull relationsAndEncodingOfClaims Coding)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD innerCompilerInputAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize)
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC wTC wLC wBC)

/-! ## 1. At any data, decisions and provers -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool) (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)

/-- The three files' protocols. -/
local notation "Ff" => threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt

/-- The same at 0 bits of proof of work. -/
local notation "Fz" =>
  threeProtocolsAtFullSize A R (noWork DK) (noWork DP) runK runP (ds.map rd0) xs dec rK rP depthReq early salt

/-- The pair between the two. -/
local notation "Pr" => filesPairFullD R DK DP runK runP ds xs dec rK rP depthReq early salt

/-- The configuration. -/
local notation "Cf" => OnBytes.Slice.DecR.configurationOfStoredTable A R

variable
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

/-- The object. -/
local notation "Lo" => OnBytes.Flat.Files.withProvers Ff P

/-- The wiring. -/
local notation "Ww" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/- The statements name these letters through the notations alone. -/
include A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/-! ### The key file -/

/-- The wiring's wire of the key file says the pair's words.
It is `wqWhole` (OnBytes/Maker/Wire.lean) at the key file's data. -/
theorem fits_key_fullD : Fits (Pr).key.pair.toPair _ (Ww).T.sh :=
  fits_whole (ckP .two) (kitFree_ckP .two) K (chalP .two K) (DK.at frS.P.T.a)
    (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK

omit P K depthReqT in
/-- The pair of the key file keeps probabilities. -/
theorem unif_key_fullD : (Pr).key.pair.toPair.Unif := by
  show (wholeBatchPair (ckP .two) (kitFree_ckP .two) OnBytes.Flat.silK runK (DK.at frS.P.T.a)
    (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK) ByteArray.empty).pair.toPair.Unif
  rw [wholeBatchPair_toPair]
  exact pairW_unif _ _ _ _ _ _

/-- **The key file: `AccLaw`, where the compiled prover's accept law is spent, is `AccPassAt`
along the pair.** -/
theorem accLaw_key_fullD (x : (Cf).Rec) (y : ((Cf).E0).Str)
    (σ : Strat (Lo).offline.shape Unit) (B : Set (Rho (Lo).offline.shape)) :
    AccLaw (batTC Lo (Ff).annT) (wTC Ww) x y σ B ↔ AccPassAt (Pr).key.loc x y σ B :=
  accLaw_iff (Pr).key (wTC Ww)
    (fits_key_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ B

/-- The verifier at 0 bits of proof of work accepts a strategy's runs outside B₀ if and only if the
strategy carried up has `AccLaw` at the set of verifier randomness whose old part lies in B₀. -/
theorem accLaw_key_fullD_up (x : (Cf).Rec) (y : ((Cf).E0).Str)
    (σ₀ : Strat (Fz).key.shape Unit) (B₀ : Set (Rho (Fz).key.shape)) :
    (∀ ρ, ρ ∉ B₀ → (Fz).key.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw (batTC Lo (Ff).annT) (wTC Ww) x y ((Pr).key.pair.toPair.up σ₀)
        {ρ' | (Pr).key.pair.toPair.oldR ρ' ∈ B₀} :=
  accLaw_up_iff (Pr).key (wTC Ww)
    (fits_key_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ₀ B₀

/-- `AccLaw` of σ at B, said at 0 bits of proof of work: the verifier there accepts the runs of σ
carried down, at verifier randomness whose image lies outside B. The strategy carried down is
ANOTHER STRATEGY, OF ANOTHER PROTOCOL: it is σ where every test is passed, with the nonces
dropped. -/
theorem accLaw_key_fullD_dn (x : (Cf).Rec) (y : ((Cf).E0).Str)
    (σ : Strat (Lo).offline.shape Unit) (B : Set (Rho (Lo).offline.shape)) :
    AccLaw (batTC Lo (Ff).annT) (wTC Ww) x y σ B ↔
      ∀ ρ, (Pr).key.pair.toPair.zeroR ρ ∉ B →
        (Fz).key.accept x y (((Pr).key.pair.toPair.dn σ).run ρ).1 = true :=
  accLaw_dn_iff (Pr).key (wTC Ww)
    (fits_key_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ B

/-- The number beside it, for every set B: what the compiled prover's law measures is the
probability, at 0 bits, of the set outside which the statement above speaks. -/
theorem prRho_zero_key_fullD (B : Set (Rho (Lo).offline.shape)) :
    pr (unif (Rho (Lo).offline.shape))
        {ρ | RoundsQueryLayout.zero (Lo).offline.shape (Ff).annT (wTC Ww).sh ρ ∈ B} =
      prRho {ρ : Rho (Fz).key.shape | (Pr).key.pair.toPair.zeroR ρ ∈ B} :=
  Fits.prRho_zero
    (fits_key_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    (unif_key_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt) B

/-! ### The copy's file -/

/-- The wiring's wire of the copy's file says the pair's words.
By definition it is `sibW` (Johnson/Top/EntrySib.lean), which is `wSib`
(Johnson/EntryRec/OklaSib.lean; `wireOfFull_eq_sibD`, Johnson/Flat/Dec/WiresAtSizes.lean). The proof
goes through `wqW` (Johnson/RunOne/StrictLinkW.lean): the three have the same rounds' wires. -/
theorem fits_entry_fullD : Fits (Pr).entry.pair.toPair _ (Ww).Lk.sh :=
  fits_link (ckP .two) (kitFree_ckP .two) K (chalP .two K) ds frS.P.T.a xs dec

omit P K depthReqT in
/-- The pair of the copy's file keeps probabilities. -/
theorem unif_entry_fullD : (Pr).entry.pair.toPair.Unif := by
  show (linkBatchPair (ckP .two) (kitFree_ckP .two) ds frS.P.T.a xs dec).pair.toPair.Unif
  rw [linkBatchPair_toPair]
  exact pairL_unif _ _ _

/-- **The copy's file: `AccLaw`, where the compiled prover's accept law is spent, is `AccPassAt`
along the pair.** -/
theorem accLaw_entry_fullD (x : (Cf).Rec × (Cf).Rec) (y : (twoExternalStrings (Cf).n (Cf).Sg).Str)
    (σ : Strat (Lo).link.shape Unit) (B : Set (Rho (Lo).link.shape)) :
    AccLaw (batLC Lo (Ff).annL) (wLC Ww) x y σ B ↔ AccPassAt (Pr).entry.loc x y σ B :=
  accLaw_iff (Pr).entry (wLC Ww)
    (fits_entry_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ B

/-- The verifier at 0 bits of proof of work accepts a strategy's runs outside B₀ if and only if the
strategy carried up has `AccLaw` at the set of verifier randomness whose old part lies in B₀. -/
theorem accLaw_entry_fullD_up (x : (Cf).Rec × (Cf).Rec) (y : (twoExternalStrings (Cf).n (Cf).Sg).Str)
    (σ₀ : Strat (Fz).entry.shape Unit) (B₀ : Set (Rho (Fz).entry.shape)) :
    (∀ ρ, ρ ∉ B₀ → (Fz).entry.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw (batLC Lo (Ff).annL) (wLC Ww) x y ((Pr).entry.pair.toPair.up σ₀)
        {ρ' | (Pr).entry.pair.toPair.oldR ρ' ∈ B₀} :=
  accLaw_up_iff (Pr).entry (wLC Ww)
    (fits_entry_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ₀ B₀

/-- `AccLaw` of σ at B, said at 0 bits of proof of work: the verifier there accepts the runs of σ
carried down, at verifier randomness whose image lies outside B. The strategy carried down is
ANOTHER STRATEGY, OF ANOTHER PROTOCOL: it is σ where every test is passed, with the nonces
dropped. -/
theorem accLaw_entry_fullD_dn (x : (Cf).Rec × (Cf).Rec) (y : (twoExternalStrings (Cf).n (Cf).Sg).Str)
    (σ : Strat (Lo).link.shape Unit) (B : Set (Rho (Lo).link.shape)) :
    AccLaw (batLC Lo (Ff).annL) (wLC Ww) x y σ B ↔
      ∀ ρ, (Pr).entry.pair.toPair.zeroR ρ ∉ B →
        (Fz).entry.accept x y (((Pr).entry.pair.toPair.dn σ).run ρ).1 = true :=
  accLaw_dn_iff (Pr).entry (wLC Ww)
    (fits_entry_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ B

/-- The number beside it, for every set B: what the compiled prover's law measures is the
probability, at 0 bits, of the set outside which the statement above speaks. -/
theorem prRho_zero_entry_fullD (B : Set (Rho (Lo).link.shape)) :
    pr (unif (Rho (Lo).link.shape))
        {ρ | RoundsQueryLayout.zero (Lo).link.shape (Ff).annL (wLC Ww).sh ρ ∈ B} =
      prRho {ρ : Rho (Fz).entry.shape | (Pr).entry.pair.toPair.zeroR ρ ∈ B} :=
  Fits.prRho_zero
    (fits_entry_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    (unif_entry_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt) B

/-! ### The proof file -/

/-- The wiring's wire of the proof file says the pair's words.
It is `wqWhole` at the proof file's data. -/
theorem fits_proof_fullD : Fits (Pr).proof.pair.toPair _ (Ww).B.sh :=
  fits_whole (ckP .two) (kitFree_ckP .two) K (chalP .two K) (DP.at frS.P.T.a)
    (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP

omit P K depthReqT in
/-- The pair of the proof file keeps probabilities. -/
theorem unif_proof_fullD : (Pr).proof.pair.toPair.Unif := by
  show (wholeBatchPair (ckP .two) (kitFree_ckP .two) OnBytes.Flat.silP runP (DP.at frS.P.T.a)
    (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP) ByteArray.empty).pair.toPair.Unif
  rw [wholeBatchPair_toPair]
  exact pairW_unif _ _ _ _ _ _

/-- **The proof file: `AccLaw`, where the compiled prover's accept law is spent, is `AccPassAt`
along the pair.** -/
theorem accLaw_proof_fullD (x : (Cf).X × (Cf).Rec) (y : ((Cf).E0).Str)
    (σ : Strat (Lo).onlineBatch.loc.shape Unit) (B : Set (Rho (Lo).onlineBatch.loc.shape)) :
    AccLaw (Lo).onlineBatch (wBC Ww) x y σ B ↔ AccPassAt (Pr).proof.loc x y σ B :=
  accLaw_iff (Pr).proof (wBC Ww)
    (fits_proof_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ B

/-- The verifier at 0 bits of proof of work accepts a strategy's runs outside B₀ if and only if the
strategy carried up has `AccLaw` at the set of verifier randomness whose old part lies in B₀. -/
theorem accLaw_proof_fullD_up (x : (Cf).X × (Cf).Rec) (y : ((Cf).E0).Str)
    (σ₀ : Strat (Fz).proof.shape Unit) (B₀ : Set (Rho (Fz).proof.shape)) :
    (∀ ρ, ρ ∉ B₀ → (Fz).proof.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw (Lo).onlineBatch (wBC Ww) x y ((Pr).proof.pair.toPair.up σ₀)
        {ρ' | (Pr).proof.pair.toPair.oldR ρ' ∈ B₀} :=
  accLaw_up_iff (Pr).proof (wBC Ww)
    (fits_proof_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ₀ B₀

/-- `AccLaw` of σ at B, said at 0 bits of proof of work: the verifier there accepts the runs of σ
carried down, at verifier randomness whose image lies outside B. The strategy carried down is
ANOTHER STRATEGY, OF ANOTHER PROTOCOL: it is σ where every test is passed, with the nonces
dropped. -/
theorem accLaw_proof_fullD_dn (x : (Cf).X × (Cf).Rec) (y : ((Cf).E0).Str)
    (σ : Strat (Lo).onlineBatch.loc.shape Unit) (B : Set (Rho (Lo).onlineBatch.loc.shape)) :
    AccLaw (Lo).onlineBatch (wBC Ww) x y σ B ↔
      ∀ ρ, (Pr).proof.pair.toPair.zeroR ρ ∉ B →
        (Fz).proof.accept x y (((Pr).proof.pair.toPair.dn σ).run ρ).1 = true :=
  accLaw_dn_iff (Pr).proof (wBC Ww)
    (fits_proof_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    x y σ B

/-- The number beside it, for every set B: what the compiled prover's law measures is the
probability, at 0 bits, of the set outside which the statement above speaks. -/
theorem prRho_zero_proof_fullD (B : Set (Rho (Lo).onlineBatch.loc.shape)) :
    pr (unif (Rho (Lo).onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero (Lo).onlineBatch.loc.shape (Lo).onlineBatch.ann (wBC Ww).sh ρ ∈ B} =
      prRho {ρ : Rho (Fz).proof.shape | (Pr).proof.pair.toPair.zeroR ρ ∈ B} :=
  Fits.prRho_zero
    (fits_proof_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT)
    (unif_proof_fullD A R DK DP runK runP ds xs dec rK rP depthReq early salt) B

end

/-! ## 2. At letters T, at the input's own object, marks and wiring -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
  {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
  {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- The library's input at T. -/
local notation "In" => innerCompilerInputAtFullSize T

/-! ### The key file -/

/-- The wire of the key file in `T.W` says the words of the pair at T. -/
theorem fits_key_at : Fits (pair0 T).key.pair.toPair _ T.W.T.sh :=
  fits_key_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT

/-- The same at the wiring of the input at T, through `wTC`. -/
theorem fits_key_input : Fits (pair0 T).key.pair.toPair _ (wTC (In).queryLayout).sh :=
  fits_key_at T

/-- The pair of the key file at T keeps probabilities. -/
theorem unif_key_at : (pair0 T).key.pair.toPair.Unif :=
  unif_key_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt

/-- **The key file, at the input's own letters: `AccLaw` is `AccPassAt` along the pair at T.** -/
theorem accLaw_key_at (x : (In).protocol.Rec) (y : (oneExternalString (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ : Strat (In).protocol.offline.shape Unit) (B : Set (Rho (In).protocol.offline.shape)) :
    AccLaw (batTC (In).protocol (In).offlineRoundSplits) (wTC (In).queryLayout) x y σ B ↔ AccPassAt (pair0 T).key.loc x y σ B :=
  accLaw_iff (pair0 T).key (wTC (In).queryLayout) (fits_key_input T) x y σ B

/-- Carried up from 0 bits of proof of work. -/
theorem accLaw_key_at_up (x : (In).protocol.Rec) (y : (oneExternalString (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ₀ : Strat (files0 T).key.shape Unit) (B₀ : Set (Rho (files0 T).key.shape)) :
    (∀ ρ, ρ ∉ B₀ → (files0 T).key.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw (batTC (In).protocol (In).offlineRoundSplits) (wTC (In).queryLayout) x y ((pair0 T).key.pair.toPair.up σ₀)
        {ρ' | (pair0 T).key.pair.toPair.oldR ρ' ∈ B₀} :=
  accLaw_up_iff (pair0 T).key (wTC (In).queryLayout) (fits_key_input T) x y σ₀ B₀

/-- Said at 0 bits of proof of work. The strategy carried down is another strategy, of another
protocol. -/
theorem accLaw_key_at_dn (x : (In).protocol.Rec) (y : (oneExternalString (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ : Strat (In).protocol.offline.shape Unit) (B : Set (Rho (In).protocol.offline.shape)) :
    AccLaw (batTC (In).protocol (In).offlineRoundSplits) (wTC (In).queryLayout) x y σ B ↔
      ∀ ρ, (pair0 T).key.pair.toPair.zeroR ρ ∉ B →
        (files0 T).key.accept x y (((pair0 T).key.pair.toPair.dn σ).run ρ).1 = true :=
  accLaw_dn_iff (pair0 T).key (wTC (In).queryLayout) (fits_key_input T) x y σ B

/-- The number beside it, for every set B. -/
theorem prRho_zero_key_at (B : Set (Rho (In).protocol.offline.shape)) :
    pr (unif (Rho (In).protocol.offline.shape))
        {ρ | RoundsQueryLayout.zero (In).protocol.offline.shape (In).offlineRoundSplits (wTC (In).queryLayout).sh ρ ∈ B} =
      prRho {ρ : Rho (files0 T).key.shape | (pair0 T).key.pair.toPair.zeroR ρ ∈ B} :=
  (fits_key_input T).prRho_zero (unif_key_at T) B

/-! ### The copy's file -/

/-- The wire of the copy's file in `T.W` says the words of the pair at T. -/
theorem fits_entry_at : Fits (pair0 T).entry.pair.toPair _ T.W.Lk.sh :=
  fits_entry_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT

/-- The same at the wiring of the input at T, through `wLC`. -/
theorem fits_entry_input : Fits (pair0 T).entry.pair.toPair _ (wLC (In).queryLayout).sh :=
  fits_entry_at T

/-- The pair of the copy's file at T keeps probabilities. -/
theorem unif_entry_at : (pair0 T).entry.pair.toPair.Unif :=
  unif_entry_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt

/-- **The copy's file, at the input's own letters: `AccLaw` is `AccPassAt` along the pair at T.** -/
theorem accLaw_entry_at (x : (In).protocol.Rec × (In).protocol.Rec) (y : (twoExternalStrings (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ : Strat (In).protocol.link.shape Unit) (B : Set (Rho (In).protocol.link.shape)) :
    AccLaw (batLC (In).protocol (In).linkRoundSplits) (wLC (In).queryLayout) x y σ B ↔ AccPassAt (pair0 T).entry.loc x y σ B :=
  accLaw_iff (pair0 T).entry (wLC (In).queryLayout) (fits_entry_input T) x y σ B

/-- Carried up from 0 bits of proof of work. -/
theorem accLaw_entry_at_up (x : (In).protocol.Rec × (In).protocol.Rec) (y : (twoExternalStrings (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ₀ : Strat (files0 T).entry.shape Unit) (B₀ : Set (Rho (files0 T).entry.shape)) :
    (∀ ρ, ρ ∉ B₀ → (files0 T).entry.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw (batLC (In).protocol (In).linkRoundSplits) (wLC (In).queryLayout) x y ((pair0 T).entry.pair.toPair.up σ₀)
        {ρ' | (pair0 T).entry.pair.toPair.oldR ρ' ∈ B₀} :=
  accLaw_up_iff (pair0 T).entry (wLC (In).queryLayout) (fits_entry_input T) x y σ₀ B₀

/-- Said at 0 bits of proof of work. The strategy carried down is another strategy, of another
protocol. -/
theorem accLaw_entry_at_dn (x : (In).protocol.Rec × (In).protocol.Rec) (y : (twoExternalStrings (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ : Strat (In).protocol.link.shape Unit) (B : Set (Rho (In).protocol.link.shape)) :
    AccLaw (batLC (In).protocol (In).linkRoundSplits) (wLC (In).queryLayout) x y σ B ↔
      ∀ ρ, (pair0 T).entry.pair.toPair.zeroR ρ ∉ B →
        (files0 T).entry.accept x y (((pair0 T).entry.pair.toPair.dn σ).run ρ).1 = true :=
  accLaw_dn_iff (pair0 T).entry (wLC (In).queryLayout) (fits_entry_input T) x y σ B

/-- The number beside it, for every set B. -/
theorem prRho_zero_entry_at (B : Set (Rho (In).protocol.link.shape)) :
    pr (unif (Rho (In).protocol.link.shape))
        {ρ | RoundsQueryLayout.zero (In).protocol.link.shape (In).linkRoundSplits (wLC (In).queryLayout).sh ρ ∈ B} =
      prRho {ρ : Rho (files0 T).entry.shape | (pair0 T).entry.pair.toPair.zeroR ρ ∈ B} :=
  (fits_entry_input T).prRho_zero (unif_entry_at T) B

/-! ### The proof file -/

/-- The wire of the proof file in `T.W` says the words of the pair at T. -/
theorem fits_proof_at : Fits (pair0 T).proof.pair.toPair _ T.W.B.sh :=
  fits_proof_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT

/-- The same at the wiring of the input at T, through `wBC`. -/
theorem fits_proof_input : Fits (pair0 T).proof.pair.toPair _ (wBC (In).queryLayout).sh :=
  fits_proof_at T

/-- The pair of the proof file at T keeps probabilities. -/
theorem unif_proof_at : (pair0 T).proof.pair.toPair.Unif :=
  unif_proof_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt

/-- **The proof file, at the input's own letters: `AccLaw` is `AccPassAt` along the pair at T.** -/
theorem accLaw_proof_at (x : (In).Instance × (In).protocol.Rec) (y : (oneExternalString (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ : Strat (In).protocol.onlineBatch.loc.shape Unit) (B : Set (Rho (In).protocol.onlineBatch.loc.shape)) :
    AccLaw (In).protocol.onlineBatch (wBC (In).queryLayout) x y σ B ↔ AccPassAt (pair0 T).proof.loc x y σ B :=
  accLaw_iff (pair0 T).proof (wBC (In).queryLayout) (fits_proof_input T) x y σ B

/-- Carried up from 0 bits of proof of work. -/
theorem accLaw_proof_at_up (x : (In).Instance × (In).protocol.Rec) (y : (oneExternalString (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ₀ : Strat (files0 T).proof.shape Unit) (B₀ : Set (Rho (files0 T).proof.shape)) :
    (∀ ρ, ρ ∉ B₀ → (files0 T).proof.accept x y (σ₀.run ρ).1 = true) ↔
      AccLaw (In).protocol.onlineBatch (wBC (In).queryLayout) x y ((pair0 T).proof.pair.toPair.up σ₀)
        {ρ' | (pair0 T).proof.pair.toPair.oldR ρ' ∈ B₀} :=
  accLaw_up_iff (pair0 T).proof (wBC (In).queryLayout) (fits_proof_input T) x y σ₀ B₀

/-- Said at 0 bits of proof of work. The strategy carried down is another strategy, of another
protocol. -/
theorem accLaw_proof_at_dn (x : (In).Instance × (In).protocol.Rec) (y : (oneExternalString (In).protocol.wordLength (In).protocol.Symbol).Str)
    (σ : Strat (In).protocol.onlineBatch.loc.shape Unit) (B : Set (Rho (In).protocol.onlineBatch.loc.shape)) :
    AccLaw (In).protocol.onlineBatch (wBC (In).queryLayout) x y σ B ↔
      ∀ ρ, (pair0 T).proof.pair.toPair.zeroR ρ ∉ B →
        (files0 T).proof.accept x y (((pair0 T).proof.pair.toPair.dn σ).run ρ).1 = true :=
  accLaw_dn_iff (pair0 T).proof (wBC (In).queryLayout) (fits_proof_input T) x y σ B

/-- The number beside it, for every set B. -/
theorem prRho_zero_proof_at (B : Set (Rho (In).protocol.onlineBatch.loc.shape)) :
    pr (unif (Rho (In).protocol.onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero (In).protocol.onlineBatch.loc.shape (In).protocol.onlineBatch.ann (wBC (In).queryLayout).sh ρ ∈ B} =
      prRho {ρ : Rho (files0 T).proof.shape | (pair0 T).proof.pair.toPair.zeroR ρ ∈ B} :=
  (fits_proof_input T).prRho_zero (unif_proof_at T) B

end

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.fits_key_fullD
#print axioms AtPublicFiles.Climb.unif_key_fullD
#print axioms AtPublicFiles.Climb.accLaw_key_fullD
#print axioms AtPublicFiles.Climb.accLaw_key_fullD_up
#print axioms AtPublicFiles.Climb.accLaw_key_fullD_dn
#print axioms AtPublicFiles.Climb.prRho_zero_key_fullD
#print axioms AtPublicFiles.Climb.fits_entry_fullD
#print axioms AtPublicFiles.Climb.unif_entry_fullD
#print axioms AtPublicFiles.Climb.accLaw_entry_fullD
#print axioms AtPublicFiles.Climb.accLaw_entry_fullD_up
#print axioms AtPublicFiles.Climb.accLaw_entry_fullD_dn
#print axioms AtPublicFiles.Climb.prRho_zero_entry_fullD
#print axioms AtPublicFiles.Climb.fits_proof_fullD
#print axioms AtPublicFiles.Climb.unif_proof_fullD
#print axioms AtPublicFiles.Climb.accLaw_proof_fullD
#print axioms AtPublicFiles.Climb.accLaw_proof_fullD_up
#print axioms AtPublicFiles.Climb.accLaw_proof_fullD_dn
#print axioms AtPublicFiles.Climb.prRho_zero_proof_fullD
#print axioms AtPublicFiles.Climb.fits_key_at
#print axioms AtPublicFiles.Climb.fits_key_input
#print axioms AtPublicFiles.Climb.unif_key_at
#print axioms AtPublicFiles.Climb.accLaw_key_at
#print axioms AtPublicFiles.Climb.accLaw_key_at_up
#print axioms AtPublicFiles.Climb.accLaw_key_at_dn
#print axioms AtPublicFiles.Climb.prRho_zero_key_at
#print axioms AtPublicFiles.Climb.fits_entry_at
#print axioms AtPublicFiles.Climb.fits_entry_input
#print axioms AtPublicFiles.Climb.unif_entry_at
#print axioms AtPublicFiles.Climb.accLaw_entry_at
#print axioms AtPublicFiles.Climb.accLaw_entry_at_up
#print axioms AtPublicFiles.Climb.accLaw_entry_at_dn
#print axioms AtPublicFiles.Climb.prRho_zero_entry_at
#print axioms AtPublicFiles.Climb.fits_proof_at
#print axioms AtPublicFiles.Climb.fits_proof_input
#print axioms AtPublicFiles.Climb.unif_proof_at
#print axioms AtPublicFiles.Climb.accLaw_proof_at
#print axioms AtPublicFiles.Climb.accLaw_proof_at_up
#print axioms AtPublicFiles.Climb.accLaw_proof_at_dn
#print axioms AtPublicFiles.Climb.prRho_zero_proof_at
