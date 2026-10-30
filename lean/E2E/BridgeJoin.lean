-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeJoin.lean: `OnBytes.Prover.HonFit` (Johnson/Prover/All/OfHonest.lean) is proved, from
hypotheses, at the three honest provers `proversOf hT hL famL`. `HonFit` is what the prover of a
whole request asks of three honest provers and three families of falls (`Falls`: sets of verifier
randomness that are set aside on the acceptance side). The third of the three, the prover of one
request's protocol (the session's prover), is `famL`: the family `famAlong` (E2E/BridgeAlong.lean)
of honest provers of `ProofFile.Honest.honestBatchProverOfFile`, read along a writing map wr, one prover for each number
n of a stored copy (the copy's number). Its falls are `fallL`, the fall's set `fallAlong`
(E2E/BridgeFalls.lean), made empty at the out-of-domain (OOD) seeds that are set aside (`guardFall`,
E2E/BridgeAccept.lean). The theorem is `honFit_of` (E2E/BridgeAccept.lean), with those of its
hypotheses filled in that E2E/BridgeLink.lean and E2E/BridgeFalls.lean prove. It is for files that
have to show the acceptance side (`HonFit`): E2E/BridgeJoinAtFiles.lean calls the three theorems at
three public files. All is stated at the protocol and the wiring of the compiled verifier, at any
parameters T of the full size (`InnerCompilerInputAndAnalysisFieldsAtFullSize`, Johnson/Flat/Dec/TwoSizesAt.lean). General in
the description F, the writing map, the book of coins B (`ProverCoinCounts`), the rows G (`Sides`: for each
sub-protocol the prover's part and its simulator), the prover structure H (`ProofFile.Honest.Prover`) and
the seam J (`KeyAndJoiningRoundMessages`). hT and hL, the key file's prover and the link's, are free parameters.

  `honFit_link`: `HonFit` at the provers `proversOf hT hL famL`, the falls
    `fallsOf hT hL _ FT FL (guardFall Z fallL)`, the wiring `T.W`, any S of the type `SdOf T`, and
    the bounds ζ, pT, pL and, for the session's prover, zB + z + pF. Of the hypotheses of
    `honFit_of` on the session's prover these are proved here: `AccAtTied`, the acceptance statement
    (from `YesAt` and the four hypotheses next to it in `accAtTied_of_yes`), and `WithheldZero` and
    `FallZero`: neither the abort set nor the fall depends on the test bits (with no hypothesis).
    The others stay hypotheses, and so does `NineFit`: see Hypotheses
  `num_link`: the hypothesis hn of `honFit_link`, from which `honFit_of` has the field `num` of
    `HonFit`: a transcript that is the run of a strategy of `famL` at the number n, but for nonces
    (`Puts`), passes the test of S on the copy's number: `S.num n` is true at its plain parts.
    Proved where that test reads the number in the front round's plain part (hS) and the seam's
    value `front` holds n (hF)
  `hidZero_link`: `HidZero` (E2E/BridgePrivacy.lean) of `famL` at the wiring `T.W`: the abort set
    `Hid`, which may depend on the private input, does not depend on the proof-of-work test bits.
    With no hypothesis: it is `hidZero_along` (E2E/BridgeAlong.lean), written at T. `honFit_link`
    does not call it: `HidZero` is a hypothesis of `stops_of_small` (E2E/BridgePrivacy.lean), on the
    privacy side
  `SdOf T`: an abbreviation: the type of S: `OutOfDomainSampleQueryLayout` (Johnson/TypedOracleCompiler/RecCompile/Seeds.lean), the
    structure of the OOD-seed wire, at the library's object (the `withProvers P` of `threeProtocolsAtFullSize`, at the
    parameters in the type of T) and at the wiring's number of hash blocks `T.W.K`. Among its
    fields: `seed`, the map from `T.W.K` digests to an OOD seed, and `num`, the test on the copy's
    number
  `famL`, `fallL`: abbreviations, written above without their arguments: `famAlong` at the prover
    structure `G.prover H` (H with the prover's parts of the rows G), and `fallAlong` at G and H;
    both at `relationsAndEncodingOfClaims A E` and at the other parameters in the type of T

By what. `honFit_link` is one call of `honFit_of` (E2E/BridgeAccept.lean). Its hypothesis
`AccAtTied` comes from `accAtTied_of_yes` (E2E/BridgeLink.lean), which goes through the theorem on
the compiled verifier's slot (`LPFFrame.frame_at_slot`, Johnson/LPFFrame/Proofs.lean);
`WithheldZero` and `FallZero` are `withheldZero_along` and `fallZero_along` (E2E/BridgeFalls.lean).
These two and `hidZero_along` are stated at the library's wiring `wireOfFullD`
(Johnson/Flat/Dec/WiresAtSizes.lean); `T.W` is that wiring at K and `T.depthReqT`, by unfolding.
`num_link` joins two statements. `LPFFrame.puts_same` (Johnson/LPFFrame/Proofs.lean; its statement:
Johnson/LPFFrame/Statements.lean): a transcript that is another's but for nonces has the same plain
parts in the three rounds without a challenge; only the front round's is used. `front_famBC`
(E2E/BridgeRunVals.lean): where the seam's value `front` holds n, so does the front round's plain
part in the run of the family's strategy, at every verifier randomness. Definitions: `proversOf`,
`HidSmall`, `ValidTied`, `ExtIsEnc` (E2E/BridgePrivacy.lean); `fallsOf`, `NineFit`, `ValidTiedZ`,
`BadSmall`, `FallSmall` (E2E/BridgeAccept.lean); `YesAt` (E2E/BridgeLink.lean); `FullAt`, `Carries`
(Johnson/LPFFrame/Statements.lean); `Puts` (OnBytes/Prover/Inv.lean); `chainsOf`
(OnBytes/Maker/Whole.lean); `plF` (Compile/Joined/Types.lean); `FrontMsg`
(OnBytes/Maker/SilentParts.lean).

Hypotheses of `honFit_link`. Yes is the relation of true instances, between an index i and a request
x; `Z i r` is the set of OOD seeds that are set aside, given the index and the committer's
randomness r. TiedX is a relation at the description's instances, read at `wr a` for an instance a
of the object; TiedM is a relation at the object's own instances. g: `NineFit`: the nine clauses of
`HonFit` that do not read the session's prover: on the key file's prover hT and on the link's prover
hL, with their falls FT and FL, and on the measure ζ of the OOD seeds that are set aside. hFull,
hCar, hrun, hsil, hyes: the hypotheses of `accAtTied_of_yes`, word for word (E2E/BridgeLink.lean,
Hypotheses). hyes is `YesAt`: at the inputs of TiedX and at every coin, the description's decision
accepts the three views of the honest run, at every verifier randomness that passes the
proof-of-work tests and lies outside the abort set and the fall's set at that coin. he: `ExtIsEnc`:
the family's external strings are the encoded index. hA: `ValidTiedZ`: true instances are tied at
the OOD seeds that are not set aside: where `Yes i x` holds and e is outside `Z i r`, TiedX holds at
every number, at (i, r, e) and at what wr writes for x with the OOD sample of (i, r, e). hb:
`BadSmall`: the measure of the public abort set `Bad` is at most zB. hz: `HidSmall`: at the inputs
of TiedM, the measure of the abort set `Hid`, which may depend on the private input, is at most z.
hM: `ValidTied`: true instances are tied, in TiedM, at all OOD seeds, those that are set aside
included. hf: `FallSmall`: at the inputs of TiedX, at each fixed coin, the measure of `fallL` is at
most pF. hn: the conclusion of `num_link`. Yes, Z, TiedX, TiedM, FT, FL and the bounds are free
parameters. Of `num_link`. hS: `S.num k` at plain parts is the test whether the field `copy` of the
front round's plain part (`plF`; a `FrontMsg`) is k. hF: at every number n, all run values and all
inputs, the field `copy` of the value `front` of the seam `J n r2 r3` is n.

Limits.
- Conditional throughout: no value is shown to meet the hypotheses together.
- The limits of E2E/BridgeAccept.lean, E2E/BridgeLink.lean and E2E/BridgeFalls.lean hold here too;
  the next item is among them.
- The lists of falls are free parameters (fields of the rows G). A fall whose test always returns
  something makes the statement on acceptance (the field `accB`) vacuous. At a sub-protocol without
  a round, a fall whose test is "this sub-protocol's own step rejects" makes "the run meets no fall"
  contain a part of the conclusion. So that statement says something at a sub-protocol only next to
  each fall's test as written and its measured share (`FallSmall`, at each fixed coin): without that
  measure it says nothing there.
- The clauses on the key file's prover and on the link's, and the measure of the OOD seeds that are
  set aside, are a hypothesis: `NineFit` (E2E/BridgeAccept.lean).
- S is any value of `SdOf T`: nothing ties it to T but the wiring's number of hash blocks `T.W.K`.
- What is concluded are hypotheses of other statements: `HonFit` of the theorem on completeness
  (`complete_of_honFit`, Johnson/WholeKey/CompleteOfRecs.lean) and of `parts_of_honFit`
  (Johnson/Prover/All/CompleteAsIOPOfHonFit.lean; E2E/CompleteAsIOPByYes.lean calls that one at such
  a value), `HidZero` of `stops_of_small`. None is called here. No statement of completeness is
  made here, and nothing on soundness or hiding.
-/
import E2E.BridgeLink

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull Coding silP front₀ join₀)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides)
open OnBytes.Prover (HonFit Puts)
open TypedOracleCompiler.Compile.Batch.Cms (wBC)

variable {X Xi : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → View → View → View → Bool}
  {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
  (F : FileDescription Xi) (wr : X × RecFull → Xi)
  (silent : Xi → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (G : Sides F B (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky Tr X₀ X')
  (H : Prover (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Xi Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed Xi Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → F.S₂)
  (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
    (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- The type of S in `num_link` and `honFit_link`: `OutOfDomainSampleQueryLayout`, the structure of the OOD-seed wire, at
the library's object and at the wiring's number of hash blocks `T.W.K`. -/
abbrev SdOf : Type :=
  TypedOracleCompiler.Compile.Batch.Cms.OutOfDomainSampleQueryLayout 256 T.W.K
    ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
    (List Bool) (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
      salt).annT
    (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).annL

/-- The session's prover of this file: the family `famAlong` at the prover structure `G.prover H`.
-/
abbrev famL :=
  famAlong A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B
    (G.prover H) J sh ext P

/-- Its falls: the fall's sets `fallAlong` at the rows G and the prover structure H. -/
abbrev fallL :=
  fallAlong A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B G H J
    sh ext P

/-- The abort set `Hid`, which may depend on the private input, does not depend on the test bits:
`HidZero` of `famL`, at the wiring `T.W` of the parameters T. -/
theorem hidZero_link : HidZero (famL (P := P) F wr silent B G H J sh ext) T.W :=
  hidZero_along A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B
    (G.prover H) J sh ext P K T.depthReqT

/-- **A transcript that is the honest run's but for nonces passes the test on the copy's number**
(`S.num`): where that test reads the front round's number (hS), and the seam's value `front` holds n
(hF). -/
theorem num_link (S : SdOf T)
    (hS : ∀ k π, S.num k π =
      decide (((OnBytes.Maker.chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
        ByteArray.empty).plF π).copy = k))
    (hF : ∀ n r2 r3 w₀ rc sd x, ((J n r2 r3).front w₀ rc sd x).copy = n) :
    ∀ n w x c (τ : Iop.Tr _),
      Puts _ _ (wBC T.W).sh (((famL (P := P) F wr silent B G H J sh ext).strat n w x c).run τ.rho).1
          τ → S.num n τ.plains = true := by
  intro n w x c τ hp
  have s := (LPFFrame.puts_same (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty silP runP _ τ hp).2.2.1
  have f := front_famBC (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty F silent
    B (G.prover H) J sh ext (·.copy) hF n w (wr x) c τ.rho
  rw [hS]
  exact decide_eq_true ((congrArg (·.copy) s).trans f)

/-- **`HonFit` at the provers `proversOf hT hL famL`**, with the falls `fallL` made empty at the OOD
seeds that are set aside, at any S. The hypotheses are listed in this file's head. -/
theorem honFit_link (S : SdOf T) (hT) (hL) (FT) (FL)
    (Z) {Yes} {ζ pT pL zB z pF : ℝ≥0∞}
    {TiedX : ℕ → (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed → Xi → Prop} {TiedM}
    (g : NineFit hT hL T.W FT FL Z S Yes ζ pT pL)
    (hFull : LPFFrame.FullAt (ckP .two) (DP.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hrun : ∀ a v₁ v₂ v₃, F.run (wr a) v₁ v₂ v₃ = true → runP a v₁ v₂ v₃ = true)
    (hsil : ∀ n r2 r3 w a, TiedX n w (wr a) →
      silP a ((J n r2 r3).front w.1 w.2.1 w.2.2 (wr a)) ((J n r2 default).join w.1 w.2.1 w.2.2)
        ((J n r2 r3).seam w.1 w.2.1 w.2.2 (wr a)) = true)
    (hyes : YesAt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty F silent B G
      H J sh ext K (chalP .two K) TiedX)
    (he : ExtIsEnc (famL (P := P) F wr silent B G H J sh ext))
    (hA : ValidTiedZ (fun n w a => TiedX n w (wr a)) Yes Z)
    (hb : BadSmall (famL (P := P) F wr silent B G H J sh ext) zB)
    (hz : HidSmall (famL (P := P) F wr silent B G H J sh ext) TiedM z)
    (hM : ValidTied TiedM (fun _ => True) (fun _ => True) Yes)
    (hf : FallSmall (famL (P := P) F wr silent B G H J sh ext)
      (fallL (P := P) F wr silent B G H J sh ext) (fun n w a => TiedX n w (wr a)) pF)
    (hn : ∀ n w x c (τ : Iop.Tr _),
      Puts _ _ (wBC T.W).sh (((famL (P := P) F wr silent B G H J sh ext).strat n w x c).run τ.rho).1
          τ → S.num n τ.plains = true) :
    HonFit (proversOf hT hL (famL (P := P) F wr silent B G H J sh ext))
      (fallsOf hT hL _ FT FL (guardFall Z (fallL (P := P) F wr silent B G H J sh ext))) T.W
      S Yes Z ζ pT pL (zB + z + pF) :=
  honFit_of hT hL _ _ T.W FT FL Z S g he
    (withheldZero_along A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt
      silent B (G.prover H) J sh ext P K T.depthReqT)
    (fallZero_along A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent
      B G H J sh ext P K T.depthReqT)
    (accAtTied_of_yes T F wr silent B G H J sh ext hFull hCar hrun hsil hyes) hA hb hz hM hf hn

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.hidZero_link
#print axioms AtPublicFiles.AtFiles.num_link
#print axioms AtPublicFiles.AtFiles.honFit_link
#print axioms AtPublicFiles.AtFiles.SdOf
#print axioms AtPublicFiles.AtFiles.famL
#print axioms AtPublicFiles.AtFiles.fallL
