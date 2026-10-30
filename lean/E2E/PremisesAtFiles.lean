-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/PremisesAtFiles.lean: fifteen of the twenty fields of `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean), those that read no prover's strategy, no coin and no simulator,
together, at the input at which `VerifierAndGoals.verify` calls the compiled verifier, at three public files Z
in scope.

  `NoProverSide W S cA Gs N M capT capL capB`: these fifteen fields, as a name: the counts of reads
    with the clause `hidE`; the two budgets; the measure of the OOD seeds outside Gs; `ReadsFree`
    three times; the wires' laws; the formats; `NoncesBack` three times; `SeedPlain`; the marks'
    coherence; locality. Of the honest side it reads four letters: the number M (there are M + 1
    copies) and the three caps.
  `premW_iff`: `PremW` holds if and only if `NoProverSide` does and the five other fields do
    (`ExtEnc`, `RunVals`, `Sims.Good`, `StopsSmall`, `CoinsFit`).
  `NoProverSide.restrict`: it passes to every smaller set Gs' of OOD seeds, at any bound on the
    measure of the OOD seeds outside Gs'. `NoProverSide.noSeeds`: a warning: at no OOD seed at all
    it passes to every larger number of columns.
  `noProverSide_at`: `NoProverSide` at any letters T of the full size, from the library's one test
    on numbers, `SeedPlain`, the reads, the two budgets and the OOD seeds' measure.
  `indexPrivacyNumbers`: the numbers: at most 44,040,191 columns of one table may be read in all (a table has
    2^32); the key file's verifier reads at most 62, a link's at most 62 of the first table and 62
    of its copy, ONE REQUEST's verifier of the proof file at most 64; δ = 0.
  `one_atFiles`, `readsG_atFiles`: the last count; so the counts and the clause `hidE` stand in the
    form in which `PremW` asks them (`Hiop.Seeded.ReadsG`), at all OOD seeds.
  `seedPlain_atFiles`: `SeedPlain` at the letters at Z.
  `noProverSide_atFiles`: a member: at the letters `(dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀`, at every Z in
    scope, Gs := all OOD seeds, at most 710,324 copies, at most 688,127 sessions a copy (of one
    request each), and all caps.
  `noProverSide_built`, **`noProverSide_description`**: THE MEMBER AT THE INPUT
    `(atSecondHashFunction theDescription).input Z c m`, at its own wiring, OOD seed's letters and code of the
    answers. That `VerifierAndGoals.verify` calls the compiled verifier at that input is its definition
    (`verify_calls`, E2E/DescriptionTie.lean).
  THREE TESTS THAT FAIL: `not_noProverSide_column`, `not_noProverSide_column_built`,
    **`not_noProverSide_column_description`**: at 44,040,192 columns or more, with Gs all OOD seeds,
    it fails at every Z, whatever the other numbers, the caps, c and m (from
    E2E/TableHidesGuardAtFiles.lean); the last at the same input as the member.
    `not_noProverSide_copy`, `not_noProverSide_session`: at `indexPrivacyNumbers` it fails at 710,325 copies and
    at 688,128 sessions. These two are arithmetic alone, at every object and wiring.
  `seedRe`, `NoProverSide.reIndex`, `NoProverSide.cut`, `noProverSide_objAt`: it goes over from any
    object to the same object on other indices (E2E/CutIndex.lean), with the same wiring and code;
    so it holds at the object cut to the matrices in range (`objAt`, E2E/ObjectAtFiles.lean).
    `PremW` does not ask this: it keeps the index type and takes the range of indices as a guard.

How the fifteen are met at the member. By the written data, the code's numbers and the library's
laws: the four counts, `hidE`, the two budgets, the wires' laws, the formats, coherence, locality.
(44,040,191 is the most at this object. 710,324 and 688,127 are the most AT THE COUNTS 62 AND 64,
which are upper bounds: that the verifiers ever read so many columns is not shown.) More than is
asked: `ReadsFree`: these verifiers' reads hang on no plain part at all. By type or by default, so
that little is said: the OOD seeds' measure (Gs is all OOD seeds, the set is empty); `NoncesBack` at
all caps (in these rounds a nonce is a natural number and is its own reading; in a file a nonce has
eight bytes, and nothing here bounds a cap); `SeedPlain` (the front round has no test, and `nonceOf`
then says 0).

Limits.
  * NOTHING HERE SAYS THAT `PremW` HOLDS OF ANYTHING. Its five fields on provers, coins and
    simulators are not touched. No honest prover is written in this file. At the protocol in view no
    member of `PremW` all three of whose provers send the protocol's messages is known; one with
    provers that send fixed messages follows from E2E/FiveLeftSilent.lean; one in which the link's
    prover is the written one and the other two send fixed messages, at the input at one fixed
    digest, at which verify is not proved ever to be called: E2E/LinkLaidPrivacy.lean.
  * IT IS NOT THE VERIFIER'S SIDE. The library has that notion (`HolographicProtocol.v`, Hiop/RecSide.lean), which
    reads no encoder. The clause `hidE` reads the encoder, its randomness and the map to the OOD
    answers. They are fields of the input's object, and no verifier reads them: for `hidE`, "at this
    input" is only as good as what makes that encoder the protocol's (the head of
    E2E/DescriptionTie.lean).
  * Fifteen FIELDS, not every clause: among the other five, `CoinsFit` has four clauses on the wires
    and on numbers alone (the number of rounds, the window of trees and leaves). They are not
    treated: they share letters with the laws on coins.
  * With Gs := all OOD seeds, the fields `good` and `stops` of `PremW` are asked at every OOD seed.
    Whoever wants fewer takes `NoProverSide.restrict` and owes the measure.
  * The premise `InScope Z` is spent on the four counts alone. All else holds at every Z. Where the
    test on the public files rejects, the key file's and the proof file's rounds' data are empty and
    all three decisions reject (the head of E2E/ObjectAtFiles.lean): there the member speaks of
    verifiers that read nothing and accept nothing; and that the IOP's own tests on the public files
    pass is shown in the side library: at the library's two named sets of public files
    (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files under every policy within
    four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no theorem ties any of these
    to a file on a disk.
  * The clause `hidE` is E2E/ReadsAtFiles.lean's and E2E/TableHides.lean's; all their limits stand.
    Beside it, always:
    (a) It is a law of the encoder and its coins alone: no message of a prover is covered, and it is
    not zero knowledge.
    (b) It supposes fresh uniform pads and encoding randomness for each table, one OOD sample a
    table, and a seed that hangs on nothing hidden.
    (c) The budget has no slack, and nobody keeps it: in PremW it is two premises on numbers, and
    Lean's prover has no state.
    (d) That the encoder is the protocol's is a reading of the format: no verifier and no program
    reads it.
  * At the cut object the wiring is the same term. An OOD seed's letters (`OutOfDomainSampleQueryLayout`), the wires' laws
    (`OKA`) and the law of the answers' code (`AnsOK`) are structures with the object as a
    parameter: they are built anew, field by field, from the same fields.
  * `atSecondHashFunction theDescription` is where all goals but two read the IOP as written in Lean. At another
    function in that place nothing is said (the head of E2E/DescriptionTie.lean).
  * The test on the columns lives on some OOD seed: at a set Gs that holds no OOD seed, with δ = 1,
    `NoProverSide` passes to every larger number of columns (`NoProverSide.noSeeds`).
  * `PremW` states no goal, by its own head.

`NoProverSide` names premises of another file's statement and adds nothing to them. It may be read
as part of a goal. It is not among this library's goals.

-/
import E2E.PremisesAtWiring
import E2E.ReadsAtFiles
import Johnson.Goal.Conditions.NumbersAtThe
import Johnson.Top.Fire.Code.TieAtValues
import Johnson.Goal.Description.Description
import E2E.TableHidesGuardAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Premises
open OnBytes.WholeKey OnBytes.Prover Prob
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile (Params)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (RecFull relationsAndEncodingOfClaims Coding)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize FrameFitFullD)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) blocksNonempty (k lam : ℕ) : Nonempty (Fin k → Dig lam) :=
  ⟨fun _ _ => false⟩

/-! ## 1. The premises that read no prover -/

section
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The fields of `PremW` that read no prover, no coin and no simulator.** M: the number of copies
is M + 1. A member: `noProverSide_atFiles`. -/
structure NoProverSide (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (Gs : L.OutOfDomainSeed → Prop) (N : NumsW) (M : ℕ)
    (capT capL capB : ℕ → ℕ) : Prop where
  reads : Hiop.Seeded.ReadsG L Gs N.b N.qT N.qpar N.qch N.qon
  budget₀ : N.qT + (M + 1) * N.qpar ≤ N.b
  budget₁ : N.qch + N.s1 * N.qon ≤ N.b
  seeds : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ N.δ
  freeT : ReadsFree (batTC L aT) (wTC W).sh
  freeL : ReadsFree (batLC L aL) (wLC W).sh
  freeB : ReadsFree L.onlineBatch (wBC W).sh
  wires : OKA W cA
  fmt : aT.Fmt ∧ aL.Fmt ∧ L.onlineBatch.ann.Fmt
  backT : NoncesBack L.offline.shape aT (wTC W).sh capT 0
  backL : NoncesBack L.link.shape aL (wLC W).sh capL 0
  backB : NoncesBack L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0
  plain : SeedPlain W S
  coherent : aT.Coherent ∧ aL.Coherent ∧ L.onlineBatch.ann.Coherent
  isLocal : L.offline.IsLocal ∧ L.link.IsLocal ∧ L.onlineBatch.loc.IsLocal

/-- **`PremW` is `NoProverSide` and the five fields on provers, coins and simulators.** -/
theorem premW_iff (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params) (a : AtRecs lam L Bd aT aL) (Sm : Sims L)
    (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd) (N : NumsW) :
    PremW W S cA p a Sm ok Gs Ryes c N ↔
      NoProverSide W S cA Gs N a.M a.capT a.capL a.capB ∧ ExtEnc a.Hs ∧ RunVals a ok ∧
        Sm.Good a.Hs W ok Gs Ryes N.zT N.zL N.zO ∧
        StopsSmall a.Hs W ok Gs Ryes N.hT N.hL N.hO ∧ CoinsFit W p a c :=
  ⟨fun h => ⟨⟨h.reads, h.budget₀, h.budget₁, h.seeds, h.freeT, h.freeL, h.freeB, h.wires, h.fmt,
      h.backT, h.backL, h.backB, h.plain, h.coherent, h.isLocal⟩, h.ext, h.runVals, h.good,
      h.stops, h.coins⟩,
    fun h => ⟨h.2.1, h.2.2.1, h.1.reads, h.1.budget₀, h.1.budget₁, h.2.2.2.1, h.2.2.2.2.1,
      h.1.seeds, h.1.freeT, h.1.freeL, h.1.freeB, h.1.wires, h.1.fmt, h.1.backT, h.1.backL,
      h.1.backB, h.1.plain, h.1.coherent, h.1.isLocal, h.2.2.2.2.2⟩⟩

/-- **To a smaller set of OOD seeds**, at any bound δ' on the measure of the OOD seeds outside it.
The clause `hidE` is asked at fewer OOD seeds; the measure is the premise; the other fields do not
read Gs. -/
theorem NoProverSide.restrict {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} {Gs : L.OutOfDomainSeed → Prop} {N : NumsW} {M : ℕ}
    {capT capL capB : ℕ → ℕ} (h : NoProverSide W S cA Gs N M capT capL capB)
    (Gs' : L.OutOfDomainSeed → Prop) (hsub : ∀ s, Gs' s → Gs s) (δ' : ℝ≥0∞)
    (hδ : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs' (S.seed u)} ≤ δ') :
    NoProverSide W S cA Gs' { N with δ := δ' } M capT capL capB where
  reads := ⟨h.reads.cntT, h.reads.cntLp, h.reads.cntLc, h.reads.cntO,
    fun Q hQ s hs i i' => h.reads.hidE Q hQ s (hsub s hs) i i'⟩
  budget₀ := h.budget₀
  budget₁ := h.budget₁
  seeds := hδ
  freeT := h.freeT
  freeL := h.freeL
  freeB := h.freeB
  wires := h.wires
  fmt := h.fmt
  backT := h.backT
  backL := h.backL
  backB := h.backB
  plain := h.plain
  coherent := h.coherent
  isLocal := h.isLocal

/-- **A warning**: at a set that holds no OOD seed, with δ = 1, it holds at every larger number of
columns too: the clause `hidE` then asks nothing, no count reads that number, and the budgets
loosen. -/
theorem NoProverSide.noSeeds {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} {Gs : L.OutOfDomainSeed → Prop} {N : NumsW} {M : ℕ}
    {capT capL capB : ℕ → ℕ} (h : NoProverSide W S cA Gs N M capT capL capB) (b' : ℕ)
    (hb : N.b ≤ b') :
    NoProverSide W S cA (fun _ => False) { N with b := b', δ := 1 } M capT capL capB where
  reads := ⟨h.reads.cntT, h.reads.cntLp, h.reads.cntLc, h.reads.cntO,
    fun _ _ _ hs => hs.elim⟩
  budget₀ := le_trans h.budget₀ hb
  budget₁ := le_trans h.budget₁ hb
  seeds := pr_le_one _ _
  freeT := h.freeT
  freeL := h.freeL
  freeB := h.freeB
  wires := h.wires
  fmt := h.fmt
  backT := h.backT
  backL := h.backL
  backB := h.backB
  plain := h.plain
  coherent := h.coherent
  isLocal := h.isLocal

end

/-! ## 2. The same object on other indices -/

section
variable {I I' X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- An OOD seed's letters, read at the object on other indices: the same nine fields. (`OutOfDomainSampleQueryLayout` is a
structure with the object as a parameter, so a value at L is no value at `reIndex L f g`, though
each field has the same type.) -/
def seedRe (f : I' → I) (g : I → Option I') {K : ℕ} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    OutOfDomainSampleQueryLayout lam K (AtPublicFiles.Cut.reIndex L f g) Bd aT aL :=
  ⟨S.t, S.cfg, S.shape, S.pl0, S.pl1, S.seed, S.code, S.num, S.decS⟩

/-- **`NoProverSide` goes over to the object on other indices** (`reIndex`, E2E/CutIndex.lean), WITH
THE SAME WIRING AND CODE, and the same OOD seed's letters read there (`seedRe`): the three
protocols, the marks, the number of requests in a batch and the types of OOD seeds and answers are
the same terms, so the carrier over which a wiring is typed is the same. The clause `hidE` is asked
at f i, f i'. -/
theorem NoProverSide.reIndex (f : I' → I) (g : I → Option I')
    {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} {Gs : L.OutOfDomainSeed → Prop} {N : NumsW} {M : ℕ}
    {capT capL capB : ℕ → ℕ} (h : NoProverSide W S cA Gs N M capT capL capB) :
    NoProverSide (L := AtPublicFiles.Cut.reIndex L f g) (Bd := Bd) (aT := aT) (aL := aL) W (seedRe f g S) cA
      Gs N M capT capL capB where
  reads := ⟨h.reads.cntT, h.reads.cntLp, h.reads.cntLc, h.reads.cntO,
    fun Q hQ s hs i i' => h.reads.hidE Q hQ s hs (f i) (f i')⟩
  budget₀ := h.budget₀
  budget₁ := h.budget₁
  seeds := h.seeds
  freeT := h.freeT
  freeL := h.freeL
  freeB := h.freeB
  wires := ⟨h.wires.base, h.wires.T, h.wires.Lk, h.wires.B, ⟨h.wires.ans.inj, h.wires.ans.len⟩⟩
  fmt := h.fmt
  backT := h.backT
  backL := h.backL
  backB := h.backB
  plain := h.plain
  coherent := h.coherent
  isLocal := h.isLocal

/-- The case of the object cut to the indices with p. -/
theorem NoProverSide.cut (p : I → Prop) {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {Gs : L.OutOfDomainSeed → Prop} {N : NumsW}
    {M : ℕ} {capT capL capB : ℕ → ℕ} (h : NoProverSide W S cA Gs N M capT capL capB) :
    NoProverSide (L := AtPublicFiles.Cut.cut L p) (Bd := Bd) (aT := aT) (aL := aL) W
      (seedRe Subtype.val (AtPublicFiles.Cut.back p) S) cA Gs N M capT capL capB :=
  h.reIndex Subtype.val (AtPublicFiles.Cut.back p)

end

/-! ## 3. At letters T of the full size -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
  {DK DP : WholeD} {runK : RecFull → View → View → View → Bool}
  {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (X := X) A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- `NoProverSide` at letters T, from what hangs on the data, the OOD seed's letters and the
numbers. -/
theorem noProverSide_at {v : ℕ} (f : FrameFitFullD K v depthReq T.depthReqT DK DP ds xs)
    (hpl : SeedPlain T.W T.letters.Sd) (Gs : _ → Prop) (N : NumsW) (M : ℕ)
    (hr : Hiop.Seeded.ReadsG
      ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P) Gs
      N.b N.qT N.qpar N.qch N.qon)
    (h₀ : N.qT + (M + 1) * N.qpar ≤ N.b) (h₁ : N.qch + N.s1 * N.qon ≤ N.b)
    (hs : pr (unif (Fin T.W.K → Dig 256)) {u | ¬ Gs (T.letters.Sd.seed u)} ≤ N.δ)
    (capT capL capB : ℕ → ℕ) :
    NoProverSide T.W T.letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) Gs N M capT capL
      capB where
  reads := hr
  budget₀ := h₀
  budget₁ := h₁
  seeds := hs
  freeT := (free_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT).1
  freeL := (free_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT).2.1
  freeB := (free_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT).2.2
  wires := oka_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT f
  fmt := fmt_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P
  backT := (back_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT capT capL capB).1
  backL := (back_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT capT capL capB).2.1
  backB := (back_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT capT capL capB).2.2
  plain := hpl
  coherent := coherent_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P
  isLocal := local_fullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P

end

/-! ## 4. At three public files Z -/

/-- The numbers: at most 44,040,191 columns of one table may be read in all; 62, 62, 62 are read by
the key file's verifier and by a link's on either table, 64 by one request's verifier of the proof
file; no OOD seed is set aside. -/
def indexPrivacyNumbers (s1 : ℕ) (zT zL zO hT hL hO : ℝ≥0∞) : NumsW :=
  ⟨44040191, 62, 62, 62, 64, s1, zT, zL, zO, hT, hL, hO, 0⟩

/-- **One request's verifier of the proof file reads at most 64 columns**, at every Z in scope, with
the gate open or shut. (E2E/ReadsAtFiles.lean counts a whole batch together.) -/
theorem one_atFiles (Z : PublicFiles) (scope : InScope Z = true) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers) :
    ∀ x ρ, ((((AtPublicFiles.AtFiles.filesAt Z).withProvers P).onlineBatch.loc.extReads x ρ).card ≤ 64) := fun _ ρ => by
  refine le_trans (AtPublicFiles.Reads.whole_card ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (_root_.Run.ckP .two)
    (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty OnBytes.Flat.silP (dataAtFiles flashProveData Z).runP ρ) ?_
  cases live : FlashProve.protocolDataWellFormed (asDescriptionFiles Z) with
  | true =>
    rw [AtPublicFiles.Reads.proof_data Z scope live, AtPublicFiles.Reads.proof_sums.1, AtPublicFiles.Reads.proof_sums.2.1,
      AtPublicFiles.Reads.proof_sums.2.2]
  | false =>
    rw [(AtPublicFiles.Reads.data_shut Z live).2]
    show AtPublicFiles.Reads.storedSum FlashProve.emptyRoundsData.ds₁ + (AtPublicFiles.Reads.storedSum FlashProve.emptyRoundsData.ds₂ +
                         AtPublicFiles.Reads.storedSum FlashProve.emptyRoundsData.ds₃) ≤ 64
    rw [AtPublicFiles.Reads.dead_sums.1, AtPublicFiles.Reads.dead_sums.2.1, AtPublicFiles.Reads.dead_sums.2.2]
    exact Nat.zero_le _

/-- **The counts of reads and the clause `hidE`, in the form in which `PremW` asks them**, at every
Z in scope, for all provers, at all OOD seeds. -/
theorem readsG_atFiles (Z : PublicFiles) (scope : InScope Z = true) (P : (AtPublicFiles.AtFiles.filesAt Z).Provers) :
    Hiop.Seeded.ReadsG ((AtPublicFiles.AtFiles.filesAt Z).withProvers P) (fun _ => True) 44040191 62 62 62 64 :=
  have h := AtPublicFiles.Reads.reads_filesAt_scope Z scope P
  ⟨h.cntT, h.cntLp, h.cntLc, one_atFiles Z scope P, fun Q hQ s _ i i' => h.hidE Q hQ s i i'⟩

/-- The plain parts of an OOD seed's two queries are of the key file's front round, whose wire has
no test. -/
theorem seedPlain_atFiles (Z : PublicFiles) (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    SeedPlain ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).letters.Sd :=
  ⟨nonceOf_plainFirst _ _ _ _ _ _ rfl, nonceOf_plainFirst _ _ _ _ _ _ rfl⟩

/-- **A member of `NoProverSide`: the letters from which the verifier is compiled**, at every Z in
scope, with no OOD seed set aside, at most 710,324 copies, at most 688,127 sessions a copy (of one
request each), all caps. -/
theorem noProverSide_atFiles (Z : PublicFiles) (scope : InScope Z = true)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) (M s1 : ℕ) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (zT zL zO hT hL hO : ℝ≥0∞) (capT capL capB : ℕ → ℕ) :
    NoProverSide ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).letters.Sd
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (fun _ => True)
      (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB :=
  noProverSide_at ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)
    (VerifiableInference.OnPublicFiles.frameFitFullD_parts (FlashProve.fit_theLay Z))
    (seedPlain_atFiles Z c₀ m₀) (fun _ => True) (indexPrivacyNumbers s1 zT zL zO hT hL hO) M
    (readsG_atFiles Z scope (dataAtFiles flashProveData Z).P)
    (by show 62 + (M + 1) * 62 ≤ 44040191; omega) (by show 62 + s1 * 64 ≤ 44040191; omega)
    (by
      have e : {u : Fin ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W.K → Dig 256 |
          ¬ (fun _ => True) (((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).letters.Sd.seed u)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun _ hu => hu trivial
      rw [e, pr_empty]
      exact le_refl _)
    capT capL capB

/-- The member, spelled at the input of the value that the library builds: its wiring, its OOD
seed's letters and its code of the answers are those of the letters above, by unfolding. -/
theorem noProverSide_built (Z : PublicFiles) (scope : InScope Z = true) (M s1 : ℕ) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (zT zL zO hT hL hO : ℝ≥0∞) (capT capL capB : ℕ → ℕ)
    (c : VerifiableInference.Digest) (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    NoProverSide ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).queryLayout
      ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).seedQueries
      ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).answerCode (fun _ => True)
      (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB :=
  noProverSide_atFiles Z scope c m M s1 hM hs zT zL zO hT hL hO capT capL capB

/-- **THE MEMBER AT THE INPUT AT WHICH THE GOALS' VERIFIER CALLS THE COMPILED VERIFIER**: at the IOP
as written in Lean where all goals but two read it (`atSecondHashFunction theDescription`), at every Z in scope,
every value c of the type of digests and every further reading m: the wiring, the OOD seed's letters
and the code of the answers are the input's own fields. (That `VerifierAndGoals.verify` calls the compiled
verifier at `D.input Z c m` is its definition: `verify_calls`, E2E/DescriptionTie.lean.) -/
theorem noProverSide_description (Z : PublicFiles) (scope : InScope Z = true) (M s1 : ℕ)
    (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127) (zT zL zO hT hL hO : ℝ≥0∞)
    (capT capL capB : ℕ → ℕ) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      NoProverSide ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).queryLayout
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).seedQueries
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).answerCode (fun _ => True)
        (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More),
      NoProverSide (D.input Z c m).queryLayout (D.input Z c m).seedQueries (D.input Z c m).answerCode (fun _ => True)
        (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB)
    (noProverSide_built Z scope M s1 hM hs zT zL zO hT hL hO capT capL capB)

/-! ### Three tests that fail -/

/-- **At one column more it fails**, and at every larger number: at every Z, with Gs all OOD seeds,
whatever the other numbers, the caps, c₀ and m₀. -/
theorem not_noProverSide_column (Z : PublicFiles) (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256))
    (N : NumsW) (hb : 44040192 ≤ N.b) (M : ℕ) (capT capL capB : ℕ → ℕ) :
    ¬ NoProverSide ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).letters.Sd
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (fun _ => True) N M capT capL capB :=
  fun h => AtPublicFiles.Table.not_hidE_filesAt Z (dataAtFiles flashProveData Z).P
    fun Q hQ s i i' => h.reads.hidE Q (le_trans hQ hb) s trivial i i'

/-- The same, spelled at the input of the value that the library builds. -/
theorem not_noProverSide_column_built (Z : PublicFiles) (N : NumsW) (hb : 44040192 ≤ N.b) (M : ℕ)
    (capT capL capB : ℕ → ℕ) (c : VerifiableInference.Digest)
    (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    ¬ NoProverSide ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).queryLayout
      ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).seedQueries
      ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).answerCode (fun _ => True) N M capT capL capB :=
  not_noProverSide_column Z c m N hb M capT capL capB

/-- **The test that fails, at the same input as the member**: at 44,040,192 columns or more, with Gs
all OOD seeds. -/
theorem not_noProverSide_column_description (Z : PublicFiles) (N : NumsW) (hb : 44040192 ≤ N.b) (M : ℕ)
    (capT capL capB : ℕ → ℕ) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      ¬ NoProverSide ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).queryLayout
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).seedQueries
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m).answerCode (fun _ => True) N M capT capL
        capB :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More),
      ¬ NoProverSide (D.input Z c m).queryLayout (D.input Z c m).seedQueries (D.input Z c m).answerCode (fun _ => True) N M
        capT capL capB)
    (not_noProverSide_column_built Z N hb M capT capL capB)

section
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} {Gs : L.OutOfDomainSeed → Prop}

/-- At these numbers it fails at one copy more, at every object and wiring: arithmetic alone. So
710,324 is the most at the count 62, which is an upper bound. -/
theorem not_noProverSide_copy (s1 : ℕ) (zT zL zO hT hL hO : ℝ≥0∞) (capT capL capB : ℕ → ℕ) :
    ¬ NoProverSide W S cA Gs (indexPrivacyNumbers s1 zT zL zO hT hL hO) 710324 capT capL capB := fun h => by
  have h' : 62 + (710324 + 1) * 62 ≤ 44040191 := h.budget₀
  omega

/-- And at one session more: 688,127 is the most at the counts 62 and 64. -/
theorem not_noProverSide_session (zT zL zO hT hL hO : ℝ≥0∞) (M : ℕ) (capT capL capB : ℕ → ℕ) :
    ¬ NoProverSide W S cA Gs (indexPrivacyNumbers 688128 zT zL zO hT hL hO) M capT capL capB := fun h => by
  have h' : 62 + 688128 * 64 ≤ 44040191 := h.budget₁
  omega

end

/-- **The same at the object cut to the matrices in range** (`objAt`, E2E/ObjectAtFiles.lean), at
the library's own provers, with the same wiring and code and the same OOD seed's letters read
there. -/
theorem noProverSide_objAt (Z : PublicFiles) (scope : InScope Z = true)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) (M s1 : ℕ) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (zT zL zO hT hL hO : ℝ≥0∞) (capT capL capB : ℕ → ℕ) :
    NoProverSide (L := AtPublicFiles.AtFiles.objAt Z (dataAtFiles flashProveData Z).P) ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W
      (seedRe Subtype.val (AtPublicFiles.Cut.back AtPublicFiles.AtFiles.inRange)
        ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).letters.Sd)
      (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) (fun _ => True)
      (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB :=
  (noProverSide_atFiles Z scope c₀ m₀ M s1 hM hs zT zL zO hT hL hO capT capL capB).cut
    AtPublicFiles.AtFiles.inRange

end AtPublicFiles.Premises

#print axioms AtPublicFiles.Premises.premW_iff
#print axioms AtPublicFiles.Premises.NoProverSide.restrict
#print axioms AtPublicFiles.Premises.NoProverSide.noSeeds
#print axioms AtPublicFiles.Premises.NoProverSide.reIndex
#print axioms AtPublicFiles.Premises.NoProverSide.cut
#print axioms AtPublicFiles.Premises.noProverSide_at
#print axioms AtPublicFiles.Premises.one_atFiles
#print axioms AtPublicFiles.Premises.readsG_atFiles
#print axioms AtPublicFiles.Premises.seedPlain_atFiles
#print axioms AtPublicFiles.Premises.noProverSide_atFiles
#print axioms AtPublicFiles.Premises.noProverSide_built
#print axioms AtPublicFiles.Premises.noProverSide_description
#print axioms AtPublicFiles.Premises.not_noProverSide_column
#print axioms AtPublicFiles.Premises.not_noProverSide_column_built
#print axioms AtPublicFiles.Premises.not_noProverSide_column_description
#print axioms AtPublicFiles.Premises.not_noProverSide_copy
#print axioms AtPublicFiles.Premises.not_noProverSide_session
#print axioms AtPublicFiles.Premises.noProverSide_objAt
