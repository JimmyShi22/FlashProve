-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/PrivacyAtDescription.lean: THE CONCLUSION OF `OnBytes.WholeKey.wholeKeyPrivacy`
(Johnson/WholeKey/Main.lean, Statement.lean) AT THE INPUT AT WHICH `VerifierAndGoals.verify` CALLS THE
COMPILED VERIFIER, FROM THE FIVE FIELDS OF ITS LIST OF PREMISES THAT ARE LEFT. By calls: `premW_iff`
and `noProverSide_description` (E2E/PremisesAtFiles.lean), then `wholeKeyPrivacy`.

`wholeKeyPrivacy` has one list of premises, `PremW` (Johnson/WholeKey/Premises.lean), of twenty
fields. Fifteen read no prover's strategy, no coin and no simulator: they hold at that input
(E2E/PremisesAtFiles.lean). Five are left.

  `FiveLeft r a Sm ok Gs Ryes c N`: these five fields at an input r, at its own wiring and its own
    parameters, in the words of `PremW`: `ExtEnc`, `RunVals`, `Sims.Good`, `StopsSmall`, `CoinsFit`.
  `three_of_five_silent`: A WARNING: three of them are met at every input, at errors 0, by sides
    that send fixed messages.
  `premW_of_five`: `NoProverSide` and `FiveLeft` at r give `PremW` at r.queryLayout, r.seedQueries, r.answerCode, r.compilerParameters.
  `privacy_of_five`: so they give the conclusion of `wholeKeyPrivacy` at the scheme `wholeKeySchemeOverTypedOracles r`
    (Johnson/WholeKey/AtInput.lean).
  `PrivacyFromFive r`: at r, for all honest sides a with at most 710,324 copies, all simulators, all
    ranges of indices, at most 688,127 sessions a copy (of one request each), no OOD seed set aside
    and the numbers `indexPrivacyNumbers`: `FiveLeft` gives that conclusion.
  `privacyFromFive_of`: it holds at every input at which the fifteen hold at these numbers.
  **`privacyFromFive_description`**: `PrivacyFromFive` holds at
    `(atSecondHashFunction theDescription).input Z c m`, at every Z in scope, every c and every m.

Limits.
  * CONDITIONAL, AND THE PREMISE IS MET BY PROVERS THAT SEND FIXED MESSAGES. All five fields are met
    together, at errors 0, by sides that send fixed messages and never stop: at the input in view
    (`hasSilentMember_description`), and at every input whose type LeafBody has a member
    (`fiveLeft_silent`; both in E2E/FiveLeftSilent.lean); three of them already by
    `three_of_five_silent`, from `silent_good` (Johnson/WholeKey/Foes.lean).
    That the five fields are met at the honest provers of the protocol (`honestProvers`,
    E2E/TheHonestProver.lean) is not shown here: the statements that name `FiveLeft` have it at
    provers that send fixed messages alone (E2E/FiveLeftSilent.lean, FiveLeftSilentCaps.lean,
    FiveLeftSilentWindows.lean). `compiled_indexPrivacy` (Johnson/T3/CompiledPrivacy.lean) derives
    `PremW`, inside its proof, for any provers from their honest-verifier zero knowledge as
    interactive oracle proofs and its premises on run values, coins and the public layout, at its
    own layout of hash queries. Of the three parts the link's prover and its simulator stand as one
    of three in E2E/LinkLaidPrivacy.lean, beside two provers that send fixed messages, at the input
    at one fixed digest, at which verify is not proved ever to be called. In the words of
    Johnson/WholeKey/Statement.lean on its own statement, to the letter:
    "NOTHING OF A PROTOCOL UNLESS COMPLETENESS OF THE SAME HONEST SIDES, AT A SMALL ERROR, STANDS
    BESIDE IT. Index privacy alone is cheap: silent honest sides, which send fixed messages, meet
    the premises on provers with error 0 (proved: silent_good, Johnson/WholeKey/Foes.lean). What
    they are meant to fail is completeness."
  * R and Ryes are free letters: no relation is named. The range ok is a free letter too, tied to
    nothing. In the same file's words, to the letter:
    "THE RANGE ok, BY NAME. Nothing is said of an index outside it, and NO TERM OF ζ PAYS FOR IT: at
    a small range the premises are weak, ζ stays small and little is said. A quote says which range
    it is; that it holds two indices or more; and that every index with a true instance lies in it."
    "ONE REQUEST A PROOF (batches of at most one slot)."
  * Of Z the one premise is `InScope Z`. That the IOP's own test on the public files accepts at Z is
    no premise here; that it accepts is shown in the side library: at the library's two named sets
    of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files under every
    policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no theorem ties
    any of these to a file on a disk.
  * What the conclusion means, and what it does not, is said at `Spec.wholeKeyPrivacy`
    (Johnson/WholeKey/Statement.lean) and not here. This file adds no sentence on it.
  * The error `zetaW` is a letter's worth: no number is computed here (at the honest sides that send
    fixed messages, a bound and a number: E2E/ZetaAtCaps.lean). It reads the free letter c, which
    holds the number of free bits in a leaf's salt. In the words of Johnson/WholeKey/Zeta.lean, to
    the letter:
    "A bound that is 1 or more makes a statement of index privacy trivially true: a bar on ζ at
    named letters is owed by whoever uses it."
  * The scheme is `wholeKeySchemeOverTypedOracles r`, not the scheme that `VerifierAndGoals.verify` belongs to: what ties the two is
    said in Johnson/WholeKey/AtInput.lean.
  * All limits of E2E/PremisesAtFiles.lean stand: above all those beside the clause `hidE`; that
    five of the fifteen hold by type or by default; that `atSecondHashFunction theDescription` is where all goals
    but two read the IOP as written in Lean; that the IOP's own tests on the public files are shown
    to pass by no theorem of this folder (the side library shows it at the library's two named sets
    of public files, AtFullSide/E2E/AtWrittenFiles.lean, and at the first set's files under every
    policy within four bounds: `theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean), and that no
    theorem ties any of these to a file on a disk.
  * With no OOD seed set aside, `Sims.Good` and `StopsSmall` are asked at every OOD seed.

`FiveLeft` and `PrivacyFromFive` may be read as stating a goal. They are not among this library's
goals.

-/
import E2E.PremisesAtFiles
import Johnson.WholeKey.Main
import Johnson.WholeKey.Foes

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Premises
open OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope)

/-- **The five fields of `PremW` that are left**, at an input r: at its own wiring and parameters.
-/
structure FiveLeft (r : InnerCompilerInput) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol)
    (ok : r.Index → Prop) (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) (c : CoinNums r.LeafBody)
    (N : NumsW) : Prop where
  ext : ExtEnc a.Hs
  runVals : RunVals a ok
  good : Sm.Good a.Hs r.queryLayout ok Gs Ryes N.zT N.zL N.zO
  stops : StopsSmall a.Hs r.queryLayout ok Gs Ryes N.hT N.hL N.hO
  coins : CoinsFit r.queryLayout r.compilerParameters a c

/-- **A warning: provers that send fixed messages meet three of the five.** At every input, for all
sets of OOD seeds and all relations, the sides that send each round's fixed message and never stop
(`silent`, Johnson/WholeKey/Foes.lean) meet three of the five fields at errors 0, at all indices. -/
theorem three_of_five_silent (r : InnerCompilerInput) (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) :
    ExtEnc (silent r.protocol) ∧
      (∃ Sm : Sims r.protocol, Sm.Good (silent r.protocol) r.queryLayout (fun _ => True) Gs Ryes 0 0 0) ∧
      StopsSmall (silent r.protocol) r.queryLayout (fun _ => True) Gs Ryes 0 0 0 :=
  ⟨extEnc_silent r.protocol, silent_good r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout Gs Ryes⟩

section
variable (r : InnerCompilerInput) {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol} {ok : r.Index → Prop}
  {Gs : r.protocol.OutOfDomainSeed → Prop} {Ryes : r.Index → r.Instance → Prop} {c : CoinNums r.LeafBody} {N : NumsW}

/-- The fifteen and the five give `PremW`. -/
theorem premW_of_five (h0 : NoProverSide r.queryLayout r.seedQueries r.answerCode Gs N a.M a.capT a.capL a.capB)
    (h : FiveLeft r a Sm ok Gs Ryes c N) : PremW r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm ok Gs Ryes c N :=
  (premW_iff r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm ok Gs Ryes c N).2
    ⟨h0, h.ext, h.runVals, h.good, h.stops, h.coins⟩

/-- So they give the conclusion of `wholeKeyPrivacy` at the scheme `wholeKeySchemeOverTypedOracles r`. -/
theorem privacy_of_five (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index)
    (hR : ∀ i x w, R.yes i x w → Ryes i x)
    (h0 : NoProverSide r.queryLayout r.seedQueries r.answerCode Gs N a.M a.capT a.capL a.capB)
    (h : FiveLeft r a Sm ok Gs Ryes c N) :
    ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r a.side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ N.s1 Gs Unit) (zetaW r.queryLayout r.seedQueries r.compilerParameters a c N) ok :=
  wholeKeyPrivacy r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters a Sm ok Gs Ryes c N R i₀ hR
    (premW_of_five r h0 h)

end

/-- At the input r: for all honest sides with at most 710,324 copies, all simulators, ranges and
relations, at most 688,127 sessions a copy, no OOD seed set aside, at the numbers `indexPrivacyNumbers`: the five
fields that are left give the conclusion of `wholeKeyPrivacy`. -/
def PrivacyFromFive (r : InnerCompilerInput) : Prop :=
  ∀ (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol) (ok : r.Index → Prop)
    (Ryes : r.Index → r.Instance → Prop) (c : CoinNums r.LeafBody) (s1 : ℕ) (zT zL zO hT hL hO : ℝ≥0∞)
    (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index),
    a.M + 1 ≤ 710324 → s1 ≤ 688127 → (∀ i x w, R.yes i x w → Ryes i x) →
    FiveLeft r a Sm ok (fun _ => True) Ryes c (indexPrivacyNumbers s1 zT zL zO hT hL hO) →
    ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r a.side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ s1 (fun _ => True) Unit)
      (zetaW r.queryLayout r.seedQueries r.compilerParameters a c (indexPrivacyNumbers s1 zT zL zO hT hL hO)) ok

/-- At any input at which the fifteen hold at these numbers. (Stated at a letter r, so that Lean
does not open the value at which it is called.) -/
theorem privacyFromFive_of (r : InnerCompilerInput)
    (h0 : ∀ (M s1 : ℕ), M + 1 ≤ 710324 → s1 ≤ 688127 →
      ∀ (zT zL zO hT hL hO : ℝ≥0∞) (capT capL capB : ℕ → ℕ),
        NoProverSide r.queryLayout r.seedQueries r.answerCode (fun _ => True) (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB) :
    PrivacyFromFive r :=
  fun a Sm ok Ryes c s1 zT zL zO hT hL hO R i₀ hM hs hR h =>
    privacy_of_five r (a := a) (Sm := Sm) (ok := ok) (Gs := fun _ => True) (Ryes := Ryes) (c := c)
      (N := indexPrivacyNumbers s1 zT zL zO hT hL hO) R i₀ hR
      (h0 a.M s1 hM hs zT zL zO hT hL hO a.capT a.capL a.capB) h

/-- **At the input at which the goals' verifier calls the compiled verifier**, at every Z in scope,
every value c of the type of digests and every further reading m. CONDITIONAL, AND THE PREMISE IS
MET BY PROVERS THAT SEND FIXED MESSAGES: `three_of_five_silent`, and E2E/FiveLeftSilent.lean. -/
theorem privacyFromFive_description (Z : PublicFiles) (scope : InScope Z = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      PrivacyFromFive ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  fun c m => privacyFromFive_of ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m)
    fun M s1 hM hs zT zL zO hT hL hO capT capL capB =>
      noProverSide_description Z scope M s1 hM hs zT zL zO hT hL hO capT capL capB c m

end AtPublicFiles.Premises

#print axioms AtPublicFiles.Premises.three_of_five_silent
#print axioms AtPublicFiles.Premises.premW_of_five
#print axioms AtPublicFiles.Premises.privacy_of_five
#print axioms AtPublicFiles.Premises.privacyFromFive_of
#print axioms AtPublicFiles.Premises.privacyFromFive_description
