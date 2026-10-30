-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SoundAsIOPProbabilityAtFiles.lean: SOUNDNESS AS AN IOP AT THE PUBLIC FILES Z, AS A PROBABILITY: for
every prover of the whole run, the chance that all three verifiers accept and the conclusion fails,
OVER THE CHALLENGES THAT PASS THE TESTS OF PROOF OF WORK. Definitions and statements; the proofs are in
E2E/SoundAsIOPProbabilityAtFilesProofs.lean and E2E/SoundAsIOPWorkIsTheVerifiers.lean. Nothing is
proved in this file.

If this holds: whatever a prover of the whole run does (Hiop/SoundAsIOP.lean, line 6), the chance that
the three verifiers accept while the first table decodes to no index, or the copy to another, or the
request is false at that index, is at most
      (number of rounds of the whole run) * 2^(mostWorkAtFiles Z) * 2^-128.

THE MEASURE. The two points of the out-of-domain samples are uniform. The challenges of the offline,
the link and the online part are uniform challenges with the bits of proof of work set to 0, round by
round, as the verifier's wires at Z declare these bits (RoundsQueryLayout.zero, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean).
THESE ARE THE VERIFIERS' OWN CHALLENGES: each of the three verifiers accepts only a transcript whose
challenges pass every test of the wires (Statements.verifiersAskTheWork, (h)).
IT IS THE UNIFORM MEASURE ON THEM: in each part, challenges that pass are the cleared form of exactly
2^(all that part's bits of work) challenges, and the others of none
(Statements.clearedIsUniformOnPassing, (i)). That is said in counts, part by part; no conditional law is
written as a probability, and none on the challenges of the whole run at once.
Why not uniform challenges: of all challenges of a part one in 2^(all its bits of work) passes
(RoundsQueryLayout.passing_share, Hiop/SoundAsIOPClearing.lean), and elsewhere the verifier rejects; so over uniform
challenges every prover, the honest one too, is seldom accepted, and a bound there is true and says
nothing.
Completeness as an IOP is stated over the same measure, by the text of that statement's files; no file
imports both. Its workAtFiles Z (E2E/CompleteAsIOPAtFiles.lean) is partsWorkOfWire (lettersZ Z allZeroDigest []).W,
whose three fields "cleared" unfold to RoundsQueryLayout.zero at (wTC W).sh, (wLC W).sh, (wBC W).sh with the marks
(filesAt Z).annT, (filesAt Z).annL, (protocolAtFiles Z).onlineBatch.ann: the three terms in Statements.clearingIsTheWires.

  wiringAtFiles Z      the verifier's wiring at Z, at the written pair (allZeroDigest, []); it is the same at
                       every digest and further reading (wiring_any, E2E/BridgePremWLink.lean).
  offlineClearing Z, linkClearing Z, onlineClearing Z   the wires' clearings of the three parts.
  clearingAtFiles Z P fill   the clearing of the whole run: the identity on the five added rounds (two
                       points, two answers, the naming of a request), these three on the parts.
  mostWorkAtFiles Z    the largest number of bits of work that a round's wire at Z declares.
  ConclusionFails Z P fill prover   the event, as a set of challenges of the whole run.
  Statements.clearingIsTheWires   what the clearing does to the verifier's draw: the points stay, each
                       part's challenges go through RoundsQueryLayout.zero at that part's wires.
  Statements.clearedPasses        cleared challenges pass every test of work of the three parts.
  Statements.probabilityAtFiles   (a) THE BOUND, with mostWorkAtFiles Z.
  Statements.mostWorkAtFiles_le   (b) mostWorkAtFiles Z ≤ 64, at every Z.
  Statements.probabilityAtFiles64 (c) so: at most (number of rounds) * 2^-64.
  Statements.roundsAtFiles_le     (d) the whole run has at most 2^20 rounds, at every Z.
  Statements.probabilityAtFiles44 (e) so: at most 2^-44. A NUMBER BELOW 1, WITH NO LETTER LEFT IN IT.
  Statements.mostWorkAtFiles_ge   (f) 32 ≤ mostWorkAtFiles Z, at every Z: a round of the link, whose data
                       are written and do not depend on Z, has 32 bits. So the right side of (a) is
                       nowhere below (rounds) * 2^-96.
  Statements.clearingIsNotTheIdentity   (g) at every Z some challenges of the link are not their own
                       cleared form.
  Statements.verifiersAskTheWork  (h) at every Z and P each verifier accepts only where the wires' tests
                       pass. Proved in E2E/SoundAsIOPWorkIsTheVerifiers.lean.
  Statements.clearedIsUniformOnPassing  (i) at every Z, in each part, the fibres of the clearing are equal.
  Statements.conclusionFails_provers    (j) the rounds and the event are the same at any two P.

WHAT THE NUMBERS SAY, AND WHAT NOT.
- AT THE IOP LEVEL A ROUND WITH w BITS OF PROOF OF WORK HAS ERROR AT MOST 2^-(128-w) AMONG THE CHALLENGES
  THAT PASS, because the IOP does not charge the search for a nonce. The compiler's theorem counts a
  round's error WITH its work (at most 2^-128 so counted) and charges the search to the cheating
  prover's hash queries: its own bound is VerifierAndGoals.soundnessErrorInQueries: 16 / 2^128 for each query (Ladder/Bits.lean).
  These are figures of two different objects. NOBODY MAY TELL THE IOP's SOUNDNESS AS 128 BITS A ROUND.
- In counts: a round's error of 2^-128 is a share of ALL that round's challenges; as a share of the
  challenges that pass it is 2^-128 * 2^(that round's bits of work). (a) takes the largest such round
  for all rounds.
- (c) IS 64 BITS FOR A WHOLE RUN, LESS THE LOGARITHM OF THE NUMBER OF ROUNDS: NOT 128, AND NOT 96. 64 is
  what is a theorem at every Z: the frame's own test on numbers (sizeNumbersFitAtFullSize: WholeD.workFit for the
  offline and the online part, entryFitB for the link), which fails closed.
- At files whose rounds have at most 32 bits of work (a) reads (number of rounds) * 2^-96. (b) and (d)
  are stated at EVERY Z, with no hypothesis, and there 32 is not claimed. THE SHARP NUMBERS STAND UNDER
  THE HYPOTHESES OF (a), in E2E/SoundAsIOPNumbers.lean: at Z in scope where protocolDataWellFormed says yes the rounds'
  data are the written ones, so mostWorkAtFiles Z ≤ 32 and the whole run has 67391 rounds, by
  evaluation in Lean's kernel; with (a): at most 67391 * 2^-96. (c) and (e) are what is had without
  that evaluation.
- THE NUMBER OF ROUNDS is (wholeRunShape fill).length, a function of Z. It counts every round, also those
  in which the verifier sends nothing (three in the offline and three in the online part, the link's
  front round, three of the five added): an overcount. (d) bounds it by 2^20: that is
  the frame's bound on the compiled verifier's own count of hash queries, which holds one query for
  each round and many more for the openings. It is a coarse bound: the link alone has 42 rounds at the
  written data (sibF_len). So (e), 2^-44, is far from what the protocol has; it is what follows from
  the two tests on numbers that fail closed (work ≤ 64, count ≤ 2^20) with no evaluation of the
  offline or the online part's data.

Limits.
- All of Hiop/SoundAsIOP.lean's and of E2E/SoundAsIOPAtFiles.lean's: one whole run; soundness alone; the
  relation is the relaxed one at the files' policy; under InScope, readFiles, protocolDataWellFormed.
- A deterministic prover; a randomised one is a mixture of these, and the bound holds for each.
- P, THE OBJECT's OWN PROVERS, IS A LETTER OF THE TYPES ALONE: (j) shows that the event does not read the
  fields that P fills (honestOfflineProver, honestLinkProver, honestOnlineBatchProver). By reading the definitions, and by no theorem: of the object the
  event reads wordLength, Symbol, OutOfDomainSeed, OutOfDomainAnswer, decodeIndex, offline, link, onlineBatch, early, and not encodeIndex, honestOutOfDomainAnswer, EncodingRandomness. The prover of the
  statements is the argument "prover": any strategy of the whole run.
- That any prover is accepted under this measure is not shown here: that is completeness.
- The bounds (a), (c), (e) rest on neither (h) nor (i): what they spend is that at most 2^(a round's bits
  of work) challenges of that round have one cleared form. (h) and (i) say what the measure is.
-/
import Hiop.SoundAsIOPClearing
import E2E.SoundAsIOPAtFiles
import Johnson.Goal.Conditions.BindsAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Prob Hiop
open _root_.Iop (Clearing Strat Rho Tr)
open TypedOracleCompiler.Iop (RoundsQueryLayout.zero RoundsQueryLayout.pass RoundsQueryLayout.clearing RoundsQueryLayout.mostWork
  RoundsQueryLayout.ClearedIsUniformOnPassing)
open TypedOracleCompiler.Compile.Batch.Cms (wTC wLC wBC)
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles asDescriptionFiles InScope readFiles)
open FlashProve (protocolDataWellFormed allZeroDigest)

/-- The verifier's wiring at Z. -/
abbrev wiringAtFiles (Z : PublicFiles) := (lettersZ Z allZeroDigest []).W

/-- The offline part's clearing at Z: in each round, the bits of work that its wire declares set
to 0. -/
def offlineClearing (Z : PublicFiles) : Clearing (protocolAtFiles Z).offline.shape :=
  RoundsQueryLayout.clearing (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh

/-- The link's. -/
def linkClearing (Z : PublicFiles) : Clearing (protocolAtFiles Z).link.shape :=
  RoundsQueryLayout.clearing (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh

/-- The online part's. -/
def onlineClearing (Z : PublicFiles) : Clearing (protocolAtFiles Z).onlineBatch.loc.shape :=
  RoundsQueryLayout.clearing (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh

/-- **The clearing of the whole run at Z.** P: any provers; the rounds do not depend on them. -/
def clearingAtFiles (Z : PublicFiles) (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill) :
    Clearing (((filesAt Z).withProvers P).wholeRunShape fill) :=
  ((filesAt Z).withProvers P).wholeRunClearing fill (offlineClearing Z) (linkClearing Z) (onlineClearing Z)

/-- **The largest number of bits of proof of work of a round at Z**, over the three parts. -/
def mostWorkAtFiles (Z : PublicFiles) : ℕ :=
  max (RoundsQueryLayout.mostWork (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh)
    (max (RoundsQueryLayout.mostWork (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh)
      (RoundsQueryLayout.mostWork (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh))

/-- **The event**: the challenges of the whole run at whose cleared form the prover's run does not
meet the conclusion: for some request with the named one's early part all three verifiers accept,
while the extractor answers no index, or the copy decodes to another, or the relation fails. -/
def ConclusionFails (Z : PublicFiles) (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill)
    {β : Type} (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β) :
    Set (Rho (((filesAt Z).withProvers P).wholeRunShape fill)) :=
  {ρ | ¬ (((filesAt Z).withProvers P).wholeRunOf fill
      (prover.run ((clearingAtFiles Z P fill).cleared ρ)).1).Concludes (relationAtFiles Z)}

namespace Statements

/-- States: **the clearing is the wires'**: of the verifier's draw of a whole run the two points stay,
and each part's challenges go through RoundsQueryLayout.zero at that part's wires. -/
def clearingIsTheWires : Prop :=
  ∀ (Z : PublicFiles) (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill)
      (ρ : Rho (((filesAt Z).withProvers P).wholeRunShape fill)),
    ((filesAt Z).withProvers P).wholeRunDraw fill ((clearingAtFiles Z P fill).cleared ρ) =
      ((((filesAt Z).withProvers P).wholeRunDraw fill ρ).1,
        (RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh
            (((filesAt Z).withProvers P).wholeRunDraw fill ρ).2.1,
          RoundsQueryLayout.zero (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh
            (((filesAt Z).withProvers P).wholeRunDraw fill ρ).2.2.1,
          RoundsQueryLayout.zero (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh
            (((filesAt Z).withProvers P).wholeRunDraw fill ρ).2.2.2))

/-- States: **cleared challenges pass every test of work**, in each of the three parts, at every Z. -/
def clearedPasses : Prop :=
  ∀ Z : PublicFiles,
    (∀ ρ, RoundsQueryLayout.pass (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh
      ((offlineClearing Z).cleared ρ) = true) ∧
    (∀ ρ, RoundsQueryLayout.pass (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh
      ((linkClearing Z).cleared ρ) = true) ∧
    (∀ ρ, RoundsQueryLayout.pass (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh
      ((onlineClearing Z).cleared ρ) = true)

/-- States: **(a) THE BOUND.** At Z in scope, read, where protocolDataWellFormed says yes: for every P, every fill and
every prover of the whole run, over uniform points and the challenges that pass, the conclusion fails
with probability at most (number of rounds) * (2^(the largest work of a round) * 2^-128). -/
def probabilityAtFiles : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill)
      (β : Type) (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β),
    pr (unif (Rho (((filesAt Z).withProvers P).wholeRunShape fill))) (ConclusionFails Z P fill prover) ≤
      ((((filesAt Z).withProvers P).wholeRunShape fill).length : ℝ≥0∞) *
        (((2 ^ mostWorkAtFiles Z : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128)

/-- States: **(b) no round at any Z has more than 64 bits of work.** -/
def mostWorkAtFiles_le : Prop :=
  ∀ Z : PublicFiles, mostWorkAtFiles Z ≤ 64

/-- States: **(c) so: at most (number of rounds) * 2^-64.** -/
def probabilityAtFiles64 : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill)
      (β : Type) (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β),
    pr (unif (Rho (((filesAt Z).withProvers P).wholeRunShape fill))) (ConclusionFails Z P fill prover) ≤
      ((((filesAt Z).withProvers P).wholeRunShape fill).length : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 64

/-- States: **(d) the whole run at any Z has at most 2^20 rounds.** -/
def roundsAtFiles_le : Prop :=
  ∀ (Z : PublicFiles) (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill),
    (((filesAt Z).withProvers P).wholeRunShape fill).length ≤ 2 ^ 20

/-- States: **(e) so: at most 2^-44.** -/
def probabilityAtFiles44 : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill)
      (β : Type) (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β),
    pr (unif (Rho (((filesAt Z).withProvers P).wholeRunShape fill))) (ConclusionFails Z P fill prover) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 44

/-- States: **(f) at every Z some round has at least 32 bits of work**: so the right side of (a) is
nowhere below (number of rounds) * 2^-96. -/
def mostWorkAtFiles_ge : Prop :=
  ∀ Z : PublicFiles, 32 ≤ mostWorkAtFiles Z

/-- States: **(g) at every Z the clearing is not the identity**: some challenges of the link are not
their own cleared form. -/
def clearingIsNotTheIdentity : Prop :=
  ∀ Z : PublicFiles, ∃ ρ, (linkClearing Z).cleared ρ ≠ ρ

/-- States: **(h) the verifiers ask the work**: at every Z and for any provers P, each of the three
verifiers accepts only a transcript whose challenges pass every test of that part's wires. -/
def verifiersAskTheWork : Prop :=
  ∀ (Z : PublicFiles) (P : (filesAt Z).Provers),
    (∀ x y (τ : Tr ((filesAt Z).withProvers P).offline.shape), ((filesAt Z).withProvers P).offline.accept x y τ = true →
      RoundsQueryLayout.pass (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh τ.rho = true) ∧
    (∀ x y (τ : Tr ((filesAt Z).withProvers P).link.shape), ((filesAt Z).withProvers P).link.accept x y τ = true →
      RoundsQueryLayout.pass (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh τ.rho = true) ∧
    (∀ x y (τ : Tr ((filesAt Z).withProvers P).onlineBatch.loc.shape),
      ((filesAt Z).withProvers P).onlineBatch.loc.accept x y τ = true →
      RoundsQueryLayout.pass (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh τ.rho = true)

/-- States: **(i) uniform challenges, cleared, are uniform on the challenges that pass**, in each of the
three parts, at every Z; in counts (RoundsQueryLayout.ClearedIsUniformOnPassing, Hiop/SoundAsIOPClearing.lean). -/
def clearedIsUniformOnPassing : Prop :=
  ∀ Z : PublicFiles,
    RoundsQueryLayout.ClearedIsUniformOnPassing (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh ∧
    RoundsQueryLayout.ClearedIsUniformOnPassing (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh ∧
    RoundsQueryLayout.ClearedIsUniformOnPassing (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh

section
/- Lean compares these names and does not unfold them: what follows reads of the object at Z only how
it is made of the three protocols and the provers. -/
attribute [local irreducible] filesAt offlineClearing linkClearing onlineClearing relationAtFiles

/-- States: **(j) neither the rounds nor the event depend on the provers P**: at two P's the whole run
has the same list of rounds, and a prover of the whole run has the same event. -/
def conclusionFails_provers : Prop :=
  ∀ (Z : PublicFiles) (P P' : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill) (β : Type)
      (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β),
    ((filesAt Z).withProvers P).wholeRunShape fill =
        ((filesAt Z).withProvers P').wholeRunShape ⟨fill.table, fill.answer, fill.request⟩ ∧
      ConclusionFails Z P fill prover =
        ConclusionFails Z P' ⟨fill.table, fill.answer, fill.request⟩ prover

end

end Statements

end AtPublicFiles.AtFiles
