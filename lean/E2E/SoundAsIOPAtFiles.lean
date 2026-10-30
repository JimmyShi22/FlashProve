-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SoundAsIOPAtFiles.lean: SOUNDNESS AS AN IOP (Hiop/SoundAsIOP.lean) AT THE PROTOCOL OF THE PUBLIC
FILES Z, the object at which verify calls the compiled verifier. Definitions and statements; the proofs are in
E2E/SoundAsIOPAtFilesProofs.lean.

  relationAtFiles Z   the object's relation: the matrix is in range, and the claim of the request
                      holds on it. IT IS A RELAXED RELATION, AT THE FILES' POLICY: see below.
  offlinePlaces Z     the places of a batch of the offline part, as the compiler's wire has them.
  SoundAsIOPAtFiles Z P   IndexKnowledgeSoundIOP of (filesAt Z).withProvers P at that relation, every round's error
                      at most 2^-128 of ALL its challenges, the bits of proof of work among them.
                      P: the object's HONEST provers, not the cheating one.
  Statements.soundAsIOPAtFiles        it holds: at Z in scope, read, where protocolDataWellFormed says yes, FOR EVERY
                      P: from keySound_holds, entrySound, proofSoundAt_of_verify, obj_noneColl,
                      entryFull_record and a bound on the count of that last one.
  NO BOUND ON A PROVER'S PROBABILITY IS STATED IN THIS FILE (Limits): that is
  E2E/SoundAsIOPProbabilityAtFiles.lean, over the challenges that pass the tests of proof of work.
  Statements.wholeRunAtFiles          so the one statement on the whole run holds there, every round at
                      most 2^-128 of its challenges.
  Statements.relationMeans            what the relation gives for a request that is built from a prompt
                      and output tokens.
  Statements.compilerPremises         SoundAsIOPAtFiles Z at the placeholder provers gives the three
                      hypotheses on soundness of the compiler's theorem (CompilerSoundnessConditionStatements.keySound, entrySound,
                      proofSound) and CompilerSoundnessConditionStatements.noneColl, at the compiler's input rZ Z.
  Statements.soundOfVerifyThroughIOP  the statement of sound_of_verify_at, to the letter, FROM
                      SoundAsIOPAtFiles Z where protocolDataWellFormed says yes.
  THESE LAST TWO SHOW NOTHING BY THEIR STATEMENTS ALONE: their conclusions are theorems of this
  library, so each could be proved with its premise thrown away. That the premise IS what the
  compiler's theorem asks is said for every input, where nothing is known beforehand, in
  Johnson/Top/SoundAsIOPIsThePremise.lean. That the proofs here do go through the premise is not
  tested by any file of this library.

The value. protocolAtFiles Z (E2E/BridgeJoinAtFiles.lean) is (filesAt Z).withProvers (filesAt Z).fixedMessageProvers (the example below):
the object in the input at which VerifierAndGoals.verify calls the compiled verifier, at every digest and further
reading (object_description, E2E/DescriptionTie.lean). rZ Z is the compiler's input at two fixed values of
these readings (theC0, theM0); verify calls the input at the digest that it reads; the OBJECT is the
same in all of them. THE THREE PROVERS IN protocolAtFiles Z ARE PLACEHOLDERS that send fixed messages: nothing on
completeness or on what a view shows can be said with them (OnBytes/Flat/Silent.lean). No clause of
soundness reads a field of the honest side, so the statement is made FOR EVERY VALUE P of the object's
honest provers: at whichever provers completeness and zero knowledge are stated, over these three
protocols, soundness holds of that same object; and then at protocolAtFiles Z. The cheating prover is none of
these: it is what Doomed quantifies over, message by message.

THE RELATION. relationAtFiles Z matrix request says: the matrix holds an index of the integer model
(every entry a digit in range), and at such an index SOME trace meets the library's relaxed relation
with the cost ledger, at the protocol's prime and at the table of scales and policy that is read from Z
(the reference's table where the reader refuses: ppAtFiles) (Flat.RelLAt,
Johnson/Top/H/TargetAtPolicy.lean; Policy.LedgerRel.Rno, Policy/Rel/LedgerRel.lean: relaxed in that the
trace's cells are below 2^18 in absolute value, where the honest relation asks 129). It is the relation
of the compiler's theorem. What it admits is named by
Statements.relationMeans: for a request built from a prompt and output tokens, the matrix gives weights
at which the output tokens MEET THE FILES' POLICY on the prompt (Policy.MeetsPolicy). At exact match
that is: each output token is the model's (Policy.meetsPolicy_exact_iff); at a tolerant policy it
admits every output that the policy accepts, AND SOME POLICIES IN SCOPE FORBID LITTLE: some leave every
counted token free (the docstring of VerifierAndGoals.InScope), and where 257 ≤ theta and 257 ≤ C every
well-formed request meets the policy at the all-zero weights (the head of Ladder.lean, 6). At this
object the configuration's two relations are one, so relationAtFiles Z is also its honest relation
(RyesZ Z, E2E/TiedAtFiles.lean, by unfolding; not proved here).

WHAT IS EXTRACTED, AND WHAT NOT. The index: a matrix of the full size's shape; the decoder returns
matrices in range alone. The library's form of the online clause has a witness map; at this object the
type of witnesses has one element ((Cz Z).Cells is Unit), and the model's trace stands under an
existential quantifier inside the claim. So nothing extracts the trace, and relationAtFiles is written
without a witness.

Limits.
- All of Hiop/SoundAsIOP.lean's: one whole run; soundness alone.
- NO PROBABILITY IS STATED IN THIS FILE. The bound 2^-128 a round is a share of ALL that round's
  challenges, the bits of proof of work among them (in the rounds that draw positions, up to 32 bits);
  as a share of the challenges that pass the test of work it is 2^-128 times 2^(that round's work): at
  32 bits of work, 2^-96. IT IS NOT "128 BITS OF SOUNDNESS A ROUND" OF THE IOP.
  Over uniform challenges a bound on a prover's probability would be true and say nothing (every
  prover is accepted with probability at most 2^-(all bits of work)); over the challenges that pass:
  E2E/SoundAsIOPProbabilityAtFiles.lean. How many bits of work a round has, and how many rounds there
  are, stands in no statement of this file.
- The link's places: 1, since the depth of a request tree of the link is 0 at this input.
- WHERE protocolDataWellFormed SAYS NO all three decisions reject everything, and nothing is claimed here. THE THREE HYPOTHESES HAVE A MEMBER: in scope, read, protocolDataWellFormed says yes: at the
  library's written copy of the full-size public files, in the side library (premises_zFull,
  AtFullSide/Bind/LiveAtNamed.lean; the statements there with no hypothesis:
  AtFullSide/E2E/SoundAsIOPAtWritten.lean); not at files on a disk. The side library's proof that
  protocolDataWellFormed says yes has been replayed by no independent checker (AtFullSide/Top/LiveAtFull.lean).
- flashProveData is the IOP as written in Lean at the format's second hash function, which the test on the
  public files reads (E2E/ObjectAtFiles.lean).
- That any prover is accepted at this object is not shown here: that is completeness.
- "THROUGH SOUNDNESS AS AN IOP" HOLDS OF THE THREE PARTS, NOT OF THE ROUND OF A SAMPLE'S POINT. Of the
  five clauses of SoundInParts the proof of soundOfVerifyThroughIOP spends three: offline, link, online.
  The clauses samplePoint and nothingAtCollision are not spent: the compiler's theorem has a premise of
  its own on how a sample's point is made from hash answers (CompilerSoundnessConditionStatements.seedLaw), which rests on the same
  count of points with a collision, times the samplers' bias, and is no consequence of a clause here;
  it fills the library's clause on the count with the number of all points (CompilerSoundnessConditions.binds), and proves
  noneColl anew.
- The lists of errors stand under an existential quantifier; what is stated of them is the bound.
- The public files are fixed before anything is drawn.
- Beneath the three called theorems stand files on coding theory adapted from third-party Lean
  (lean/LIMITS.md, L15).
-/
import Hiop.SoundAsIOP
import E2E.DescriptionTie
import E2E.BridgeJoinAtFiles
import Johnson.Goal.Skeleton.SoundOfVerifyMore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop
open VerifiableInference VerifiableInference.OnPublicFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles InScope readFiles settingsOfRead systemOfRecord atSecondHashFunction theDescription)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed theC0 theM0 thePhiO)
open VerifierAndGoals.AtTheName (rZ bZ)

/-- **The relation at Z**: the object's own, whose type of witnesses has one element: the matrix is in
range, and the claim of the request holds on it. -/
def relationAtFiles (Z : PublicFiles) (matrix : FullSizeMatrix) (request : XF) : Prop :=
  (Cz Z).Rno matrix request ()

/-- The places of a batch of the offline part at Z. -/
def offlinePlaces (Z : PublicFiles) : ℕ := 2 ^ (LPFD.Full.sTG (dataAtFiles flashProveData Z).G).logLeaves

/-- **The protocol at Z is sound as an IOP, round by round, the index being extracted by
extractIndex, every round's error at most 2^-128 of all its challenges.** P: any value of the object's
honest provers; no clause reads them. -/
def SoundAsIOPAtFiles (Z : PublicFiles) (P : (filesAt Z).Provers) : Prop :=
  ((filesAt Z).withProvers P).IndexKnowledgeSoundIOP (relationAtFiles Z) (filesAt Z).annT (offlinePlaces Z)
    (filesAt Z).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128)

example (Z : PublicFiles) : protocolAtFiles Z = (filesAt Z).withProvers (filesAt Z).fixedMessageProvers := rfl

namespace Statements

/-- States: **it holds**, at Z in scope, read, where protocolDataWellFormed says yes, for every P. -/
def soundAsIOPAtFiles : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ P : (filesAt Z).Provers, SoundAsIOPAtFiles Z P

/-- States: **it holds at the protocol's value protocolAtFiles Z.** -/
def soundAsIOPAtTheProtocol : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true →
    (protocolAtFiles Z).IndexKnowledgeSoundIOP (relationAtFiles Z) (filesAt Z).annT (offlinePlaces Z) (filesAt Z).annL 1
      ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- States: **the one statement on the whole run**, there: one list of errors, each at most 2^-128 of
its round's challenges, the two rounds in which a point is drawn among them; and the prover has lost
at the start towards the conclusion. -/
def wholeRunAtFiles : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill),
    ∃ errors : ((filesAt Z).withProvers P).RoundErrors,
      Err.Below (errors.wholeRun fill) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
        ((filesAt Z).withProvers P).WholeRunSound (relationAtFiles Z) errors fill

/-- States: **what the relation gives**: for a request that the verifier's builder makes of a prompt
and output tokens, the matrix gives weights at which the output tokens meet the files' policy on the
prompt. -/
def relationMeans : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ read : readFiles Z = .ok pp,
    ∀ (matrix : FullSizeMatrix) (prompt output more : List Token) (request : XF),
    (rZ Z).buildInstance (prompt, output) more = some request → relationAtFiles Z matrix request →
    ∃ weights, thePhiO Z (settingsOfRead pp) (VerifierAndGoals.valid_of_read read) matrix = some weights ∧
      Policy.MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output

/-- States: **soundness as an IOP gives the compiler's theorem its hypotheses on soundness**, at the
compiler's input rZ Z. (Its statement alone shows nothing: see the head.) -/
def compilerPremises : Prop :=
  ∀ Z : PublicFiles, SoundAsIOPAtFiles Z (filesAt Z).fixedMessageProvers →
    CompilerSoundnessConditionStatements.noneColl (r := rZ Z) ∧ CompilerSoundnessConditionStatements.keySound (bZ Z) ∧ CompilerSoundnessConditionStatements.entrySound (bZ Z) ∧
      CompilerSoundnessConditionStatements.proofSound (bZ Z)

/-- States: **the statement of sound_of_verify_at, from soundness as an IOP.** (Its statement alone
shows nothing: see the head.) -/
def soundOfVerifyThroughIOP : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    pp.pol = Inst.Model.AcceptancePolicy.exact →
    (protocolDataWellFormed (asDescriptionFiles Z) = true → SoundAsIOPAtFiles Z (filesAt Z).fixedMessageProvers) →
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1

end Statements

end AtPublicFiles.AtFiles
