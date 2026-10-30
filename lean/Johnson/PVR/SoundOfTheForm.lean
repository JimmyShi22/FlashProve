-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/SoundOfTheForm.lean: A PAIR: `verify` IS SOUND; THE EXECUTABLE FORM COMPUTES IT. The
soundness theorem (`VerifierAndGoals.AtTheName.sound_of_verify_at`,
Johnson/Goal/Skeleton/SoundOfVerifyAt.lean) speaks of `VerifierAndGoals.verify`, an algorithm with access to a
hash function. The term that is executed is another one: the step-by-step form of
Johnson/PVR/RideThe.lean. This file puts the two side by side in one theorem. It states no goal and
turns no other file: each proof is one call of a theorem that stands elsewhere.
  `theForm Z O commitment prompt output B`: the executable form at one question, under one name:
    `verdictThe Z O B (rideOf letsThe Z O B commitment prompt output)`. Z: the three public files.
    O: a function from bytes to bytes in the hash function's place. B: the proof as bytes
    (`FormBytes`, Johnson/Goal/Tie/DescriptionOnBytes.lean). `some true`: accept; `some false`: reject;
    `none`: no verdict.
  `theForm_accepts_only`: what the form accepts, `VerifierAndGoals.verify` accepts, at the hash function that
    O makes. At every O; no premise.
  `theForm_total`: where O's answers have 32 bytes, the form gives a verdict.
  `theForm_eq_verify`: there its verdict is the decision of `VerifierAndGoals.verify`: the form computes
    `VerifierAndGoals.verify`.
  `theForm_at_hash`: the same at every hash function h of the soundness theorem's model, at the
    function on bytes `Run.oOf fun _ => h`.
  **`sound_of_the_form_at`**: at public files that are in scope and read, with exact match (the
    three hypotheses of `sound_of_verify_at`, and no other): (1) `VerifiableInference.Sound` of the
    system of record, at the same bound `fun t => VerifierAndGoals.soundnessErrorInQueries t 1`; and (2) at every function on
    bytes with 32-byte answers, on every commitment, prompt, output and proof, the form's verdict is
    `some` of the decision of THAT SYSTEM's OWN `verify`. So the form accepts exactly what the
    verifier of (1) accepts, and the bound of (1) is a bound on the form's accepting.
By `sound_of_verify_at`; `verdictThe_is_theDescription` (RideThe.lean); `verdictThe_some`,
`verdictThe_eq`, `verify_every_hash` (Johnson/PVR/RideEveryHash.lean).
Limits. WHAT IT DOES NOT GIVE. A PAIR, NOT A CHAIN CARRIED OUT: the probability in (1) stays worded
of `verify`, and the form stands in no probability here; that the bound of (1) bounds the form's
accepting follows from (2) by rewriting (`theForm_at_hash`, which is no conjunct of the top theorem;
`run_bind`, `DeterministicAlgorithm.run_toRandomized`, VerifiableInference/Bridge.lean). The
statement with the form's own decision inside the probability is
Johnson/PVR/SoundOfTheFormEvents.lean's. Nothing on how the form is run: that an evaluator or
compiled code computes what a term says is the matter of Lean's compiler and runtime.
`theForm_total` speaks of a term's VALUE: not of whether, or when, an evaluation of it ends. WHICH
TERM A RUN HAS EXECUTED (these parameters or `letsTell`, the decisions that report; which function
on bytes) is for that run's own print to say: the runs that RideThe.lean's and
SoundOfVerifyAt.lean's heads tell rode working copies and a driver outside this library, and their
tie to `theForm` is by name and statement, not by bytes. No program: this file makes none. No
theorem here speaks of one, so nothing is proved here of whatever runs the form. Not the reader of
files in front of it, which makes Z, the commitment, the prompt, the output and B out of files. Not
completeness: nothing says that an honest proof is accepted. Not a real hash function: (1) draws the
hash function at random; (2) holds at every function with 32-byte answers, a real one among them,
but (1) says nothing of a real one. (2) is an equation between two values: it says nothing of which
strings are asked, or how many. `Run.oOf` has no code. At the parameters `letsThe` and at the
description's own parser alone; at `atSecondHashFunction theDescription`, the description at the format's second
hash. Every limit of `sound_of_verify_at` stands: one set of public files fixed in advance; exact
match; a prover with a bounded number of queries.
Terms: lean/GLOSSARY.md.
-/
import Johnson.PVR.RideEveryHash
import Johnson.Goal.Skeleton.SoundOfVerifyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.Ride
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **The executable form**, at one question: the public files Z, a function O from bytes to bytes
in the hash function's place, a commitment, a prompt, output tokens, and a proof as bytes.
`some true`: accept. `some false`: reject. `none`: no verdict. -/
def theForm (Z : PublicFiles) (O : ByteArray → ByteArray) (commitment : Commitment)
    (prompt output : List Token) (B : FormBytes) : Option Bool :=
  verdictThe Z O B (rideOf letsThe Z O B commitment prompt output)

/-- What the form accepts, `VerifierAndGoals.verify` accepts: at every O, with no premise. -/
theorem theForm_accepts_only (Z : PublicFiles) (O : ByteArray → ByteArray) (commitment : Commitment)
    (prompt output : List Token) (B : FormBytes)
    (h : theForm Z O commitment prompt output B = some true) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
      output B).evaluate (hashOf O) = true :=
  (verdictThe_is_theDescription Z O B commitment prompt output true h).symm

/-- Where O's answers have 32 bytes the form gives a verdict. -/
theorem theForm_total (Z : PublicFiles) (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (theForm Z O commitment prompt output B).isSome = true :=
  Option.isSome_iff_exists.2 (verdictThe_some Z O hO B commitment prompt output)

/-- **THE FORM COMPUTES `VerifierAndGoals.verify`**: where O's answers have 32 bytes, its verdict is there
and is the decision of `VerifierAndGoals.verify` at the hash function that O makes. -/
theorem theForm_eq_verify (Z : PublicFiles) (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    theForm Z O commitment prompt output B =
      some ((VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
        prompt output B).evaluate (hashOf O)) :=
  verdictThe_eq Z O hO B commitment prompt output

/-- The same at every hash function of the soundness theorem: each is made by a function on bytes
with 32-byte answers. -/
theorem theForm_at_hash (Z : PublicFiles) (h : Hash) (commitment : Commitment)
    (prompt output : List Token) (B : FormBytes) :
    theForm Z (_root_.Run.oOf fun _ => h) commitment prompt output B =
      some ((VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
        prompt output B).evaluate h) :=
  verify_every_hash Z h B commitment prompt output

/-- **A PAIR: `verify` IS SOUND, AND THE EXECUTABLE FORM COMPUTES `verify`: AT ONE SET OF PUBLIC
FILES, IN SCOPE, READ, WITH EXACT MATCH**: the system of `sound_of_verify_at` is sound at its bound,
and the form computes that very system's verifier: at every function on bytes with 32-byte answers,
on every commitment, prompt, output and proof, it gives a verdict: that verifier's decision. -/
theorem sound_of_the_form_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
        (fun t => VerifierAndGoals.soundnessErrorInQueries t 1) ∧
      ∀ (O : ByteArray → ByteArray), (∀ x, (O x).size = 32) →
        ∀ (commitment : Commitment) (prompt output : List Token) (B : FormBytes),
          theForm Z O commitment prompt output B =
            some (((systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)).verify commitment
              prompt output B).evaluate (hashOf O)) :=
  ⟨sound_of_verify_at Z pp scope read exact,
    fun O hO commitment prompt output B => theForm_eq_verify Z O hO commitment prompt output B⟩

end PV.Ride

#print axioms PV.Ride.theForm_accepts_only
#print axioms PV.Ride.theForm_total
#print axioms PV.Ride.theForm_eq_verify
#print axioms PV.Ride.theForm_at_hash
#print axioms PV.Ride.sound_of_the_form_at
