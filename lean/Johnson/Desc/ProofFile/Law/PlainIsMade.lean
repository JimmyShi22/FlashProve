-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/PlainIsMade.lean: the plain road's copies of `sendsOf` and `madeOf`
(`ProofFile.PlainG.sendsOf`, `ProofFile.PlainG.madeOf`, Johnson/Desc/ProofFile/PlanPlain.lean) against the
library's routines.

What it is. Laws beside the proof file's description; no file of the description imports this one.
The statements and the proofs have different writers.

  `blankM m`: m with `blankB` (Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean) on the segments'
    records in the planner's value.
  `sendsOf_eq`: the copy of `sendsOf` is the copy of `planned`, then `sendsFrom`
    (Johnson/Desc/Ok/NumberPrices/AtDigest.lean) of what it made. By definition.
  `madeOf_eq`: the copy of `madeOf` returns what `madeOfAtO`
    (Johnson/Desc/Ok/PlanWritten/MadeAt.lean) returns at the same files, the same o and the constant
    `fixedConfigurationDigest`, after `blankM`; where one refuses the other refuses with the same words. It rests on
    `planned_eq` (PlainIsPlanned.lean).
  `pub_madeOfAtO`: where the public part Z of the proof file's description is computed, `madeOfAtO`
    returns a value m there, and `blankM m` is Z.made.

Limits. The digest in these values is the constant `fixedConfigurationDigest`, not the digest of the files. `blankM`
changes the field `run` of the segments' records: the equations say nothing of what stands there.
Nothing says that a value is returned at any files. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.Desc.Ok.PlanWritten.MadeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.Desc (fixedConfigurationDigest)
open VerifiableInference.Number (sendsFrom packMade)
open VerifiableInference.PlanWritten (madeOfAtO plannedAtO)

/-- The planner's whole value, with `blankB` on the segments' records in it. -/
def blankM (m : Johnson.G.OfPlan.Made) : Johnson.G.OfPlan.Made :=
  { m with p := { m.p with built := blankB m.p.built } }

/-- The copy of `sendsOf` is the copy of `planned`, then the library's `sendsFrom` of what it
made. -/
theorem sendsOf_eq (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    ProofFile.PlainG.sendsOf o pol lay KL =
      ProofFile.Plain.planned o pol KL (some lay) >>= fun p => sendsFrom p.chains.made := rfl

/-- The copy of `madeOf` returns what `madeOfAtO` returns at `fixedConfigurationDigest`, with `blankM`; refusals
too. -/
theorem madeOf_eq (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    ProofFile.PlainG.madeOf o pol lay KL = (madeOfAtO o pol lay KL fixedConfigurationDigest).map blankM := by
  unfold ProofFile.PlainG.madeOf madeOfAtO
  rw [sendsOf_eq, planned_eq]
  cases plannedAtO o pol KL (some lay) fixedConfigurationDigest with
  | error e => rfl
  | ok p =>
    show (sendsFrom p.chains.made >>= fun s =>
        match s with
        | [k0, k1, k2, _, p0, p1, p2] =>
          (pure ⟨{ p with built := blankB p.built }, (k0, k1, k2), (p0, p1, p2)⟩ :
            Except String Johnson.G.OfPlan.Made)
        | _ => throw "the list of sendings has not seven chains (key 0 1 2, entry, proof 0 1 2)") =
      (sendsFrom p.chains.made >>= packMade p).map blankM
    cases sendsFrom p.chains.made with
    | error e => rfl
    | ok s =>
      rcases s with
        _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, _ | ⟨s6, _ | ⟨s7, t⟩⟩⟩⟩⟩⟩⟩⟩ <;> rfl

/-- For a user. Where the public part Z of the proof file's description is computed, `madeOfAtO`
returns a value at the same files, the same o and `fixedConfigurationDigest`, and Z.made is that value after
`blankM`. -/
theorem pub_madeOfAtO {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    ∃ m, madeOfAtO o pol lay KL fixedConfigurationDigest = .ok m ∧ blankM m = Z.made := by
  have hm : ProofFile.PlainG.madeOf o pol lay KL = .ok Z.made :=
    pubBy_made (show pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL = .ok Z from h)
  rw [madeOf_eq] at hm
  cases hq : madeOfAtO o pol lay KL fixedConfigurationDigest with
  | error e =>
    rw [hq] at hm
    cases hm
  | ok m =>
    rw [hq] at hm
    exact ⟨m, rfl, Except.ok.inj hm⟩

end ProofFile.Law

#print axioms ProofFile.Law.sendsOf_eq
#print axioms ProofFile.Law.madeOf_eq
#print axioms ProofFile.Law.pub_madeOfAtO
