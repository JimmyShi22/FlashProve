-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Pub/FieldsOfWritten.lean: THE HEAD's EXAMPLE: THE PROOF FILE's PUBLIC PART:
THE FIELDS OF THE VALUE THAT pubPlain_of_written NAMES, FOR THE ROWS THAT READ THEM.
  eq_of_written      under pubPlain_of_written's seven premises, whatever pubPlain returns IS that
                     value
  fields_of_written  so its fields, one by one: made · p.X · p.chains · first · cuts · depth · D ·
                     told · P · s₀
  rows_of_written    in the rows' own letters: FirstWritten Z.first · the three planned lists · the
                     sized shapes, and the proof file's among them · the table of stretches · the
                     number of answers to a sample (from hpl, by hn_of_plans: FirstWritten does
                     not reach it) · the first state's codes, request's shape and groups. A row
                     that asks an equation the other way round takes «.symm».
ITS BEST USE: Z.p.X = X₀ carries every row that reads the public record X over to hX's letter, and
so, at the stored full-size files, to the value of Johnson/AtFull/Public/Join.lean.
NOT REACHED: rows that ask the declared rounds' entries (Z.D.1.map (·.entry) = the written): here D
is a letter: they want the value at which u₃ is shown · ties between constants of one text under
several names.
THE PREMISES ARE pubPlain_of_written's SEVEN (PubOfWritten.lean), EACH RAW, NONE PROVED HERE AT ANY
FILES, AND hZ : pubPlain o pol lay KL = .ok Z, which follows from the seven and is asked only so
that a row's own letter Z is met.
LIMITS. Projections of one record, by rfl, and one law of the library (Key.madeAt_public). It pays
no premise. No example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth. No
soundness is claimed.

-/
import Johnson.AtFull.Pub.PubOfWritten
import Johnson.Desc.Key.NoCfgLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Pub
open OnBytes OnBytes.Model
open ProofFile (pubPlain plainStarts toldOf SecondHashFunctionArgument Root)
open ProofFile.Law (blankM)
open VerifiableInference.PlanWritten (publicOfO proofSizedFull FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open VerifiableInference.Desc.First (S)
open Johnson.G (layoutFull)
open Johnson.G.OfPlan (Made declPOf)
open Johnson.AtFull.Cut (cutWritten)
open _root_.AtFull.Top (pubOfParts)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {X₀ : Verify.Public} {m : Made}
  {D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound}
  {told : List Root × List Root × List Root} {Z : ProofFile.Pub}

/-- Whatever pubPlain returns is the value that pubPlain_of_written names. -/
theorem eq_of_written
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok D) (u₄ : toldOf (blankM m) = .ok told)
    (hZ : pubPlain o pol lay KL = .ok Z) :
    Z = pubOfParts plainStarts pol KL (blankM m) D told 32 cutWritten
      (S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull) :=
  Except.ok.inj (hZ.symm.trans (pubPlain_of_written hX hm hF hz hpl u₃ u₄))

/-- **The fields of that value.** -/
theorem fields_of_written
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok D) (u₄ : toldOf (blankM m) = .ok told)
    (hZ : pubPlain o pol lay KL = .ok Z) :
    Z.made = blankM m ∧ Z.p.X = X₀ ∧ Z.p.chains = m.p.chains ∧
      Z.first = m.p.chains.proof.first ∧ Z.cuts = cutWritten ∧ Z.depth = 32 ∧ Z.D = D ∧
      Z.told = told ∧ Z.P = plainStarts.par m.p.chains.proof.first ∧
      Z.s₀ = S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull := by
  have hx : m.p.X = X₀ := VerifiableInference.Desc.Key.madeAt_public hm
  rw [eq_of_written hX hm hF hz hpl u₃ u₄ hZ]
  exact ⟨rfl, hx, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The same in the rows' own letters.** -/
theorem rows_of_written
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok D) (u₄ : toldOf (blankM m) = .ok told)
    (hZ : pubPlain o pol lay KL = .ok Z) :
    FirstWritten Z.first ∧
      Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] ∧
      Z.p.chains.made.sized = writtenSized ∧ Z.p.chains.made.sized.proof = proofSizedFull ∧
      Z.cuts = cutWritten ∧ Z.P.samples = proofSizedFull.request.answers ∧
      Z.s₀.st.codes = proofSizedFull.codes ∧ Z.s₀.check.frame.shape = proofSizedFull.request ∧
      Z.s₀.check.frame.groups = reqGroups proofSizedFull.request := by
  obtain ⟨-, -, hc, hf, hcu, -, -, -, hP, hs⟩ := fields_of_written hX hm hF hz hpl u₃ u₄ hZ
  refine ⟨hf ▸ hF, hc ▸ hpl, hc ▸ hz, ?_, hcu, ?_, ?_, ?_, ?_⟩
  · rw [hc, hz]
    rfl
  · rw [hP]
    exact hn_of_plans hX hm hpl
  · rw [hs]
    rfl
  · rw [hs]
    rfl
  · rw [hs]
    rfl

end Johnson.AtFull.Pub

#print axioms Johnson.AtFull.Pub.eq_of_written
#print axioms Johnson.AtFull.Pub.fields_of_written
#print axioms Johnson.AtFull.Pub.rows_of_written
