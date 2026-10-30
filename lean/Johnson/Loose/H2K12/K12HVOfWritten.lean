-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Loose/H2K12/K12HVOfWritten.lean: THE HEAD's EXAMPLE: THE
PREMISE hV OF THE PROXIMITY TEST's (the kind K12's) ROWS, H2U.p12OfMade Z.made = piLFull, FROM THE
RAW PREMISES OF THE PROOF FILE's PUBLIC PART AS WRITTEN. A joining: two calls and two rewritings; no
evaluation in Lean's kernel stands in this file.
  v12_of   under the eight premises of Johnson.AtFull.Pub.rows_of_written | fields_of_written
           (Johnson/AtFull/Pub/FieldsOfWritten.lean), in their own letters and order (hX hm hF hz
           hpl u₃ u₄ hZ), and hs : m.proof = proofSendsFull: the first conjunct of
           H2K12.members_written_front (Johnson/Loose/H2K12/K12MemberFront.lean).
HOW THE FIVE PREMISES OF members_written_front ARE MET. hZ: ProofFile.pureRoad.pub is ProofFile.pubPlain by
definition (Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean). The setting: rows_of_written's third conjunct
(Z.p.chains.made.sized = writtenSized), and writtenSized.set is recordSet by definition. The sizes
and the three lists: its fourth and second conjuncts, to the letter. What is sent:
fields_of_written's first conjunct (Z.made = blankM m); blankM turns m.p.built alone
(Johnson/Desc/ProofFile/Law/PlainIsMade.lean), so (blankM m).proof is m.proof by definition; then
hs.
WHAT FOR: the hypothesis v12 of the join of the first chain's second rows (ProofFile.Sk.Full.second_rows,
Johnson/Desc/ProofFile/Law/Skel/Full/SecondRows.lean): with this it falls to hypotheses that the
join has already.
WHAT IT IS NOT: it pays none of the nine: each is raw, none is shown of any public files by Lean's
kernel. Whoever shows hZ at given files by the kernel meets treesSent's check over all rounds of the
first chain inside it (K12MemberFront.lean's head). The full size alone. No example of the head is
shown in this file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth. No soundness statement. Nothing on
hiding.

-/
import Johnson.Loose.H2K12.K12MemberFront
import Johnson.AtFull.Pub.FieldsOfWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes OnBytes.Model
open ProofFile (pubPlain toldOf SecondHashFunctionArgument Root)
open ProofFile.Law (blankM)
open VerifiableInference.PlanWritten (publicOfO FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G (proofSendsFull)
open Johnson.G.OfPlan (Made declPOf)

/-- **hV, from the raw premises of the public part as written.** -/
theorem v12_of {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {X₀ : Verify.Public} {m : Made}
    {D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound}
    {told : List Root × List Root × List Root} {Z : ProofFile.Pub}
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok D) (u₄ : toldOf (blankM m) = .ok told)
    (hZ : pubPlain o pol lay KL = .ok Z) (hs : m.proof = proofSendsFull) :
    H2U.p12OfMade Z.made = H2K.Member.piLFull := by
  obtain ⟨hmade, -⟩ := Johnson.AtFull.Pub.fields_of_written hX hm hF hz hpl u₃ u₄ hZ
  obtain ⟨-, hp, hsz, hzp, -⟩ := Johnson.AtFull.Pub.rows_of_written hX hm hF hz hpl u₃ u₄ hZ
  have hZ' : ProofFile.pureRoad.pub o pol lay KL = .ok Z := hZ
  have hset : Z.p.chains.made.sized.set = OnBytes.Params.recordSet := by
    rw [hsz]
    rfl
  have hc : Z.made.proof = proofSendsFull := by
    rw [hmade]
    exact hs
  exact (members_written_front hZ' hset hzp hp hc).1

end H2K12

#print axioms H2K12.v12_of
