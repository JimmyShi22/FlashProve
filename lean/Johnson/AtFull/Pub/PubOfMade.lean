-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Pub/PubOfMade.lean: THE HEAD's EXAMPLE: THE PROOF FILE's PUBLIC PART: THE JOIN:
NO LETTER IS LEFT IN THE VALUE BUT THE PLANNER's m.
  DW · toldW            the written declared rounds; the trees with their tenants, as terms
  decl_of_made · told_of_made   the master ledger's u₃ and u₄ at these, from hX · hm · hz · hpl · hs
  pubPlain_of_made      MAIN: IF publicOfO and the key file's planner return (hX · hm) AND four
                        equations hold of the planner's value m (hF · hz · hpl · hs), THEN pubPlain
                        returns: m blanked, the written declared rounds DW, the written trees toldW,
                        the depth 32, the written table of stretches, the first state at the three
                        written values
THE SIX PREMISES, EACH RAW, NONE PROVED HERE AT ANY FILES:
  hX   publicOfO returns X₀ (at the stored full-size files: Johnson/AtFull/Public/Join.lean, from
       the layout file's size)
  hm   Key.madeAt X₀ lay fixedDigest returns m
  hF   the six equations FirstWritten on m's first proof chain as read back
  hz   m's sized shapes are the written ones
  hpl  m's three planned lists of the proof file (m.p.chains.made.proof) are the three written plans
  hs   m's three lists of what the proof file's chains send (m.proof) are the written ones
A JOIN: pubPlain_of_written (PubOfWritten.lean) at u₃ | u₄ := declPOf_at_fields |
toldOf_at_fields (Johnson/AtFull/ProofBack/Back.lean), whose eleven premises are paid so: the sized
proof shapes: hz · the sendings: hs · the three plans as read back: given3_of_plans · the six closed
facts at the written plans: E0 (Johnson/Desc/First/Att/Row/K5FrontE0.lean) and E1 · E2 · O0 · O1 ·
O2 (Johnson/AtFull/Plans/PlansSix.lean): E1 | E2 | O1 | O2 rest on two decisions of the kernel, each
with a negative test beside it; O0 on none. O_k reads «entries.length - rounds.length = 0», a
truncated difference: «no entry that is no round» is how PlansSix.lean proves it (entries = rounds).
CAN THE PREMISES HOLD TOGETHER? hF and hs are halves of the library's test madePinned (firstIs ·
proofSendsIs), which said yes at the full-size files in evaluations. OF hz THAT TEST ASKS THE PROOF
FILE's SHAPES ALONE, OF hpl THE FIRST PLAN ALONE. That the whole of hz and hpl holds there is said
by the library's made_in_scope, which takes pubPlain's return as a premise: so it cannot show them
for this statement. So: evaluated in part; whole, by nothing that this file's writer knows; not
proved in this file; whether theorems elsewhere show it was not examined for this file; that the
head has a member at storedPublicFiles alone is AtFullSide.Top.headMember_zFull, whose own Limits say what it is
worth. LIMITS. It pays no premise at any files. General in the files as a statement; the written
values are the full size's: elsewhere idle. No example of the head is shown in this file; one, at
storedPublicFiles alone, is AtFullSide.Top.headMember_zFull, whose own Limits say what it is worth.
No soundness is claimed.
-/
import Johnson.AtFull.Pub.PubOfWritten
import Johnson.AtFull.Plans.PlansSix
import Johnson.AtFull.ProofBack.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Pub
open OnBytes OnBytes.Model
open ProofFile (pubPlain plainStarts toldOf SecondHashFunctionArgument Root)
open ProofFile.Law (blankM)
open VerifiableInference.PlanWritten (publicOfO proofSizedFull FirstWritten declRecsFull)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open VerifiableInference.Desc.First (S)
open Johnson.G (layoutFull proofSendsFull)
open Johnson.G.OfPlan (Made declPOf)
open Johnson.G.Runs (unrunG)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Plans (E1 E2 O0 O1 O2)
open _root_.AtFull.Top (pubOfParts)
open Johnson.AtFull.ProofBack (declPOf_at_fields toldOf_at_fields tl0 tl1 tl2 extra0 extra1 extra2
  maskW)
open Johnson.Unfolds (mineW)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {X₀ : Verify.Public} {m : Made}

/-- The written declared rounds of the proof file's three chains. -/
def DW : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound :=
  (unrunG declRecsFull Johnson.G.dryProofRunsFull0, unrunG declRecsFull Johnson.G.dryProofRunsFull1,
    unrunG declRecsFull Johnson.G.dryProofRunsFull2)

/-- The three chains' trees with their tenants, as terms over the written values. -/
def toldW : List Root × List Root × List Root :=
  (mineW tl0 extra0 none, mineW tl1 extra1 maskW, mineW tl2 extra2 none)

theorem DW_fst : DW.1 = unrunG declRecsFull Johnson.G.dryProofRunsFull0 := rfl
theorem DW_snd : DW.2.1 = unrunG declRecsFull Johnson.G.dryProofRunsFull1 := rfl
theorem DW_trd : DW.2.2 = unrunG declRecsFull Johnson.G.dryProofRunsFull2 := rfl

/-- The master ledger's u₃, at the written declared rounds. -/
theorem decl_of_made (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (hs : m.proof = proofSendsFull) : declPOf (blankM m) = .ok DW := by
  obtain ⟨p0, p1, p2⟩ := given3_of_plans hX hm hpl
  have hz' : m.p.chains.made.sized.proof = proofSizedFull := by
    rw [hz]
    rfl
  exact declPOf_at_fields hz' hs p0 p1 p2 H2K5.Row.E0 O0 E1 O1 E2 O2

/-- The master ledger's u₄, at the written trees. -/
theorem told_of_made (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (hs : m.proof = proofSendsFull) : toldOf (blankM m) = .ok toldW := by
  obtain ⟨p0, p1, p2⟩ := given3_of_plans hX hm hpl
  have hz' : m.p.chains.made.sized.proof = proofSizedFull := by
    rw [hz]
    rfl
  exact toldOf_at_fields hz' hs p0 p1 p2 H2K5.Row.E0 O0 E1 O1 E2 O2

/-- **IF publicOfO and the key file's planner return, and four equations hold of the planner's
value, THEN pubPlain returns**, and no letter is left in the value but that value. -/
theorem pubPlain_of_made (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (hs : m.proof = proofSendsFull) :
    pubPlain o pol lay KL = .ok (pubOfParts plainStarts pol KL (blankM m) DW toldW 32 cutWritten
      (S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull)) :=
  pubPlain_of_written hX hm hF hz hpl (decl_of_made hX hm hz hpl hs) (told_of_made hX hm hz hpl hs)

end Johnson.AtFull.Pub

#print axioms Johnson.AtFull.Pub.DW_fst
#print axioms Johnson.AtFull.Pub.DW_snd
#print axioms Johnson.AtFull.Pub.DW_trd
#print axioms Johnson.AtFull.Pub.decl_of_made
#print axioms Johnson.AtFull.Pub.told_of_made
#print axioms Johnson.AtFull.Pub.pubPlain_of_made
