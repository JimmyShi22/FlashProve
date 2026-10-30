-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Pub/PubOfWritten.lean: THE HEAD's EXAMPLE: THE PROOF FILE's PUBLIC PART:
A JOIN, BY FIELD: where publicOfO and the key file's planner return, and five things hold of the
planner's value m, pubPlain returns, and what.
  given3_of_plans  the three proof chains' plans as read back are the three written plans, from the
                   planner's three lists: at m, ahead of any return of pubPlain · given_of_plans
  u6_of_plans      the master ledger's u₆ at cuts := the written table of stretches (cutWritten)
  hn_of_plans      the master ledger's hn (the number of answers to a sample)
  pubPlain_of_written   MAIN. General in the files and in the second hash function as a statement;
                 but the written values are the full size's: at other files its premises fail: idle.
THE PREMISES, EACH RAW, NONE PROVED HERE AT ANY FILES:
  hX   publicOfO returns X₀ (at the stored full-size files: Johnson/AtFull/Public/Join.lean, from
       the layout file's size)
  hm   Key.madeAt X₀ lay fixedDigest returns m
  hF   the six equations FirstWritten on m's first proof chain as read back
  hz   m's sized shapes are the written ones
  hpl  m's three planned lists of the proof file (m.p.chains.made.proof) are the three written plans
  u₃   declPOf (blankM m) returns D     u₄   toldOf (blankM m) returns told
A JOIN: it calls the ledger pubPlain_of_parts (Johnson/AtFull/Top/PubPlainLedger.lean) and pays
u₂ · u₅ · u₇ by Johnson/AtFull/Pub/SmallOwed.lean, u₆ by cut_written
(Johnson/AtFull/Cut/CutAtWritten.lean) with the equation E0 of
Johnson/Desc/First/Att/Row/K5FrontE0.lean; u₃ and u₄ it hands on as they stand.
WHO SPENDS WHAT. A file of the master ledger (one that is not in this
library) does not spend a return of pubPlain: it asks u₃, u₄, u₆ and hn one by one.
MAIN is for whoever wants the return itself (hZ).
KIN, NOT TWINS: cuts_made | plans_made | first_plan_made
(Johnson/Desc/First/Att/Row/) go FROM a return of pubPlain under the same hpl; the lemmas here stand
AHEAD of the return.
BEHIND u₃ AND u₄ STANDS ONE RAW PREMISE MORE. What shows them (declPOf_written | toldOf_written,
Johnson/AtFull/ProofBack/Back.lean) asks eight equations on m: the sized proof shapes (from hz) ·
the three plans' rounds (given3_of_plans, with E0 for the first; the like for the second and third
written plans: Johnson/AtFull/Plans/PlansSix.lean) · «no entry that is no round», thrice (closed
facts at the written plans: the same file) · AND hs : m.proof = proofSendsFull, THE LISTS OF WHAT IS
SENT, WHICH NONE OF hF · hz · hpl SAYS. So with u₃ and u₄ shown (PubOfMade.lean beside this file)
the premises are hX · hm · hF · hz · hpl · hs. CAN THE PREMISES HOLD TOGETHER? hF is a half of the
library's test madePinned (firstIs), and hs, which stands behind u₃ | u₄, another (proofSendsIs);
that test said yes at the full-size files in evaluations. OF hz IT ASKS THE PROOF FILE's SHAPES
ALONE, OF hpl THE FIRST PLAN ALONE. That the whole of hz and hpl holds there is said by the
library's made_in_scope, which takes pubPlain's return as a premise: so it cannot show them for this
statement. So: evaluated in part; whole, by nothing shown here; not proved in
this file; whether theorems elsewhere show it was not examined for this file; that the head has a
member at storedPublicFiles alone is AtFullSide.Top.headMember_zFull, whose own Limits say what it is worth.
LIMITS. It pays no premise at any files. No example of the head is shown in this file; one, at storedPublicFiles
alone, is AtFullSide.Top.headMember_zFull, whose own Limits say what it is worth. No soundness
is claimed.
-/
import Johnson.AtFull.Top.PubPlainLedger
import Johnson.AtFull.Pub.SmallOwed
import Johnson.AtFull.Cut.CutAtWritten
import Johnson.Desc.First.Att.Row.K5FrontE0
import Johnson.G.PlansPriced
import OnBytes.Model.ReadBackMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Pub
open OnBytes OnBytes.Model
open ProofFile (pubPlain plainStarts toldOf SecondHashFunctionArgument Root)
open ProofFile.Law (blankM)
open VerifiableInference.PlanWritten (publicOfO proofSizedFull FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree proof_fit0 proof_fit1 proof_fit2)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open VerifiableInference.Desc.First (S cutOf)
open Johnson.G (layoutFull)
open Johnson.G.OfPlan (Made declPOf)
open Johnson.AtFull.Cut (cutWritten cut_written)
open _root_.AtFull.Top (pubOfParts pubPlain_of_parts)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {X₀ : Verify.Public} {m : Made}

/-- The three proof chains' plans as read back are the three written plans: at the planner's value,
ahead of any return of pubPlain. -/
theorem given3_of_plans (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    m.p.chains.proof.first.given.plan = proofThree.A.plan.plan ∧
      m.p.chains.proof.shared.given.plan = proofThree.B.plan.plan ∧
      m.p.chains.proof.second.given.plan = proofThree.C.plan.plan := by
  obtain ⟨l, x, hc, -, -, hk⟩ :=
    Johnson.G.OfPlan.chainsOf_made (FlashProve.plannedAtO_of_madeAt hX hm).2
  refine OnBytes.Params.proof_read_made hc hk (fun P hP => ?_) hpl
  rw [hpl] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact proof_fit0
  · exact proof_fit1
  · exact proof_fit2

/-- The first of the three. -/
theorem given_of_plans (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    m.p.chains.proof.first.given.plan = proofThree.A.plan.plan := (given3_of_plans hX hm hpl).1

/-- The master ledger's u₆, at the written table of stretches. -/
theorem u6_of_plans (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    cutOf m.p.chains.proof.first.given.rounds = some cutWritten := by
  show cutOf m.p.chains.proof.first.given.plan.rounds = some cutWritten
  rw [given_of_plans hX hm hpl, H2K5.Row.E0]
  exact cut_written

/-- The master ledger's hn. -/
theorem hn_of_plans (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    m.p.chains.proof.first.given.plan.samples = proofSizedFull.request.answers := by
  rw [given_of_plans hX hm hpl]
  exact samples_written

/-- **IF publicOfO and the key file's planner return, and five things hold of the planner's value,
THEN pubPlain returns**: the planner's value blanked, the written table of stretches, the depth 32,
the first state at the three written values; D and told as their makers return them. -/
theorem pubPlain_of_written
    {D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound}
    {told : List Root × List Root × List Root}
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok D) (u₄ : toldOf (blankM m) = .ok told) :
    pubPlain o pol lay KL = .ok (pubOfParts plainStarts pol KL (blankM m) D told 32 cutWritten
      (S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull)) :=
  pubPlain_of_parts hX hm (u2_of_first hF) u₃ u₄ (u5_of_sized hz) (u6_of_plans hX hm hpl)
    (u7_of_plan hF (given_of_plans hX hm hpl))

end Johnson.AtFull.Pub

#print axioms Johnson.AtFull.Pub.given3_of_plans
#print axioms Johnson.AtFull.Pub.given_of_plans
#print axioms Johnson.AtFull.Pub.u6_of_plans
#print axioms Johnson.AtFull.Pub.hn_of_plans
#print axioms Johnson.AtFull.Pub.pubPlain_of_written
