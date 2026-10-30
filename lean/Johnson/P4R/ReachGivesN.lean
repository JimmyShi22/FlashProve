-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/ReachGivesN.lean.
WHAT IT DOES NOT SHOW. No soundness. ONE PREMISE BESIDE "REACHED": hplan: the sub-protocol that
stands at 340 passes its test on the plan: a test with code on public data; "reached" brings no test
on the plan (P4R/FreeAt341N.lean says why it is asked). No example shows here that the premises can
be met together at the release's values.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on.
LETTERS. "There is" in the conclusion: n4: the name under which the output head's own sub-protocol
stands in the chain; and ReachGives' own.
OBJECT. Desc/Reads/RunIsAtBorder.lean: ReachGives: what a state behind the fourth place of the
head's link must bring for the law on the output head's twelve reads.
USER. That file's runIs_at_reach, which is general in the four letters that are filled here (same,
but, a4, n4).
WHAT IT IS. IN THE GOALS' SCOPE, A STATE REACHED AT THE BORDER 342 HAS ReachGives.
  reach_gives       by P4.reach_gives0; the term IM.seatedAs and the reads' law's
                    "dressed" (Desc/Reads/RowAtLot.lean) unfold to one term.

-/
import Johnson.P4R.ReachGives0N
import Johnson.Desc.Reads.RunIsAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S hearsReply)
open VerifiableInference.Reads.AtSeat (ReachGives)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- **A state reached at the border 342 has ReachGives.** -/
theorem reach_gives {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hplan : ∀ b, c.blocksInOrder[340]? = some b → b.planOk = true) {XP : Type} {start : XP → S} {z : XP}
    {s : S} (h : Reach 0 c.blocksInOrder start 342 (z, s)) :
    ∃ n4, ReachGives Z Bs.G₀ ProofFile.sameReply hearsReply IM.k6Place n4 s := by
  obtain ⟨b', _, n4, s0, rs, gs, -, -, hm, d, -, hW⟩ := reach_gives0 hS hR O hplan h
  exact ⟨n4, b', s0, rs, gs, hm, d, hW⟩

end P4

#print axioms P4.reach_gives
