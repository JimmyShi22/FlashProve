-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/ReachGives0N.lean.
WHAT IT DOES NOT SHOW. No soundness. ONE PREMISE BESIDE "REACHED": hplan: the sub-protocol that
stands at 340 passes its test on the plan (P4R/FreeAt341N.lean says why). IT IS NOT YET THE READS'
LAW's OWN PREMISE (Desc/Reads/RunIsAtBorder.lean: ReachGives): it says the same three clauses with
the second IN THE TERM IM.seatedAs; that this term is that file's "dressed" is
another file's.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "Well laid": the
ledger's three lists have one entry for each of its numbers.
LETTERS. "There is" in the conclusion: b': the lot's own term for the output head's own
sub-protocol; ms: the messages that must have been sent; n4: the name under which it stands; s0: the
state in front; the rounds and columns.
OBJECT. In the goals' scope, at the opened value of the IOP as written in Lean: a state reached at
the border 342, right behind the output head's own sub-protocol.
USER. P4.reach_gives, and through it the law on the output head's twelve reads at a reached state.
WHAT IT IS. WHOEVER IS REACHED AT 342 CAME BY AN ACCEPTANCE OF THE OUTPUT HEAD's OWN SUB-PROTOCOL,
AS THE CHAIN HOLDS IT, FROM A REACHED STATE WHOSE LEDGER IS WELL LAID.
  reach_gives0      by reach_last (P4R/Back341N.lean), IM.k6_of and k6_at_341, and
                    wellLaid_341 (P4R/FreeAt341N.lean).

-/
import Johnson.IMR.K6Seat
import Johnson.P4R.FreeAt341N

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (seatAt seatedClaims)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid readsOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- **Behind the output head's own sub-protocol.** -/
theorem reach_gives0 {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hplan : ∀ b, c.blocksInOrder[340]? = some b → b.planOk = true) {XP : Type} {start : XP → S} {z : XP}
    {s : S} (h : Reach 0 c.blocksInOrder start 342 (z, s)) :
    ∃ (b' : Block S Cl) (ms : List (Nat × Nat)) (n4 : String) (s0 : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))),
      P4.headBefore Z Bs.G₀ = some ms ∧ seatedClaims Bs.G₀.W 24 ms = some b' ∧
      b' ∈ P4.k6Hear Z Bs.G₀ ∧
      (IM.seatedAs ProofFile.sameReply b' n4 IM.k6Place).decide s0 rs gs = .ok s ∧
      Reach 0 c.blocksInOrder start 341 (z, s0) ∧
      WellLaid ((seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s0) := by
  obtain ⟨s0, b, h341, e, y⟩ := reach_last h
  obtain ⟨Lk, c4, b', ms, e1, e2, hms, hsc, hla, hsz, -, -⟩ := IM.k6_of hS hR O
  obtain rfl : b = c4 := Option.some.inj (e.symm.trans (IM.k6_at_341 hS hR O e1 e2).1)
  obtain ⟨rs, gs, d⟩ := step_yes y
  have hla' : b = IM.seatedAs ProofFile.sameReply b' b.name IM.k6Place := hla
  refine ⟨b', ms, b.name, s0, rs, gs, hms, hsc, ?_, ?_, h341,
    wellLaid_341 hS hR O hplan h341 _ _⟩
  · unfold P4.k6Hear
    rw [hms, hsz]
    show b' ∈ (seatedClaims Bs.G₀.W 24 ms).toList
    rw [hsc]
    exact List.mem_singleton.2 rfl
  · rw [← hla']
    exact d

end P4

#print axioms P4.reach_gives0
