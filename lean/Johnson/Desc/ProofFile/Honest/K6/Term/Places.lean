-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/Places.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6): where
the kind stands in the first chain of the online description: at number 341 alone.

WHAT IT IS NOT. A fact on the description's public list of places. It names no prover. The library's
hypothesis on the first chain is a premise. Two lines are evaluated in Lean's kernel, each on the
library's written list of places: a closed test, and a control: the same test, bent, which fails.

  writtenPlacesOfTheKind            in the written list a place of the kind K6 has number 341
  writtenPlacesOfTheKind_control    the same test with 340 fails
  firstChainHasTheKindOnce          under the hypothesis: the first two clauses of StandsAtOneBorder
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.Statements
import Johnson.Desc.ProofFile.Honest.Thread.HeadFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain Place KindName Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

set_option maxRecDepth 1000000 in
/-- In the library's written list of places a place of the kind K6 has number 341. A closed fact. -/
theorem writtenPlacesOfTheKind :
    ((List.range P5J.At.ps.length).all fun number => (P5J.At.ps[number]?).all fun p =>
      !decide (p.kind = .K6) || decide (number = 341)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with 340 the test fails. -/
theorem writtenPlacesOfTheKind_control :
    ((List.range P5J.At.ps.length).all fun number => (P5J.At.ps[number]?).all fun p =>
      !decide (p.kind = .K6) || decide (number = 340)) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the library's hypothesis the first chain has a member of the kind at number 341, at the
place IM.k6Place, and at no other number.** -/
theorem firstChainHasTheKindOnce (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∃ member, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[341]? = some member ∧
      member.place = IM.k6Place) ∧
    ∀ number member, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[number]? = some member →
      member.place.kind = .K6 → number = 341 := by
  refine ⟨?_, fun number member hm hk => ?_⟩
  · obtain ⟨member, hm, M⟩ := P4.k6_member_at_mg h.toAtMg
    obtain ⟨hp, -, -⟩ := member_is M
    exact ⟨member, hm, hp⟩
  · have hm' : cF.blocksInOrder[number]? = some member := hm
    have hw := FirstFill.place_of_member h hm'
    have hlt : number < P5J.At.ps.length := by
      by_contra hge
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hw
      cases hw
    have ht := List.all_eq_true.1 writtenPlacesOfTheKind number (List.mem_range.2 hlt)
    rw [hw] at ht
    simpa [hk] using ht

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.writtenPlacesOfTheKind
#print axioms ProofFile.Honest.K6.Term.writtenPlacesOfTheKind_control
#print axioms ProofFile.Honest.K6.Term.firstChainHasTheKindOnce
