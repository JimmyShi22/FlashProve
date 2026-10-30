-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsAtHead.lean: kind K14: THE PUBLIC PREMISES ON THE SHAPES
OF THE SHARED CHAIN's TWO SENDINGS ("send o_u", "send o_omega"), AT THE SHARED CHAIN's OWN
PARAMETERS qAt Zp Np = p14Of Zp.p.chains (beforePointOf Np), UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean). Statements with their proofs: joins, and one evaluation in Lean's kernel.
No definition.

Why. The laws on the coins of these two parts (the fields fresh and exact of Good, Honest/Side.lean)
take these premises at a free plan. Here they are met at the plan that the filling of the frame lays
(nowShared, Honest/SharedChainProverSides.lean): that it is that plan: filling_at_head,
Honest/K14/SendingsAtFilling.lean.

  p14_of_written  **under the library's equations on the public part (Written,
                  Johnson/Goal/Numbers/WrittenAtZ.lean) p14Of of the planner's chains is the typed
                  plan**: the record's setting, the shared scope, the written codes, the typed
                  shape, the item 0. (The library has this equation twice inside a proof,
                  Johnson/Desc/K14/Honest/YesAt.lean and Johnson/Goal/Numbers/K14CondAt.lean; it is
                  a named statement in neither; one of the fields, the shape, at every chains, is
                  its p14_shape, Johnson/Desc/Sound/AtDescPure.lean)
  ahead_full      at what realSized returns (Johnson/Desc/K1/Law/CondReal.lean): masks are sent
                  ahead, and the test on G_u has a first stage: an evaluation in Lean's kernel. (ON
                  THE FIRST HALF THE LIBRARY HAS A GENERAL LAW WITH A PROOF: every plan that the
                  planner makes sends the masks ahead: chainsOf_masksAhead,
                  Johnson/Desc/Third/Law/MasksAhead.lean: not called here)
  sendings_of_written   under Written at the size that realSized returns, at every list bp:
                  sendingsFit (Honest/K14/SendingsShapes.lean; by sendingsFit_real,
                  SendingsShapesAt.lean) · the shape splits (the library's splits_full) ·
                  FreshPublic at n = 63, r = 152 (the library's fresh_public_full,
                  Johnson/Desc/K14/Honest/FreshAtShapes.lean) · ahead_full's two
  sendings_of_laid, sendings_at_head   **the same in the goals' scope from LaidAt, and under the
                  head**, with SpShape (Johnson/Desc/K14/Honest/FreshAtChain.lean) and the tail's
                  count in FreshPublic's place: Written by the library's Sh.written_of_made, as in
                  plan2_of_laid (Honest/K14/PlanAtHead.lean)

63 AND 152 ARE THE FULL SIZE's NUMBERS: o_sp's mask code has 64 message entries and a tail of 152.
THE SMALL STORED EXAMPLE IS NOT TREATED HERE: the head holds in the goals' scope alone. Into
realSized the two numbers are written by hand (FreshAtShapes.lean's own head); that the planner's
sizes at the public files are these is what Written says.

What is not claimed. No example of the head is shown in this file; one, at VerifierAndGoals.storedPublicFiles, is
AtFullSide/Top/HeadMemberAtFull.lean's. The other premises of the laws on these parts: on the book,
on the count of positions, on the stand. Nothing of a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapesAt
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.K14.Honest.FreshAtShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Params (LinSized recordSet)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open Desc.K14 (P14 p14Of beforePointOf)
open Desc.K14.Law (Written sized_one)
open Desc.K14.Honest (FreshPublic SpShape spSymCode fresh_public_full splits_full)

/-- **Under the library's equations on the public part, the shared chain's parameters out of the
planner's chains are the typed ones.** -/
theorem p14_of_written {Z : ProofFile.Pub} {x : LinSized} (W : Written Z x) (bp : List (Nat × Nat)) :
    p14Of Z.p.chains bp = ⟨recordSet, .shared, codesFull2, x.shape, 0, bp⟩ := by
  unfold p14Of
  simp only [W.set, W.codes, W.shape, W.batch, Bool.false_eq_true, if_false]

/-- At what realSized returns: masks are sent ahead, and the test on G_u has a first stage. -/
theorem ahead_full : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    x.shape.masksAhead = true ∧ ∃ s, x.shape.testU.head? = some s := by
  obtain ⟨x, _, _, hx, _⟩ := VerifiableInference.Desc.K1.real_members
  have h : (realSized.all fun p =>
      p.1.shape.masksAhead && p.1.shape.testU.head?.isSome) = true := by decide +kernel
  rw [hx] at h
  have h' : (x.shape.masksAhead && x.shape.testU.head?.isSome) = true := h
  rw [Bool.and_eq_true] at h'
  exact ⟨x, hx, h'.1, Option.isSome_iff_exists.1 h'.2⟩

/-- **The public premises on the two sendings' shapes, under the library's equations on the public
part** at the size that realSized returns. -/
theorem sendings_of_written {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (W : Written Z x) (bp : List (Nat × Nat)) :
    sendingsFit (p14Of Z.p.chains bp) = true ∧
      (p14Of Z.p.chains bp).S.sharedSplitNeeded = true ∧
      FreshPublic (p14Of Z.p.chains bp).codes (p14Of Z.p.chains bp).S 63 152 ∧
      (p14Of Z.p.chains bp).S.masksAhead = true ∧
      ∃ s, (p14Of Z.p.chains bp).S.testU.head? = some s := by
  obtain ⟨x₁, a1, hf⟩ := sendingsFit_real
  obtain rfl := sized_one hx a1
  obtain ⟨x₂, a2, hp⟩ := fresh_public_full
  obtain rfl := sized_one hx a2
  obtain ⟨x₃, a3, hs⟩ := splits_full
  obtain rfl := sized_one hx a3
  obtain ⟨x₄, a4, hm, ht⟩ := ahead_full
  obtain rfl := sized_one hx a4
  rw [p14_of_written W bp]
  exact ⟨hf 0 bp, hs, hp, hm, ht⟩

section laid
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The like in the goals' scope, from LaidAt, at the shared chain's own parameters**: ITS THIRD
CLAUSE IS ANOTHER: SpShape and the tail's count (152) stand in FreshPublic's place. -/
theorem sendings_of_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    sendingsFit (qAt Zp Np) = true ∧ (qAt Zp Np).S.sharedSplitNeeded = true ∧
      SpShape (qAt Zp Np).codes (qAt Zp Np).S 63 ∧
      (spSymCode (qAt Zp Np).codes (qAt Zp Np).S).r = 152 ∧
      (qAt Zp Np).S.masksAhead = true ∧ ∃ s, (qAt Zp Np).S.testU.head? = some s := by
  obtain ⟨x, hx, W⟩ := Desc.K14.Law.Sh.written_of_made hZ L.pub (P5J.pins_of_laid hZ L).1
    (L.run ▸ LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks)
  obtain ⟨a, b, c, d, e⟩ := sendings_of_written hx W (beforePointOf Np)
  exact ⟨a, b, c.shape, c.tail, d, e⟩

end laid

/-- **The same as sendings_of_laid, under the library's head.** -/
theorem sendings_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    sendingsFit (qAt Zp Np) = true ∧ (qAt Zp Np).S.sharedSplitNeeded = true ∧
      SpShape (qAt Zp Np).codes (qAt Zp Np).S 63 ∧
      (spSymCode (qAt Zp Np).codes (qAt Zp Np).S).r = 152 ∧
      (qAt Zp Np).S.masksAhead = true ∧ ∃ s, (qAt Zp Np).S.testU.head? = some s :=
  sendings_of_laid h.scope h.laid

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.p14_of_written
#print axioms ProofFile.Honest.K14.ahead_full
#print axioms ProofFile.Honest.K14.sendings_of_written
#print axioms ProofFile.Honest.K14.sendings_of_laid
#print axioms ProofFile.Honest.K14.sendings_at_head
