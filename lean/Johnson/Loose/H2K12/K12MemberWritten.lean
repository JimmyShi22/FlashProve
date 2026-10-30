-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12CoreW
import Johnson.Loose.H2K12.K12CutW
import Johnson.G.PlansPriced
/-
Johnson/Loose/H2K12/K12MemberWritten.lean: CONDITIONAL: THE PROXIMITY TEST's (the
kind K12's) ROW AMONG THE ROWS THAT "the proof file's description returns, with its cut" WANTS OF
EACH LOT: THE LOT's DEBT (hV of H2K12/K12RowAlone.lean): THE NUMBERS WHICH THE PLAN GIVES ARE THE
WRITTEN MEMBER: FROM FIVE EQUATIONS ON FIELDS OF WHAT THE PLANNER AND sendsOf MAKE OF THE PUBLIC
FILES, AND THE RETURN OF treesSent AT
THE THREE CHAINS. With it the like for the kind's three sub-protocols on the two later chains. No
evaluation in Lean's kernel stands in this file.
THE FIVE, BY NAME, ON m : Made: hs, hz, hp: the setting is recordSet, the proof file's sizes are
proofSizedFull, the planner's three lists are proofThree's; hg: the plans as read back are these
lists' (ProofPlansPriced, Johnson/G/PlansPriced.lean); hc: what is sent is proofSendsFull.
  places_of_trees  from the five and h0 h1 h2 (Johnson.G.OfPlan.treesSent returns at the three
                   chains, at the arguments at which H2U.firstsOfPlan calls it): H2U.placesOfMade m
                   = coreAtW (H2K12/K12CoreW.lean)
  members_of_trees from the same: H2U.p12OfMade m = piLFull; p12FoldedOfMade m 9, p12OmegaOfMade m
                   10, p12OwnOfMade m 2 are piUFull, piOFull, piWFull laid at ⟨2, none, 9⟩, ⟨2,
                   none, 10⟩, ⟨3, none, 2⟩. The three terms are spelled out, not named: another
                   file names them piU, piO, piW (Johnson/AtFull/Desc/LaterSeats.lean)
  members_written  THE SAME END FROM THE FIVE AND (D) (hD : declPOf m = .ok D): where the proof
                   file's declared rounds are made, treesSent has returned thrice: another file's
                   theorem, called: Johnson.AtFull.Desc.trees_of_decl
                   (Johnson/AtFull/Desc/TreesValue.lean). Nothing of D is
                   read
  places_return    from the five and hD: there is N with H2U.placesOfMade m = .ok N
WHAT IS LEFT BEHIND THIS FILE. The five premises: that what the planner and sendsOf make of given
public files has these values. And hD.
THE WALL IS MOVED, NOT TAKEN DOWN: treesSent ends with a check of its
own over all rounds of the plan (at the first chain: 48,293; in Lean's kernel: the square of that,
by a reading of its text; not measured).
This file goes around it by taking the RETURN as a premise. Under the five equations declPOf m reads
nothing but fields that they fix: so hD is itself a closed fact at the written values, and whoever
pays it by the kernel meets that check. It is the front's (ProofFile.pubBy runs declPOf).
WHAT IT IS NOT: the written values stand on prints of the library's own planner and evaluator. The
full size alone. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan H2U
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (proofSendsFull)
open H2K.Member (piLFull piUFull piOFull piWFull)

section
variable (m : Made) (hs : m.p.chains.made.sized.set = recordSet)
  (hz : m.p.chains.made.sized.proof = proofSizedFull)
  (hp : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
  (hg : ProofPlansPriced m proofThree.A.plan proofThree.B.plan proofThree.C.plan)
  (hc : m.proof = proofSendsFull)
include hs hz hp hg hc

/-- **From the five equations and the three returns: the routine's value.** -/
theorem places_of_trees {t0 t1 t2 : List (Sent × Nat)}
    (h0 : treesSent "proof file, first chain" m.proof.1 m.p.chains.proof.first.given.plan [] =
      .ok t0)
    (h1 : treesSent "proof file, shared chain" m.proof.2.1 m.p.chains.proof.shared.given.plan
      (ownMasks m.proof.2.1.codes m.p.chains.made.sized.proof.batch.shape
        m.p.chains.proof.shared.given.plan.rounds) = .ok t1)
    (h2 : treesSent "proof file, second chain" m.proof.2.2 m.p.chains.proof.second.given.plan [] =
      .ok t2) :
    placesOfMade m = coreAtW := by
  rw [hc, hg.1] at h0
  rw [hc, hg.2.1, hz] at h1
  rw [hc, hg.2.2] at h2
  have a0 := trees_are h0 offP0
  have a1 := trees_are h1 offP1
  have a2 := trees_are h2 offP2
  rw [placesOfMade_eq, hs, hz, hp, hg.1, hg.2.1, hg.2.2, hc,
    placesAt_core h0 h1 h2 locsP cutW, a0, a1, a2]
  rfl

/-- **From the five equations and the three returns: the four written members.** -/
theorem members_of_trees {t0 t1 t2 : List (Sent × Nat)}
    (h0 : treesSent "proof file, first chain" m.proof.1 m.p.chains.proof.first.given.plan [] =
      .ok t0)
    (h1 : treesSent "proof file, shared chain" m.proof.2.1 m.p.chains.proof.shared.given.plan
      (ownMasks m.proof.2.1.codes m.p.chains.made.sized.proof.batch.shape
        m.p.chains.proof.shared.given.plan.rounds) = .ok t1)
    (h2 : treesSent "proof file, second chain" m.proof.2.2 m.p.chains.proof.second.given.plan [] =
      .ok t2) :
    p12OfMade m = piLFull ∧
      p12FoldedOfMade m 9 = ({ piUFull with place := ⟨2, none, 9, .K12⟩ } : P12) ∧
      p12OmegaOfMade m 10 = ({ piOFull with place := ⟨2, none, 10, .K12⟩ } : P12) ∧
      p12OwnOfMade m 2 = ({ piWFull with place := ⟨3, none, 2, .K12⟩ } : P12) :=
  members_of m (by rw [places_of_trees m hs hz hp hg hc h0 h1 h2]; exact coreW)

/-- **FROM THE FIVE EQUATIONS AND "THE DECLARED ROUNDS ARE MADE": THE FOUR WRITTEN MEMBERS.** -/
theorem members_written (D : Decl3) (hD : declPOf m = .ok D) :
    p12OfMade m = piLFull ∧
      p12FoldedOfMade m 9 = ({ piUFull with place := ⟨2, none, 9, .K12⟩ } : P12) ∧
      p12OmegaOfMade m 10 = ({ piOFull with place := ⟨2, none, 10, .K12⟩ } : P12) ∧
      p12OwnOfMade m 2 = ({ piWFull with place := ⟨3, none, 2, .K12⟩ } : P12) := by
  obtain ⟨t0, t1, t2, h0, h1, h2⟩ := Johnson.AtFull.Desc.trees_of_decl hD
  exact members_of_trees m hs hz hp hg hc h0 h1 h2

theorem places_return (D : Decl3) (hD : declPOf m = .ok D) : ∃ N, placesOfMade m = .ok N := by
  obtain ⟨t0, t1, t2, h0, h1, h2⟩ := Johnson.AtFull.Desc.trees_of_decl hD
  obtain ⟨X, _, hX, _⟩ := of_fourAt coreW
  exact ⟨X, (places_of_trees m hs hz hp hg hc h0 h1 h2).trans hX⟩

end

end H2K12

#print axioms H2K12.places_of_trees
#print axioms H2K12.members_of_trees
#print axioms H2K12.members_written
#print axioms H2K12.places_return
