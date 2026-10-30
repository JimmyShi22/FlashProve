-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/BudAtNamed.lean: at each of the goals' two named sets of full-size public files as
Ladder.lean spells them (VerifierAndGoals.NamedFiles Z: Z is VerifierAndGoals.storedPublicFiles or VerifierAndGoals.zGap): THE BOUND ON THE
POSITIONS THAT THE FRAME LAYS FOR THE TREES OF THE SHARED CHAIN's TWO SENDINGS (kind K14: the label
of the linear claim's sub-protocols in the IOP as written in Lean), AT ONE REQUEST's CHALLENGES, AT
EVERY DUE LIST OF THEM: WITH NO HYPOTHESIS ON THE FILES BUT THAT THEY ARE ONE OF THE TWO NAMED SETS.
Three theorems; no definition. Joins: no new thought.

  live_named      the verifier's test on the public files accepts at both named sets (the library's
                  theLive_zFull and theLive_zGap)
  bud_at_named    **there are Zp, Np, cF and x₀ at which the library's one hypothesis at the full
                  size holds, and at these same arguments, at every due list of challenges of the
                  proof file's IOP made of them, whatever the rounds' numbers of roots: budAt
                  (Johnson/SendSim/At/Sim.lean) at "send o_u"'s public numbers, at the positions
                  that the frame lays for the shared chain's trees from number 0 on; budAt at "send
                  o_omega"'s, from number 1 on; and spBud (Honest/K14/FreshDefs.lean) there**

  bud₂_at_named   **at the same arguments: the body of the frame's field bud₂
                  (Honest/Law/OwedRule.lean) at both sendings' rows**, in the rule's own term
                  (bud₂_u, bud₂_omega: Honest/K14/BudRows.lean)

What it is not. It takes hypotheses away at two examples; it adds nothing to what follows from them
(Honest/K14/BudBoth.lean, Honest/K14/BudAtFiles.lean, Honest/K14/BudRows.lean). All limits of
AtFullSide/Top/HeadMemberAtGap.lean, over which it stands, hold here; and all limits of these three
files, above all: THAT A RUN ASKS FOR NO POSITION BEYOND WHAT THE FRAME's LIST treeAsks HOLDS IS NOT
SAID. That a due list of challenges exists is not shown here: Draws.ofDecl_due
(Honest/Law/DrawsOfDecl.lean) has a written one wherever the description has data, as LaidAt gives;
it is not joined here. That any filling has such rows is not shown. ONE REQUEST: nothing on the
union of the positions that the requests of a batch read. The arguments stand under "there are".
Counts on public numbers: no property is claimed. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.Top.HeadMemberAtGap
import Johnson.Desc.ProofFile.Honest.K14.BudRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)
open OnBytes.SendSim.At (budAt)
open ProofFile.Honest ProofFile.Honest.K14

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap

/-- The verifier's test on the public files accepts at both named sets. -/
theorem live_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) : protocolDataWellFormed (asDescriptionFiles Z) = true := by
  rcases hZ with rfl | rfl
  · exact AtFullSide.Top.theLive_zFull
  · exact AtFullSide.Top.theLive_zGap

/-- **AT EITHER NAMED SET OF PUBLIC FILES: THE HEAD's MEMBER, AND AT ITS ARGUMENTS THE BOUND ON THE
POSITIONS AT BOTH SENDINGS**: at one request's challenges. No hypothesis on the files but hZ; the
bound is said of due lists of challenges: ρ.due is a premise inside the clause. A join. -/
theorem bud_at_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    ∃ Zp Np cF x₀,
      P5J.AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x₀ ∧
      ∀ (a : Nat) (ρ : Draws), ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
        ∀ rs : List Nat,
          budAt (jobU ⟨qAt Zp Np, a⟩).Q
            (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 0) ∧
          budAt (jobOmega ⟨qAt Zp Np, a⟩).Q
            (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 1) ∧
          spBud ⟨qAt Zp Np, a⟩
            (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) rs 1) := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named Z hZ
  have live := live_named Z hZ
  have L := P5J.dpZ_live live ▸ h.laid
  exact ⟨Zp, Np, cF, x₀, h, fun a ρ hρ rs =>
    ⟨budAt_u_at_files Z h.scope live Zp Np cF L a ρ hρ rs,
      budAt_omega_at_files Z h.scope live Zp Np cF L a ρ hρ rs,
      spBud_at_files Z h.scope live Zp Np cF L a ρ hρ rs⟩⟩

/-- **AT EITHER NAMED SET: THE HEAD's MEMBER, AND AT ITS ARGUMENTS THE BODY OF THE FRAME's FIELD
bud₂ AT BOTH SENDINGS' ROWS**: at every book and every row with letters that stands at the sending's
place, has one part, and whose letter bud follows from budAt. No hypothesis on the files but hZ;
these premises on the row, that its side is there, and ρ.due stand inside the clause. A join. -/
theorem bud₂_at_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    ∃ Zp Np cF x₀,
      P5J.AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x₀ ∧
      ∀ (a : Nat) (X Pb W₀ Rc Ky : Type) (Bk : ProverCoinCounts)
        (L : Lettered Bk Desc.K14.St ProofFile.Cl Empty (Common W₀ Rc Ky) X Pb)
        (p : Part Empty (Common W₀ Rc Ky) X) (sim : Sim Pb), L.row = [(p, sim)] →
        ((L.place = sendPlace 2 ∧
            ∀ j ds asks, budAt (jobU ⟨qAt Zp Np, a⟩).Q asks → L.bud j ds asks) ∨
          (L.place = sendPlace 5 ∧
            ∀ j ds asks, budAt (jobOmega ⟨qAt Zp Np, a⟩).Q asks → L.bud j ds asks)) →
        ∀ τ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
          ∀ (pre t : List (VerifiableInference.Desc.Block Desc.K14.St ProofFile.Cl)) (n : Nat),
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ τ.block :: t →
          n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
          ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
          L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
            (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1)
              (u.rounds.map (·.2.length))
              (((rowsOfChain (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map
                (·.2.length)).sum) := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named Z hZ
  have live := live_named Z hZ
  have L₀ := P5J.dpZ_live live ▸ h.laid
  refine ⟨Zp, Np, cF, x₀, h, fun a X Pb W₀ Rc Ky Bk L p sim hrow hc => ?_⟩
  rcases hc with ⟨hpl, hb⟩ | ⟨hpl, hb⟩
  · exact bud₂_u h.scope live L₀ a p sim L hpl hrow hb
  · exact bud₂_omega h.scope live L₀ a p sim L hpl hrow hb

end AtFullSide.K14

#print axioms AtFullSide.K14.live_named
#print axioms AtFullSide.K14.bud_at_named
#print axioms AtFullSide.K14.bud₂_at_named
