-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5WrittenIsFull.lean: **THE CLOSED TERMS OF K5's FILES AND OF Johnson/P5T/ FOR THE PLAN's SEATS AT THE WRITTEN VALUES ARE ONE**: pseatsW (Door/Law/K5Written.lean) is P5T.psFull, and pseatsAllW (Door/Law/K5WrittenAll.lean) is P5T.seatsAllFull
(Johnson/P5T/PlanSeatsFull.lean). Two equations without a letter; nothing is evaluated.
Why. P5T.psFull | seatsAllFull were there first, and are made so that Lean's kernel can walk them (the roots in front of a sending off 82 pairs, not off 48,293 rounds). What the kernel shows at them is spent, through these two equations, at the Bools
that are stated at pseatsW | pseatsAllW (seatsAllW · shapesAllW, Door/Law/K5WrittenPlans.lean; tieW · tieWW, Door/Law/K5TieWritten.lean | K5TieWitness.lean).

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Main names:
  planSeatsBy_is | chainSeatsBy_is: the two liftings of P5T.planSeats' | chainSeats' text (Door/Law/K5Written.lean | K5WrittenAll.lean; Johnson/P5T/PlanSeatsAt.lean | PlanSeatsAllAt.lean) are one, the letters' order apart: by unfolding.
  roots_take: the sum over a prefix of the roots is P5T.rootsIn. rootsW₁_is | ₂ | ₃: so the three functions of Door/Law/K5WrittenAll.lean.
  **pseatsW_is : pseatsW = P5T.psFull** · **pseatsAllW_is : pseatsAllW = P5T.seatsAllFull**: by P5T.psFull_is | seatsAllFull_is (Johnson/P5T/PlanSeatsFull.lean) and request_shape_written (Johnson/Goal/Numbers/RequestWritten.lean).
IS IT EMPTY HERE? Closed facts.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5WrittenAll
import Johnson.P5T.PlanSeatsFull
import Johnson.Goal.Numbers.RequestWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.PlanWritten (proofSizedFull request_shape_written)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (dryProofFull proofSendsFull)

/-- The two liftings of the first chain's maker's text are one. -/
theorem planSeatsBy_is (c : Johnson.G.ChainSends) (S : OnBytes.Params.ReqShape) (rb : ℕ → ℕ) :
    planSeatsBy c S rb = P5T.planSeatsBy rb c S := rfl

/-- The two liftings of the other chains' maker's text are one. -/
theorem chainSeatsBy_is (chain base : ℕ) (c : Johnson.G.ChainSends) (rb : ℕ → ℕ) :
    chainSeatsBy chain base c rb = P5T.chainSeatsBy rb chain base c := rfl

/-- The sum over a prefix of the roots, in the term P5T.rootsIn (Johnson/P5T/PlanSeatsAt.lean). -/
theorem roots_take {α : Type} (l : List α) (g : α → Fmt.Entry) (k : ℕ) :
    ((l.map fun x => (g x).roots).take k).sum = P5T.rootsIn (l.map g) k := by
  unfold P5T.rootsIn
  rw [← List.map_take, ← List.map_take, List.map_map]
  rfl

theorem rootsW₁_is : rootsW₁ = P5T.rootsIn P5T.esFull.1 := funext fun k => roots_take dryProofFull.1 (fun x => x.1.entry) k
theorem rootsW₂_is : rootsW₂ = P5T.rootsIn P5T.esFull.2.1 := funext fun k => roots_take dryProofFull.2.1 (fun x => x.1.entry) k
theorem rootsW₃_is : rootsW₃ = P5T.rootsIn P5T.esFull.2.2 := funext fun k => roots_take dryProofFull.2.2 (fun x => x.1.entry) k

/-- The first chain's seats, as the maker P5T.planSeatsAt at the written values. -/
theorem pseatsW_at : pseatsW = P5T.planSeatsAt proofSendsFull.1 shapeFull P5T.esFull.1 := by
  have hr : (fun k => ((dryProofFull.1.map fun x => x.1.entry.roots).take k).sum) = P5T.rootsIn P5T.esFull.1 := rootsW₁_is
  unfold pseatsW
  rw [planSeatsBy_is, hr, request_shape_written]
  rfl

/-- **THE FIRST CHAIN's SEATS AT THE WRITTEN VALUES: ONE TERM.** -/
theorem pseatsW_is : pseatsW = P5T.psFull := pseatsW_at.trans P5T.psFull_is

/-- **ALL THREE CHAINS' SEATS AT THE WRITTEN VALUES: ONE TERM.** -/
theorem pseatsAllW_is : pseatsAllW = P5T.seatsAllFull := by
  have l1 : dryProofFull.1.length = P5T.esFull.1.length := by
    show _ = (dryProofFull.1.map fun x => x.1.entry).length
    rw [List.length_map]
  have l2 : dryProofFull.2.1.length = P5T.esFull.2.1.length := by
    show _ = (dryProofFull.2.1.map fun x => x.1.entry).length
    rw [List.length_map]
  unfold pseatsAllW
  rw [pseatsW_at, chainSeatsBy_is, chainSeatsBy_is, rootsW₁_is, rootsW₂_is, rootsW₃_is, l1, l2]
  exact P5T.seatsAllFull_is

end H2K5.Door

#print axioms H2K5.Door.planSeatsBy_is
#print axioms H2K5.Door.chainSeatsBy_is
#print axioms H2K5.Door.roots_take
#print axioms H2K5.Door.pseatsW_is
#print axioms H2K5.Door.pseatsAllW_is
