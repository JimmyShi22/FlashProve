-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/MineSeats.lean: THE TEST ON THE PLAN `SeatsFit` (Johnson/Desc/Sound/WordsLaw.lean: of
each member THE WHOLE SENDING's seats fit) AT THE LAST TABLE's MEMBERS `mineOf ms₁ ms₂ N₁ Ns`
(Johnson/LLT25R/LastMine.lean): it follows from the same test at the two tables' own lists; and at
the shared table's list it holds wherever the verifier's test on the planner's sizes accepts.

  `seatsFit_mineOf`: `SeatsFit` at ms₁ and at ms₂ ⊢ at `mineOf ms₁ ms₂ N₁ Ns`: mine are members of
    the two lists.
  `seatsFit_msSh`: `SeatFits` at the shared chain's two sendings ⊢ `SeatsFit` at `msSh …`.
  `withU_sized` · `toldFit_sized`: two closed facts at the written sizes, by the kernel: "send o_u"
    has its messages; `toldFitB` (Johnson/Second/Seam/SeatOfTold.lean) accepts at the two sendings'
    layouts. `toldFit_can_fail`: the negative test: o_omega's places one tree further: it rejects.
  **`seatsFit_sh`**: in the goals' scope, where the public part is made and `madePinnedAt` accepts:
    `SeatsFit (p14At Z).codes G (Sh.ms (Sh.planAt Z N G))`, for every G whose shared chain tells
    what `chainOf` tells at the seat's parameters (hG). By `Second.Seam.seatFits_of_told`.
  `codes_one`: there the first chain's codes as read back are the planner's.
Limits. hG is a premise here. The full size alone. That any public files meet the premises is not
shown. Nothing on soundness. On hiding nothing.

-/
import Johnson.LLT25R.LastNum
import Johnson.LLT25R.LastMine
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Second.Seam.SeatOfTold
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LLT25
open OnBytes OnBytes.Params
open VerifiableInference.Desc (FileDescription Block oraclesOf)
open VerifiableInference.Desc.Sound (Mem membersOf SeatFits SeatsFit)
open VerifiableInference.Desc.Shared (NumbersS)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.PlanWritten (proofSizedFull madePinnedAt sized_in_scope first_in_scope
  sized_of_made first_of_made)
open _root_.Desc.K14 (withU withOmega p14Of beforePointOf chainOf St)
open _root_.Desc.K14.Law.Fence (msSh sendingU sendingO)
open _root_.Desc.K14.Law (Sh.planAt Sh.ms Sh.t₁ Sh.layU Sh.layO)
open Second.Seam (toldFitB seatFits_of_told)
open ToldDesc (p14At)

/-- **Mine are members of the two lists.** -/
theorem seatsFit_mineOf {Xi : Type} {G : FileDescription Xi} {cs : Codes} {ms₁ ms₂ : List Mem}
    {N₁ : Numbers} {Ns : NumbersS} (h₁ : SeatsFit cs G ms₁) (h₂ : SeatsFit cs G ms₂) :
    SeatsFit cs G (mineOf ms₁ ms₂ N₁ Ns) := by
  intro x hx
  rcases mem_mineOf.1 hx with ⟨hm, -⟩ | ⟨hm, -⟩
  · exact h₁ x hm
  · exact h₂ x hm

/-- The shared chain's members are members of its two sendings. -/
theorem seatsFit_msSh {Xi : Type} (G : FileDescription Xi) (cs : Codes) (S : LinShape)
    (rU rO rSp lo : ℕ) (layU layO : TreeLay)
    (hU : SeatFits G cs (sendingU S rU lo layU layO).l (sendingU S rU lo layU layO).seat)
    (hO : SeatFits G cs (sendingO S rO rSp lo layU layO).l (sendingO S rO rSp lo layU layO).seat) :
    SeatsFit cs G (msSh S rU rO rSp lo layU layO) := by
  intro x hx
  unfold msSh membersOf at hx
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact hU
  · exact hO

set_option maxRecDepth 1000000 in
/-- At the written sizes "send o_u" has its messages. -/
theorem withU_sized : (withU proofSizedFull.batch.shape).isSome = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At the written sizes what the two sending sub-protocols tell fits the three seats. -/
theorem toldFit_sized : toldFitB proofSizedFull.codes proofSizedFull.batch.shape
    ((layTrees proofSizedFull.codes ((withU proofSizedFull.batch.shape).getD #[])).getD default)
    ((layTrees proofSizedFull.codes (withOmega proofSizedFull.batch.shape)).getD default) =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with a tree more in o_u's layout, o_omega's places lie one tree further. -/
theorem toldFit_can_fail : toldFitB proofSizedFull.codes proofSizedFull.batch.shape
    { (layTrees proofSizedFull.codes ((withU proofSizedFull.batch.shape).getD #[])).getD default
      with shapes := ((layTrees proofSizedFull.codes
        ((withU proofSizedFull.batch.shape).getD #[])).getD default).shapes.push {} }
    ((layTrees proofSizedFull.codes (withOmega proofSizedFull.batch.shape)).getD default) =
      false := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

/-- **The shared table's members' seats fit.** -/
theorem seatsFit_sh {Xi : Type} (hW : VerifierAndGoals.InScope W = true)
    (pub : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (N : H2U.Places4)
    (G : FileDescription Xi) (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hG : oraclesOf G.shared.blocksInOrder =
      oraclesOf (chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N)) tests last).blocksInOrder) :
    SeatsFit (p14At Z).codes G (Sh.ms (Sh.planAt Z N G)) := by
  have hs : Z.p.chains.made.sized.proof = proofSizedFull :=
    sized_in_scope hW pub (sized_of_made hy)
  obtain ⟨sentU, hU⟩ := Option.isSome_iff_exists.1 withU_sized
  have hU' : withU (p14Of Z.p.chains (beforePointOf N)).S = some sentU := by
    show withU Z.p.chains.made.sized.proof.batch.shape = _
    rw [hs]
    exact hU
  have hB : toldFitB (p14Of Z.p.chains (beforePointOf N)).codes
      (p14Of Z.p.chains (beforePointOf N)).S (Sh.layU (Sh.planAt Z N G))
      (Sh.layO (Sh.planAt Z N G)) = true := by
    show toldFitB Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch.shape
      ((layTrees Z.p.chains.made.sized.proof.codes
        ((withU Z.p.chains.made.sized.proof.batch.shape).getD #[])).getD default)
      ((layTrees Z.p.chains.made.sized.proof.codes
        (withOmega Z.p.chains.made.sized.proof.batch.shape)).getD default) = true
    rw [hs]
    exact toldFit_sized
  have F := seatFits_of_told G (p14Of Z.p.chains (beforePointOf N)) (Sh.t₁ (Sh.planAt Z N G))
    (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G)) Z.p.chains tests last hU' rfl hG hB
    ((Sh.planAt Z N G).rad2 0) ((Sh.planAt Z N G).rad5 0) ((Sh.planAt Z N G).rad5 1)
  exact seatsFit_msSh G _ _ _ _ _ _ _ _ F.1 F.2

/-- **The first chain's codes as read back are the planner's.** -/
theorem codes_one (hW : VerifierAndGoals.InScope W = true)
    (pub : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.codes = (p14At Z).codes := by
  show Z.first.codes = Z.p.chains.made.sized.proof.codes
  rw [sized_in_scope hW pub (sized_of_made hy)]
  exact (first_in_scope hW pub (first_of_made hy)).1

end LLT25

#print axioms LLT25.seatsFit_mineOf
#print axioms LLT25.seatsFit_msSh
#print axioms LLT25.withU_sized
#print axioms LLT25.toldFit_sized
#print axioms LLT25.toldFit_can_fail
#print axioms LLT25.seatsFit_sh
#print axioms LLT25.codes_one
