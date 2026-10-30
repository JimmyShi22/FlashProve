-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RowsIn.lean: CONDITIONAL where it says so. NOT a law on a
distribution of its own, NOT `plays`, NOT `acc`: HOW THE ROW OF THE SUB-PROTOCOL "the output head's
own rounds" GOES INTO THE FRAME's LIST OF ROWS: as an `SLot` (Honest/Thread/Rows.lean): the lot's
rows WITH their simulators, On and bud; one equation to the lot's honest side that is already seated
(`headLot`, Honest/K6/Part.lean; `headLotAt`, Honest/K6/Wit.lean); and `Good` at each row's own
side.

  1  `headUnlettered`, `headSLot`, `headSLotAt`   a row without letters: the place, the parts with
     their simulators (`headSided`), On := True, bud := `headBud`; the lot of such rows: one for
     each block that the lot seats, where the test on the public numbers says yes, else none; the
     lot at the two shared readers
  2  `headUnlettered_half`, `headSLot_toHLot`, `headSLotAt_toHLot`   THE ONE EQUATION: the rows'
     halves are the frame's: `(headSLot fits wit).toHLot = headLot fits wit`. No premise
  3  `headSLot_rows`   every row of the lot is `headUnlettered` at a block that the lot seats
  4  `head_good_row`   CONDITIONAL: `Good` AT A ROW's OWN SIDE, as `Side.seated` lays it AT WHATEVER
     FALLS, at every `pre`, at A := False and whatever B, at the row's own On and bud: meant for
     `hand_of_house` (Honest/Thread/RowsMore.lean)
  5  `head_bud_share`   CONDITIONAL: the first chain's clause of `BudDebts`
     (Honest/Law/OwedRule.lean) at this row, to its letter, at whatever letters A and B

All of it has code: no definition here is noncomputable.

Called. `Unlettered`, `SLot`, `SLot.toHLot`: Honest/Thread/Rows.lean. `half_of_zip`:
Honest/Thread/RowsMore.lean. `head_good_all`: Honest/K6/Law/GoodRowSum.lean. `head_bud`:
Honest/K6/Law/GoodRow.lean. `headSeated_of_seated`: Honest/K6/Law/Row.lean.

Limits. THE NAME IS WRITTEN A THIRD TIME HERE; the equation holds it against `headLot`'s. WHERE THE
TEST ON THE PUBLIC NUMBERS SAYS NO THE LOT LAYS NO ROW, as `headLot` lays no half: whether
`headFitsB` says yes at the ground at which the frame asks the rows is not shown here
(Honest/K6/Law/RowsSeatedAtHead.lean, `head_fits_at_ground`, has it at the ground that the
description's maker lays, under the library's hypothesis `P5J.AtMgA`). In 4: that the members of the
chain's list at the row's place have the declared rounds and no oracle message, and the Bool on the
book, are premises; at A := False (in `head_good_row`'s end: fun _ _ _ _ => False) `plays` and `acc`
are met for nothing; in the frame A and B are set by `Unlettered.lay` (Honest/Thread/Rows.lean). All
that the Limits of Honest/K6/Law/GoodRow.lean and GoodRowSum.lean say holds here. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore
import Johnson.Desc.ProofFile.Honest.Law.OwedRule
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Desc.ProofFile.Honest.K6.Law.GoodRowSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place FileDescription)
open VerifiableInference.Desc.Kinds (Head.Par)
open ProofFile.Honest.Small

variable {S Cl X W₀ Rc Tr : Type}

/-! ## 1 The rows -/

/-- **The row without letters**: the place; the parts with their simulators; On := True; bud: no
position is read. -/
def headUnlettered (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { place := at_, row := headSided wit p at_, On := fun _ _ _ _ => True, bud := headBud }

/-- **The lot's rows**: as `headLot` lays its halves: one for each block that the lot seats, at that
block's own place, where the test on the public numbers says yes; else none. -/
def headSLot (fits : Pub → Ground → Bool) (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { name := "the output head's own rounds (K6)"
    rows := fun Z G =>
      if fits Z G then
        (P4.k6Hear Z G).map fun b => headUnlettered (wit Z G) (headParAt G) b.place
      else [] }

/-- The lot at the two shared readers: beside `headLotAt`. -/
def headSLotAt (cells : Tr → Cells) (weights : W₀ → Weights) :
    SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  headSLot headFitsB (headWit' cells weights)

/-! ## 2 The one equation -/

/-- A row's half is the frame's. No premise. -/
theorem headUnlettered_half (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    (headUnlettered (X := X) wit p at_).half = ⟨at_, headRow wit p at_⟩ :=
  half_of_zip at_ (headRow wit p at_) (headSims p at_) _ _
    (by simp [headRow, headParts, headSims])

/-- **THE ONE EQUATION.** No premise. -/
theorem headSLot_toHLot (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) :
    (headSLot (X := X) fits wit).toHLot = headLot fits wit := by
  unfold SLot.toHLot headSLot headLot
  congr 1
  funext Z G
  by_cases h : fits Z G = true
  · simp only [h, if_true, List.map_map]
    refine List.map_congr_left fun b _ => ?_
    exact headUnlettered_half (wit Z G) (headParAt G) b.place
  · simp only [h, if_false, Bool.false_eq_true, List.map_nil]

/-- The like at the two shared readers. No premise. -/
theorem headSLotAt_toHLot (cells : Tr → Cells) (weights : W₀ → Weights) :
    (headSLotAt (Rc := Rc) (X := X) cells weights).toHLot = headLotAt cells weights :=
  headSLot_toHLot headFitsB (headWit' cells weights)

/-! ## 3 Good at a row's own side -/

/-- Every row of the lot is the row without letters at a block that the lot seats. -/
theorem headSLot_rows {fits : Pub → Ground → Bool}
    {wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk} {Z : Pub} {G : Ground}
    {r : Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    (hr : r ∈ (headSLot fits wit).rows Z G) :
    ∃ b ∈ P4.k6Hear Z G, r = headUnlettered (wit Z G) (headParAt G) b.place := by
  unfold headSLot at hr
  by_cases h : fits Z G = true
  · simp only [h, if_true, List.mem_map] at hr
    obtain ⟨b, hb, rfl⟩ := hr
    exact ⟨b, hb, rfl⟩
  · simp only [h, if_false, Bool.false_eq_true, List.not_mem_nil] at hr

/-- CONDITIONAL. **`Good` at a row's own side**, as `Side.seated` lays it AT WHATEVER FALLS fs₀, at
A := False and whatever B, at the row's own On and bud. `plays` and `acc` ARE MET FOR NOTHING THERE.
`pre` is a free letter: the term stands at every `pre`. -/
theorem head_good_row {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) {bs : List (Block S Cl)}
    {fs₀ : List (Fall S)} {σ₀ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    (hσ : Side.seated bs (headUnlettered (X := X) wit p at_).place
      (headUnlettered (X := X) wit p at_).row fs₀ = some σ₀)
    (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hb : ∀ b ∈ bs, b.place = at_ → b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => [])
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨at_, i⟩) = true) :
    Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) B
      (headUnlettered (X := X) wit p at_).On (headUnlettered (X := X) wit p at_).bud :=
  head_good_all φ (headSeated_of_seated hσ hb) Bk ord chain firstTree B hB

/-! ## 4 The row's share of bud's debt -/

/-- CONDITIONAL. **The first chain's clause of `BudDebts` (Honest/Law/OwedRule.lean: `bud₁`) AT THIS
ROW, TO ITS LETTER**, with L laid as the row written out, at whatever letters A and B, and `L.bud`
as `headBud`: a sentence on the description, the challenges and the row's cut: no input, no coin, no
run. It spends `head_bud`, which says more: at every reader of trees, number and list of challenges;
the clause's three premises on where the member stands and on the challenges are not spent. -/
theorem head_bud_share (F : FileDescription Inst) (Bk : ProverCoinCounts) (wit : Local W₀ Rc Inst Tr → HeadAsk)
    (p : Head.Par) (at_ : Place)
    (A B : Coins Bk → F.S₁ → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hb : ∀ b ∈ F.first.blocksInOrder, b.place = at_ →
      b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => []) :
    ∀ σ, (⟨at_, headSided wit p at_, A, B, fun _ _ _ _ => True, headBud⟩ :
        Lettered Bk F.S₁ F.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst).side
          F.first.blocksInOrder = some σ →
      ∀ u ∈ σ.members, ∀ pre t n, F.first.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
      headBud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum) :=
  fun _ hσ u hu _ _ _ _ _ _ _ => head_bud (headSeated_of_seated hσ hb) u hu _ _ _

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headUnlettered_half
#print axioms ProofFile.Honest.K6.headSLot_toHLot
#print axioms ProofFile.Honest.K6.headSLotAt_toHLot
#print axioms ProofFile.Honest.K6.headSLot_rows
#print axioms ProofFile.Honest.K6.head_good_row
#print axioms ProofFile.Honest.K6.head_bud_share
#print axioms ProofFile.Honest.K6.headUnlettered
#print axioms ProofFile.Honest.K6.headSLot
#print axioms ProofFile.Honest.K6.headSLotAt
