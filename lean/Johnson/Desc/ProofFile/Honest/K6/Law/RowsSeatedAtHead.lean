-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RowsSeatedAtHead.lean: CONDITIONAL. NOT a law on a distribution
of its own, NOT `plays`, NOT `acc`, and NO evaluation: the sentences of
Honest/K6/Law/RowsSeated.lean's section 4 WITHOUT THEIR NAMED PUBLIC PREMISE
`headFitsB Zp G = true`: under the library's one hypothesis at the full size (`P5J.AtMgA`) that
premise is a theorem of another file of this folder (`headFitsB_at_head`,
Honest/K6/Law/FitsScope.lean), which is called here.

  `head_fits_at_ground`   under the hypothesis, at the ground that the description's maker lays:
                          `headFitsB Zp G = true`
  `head_lot_under_head`   THE TWO SETS OF LETTERS ARE ONE: the lot lays its rows at K6's place
                          alone, and `headParAt G` is the term at the library's public data
  `head_lotSeatB_under_head`   THE LOT's ROW IS SEATED UNDER THE HEAD ALONE: the test at the lot's
                               own rows says yes at the description's first chain
  `head_lot_members_under_head`   the lot lays a row; at each row's place a member of the first
                                  chain's list stands, and what the door asks of that list holds, at
                                  the row's own place and numbers
  `head_lotSeatB_some`   that the test says yes, with the ground named by "there is"
  `head_good_lot_under_head`   under the hypothesis and the Bool on the book: the lot's rows are not
                               empty; at each: a side over the first chain's list at whatever falls,
                               and `Good` at every `pre`, at A := False and whatever B, at the row's
                               own On and bud

A THIN FILE APART, because it stands over Honest/K6/Law/FitsScope.lean, whose own import lines name
modules of the folder Johnson/Goal/. This file's import lines name none of them, and it names
nothing that is declared there.

Called. `headFitsB_at_head`: Honest/K6/Law/FitsScope.lean. `head_lot_at_head`,
`head_lotSeatB_at_head`, `head_good_lot_at_head`, `head_ground_at_head`, `headLotSeatB_iff`:
Honest/K6/Law/RowsSeated.lean. `members_at_of_seatB`: Honest/K6/Law/Row.lean. `IM.Open.blank`:
Johnson/IMR/SeatOpen.lean.

Limits. THE HYPOTHESIS IS A PREMISE: the format's second hash function (`OnBytes.secondHashFunction`), the full size
alone, in the goals' scope; met under four premises on the three public files
(Honest/K6/Law/RowAtHead.lean: `head_seated_at_files`). The Bool on the book is a premise: this file
evaluates it at no book. In `head_good_lot_under_head` `plays` and `acc` are met for nothing (A :=
False) and `fresh` holds by an empty list. All that the Limits of Honest/K6/Law/RowsSeated.lean,
GoodRow.lean and GoodRowSum.lean say holds here: the spender's half alone; one part at a time.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.FitsScope
import Johnson.Desc.ProofFile.Honest.K6.Law.RowsSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Claim Chain)
open VerifiableInference.Desc.Kinds (Head.Par Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open ProofFile.Honest.Small

variable {X W₀ Rc Tr : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL. **The named public premise holds at the ground that the description's maker lays.**
-/
theorem head_fits_at_ground (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : headFitsB Zp G = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact headFitsB_at_head h.toAtMg O

/-- CONDITIONAL. **THE TWO SETS OF LETTERS ARE ONE**, under the one hypothesis, at the ground that
the description's maker lays. -/
theorem head_lot_under_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    headLotPlaces Zp G = [IM.k6Place] ∧
      headParAt G = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) :=
  head_lot_at_head h hG (head_fits_at_ground h hG)

/-- CONDITIONAL. **THE LOT's ROW IS SEATED UNDER THE HEAD ALONE**: the test at the lot's own rows
says yes at the description's first chain. -/
theorem head_lotSeatB_under_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : headLotSeatB cF.blocksInOrder Zp G = true :=
  head_lotSeatB_at_head h hG (head_fits_at_ground h hG)

/-- CONDITIONAL. **What the door asks of the list, at each row of the lot, over the description's
first chain**: the lot lays a row; at each row's place a member of the first chain's list stands;
and every member there has the declared rounds and no oracle message: the premise of `head_good_row`
and of `head_bud_share` (Honest/K6/Law/RowsIn.lean): under the one hypothesis, at the ground that
the description's maker lays. (The letter r in the end is a row of the lot; the r in h is the run.)
-/
theorem head_lot_members_under_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    (weights : W₀ → Weights) :
    (headSLotAt (Rc := Rc) (X := X) cells weights).rows Zp G ≠ [] ∧
    ∀ r ∈ (headSLotAt (Rc := Rc) (X := X) cells weights).rows Zp G,
      (cF.blocksInOrder.any fun b => b.place == r.place) = true ∧
      ∀ b ∈ cF.blocksInOrder, b.place = r.place →
        b.rounds = (headParAt G).rounds ∧ b.oracles = (headParAt G).rounds.map fun _ => [] := by
  obtain ⟨hn, ha⟩ := (headLotSeatB_iff (Rc := Rc) (X := X) cF.blocksInOrder cells weights Zp G).1
    (head_lotSeatB_under_head h hG)
  refine ⟨hn, fun r hr => ?_⟩
  obtain ⟨hs, hm⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 ha r hr)
  exact ⟨hm, members_at_of_seatB hs⟩

/-- CONDITIONAL. That the test says yes, with the ground named by "there is". -/
theorem head_lotSeatB_some (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧ headLotSeatB cF.blocksInOrder Zp G = true := by
  obtain ⟨G, hG⟩ := head_ground_at_head h
  exact ⟨G, hG, head_lotSeatB_under_head h hG⟩

/-- CONDITIONAL. **`Good` at each row of the lot, over the description's first chain**, at whatever
falls, at A := False and whatever B, at the row's own On and bud: under the one hypothesis and the
Bool on the book. `plays` and `acc` ARE MET FOR NOTHING THERE; `fresh` HOLDS BY AN EMPTY LIST. (The
letter r in the end is a row of the lot; the r in h is the run.) `pre` is a free letter: the term
stands at every `pre`. -/
theorem head_good_lot_under_head {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (cells : Tr → Cells) (weights : W₀ → Weights) (fs₀ : List (Fall P5J.TS)) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → P5J.TS → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨IM.k6Place, i⟩) = true) :
    (headSLotAt (Rc := Rc) (X := X) cells weights).rows Zp G ≠ [] ∧
    ∀ r ∈ (headSLotAt (Rc := Rc) (X := X) cells weights).rows Zp G,
      ∃ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ ∧
        Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) B r.On r.bud :=
  head_good_lot_at_head φ h hG (head_fits_at_ground h hG) cells weights fs₀ Bk ord chain firstTree
    B hB

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_fits_at_ground
#print axioms ProofFile.Honest.K6.head_lot_under_head
#print axioms ProofFile.Honest.K6.head_lotSeatB_under_head
#print axioms ProofFile.Honest.K6.head_lot_members_under_head
#print axioms ProofFile.Honest.K6.head_lotSeatB_some
#print axioms ProofFile.Honest.K6.head_good_lot_under_head
