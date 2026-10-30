-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/BaseAt.lean: CONDITIONAL: at the full size the public part's
table of steps counts, in front of the step "A‹g›.2.scores", just the rounds that the first chain's
flat list has in front of its member number 14 (2 g + 1) + 4: the member at an attention segment's
own rounds (kind K5). So the number `base` that the maker of a place's public data lays (`seatAt`,
Honest/K5/Row.lean) is the number of rounds in front of that member.

The road. Both counts are held against written tables that lie in the library, and the two written
tables are held against one written number, 2966 + 3857 g, by Lean's kernel.
  The table of steps: under the hypothesis the first chain's declared entries are the written ones
  (`written354_of_pins`, Johnson/Loose/H2K12/ClosedOfPins354.lean), so the table is the written one
  (`cuts_of_plans`, Johnson/Desc/First/Att/Row/K5FrontOne.lean); what the count reads of it:
  `roundsBefore_by` (Johnson/Desc/First/Att/Row/K5RowTwins.lean).
  The flat list: under the hypothesis its rows (name, place, numbers of rounds and of lists of
  oracle messages, what is told, what lies before) are the written ones (`pins_at_head`,
  Johnson/Desc/First/Att/Door/Law/K5CondOfHead.lean).

  `stepsAllB`, `steps_closed`, `steps_bite`   the written table of steps: the count at the twelve
                  names; the test says no at another number
  `flatAllB`, `flat_closed`, `flat_bite`      the written rows: the sum of the numbers of rounds in
                  front of the twelve members; the test says no at another number
  `roundsTo_cut`  GENERAL: the rounds in front of a border, off a list's rows
  `base_at_head`  CONDITIONAL: **the count at the name is the number of rounds in front of the
                  member**
  `hbase_at`      CONDITIONAL: so `seatAt`'s `base` at the name "A‹g›" is that number

Limits. At the full size and the written tables alone. The hypothesis `P5J.AtMgA` is not shown here:
where it cannot be met `base_at_head` says nothing. The two closed facts are facts on written
tables: that any public files give these tables is the hypothesis's matter.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatedAt
import Johnson.Desc.First.Att.Row.K5FrontOne
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.Loose.H2K12.ClosedOfPins354

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.PlanWritten (cutOf cutFirstFull pubBy_entries)
open H2K5.Row (roundsBy cutPairsW roundsBefore_by cuts_of_plans asBy)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 Two closed facts on written tables -/

/-- The test: the written table of steps counts `want g` rounds in front of "A‹g›.2.scores". -/
def stepsAllB (want : Nat → Nat) : Bool :=
  (List.range 12).all fun g =>
    decide (roundsBy cutPairsW ("A" ++ toString g ++ ".2.scores") = some (want g))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written table of steps, at the twelve names.** No premise: a closed fact, by the kernel.
-/
theorem steps_closed : stepsAllB (fun g => 2966 + 3857 * g) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no. No premise: a closed fact, by the kernel. -/
theorem steps_bite : stepsAllB (fun g => 2967 + 3857 * g) = false := by decide +kernel

/-- The test: the written rows have `want g` rounds in front of the row number 14 (2 g + 1) + 4. -/
def flatAllB (want : Nat → Nat) : Bool :=
  (List.range 12).all fun g =>
    decide (((cutFirstFull.take (14 * (2 * g + 1) + 4)).map (·.2.2.1)).sum = want g)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written rows, in front of the twelve members.** No premise: a closed fact, by the kernel.
-/
theorem flat_closed : flatAllB (fun g => 2966 + 3857 * g) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no. No premise: a closed fact, by the kernel. -/
theorem flat_bite : flatAllB (fun g => 2967 + 3857 * g) = false := by decide +kernel

/-! ## 2 The rounds in front of a border, off a list's rows -/

/-- The rounds in front of a border are the sum of the rows' numbers of rounds. General in the list.
No premise. -/
theorem roundsTo_cut {S Cl : Type} (bs : List (Block S Cl)) (b : Nat) :
    roundsTo bs b = (((cutOf bs).take b).map (·.2.2.1)).sum := by
  unfold roundsTo declsTo cutOf
  rw [List.length_flatMap, ← List.map_take, List.map_map]
  rfl

/-! ## 3 Under the hypothesis -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **THE TABLE OF STEPS COUNTS, IN FRONT OF "A‹g›.2.scores", THE ROUNDS IN FRONT OF THE KIND's
MEMBER OF GROUP g.** CONDITIONAL: under the hypothesis h, which is not shown here; g is below 12. -/
theorem base_at_head {g : Nat} (hg : g < 12) :
    Zp.roundsBefore? ("A" ++ toString g ++ ".2.scores") =
      some (roundsTo cF.blocksInOrder (borderOf g)) := by
  obtain ⟨hm, hc⟩ := H2K5.Door.pins_at_head h.toAtMg
  have W := H2K12.written354_of_pins h.scope h.laid.pub hm h.laid.laidPOf
  have hZ := asBy h.laid.pub
  have hcuts := cuts_of_plans hZ ((pubBy_entries hZ).1.symm.trans W.entries)
  have e1 := of_decide_eq_true (List.all_eq_true.1 steps_closed g (List.mem_range.2 hg))
  have e2 := of_decide_eq_true (List.all_eq_true.1 flat_closed g (List.mem_range.2 hg))
  rw [roundsBefore_by, hcuts, roundsTo_cut, hc]
  exact e1.trans (congrArg some e2.symm)

/-- **The number `base` that the maker of the place's public data lays is the number of rounds in
front of the member.** CONDITIONAL: under the hypothesis h; g is below 12; the maker has yielded Z5
at the name "A‹g›". -/
theorem hbase_at {g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground} {l : Nat}
    {Z5 : Seat5} (hY : seatAt keyOf Zp G l ("A" ++ toString g) g = some Z5) :
    Z5.base = roundsTo cF.blocksInOrder (borderOf g) := by
  obtain ⟨A, base, -, hb, rfl, -, -⟩ := seatAt_spec hY
  exact Option.some.inj (hb.symm.trans (base_at_head h hg))

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.steps_closed
#print axioms ProofFile.Honest.K5.steps_bite
#print axioms ProofFile.Honest.K5.flat_closed
#print axioms ProofFile.Honest.K5.flat_bite
#print axioms ProofFile.Honest.K5.roundsTo_cut
#print axioms ProofFile.Honest.K5.base_at_head
#print axioms ProofFile.Honest.K5.hbase_at
