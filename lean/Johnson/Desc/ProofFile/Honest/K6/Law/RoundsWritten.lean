-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RoundsWritten.lean: UNDER THE HYPOTHESIS h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean) THE FIRST CHAIN's DECLARED ROUNDS HAVE THE LIBRARY's WRITTEN ENTRIES, AND
EACH MEMBER OF ITS FLAT LIST HAS ITS PLACE AND ITS ROUNDS' ENTRIES AS WRITTEN VALUES: A ROW OF
`cutFirstFull` AND A SLICE OF `P5T.esFull.1`. At the four members of the output head's segment in
front of K6 (numbers 337 to 340, counted from 0) with the numerals. No definition; ten theorems.

What for. With a member's place and its rounds' entries as written values, whatever is a function of
these two alone is a closed fact at that member. Files on the honest side's book of coins, which are
not in the library, read of a sub-protocol its place, its rounds' names and the scalars in its
rounds' messages: such functions.

  `k6_entries_at_head`   (cF.blocksInOrder.flatMap (·.rounds)).map (·.entry) = P5T.esFull.1
  `k6_row_at_head`       member n's row of the written cut
  `k6_roundsIn_of_cut`   GENERAL: the rounds of the first n blocks (`roundsIn`,
                         Johnson/Desc/K14/Law/CutAt.lean), off the list's rows. A TWIN of
                         `k6_rounds_of_cut` (Honest/K6/Law/PointsAtHead.lean: not in the library,
                         nor are files beneath it), which says the like of the flatMap's length:
                         ONE FACT, TWICE
  `k6_member_entries`    member n's rounds' entries are a slice of the written list
  `k6_member_at`         the same with the row's place and number and the rounds in front as letters
  `k6_rows_closed`       A CLOSED FACT, BY LEAN's KERNEL: rows 337 to 341 and the rounds in front,
                         side by side. It is there to be looked at: no theorem of this file calls it
  `k6_entries_337` … `k6_entries_340`   the four members in front of K6: each closes its two
                         premises on the written rows by an evaluation of its own in the kernel

By. The library's `rounds_at` (Johnson/Desc/Sound/StretchTags.lean), `decl_of_planOk`
(Johnson/Desc/Sound/ReadsOkProofs.lean), `descPure_plans`, `pubBy_entries`
(Johnson/Goal/Numbers/PlanWrittenPlans.lean), `AtMg.plans_written` (Johnson/P5J/NumbersAtHead.lean),
`pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean).

Limits.
  * Of a round its entry alone: nothing on its stored parts or any other field.
  * h: the full size and the format's second hash function alone.
  * Public numbers alone: nothing on a coin, a value or a run.
  * THE NUMERALS REST ON NINE EVALUATIONS IN LEAN's KERNEL (`decide +kernel`) over the library's
    written rows: one in `k6_rows_closed`, two in each of the four. `maxRecDepth` is raised for
    `k6_rows_closed` alone, and once more in front of the four, from where it stays so to the file's
    end.
  * IT STANDS OVER THE LIBRARY ALONE. IT IMPORTS BY NAME TWO MODULES UNDER lean/Johnson/Goal/
    (Numbers/PlanWrittenPlans.lean, Skeleton/PinsOfLaid.lean) AND CALLS WHAT IS DECLARED THERE.
  * Nothing on any property.
-/
import Johnson.Desc.Sound.StretchTags
import Johnson.Desc.Sound.ReadsOkProofs
import Johnson.Goal.Numbers.PlanWrittenPlans
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.NumbersAtHead
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldRounds)
open _root_.Desc.K14.Law (roundsIn)
open OnBytes.Maker (WholeD)

/-- GENERAL: the rounds of the first n blocks, off the list's rows. -/
theorem k6_roundsIn_of_cut {S Cl : Type} : ∀ (bs : List (Block S Cl)) (n : Nat),
    roundsIn (bs.take n) = (((cutOf bs).take n).map (·.2.2.1)).sum
  | [], n => by simp [roundsIn, cutOf]
  | _ :: _, 0 => by simp [roundsIn]
  | b :: bs, n + 1 => by
    have ih := k6_roundsIn_of_cut bs n
    unfold roundsIn cutOf at ih ⊢
    simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
    rw [ih]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h. **The first chain's declared rounds have the written entries.**
-/
theorem k6_entries_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder.flatMap (·.rounds)).map (·.entry) = P5T.esFull.1 := by
  obtain ⟨Z', hZ', hpl⟩ := VerifiableInference.PlanWritten.descPure_plans h.laid.value
  obtain rfl : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  obtain ⟨e1, _, _⟩ := VerifiableInference.PlanWritten.pubBy_entries hZ'
  have hdec : (P5J.F0T OnBytes.secondHashFunction Z' Np cF).roundsDeclaredByBlocks = Z'.D :=
    (VerifiableInference.Desc.Sound.decl_of_planOk _ h.laid.planOk).trans hpl
  have h1 : cF.blocksInOrder.flatMap (·.rounds) = Z'.D.1 := congrArg Prod.fst hdec
  rw [h1, e1, h.toAtMg.plans_written]

/-- CONDITIONAL: h; hb. **Member n's row of the written cut.** -/
theorem k6_row_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {n : Nat}
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[n]? = some b) :
    cutFirstFull[n]? =
      some (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) := by
  have hc : cutOf cF.blocksInOrder = cutFirstFull := (P5J.pins_of_laid h.scope h.laid).2
  rw [← hc]
  unfold cutOf
  rw [List.getElem?_map, hb]
  rfl

/-- CONDITIONAL: h; hb. **Member n's rounds' entries are a slice of the written list.** -/
theorem k6_member_entries (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {n : Nat}
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[n]? = some b) :
    b.rounds.map (·.entry) =
      (P5T.esFull.1.drop ((cutFirstFull.take n).map (·.2.2.1)).sum).take b.rounds.length := by
  have hc : cutOf cF.blocksInOrder = cutFirstFull := (P5J.pins_of_laid h.scope h.laid).2
  have hr := VerifiableInference.Desc.K13.Law.rounds_at cF.blocksInOrder n b hb
  rw [← k6_entries_at_head h, ← hc, ← k6_roundsIn_of_cut, ← List.map_drop, ← List.map_take, hr]

/-- CONDITIONAL: h; hb; the two premises on the written rows. The same, with the row's place and
number of rounds and the rounds in front as letters. -/
theorem k6_member_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {n : Nat}
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[n]? = some b) {p : Place} {len pre : Nat}
    (hrow : (cutFirstFull[n]?.map fun y => (y.2.1, y.2.2.1)) = some (p, len))
    (hpre : ((cutFirstFull.take n).map (·.2.2.1)).sum = pre) :
    b.place = p ∧ b.rounds.map (·.entry) = (P5T.esFull.1.drop pre).take len := by
  rw [k6_row_at_head h hb] at hrow
  have e2 : (b.place, b.rounds.length) = (p, len) := Option.some.inj hrow
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
  exact ⟨rfl, by rw [k6_member_entries h hb, hpre]⟩

set_option maxRecDepth 100000 in
/-- **A closed fact at the library's written rows**: rows 337 to 341: the place, the number of
rounds, and the rounds in front. -/
theorem k6_rows_closed :
    ((List.range' 337 5).map fun n => (cutFirstFull[n]?.map fun y => (y.2.1, y.2.2.1),
      ((cutFirstFull.take n).map (·.2.2.1)).sum)) =
      [(some (⟨1, some 24, 0, .frame⟩, 0), 46286), (some (⟨1, some 24, 1, .K7⟩, 1), 46286),
       (some (⟨1, some 24, 2, .K2⟩, 2), 46287), (some (⟨1, some 24, 3, .K3⟩, 1080), 46289),
       (some (⟨1, some 24, 4, .K6⟩, 82), 47369)] := by
  decide +kernel

set_option maxRecDepth 100000

/-- CONDITIONAL: h; hb. Member 337, of the kind frame: no round. -/
theorem k6_entries_337 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[337]? = some b) :
    b.place = ⟨1, some 24, 0, .frame⟩ ∧
      b.rounds.map (·.entry) = (P5T.esFull.1.drop 46286).take 0 :=
  k6_member_at h hb (by decide +kernel) (by decide +kernel)

/-- CONDITIONAL: h; hb. Member 338, of the kind K7: one round. -/
theorem k6_entries_338 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[338]? = some b) :
    b.place = ⟨1, some 24, 1, .K7⟩ ∧
      b.rounds.map (·.entry) = (P5T.esFull.1.drop 46286).take 1 :=
  k6_member_at h hb (by decide +kernel) (by decide +kernel)

/-- CONDITIONAL: h; hb. Member 339, of the kind K2: two rounds. -/
theorem k6_entries_339 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[339]? = some b) :
    b.place = ⟨1, some 24, 2, .K2⟩ ∧
      b.rounds.map (·.entry) = (P5T.esFull.1.drop 46287).take 2 :=
  k6_member_at h hb (by decide +kernel) (by decide +kernel)

/-- CONDITIONAL: h; hb. **Member 340, of the kind K3: 1,080 rounds.** -/
theorem k6_entries_340 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[340]? = some b) :
    b.place = ⟨1, some 24, 3, .K3⟩ ∧
      b.rounds.map (·.entry) = (P5T.esFull.1.drop 46289).take 1080 :=
  k6_member_at h hb (by decide +kernel) (by decide +kernel)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_roundsIn_of_cut
#print axioms ProofFile.Honest.K6.k6_entries_at_head
#print axioms ProofFile.Honest.K6.k6_row_at_head
#print axioms ProofFile.Honest.K6.k6_member_entries
#print axioms ProofFile.Honest.K6.k6_member_at
#print axioms ProofFile.Honest.K6.k6_rows_closed
#print axioms ProofFile.Honest.K6.k6_entries_337
#print axioms ProofFile.Honest.K6.k6_entries_338
#print axioms ProofFile.Honest.K6.k6_entries_339
#print axioms ProofFile.Honest.K6.k6_entries_340
