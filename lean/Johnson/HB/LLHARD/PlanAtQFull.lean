-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/PlanAtQFull.lean: the named tests on the list of what the proof file's first chain
sends, at the places of the kind K1 and at the index masks' message, as closed facts on written
values.

The tests: `planIndexSeatB`, `planIndexCodeB` (Johnson/Desc/K13/Law/PlanTestsM3.lean);
`planIndexLastB`, `planPlacesB`, `planTreesB`, `planShapesB`
(Johnson/Desc/K13/Law/PlanTestsM4.lean).

The arguments, one by one: the written term, and what ties it to what a verifier computes.
  L, M: `LFull`, `MFull` (Johnson/HB/LLHARD/LaidWritten.lean): the layout and the shapes of the
    written list of sendings. Tie: `laid_at`, `msgs_at` there, from the codes
    (`first_codes_in_scope`) and the list of sendings (`sends_in_scope`): green.
  cs: `codesFull2` (Johnson/G/PackLit.lean). Tie: `first_codes_in_scope`: green.
  P': the places `firstPar`, `parLater`, `parW` of K1 at the placeholder `qFull`
    (Johnson/Desc/K1/Law/QFull.lean) and `gpFull` := one answer to each out-of-domain (OOD) sample,
    first tree 0. Tie: `firstPar_full` and its kin there, from three equations of `first_in_scope`;
    `par_one_in_scope`: green.
  N: NO WRITTEN TERM. The tests read four things of it: `index`, `indexNo`, `msgsAt p`, `treesAt p`.
    Each statement here is at a letter N under equations on these numbers. `index` = (1, 0) has a
    tie (`N0Full_seats`, Johnson/P5T/PlanSeatsFull.lean). THE OTHER THREE ARE TIED BY NOTHING YET:
    they are laid off what the sub-protocols tell, of which no written list lies.

    (Where this and lean/THEOREM.md differ, the page holds.) The numerals come
    from a program of a reader of ours over the written sendings, under the reading that a
    sub-protocol tells just the layout of the sendings at its place. So no statement here has a form
    in scope yet.

Definitions.
  `gpFull`. `wMsgFull`: what goes out with W at the written linear shape.
  `goesOnB L M m t P'`: the three tests `planPlacesB`, `planTreesB`, `planShapesB` with the numbers
    m (messages in front) and t (trees in front) in the place of N's.
  `laterFull`: for the fifty later sendings of the 25 segments: segment, piece, moment, messages in
    front, trees in front.
Statements.
  `wMsg_written`: `wMsgFull` is no fall-back.
  `goesOn_gives`: a yes of `goesOnB` at N's two numbers gives a yes of the three tests.
  `indexSeat_written`, `indexCode_written`, `indexLast_written`.
  `first_goes_on`, `w_goes_on`, `later_go_on`: `goesOnB` at the first segment's opening (0, 0), at
    W's sending (197, 82), and at all fifty. `first_written`, `w_written`, `later_written`: so the
    three tests there, at a letter N.
Negative tests: `indexSeat_rejects` (the message's number one more), `indexCode_rejects` (an empty
table of codes), `indexLast_rejects`, `first_rejects` (one message in front), `w_rejects` (at the
list's end), `later_rejects` (the first of the fifty with one message more in front).
By evaluations in Lean's kernel (`decide +kernel`): all but `goesOn_gives` and the three that call
it.

Limits. Closed facts on written values. Nothing on soundness.
-/
import Johnson.HB.LLHARD.LaidWritten
import Johnson.Desc.K13.Law.PlanTestsM3
import Johnson.Desc.K13.Law.PlanTestsM4
import Johnson.Desc.K1.Law.QFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params Johnson.G _root_.Desc.Plain
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K12.Door (Laid toTree)
open VerifiableInference.Desc.K1 (qFull firstPar parLater parW)

/-- One answer to each OOD sample; the chain's first tree is number 0. -/
def gpFull : GPar := ⟨1, 0⟩

/-- What goes out with W, at the written linear shape. -/
def wMsgFull : Array OracleNotice := (linMessageW qFull.lin).getD #[]

/-- It is no fall-back. -/
theorem wMsg_written : linMessageW qFull.lin = some wMsgFull := by
  have h : (linMessageW qFull.lin).isSome = true := by decide +kernel
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h
  unfold wMsgFull
  rw [hm]
  rfl

/-- The three tests "the lists go on with this sending", at plain numbers. -/
def goesOnB (L : Laid) (M : List OracleShape) (m t : ℕ) (P' : K1.Par) : Bool :=
  decide (((toTree L).places.drop m).take P'.sent.size =
      K12.Coin.placesOf t P'.sent.size (K1.layOf P')) &&
    decide (((toTree L).shapes.drop t).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList) &&
    decide ((M.drop m).take (K1.shapesOf P').length = K1.shapesOf P')

/-- A yes at N's two numbers gives a yes of the three tests. -/
theorem goesOn_gives {L : Laid} {M : List OracleShape} {m t : ℕ} {P' : K1.Par} {N : Numbers}
    {p : Option Place} (hm : N.msgsAt p = m) (ht : N.treesAt p = t)
    (h : goesOnB L M m t P' = true) :
    planPlacesB L N p P' = true ∧ planTreesB L N p P' = true ∧ planShapesB M N p P' = true := by
  unfold goesOnB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  unfold planPlacesB planTreesB planShapesB
  rw [hm, ht]
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## The index masks' message -/

theorem indexSeat_written {N : Numbers} (hi : N.index = (1, 0)) (hn : N.indexNo = 4) :
    planIndexSeatB LFull N = true := by
  unfold planIndexSeatB
  rw [hi, hn]
  decide +kernel

theorem indexSeat_rejects {N : Numbers} (hi : N.index = (1, 0)) (hn : N.indexNo = 5) :
    planIndexSeatB LFull N = false := by
  unfold planIndexSeatB
  rw [hi, hn]
  decide +kernel

theorem indexCode_written {N : Numbers} (hn : N.indexNo = 4) :
    planIndexCodeB MFull codesFull2 N = true := by
  unfold planIndexCodeB
  rw [hn]
  decide +kernel

theorem indexCode_rejects {N : Numbers} (hn : N.indexNo = 4) :
    planIndexCodeB MFull {} N = false := by
  unfold planIndexCodeB
  rw [hn]
  decide +kernel

theorem indexLast_written {N : Numbers} (hn : N.indexNo = 4) :
    planIndexLastB N (firstPar qFull gpFull) = true := by
  unfold planIndexLastB
  rw [hn]
  decide +kernel

theorem indexLast_rejects {N : Numbers} (hn : N.indexNo = 5) :
    planIndexLastB N (firstPar qFull gpFull) = false := by
  unfold planIndexLastB
  rw [hn]
  decide +kernel

/-! ## The first segment's opening, and W's sending -/

theorem first_goes_on : goesOnB LFull MFull 0 0 (firstPar qFull gpFull) = true := by
  decide +kernel

theorem first_rejects : goesOnB LFull MFull 1 0 (firstPar qFull gpFull) = false := by
  decide +kernel

theorem first_written {N : Numbers} {p : Option Place} (hm : N.msgsAt p = 0)
    (ht : N.treesAt p = 0) :
    planPlacesB LFull N p (firstPar qFull gpFull) = true ∧
      planTreesB LFull N p (firstPar qFull gpFull) = true ∧
      planShapesB MFull N p (firstPar qFull gpFull) = true :=
  goesOn_gives hm ht first_goes_on

theorem w_goes_on : goesOnB LFull MFull 197 82 (parW qFull gpFull 4 wMsgFull) = true := by
  decide +kernel

theorem w_rejects : goesOnB LFull MFull 199 83 (parW qFull gpFull 4 wMsgFull) = false := by
  decide +kernel

theorem w_written {N : Numbers} {p : Option Place} (hm : N.msgsAt p = 197)
    (ht : N.treesAt p = 82) :
    planPlacesB LFull N p (parW qFull gpFull 4 wMsgFull) = true ∧
      planTreesB LFull N p (parW qFull gpFull 4 wMsgFull) = true ∧
      planShapesB MFull N p (parW qFull gpFull 4 wMsgFull) = true :=
  goesOn_gives hm ht w_goes_on

/-! ## The fifty later sendings -/

/-- Segment, piece, moment, messages in front, trees in front. -/
def laterFull : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(0, 4, 1, 5, 2), (0, 6, 2, 6, 3), (1, 4, 1, 12, 5), (1, 6, 2, 13, 6), (2, 4, 1, 20, 8),
   (2, 6, 2, 21, 9), (3, 4, 1, 27, 11), (3, 6, 2, 28, 12), (4, 4, 1, 35, 14), (4, 6, 2, 36, 15),
   (5, 4, 1, 42, 17), (5, 6, 2, 43, 18), (6, 4, 1, 50, 20), (6, 6, 2, 51, 21), (7, 4, 1, 57, 23),
   (7, 6, 2, 58, 24), (8, 4, 1, 65, 26), (8, 6, 2, 66, 27), (9, 4, 1, 72, 29), (9, 6, 2, 73, 30),
   (10, 4, 1, 80, 32), (10, 6, 2, 81, 33), (11, 4, 1, 87, 35), (11, 6, 2, 88, 36),
   (12, 4, 1, 95, 38), (12, 6, 2, 96, 39), (13, 4, 1, 102, 41), (13, 6, 2, 103, 42),
   (14, 4, 1, 110, 44), (14, 6, 2, 111, 45), (15, 4, 1, 117, 47), (15, 6, 2, 118, 48),
   (16, 4, 1, 125, 50), (16, 6, 2, 126, 51), (17, 4, 1, 132, 53), (17, 6, 2, 133, 54),
   (18, 4, 1, 140, 56), (18, 6, 2, 141, 57), (19, 4, 1, 147, 59), (19, 6, 2, 148, 60),
   (20, 4, 1, 155, 62), (20, 6, 2, 156, 63), (21, 4, 1, 162, 65), (21, 6, 2, 163, 66),
   (22, 4, 1, 170, 68), (22, 6, 2, 171, 69), (23, 4, 1, 177, 71), (23, 6, 2, 178, 72),
   (24, 5, 1, 183, 74), (24, 7, 2, 184, 75)]

set_option maxRecDepth 100000 in
theorem later_go_on : (laterFull.all fun x =>
    goesOnB LFull MFull x.2.2.2.1 x.2.2.2.2 (parLater qFull gpFull x.1 x.2.1 x.2.2.1)) = true := by
  decide +kernel

theorem later_count : laterFull.length = 50 := by decide +kernel

theorem later_rejects : goesOnB LFull MFull 6 2 (parLater qFull gpFull 0 4 1) = false := by
  decide +kernel

theorem later_written {x : ℕ × ℕ × ℕ × ℕ × ℕ} (hx : x ∈ laterFull) {N : Numbers}
    {p : Option Place} (hm : N.msgsAt p = x.2.2.2.1) (ht : N.treesAt p = x.2.2.2.2) :
    planPlacesB LFull N p (parLater qFull gpFull x.1 x.2.1 x.2.2.1) = true ∧
      planTreesB LFull N p (parLater qFull gpFull x.1 x.2.1 x.2.2.1) = true ∧
      planShapesB MFull N p (parLater qFull gpFull x.1 x.2.1 x.2.2.1) = true :=
  goesOn_gives hm ht (List.all_eq_true.1 later_go_on x hx)

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.wMsg_written
#print axioms VerifiableInference.Desc.K13.Law.goesOn_gives
#print axioms VerifiableInference.Desc.K13.Law.indexSeat_written
#print axioms VerifiableInference.Desc.K13.Law.indexSeat_rejects
#print axioms VerifiableInference.Desc.K13.Law.indexCode_written
#print axioms VerifiableInference.Desc.K13.Law.indexCode_rejects
#print axioms VerifiableInference.Desc.K13.Law.indexLast_written
#print axioms VerifiableInference.Desc.K13.Law.indexLast_rejects
#print axioms VerifiableInference.Desc.K13.Law.first_goes_on
#print axioms VerifiableInference.Desc.K13.Law.first_rejects
#print axioms VerifiableInference.Desc.K13.Law.first_written
#print axioms VerifiableInference.Desc.K13.Law.w_goes_on
#print axioms VerifiableInference.Desc.K13.Law.w_rejects
#print axioms VerifiableInference.Desc.K13.Law.w_written
#print axioms VerifiableInference.Desc.K13.Law.later_go_on
#print axioms VerifiableInference.Desc.K13.Law.later_count
#print axioms VerifiableInference.Desc.K13.Law.later_rejects
#print axioms VerifiableInference.Desc.K13.Law.later_written
