-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Mark.lean: A MARK ON THE SHARED CHAIN's STATEMENT, AND: WHERE THE PLAN HAS
TWO CODES, WHAT GOES OUT WITH o_u CAN BE SAID AND THE TWO SENDINGS PASS THEIR OWN TEST ON THE PLAN,
EACH OF THE LINEAR CLAIM's EIGHT SUB-PROTOCOLS KEEPS IT: wherever its step returns .ok at a marked
statement, the statement behind is marked. Statements with their proofs. Its statements and proofs
name nothing of the other files of this folder.

What for. The front of a proximity test asks of all constraints that lie open on its group that each
could be laid now (Johnson/Desc/Ground/Ask.lean: openClaimsE). A shape that holds no summand of a
constraint cannot say that. Johnson/Desc/Ground/Shape/Claims.lean has a mark for it, kept by the
ground's functions; the admitting keeps it at a tidy statement
(Johnson/Desc/Ground/Shape/ClaimsMarks.lean). So what the eight carry is the two together.

Main names:
  Marked, markB, markB_iff   **the mark**: the statement is tidy (Johnson/Desc/Means/Walk.lean:
                      Tidy), and Claims.lean's claimsAtB is true at every group: six of the adding's
                      eight clauses, of every constraint that lies open. markB: the same with code.
                      It is MEANT as a reader for laws: a run on shapes would ask the mark and hand
                      it on, and never compute it. Nothing here but markB_iff names markB: the laws
                      speak of Marked, and no run on shapes of this folder (End.lean: upTo;
                      Comp.lean: compRun) asks a mark
  MarkStay, groundQuiet_mark   the eight functions of the ground that ask nothing of their caller
                      keep it: the library's form GroundQuiet (Johnson/Desc/GroundQuiet.lean), from
                      its groundQuiet_tidy (Johnson/Desc/Tidy/Stay.lean) and Claims.lean's laws
  admitOn_mark        the admitting keeps it: the library's form K1.AdmitOn, from its admitOn_tidy
                      and ClaimsMarks.lean's admit_claims_tidy
  marked_first        the chain's first state is marked: no message, no group
  send_mark           a sending at this chain's state keeps it, at two rounds that fit and no
                      column, at a plan that passes the sending's own test, AND WHERE WHAT IS DONE
                      BEHIND THE SENDING KEEPS IT (the premise hb, on the function «behind» that the
                      sending is handed): by the library's sendAt_yes and K1.decideSend_rel
  stepMarks           **WHEREVER THE STEP OF ONE OF THE EIGHT RETURNS .ok AT A MARKED STATEMENT, THE
                      STATEMENT BEHIND IS MARKED**, under the premises on the plan that are named
                      below: by the library's linPoint_rel, …, split_rel
                      (Johnson/Desc/K14/Quiet.lean). That file's blocks_steps gives the like in one
                      call under each sub-protocol's WHOLE test on the plan; here less is asked: the
                      sendings' own test (planOkOwn)
  open_of_marked      what comes out for a proximity test's front: at a marked statement, at a group
                      that is there and of which no test has begun, openClaimsE returns .ok

What is assumed, as premises, at stepMarks: what goes out with o_u can be said (withU P.S = some
sentU); two codes; the two sendings' test on the plan (planOkOwn at both); Eight P; and the mark in
front. Nothing on a round or a column, and of the state the mark alone. Eight P holds the eight AT
THE KIND's OWN TYPE OF CLAIMS; a proof file's IOP as written in Lean holds them carried to another
type (Johnson/Desc/K14/Honest/StepsBack.lean says so at Eight), so a caller at the IOP carries the
steps across first (the library's laws for that: Johnson/Desc/K14/Honest/FlatSteps.lean: Like.step,
step_retype).

What the mark reads. VALUES: the heads of Claims.lean and of Johnson/Desc/Ground/Shape/Marks.lean
say where. That markB's type is Bool says nothing on that.

What is not claimed. THE MEMBERS' SAMPLE CONSTRAINTS ARE UNDER THE MARK ONLY AS FAR AS Tidy SPEAKS
OF THEM. That no constraint of this kind has a written-out factor
(Johnson/Desc/Ground/Shape/Marks.lean: stPlainB) is not shown. That a proximity test keeps the mark.
Nothing on soundness, on completeness or on hiding.
-/
import Johnson.Desc.Ground.Shape.ClaimsMarks
import Johnson.Desc.K14.Honest.StepsBack
import Johnson.Desc.K14.Quiet
import Johnson.Desc.Key.Laid.Laid2
import Johnson.Desc.Tidy.Stay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Tidy)
open VerifiableInference.Desc (OpenedColumn roundsFit K1.AdmitOn K1.decideSend_rel)
open VerifiableInference.Desc.Ground (GroundQuiet groundQuiet_tidy admitOn_tidy openClaimsE)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K1 (planOkOwn)
open VerifiableInference.Desc.Key.LaidW (sendAt_yes)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (Eight)

/-- The statement is tidy, and the mark of Claims.lean is true at every group. -/
def Marked (S : Statement) : Prop := Tidy S ∧ ∀ g, claimsAtB S g = true

/-- **The mark, with code.** Meant as a reader for laws: a run on shapes would ask the mark and hand
it on, and never compute it. Nothing here but markB_iff names it. -/
def markB (S : Statement) : Bool :=
  stTidyB S && (List.range S.groups.size).all (claimsAtB S)

/-- What the mark says. -/
theorem markB_iff {S : Statement} : markB S = true ↔ Marked S := by
  unfold markB Marked
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨tidy_of h1, fun g => ?_⟩
    by_cases hg : g < S.groups.size
    · exact h2 g (List.mem_range.2 hg)
    · refine claimsAt_iff.2 fun G hG => ?_
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hg)] at hG
      cases hG
  · rintro ⟨h1, h2⟩
    exact ⟨tidy_mark h1, fun g _ => h2 g⟩

/-- If the statement in front is marked, so is the statement behind. -/
def MarkStay (A B : Statement) : Prop := Marked A → Marked B

/-- **The eight functions of the ground that ask nothing of their caller keep it.** -/
theorem groundQuiet_mark : GroundQuiet MarkStay where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun d d' a b n h m =>
    ⟨groundQuiet_tidy.newGroup d d' a b n h m.1,
      fun g => newGroup_claims d d' a b n h g (m.2 g)⟩
  recv := fun ft d d' s i h m =>
    ⟨groundQuiet_tidy.recv ft d d' s i h m.1,
      fun g => recv_claims ft d d' s i h g (m.2 g)⟩
  join := fun d d' a o k h m =>
    ⟨groundQuiet_tidy.join d d' a o k h m.1,
      fun g => join_claims d d' a o k h g (m.2 g)⟩
  addRow := fun d d' a r h m =>
    ⟨groundQuiet_tidy.addRow d d' a r h m.1,
      fun g => addRow_claims d d' a r h g (m.2 g)⟩
  takeMask := fun d d' o n h m =>
    ⟨groundQuiet_tidy.takeMask d d' o n h m.1,
      fun g => takeMask_claims d d' o n h g (m.2 g)⟩
  closeLedger := fun d d' o h m =>
    ⟨groundQuiet_tidy.closeLedger d d' o h m.1,
      fun g => closeLedger_claims d d' o h g (m.2 g)⟩
  spendAsMask := fun d d' o h m =>
    ⟨groundQuiet_tidy.spendAsMask d d' o h m.1,
      fun g => spend_claims d d' o h g (m.2 g)⟩
  adopt := fun d d' s gv i h m =>
    ⟨groundQuiet_tidy.adopt d d' s gv i h m.1,
      fun g => adopt_claims d d' s gv i h g (m.2 g)⟩

/-- **The admitting keeps it**, where the constraints handed in are on the message. -/
theorem admitOn_mark : K1.AdmitOn MarkStay :=
  fun d d' o rows h hr m =>
    ⟨admitOn_tidy d d' o rows h hr m.1,
      fun g => admit_claims_tidy d d' o rows h (tidy_mark m.1) g (m.2 g)⟩

/-- At the first state: no message, no group. -/
theorem marked_first (codes : Codes) (key : TableKey) : Marked (first codes key).st :=
  ⟨Tidy.start codes, fun g => claims_start codes #[] g⟩

variable {P : P14} {sentU : Array OracleNotice}

/-- A sending at this chain's state keeps it: at two rounds that fit (hfit) and no column, at a plan
that passes the sending's own test (hB: planOkOwn), and where what is done behind the sending keeps
it (hb: whatever the function «behind» returns, MarkStay holds from its argument to its return). -/
theorem send_mark (n : String) (Q : VerifiableInference.Desc.K1.Par) (f : Option Fmt.Entry)
    (g : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → MarkStay d.st d'.st) (hB : planOkOwn Q = true)
    (d d' : St) (ra rb : Fmt.RoundView)
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds Q) [ra, rb] = true)
    (h : (sendAt P n Q f g behind).decide d [ra, rb] [] = .ok d') : MarkStay d.st d'.st := by
  obtain ⟨ids, x, hx, hn⟩ := sendAt_yes P n Q f g behind d d' _ _ h
  exact groundQuiet_mark.trans
    (K1.decideSend_rel groundQuiet_mark admitOn_mark Q none _ x ra rb ids hB hfit hx)
    (hb _ _ _ hn)

/-- **WHEREVER THE STEP OF ONE OF THE EIGHT RETURNS .ok AT A MARKED STATEMENT (hm), THE STATEMENT
BEHIND IS MARKED**, under five premises on the plan. hU: what goes out with o_u can be said (withU
P.S = some sentU). hS: two codes. hBU, hBO: the two sendings pass their kind's own test on the plan
(planOkOwn). B: the kind's text makes its eight at P (Eight P), at the kind's own type of claims.
Nothing is asked of a round or a column, and of the state the mark alone. -/
theorem stepMarks (hU : withU P.S = some sentU) (hS : P.S.sharedSplitNeeded = true)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (B : Eight P)
    (ft : Nat) (d d' : St) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (hm : Marked d.st) :
    (B.b1.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b2.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b3.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b4.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b5.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b6.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b7.step ft d rs c = .ok (d', n) → Marked d'.st) ∧
    (B.b8.step ft d rs c = .ok (d', n) → Marked d'.st) := by
  have H := groundQuiet_mark
  obtain ⟨_, ⟨n2, f2, g2, e2⟩, n5, f5, g5, e5⟩ := B.fronts hU
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, _, _, k, _⟩ := B.back1 hU ft d d' rs c n h
    exact linPoint_rel H _ d d' _ k hm
  · obtain ⟨Ra, Rb, _, _, hf, k⟩ := B.back2 hU ft d d' rs c n h
    rw [e2] at k
    exact send_mark n2 _ f2 g2 _ (fun a ids a' q => behindU_rel H _ a a' ids q) hBU d d' _ _ hf k hm
  · obtain ⟨_, _, k⟩ := B.back3 hU ft d d' rs c n h
    exact laysRec_rel H _ d d' _ k hm
  · obtain ⟨R, _, _, _, _, k⟩ := B.back4 hU ft d d' rs c n h
    exact loc_rel H _ d d' _ _ k hm
  · obtain ⟨Ra, Rb, _, _, hf, k⟩ := B.back5 hU ft d d' rs c n h
    rw [e5] at k
    exact send_mark n5 _ f5 g5 _ (fun a ids a' q => behindOmega_rel H _ a a' ids q) hBO d d' _ _ hf
      k hm
  · obtain ⟨_, _, k⟩ := B.back6 hU ft d d' rs c n h
    exact joins_rel H _ d d' _ k hm
  · obtain ⟨R, _, _, k, _⟩ := B.back7 hU ft d d' rs c n h
    exact linZeta_rel H d d' _ k hm
  · obtain ⟨R, _, _, k⟩ := B.back8 hU hS ft d d' rs c n h
    exact split_rel H _ d d' _ k hm

/-- **What comes out for a proximity test's front**: at a marked statement, at a group that is there
and of which no test has begun, the front's question on all constraints that lie open returns. Of
the mark the second half alone is spent (claimsAtB); Tidy is idle here. -/
theorem open_of_marked {S : Statement} (hm : Marked S) {g : Nat} {G : Group}
    (hG : S.groups[g]? = some G) (hrun : G.inRun = false) : openClaimsE S g = .ok () :=
  open_of_claims hG hrun (hm.2 g)

end Desc.K14.Shape

#print axioms Desc.K14.Shape.markB_iff
#print axioms Desc.K14.Shape.groundQuiet_mark
#print axioms Desc.K14.Shape.admitOn_mark
#print axioms Desc.K14.Shape.marked_first
#print axioms Desc.K14.Shape.send_mark
#print axioms Desc.K14.Shape.stepMarks
#print axioms Desc.K14.Shape.open_of_marked
