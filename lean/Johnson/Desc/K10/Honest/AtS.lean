-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/AtS.lean: THE STEP OF THE CLOSING OF A SEGMENT SAYS YES, AT THE STATE THAT THE
FIRST CHAIN CARRIES, UNDER THREE WRAPPERS OF THE VERIFIER's: Johnson/Desc/K10/Honest/Step.lean's theorem
carried on from the kind's own record. Theorems on the verifier's own text. No definition of an honest
prover is used.

The kind's block is typed at a record of three things. Three wrappers stand around it in the first
chain. (1) It is lifted to the chain's own state (`K9.closing`, Johnson/Desc/First/Batch/Place.lean: it
reads the record by `recOf` and lays it back by `putRec`). (2) The makers of the proof file's
description wrap each member so that a mark of failure in the state behind refuses (`guardMark`,
Johnson/Desc/ProofFile/Frames1.lean). (3) The driver lays a guard over every block: a decision that
leaves another heard reply than it found is refused, but at the one place that hears it
(`Block.guarded`, Johnson/Desc/SeatGuard.lean, at `sameReply`, the seat's default, and `hearsReply`).

  `closing_step_of`   where `closeBaseB P (recOf t) = true` the lifted block's step says yes at t, at
                      every list of 2 + k rounds of the kind's shape and every list of columns; it
                      takes no column; the state behind is `putRec t r` for some record r
  `member_step_of`    the same of the block under (1) and (2), where t bears no mark
  `guarded_step_of`   the same under (1), (2) and (3)
  `Toy.member_steps`, `Toy.guarded_steps`   the two, called at a state made by `S.start` with
                      Johnson/Desc/First/Close/Law/CloseToys.lean's frame and statement laid in: A
                      STATE BETWEEN SEGMENTS (`Toy.tS`; `Toy.tS_member`: the test says yes there)
  `Toy.guarded_step_yes`   a second road: Lean's kernel evaluates the step under the three wrappers

Limits. The description's member is `guardMark` of the lifted block with its claims retyped and under
the place's name, and the driver writes the place anew (the block's own, by which it was found):
these turn no decision and no round (Johnson/Desc/Block.lean), which is not shown here. In a segment
the lifted block stands joined with others (`joint`, `closeOf`, Place.lean; a block of the kind
"frame" that the description's makers may join behind it, Frames1.lean): not spoken of. That the first
chain lays just these wrappers, in this order, is read, not shown. NO MEMBER INSIDE AN OPEN SEGMENT,
where a run's closing stands and `recOf` and `putRec` go through the segment's own copy of the frame:
the theorems are general in the state; the toy's state is between segments. The file's tests on the
plan, which the verifier asks first (`planOk`, `shaped`, `before`: Johnson/Desc/Block.lean,
`FileDescription.planOk`), are not spoken of. Whether the state that an honest run leaves meets the test is
not said. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Step
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.Close.Law.Leaves
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.SeatGuard
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)

/-- **The lifted block's step says yes.** -/
theorem closing_step_of {Cl : Type} {P : Par} {t : S} (h : closeBaseB P (K9.recOf t) = true)
    (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) :
    ∃ r, (K9.closing (Cl := Cl) P).step ft t rs cols = .ok (K9.putRec t r, 0) := by
  obtain ⟨r, hr⟩ := close_yes_of (Cl := Cl) h (rs.map noDigest) [] (by rw [List.length_map, hl])
    (shapedAll_noDigest hs)
  have g : groupsOf ft (K9.closing (Cl := Cl) P).rounds (rs.map (·.drawn)) = [] :=
    groups_nil ft (entries P) _
  have f : roundsFit (K9.closing (Cl := Cl) P).rounds rs = true := rounds_fit (Cl := Cl) P rs hl hs
  have d : (K9.closing (Cl := Cl) P).decide t (rs.map noDigest) [] = .ok (K9.putRec t r) := by
    show (((kind (Cl := Cl)) P).decide (K9.recOf t) (rs.map noDigest) []).map (K9.putRec t) = _
    rw [hr]
    rfl
  refine ⟨r, ?_⟩
  unfold Block.step
  rw [f, g]
  show ((K9.closing (Cl := Cl) P).decide t (rs.map noDigest) []).bind _ = _
  rw [d]
  rfl

/-- **The wrapped block's step says yes, where the state bears no mark.** -/
theorem member_step_of {P : Par} {t : S} (h : closeBaseB P (K9.recOf t) = true)
    (hm : t.failed = none) (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hl : rs.length = 2 + P.k) (hs : ShapedAll rs) :
    ∃ r, (ProofFile.guardMark (K9.closing P)).step ft t rs cols = .ok (K9.putRec t r, 0) := by
  obtain ⟨r, hr⟩ := close_yes_of (Cl := ProofFile.Cl) h (rs.map noDigest) []
    (by rw [List.length_map, hl]) (shapedAll_noDigest hs)
  have g : groupsOf ft (ProofFile.guardMark (K9.closing P)).rounds (rs.map (·.drawn)) = [] :=
    groups_nil ft (entries P) _
  have f : roundsFit (ProofFile.guardMark (K9.closing P)).rounds rs = true :=
    rounds_fit (Cl := ProofFile.Cl) P rs hl hs
  have d0 : (K9.closing (Cl := ProofFile.Cl) P).decide t (rs.map noDigest) [] = .ok (K9.putRec t r) := by
    show (((kind (Cl := ProofFile.Cl)) P).decide (K9.recOf t) (rs.map noDigest) []).map (K9.putRec t) = _
    rw [hr]
    rfl
  have hk : (K9.putRec t r).failed = none := (putRec_keeps t r).2.2.1.trans hm
  have d : (ProofFile.guardMark (K9.closing P)).decide t (rs.map noDigest) [] = .ok (K9.putRec t r) := by
    show ((K9.closing (Cl := ProofFile.Cl) P).decide t (rs.map noDigest) []).bind _ = _
    rw [d0]
    show (match (K9.putRec t r).failed with
      | none => Except.ok (K9.putRec t r)
      | some m => .error ("marked: " ++ m)) = _
    rw [hk]
  refine ⟨r, ?_⟩
  unfold Block.step
  rw [f, g]
  show ((ProofFile.guardMark (K9.closing P)).decide t (rs.map noDigest) []).bind _ = _
  rw [d]
  rfl

/-- **The same under the driver's guard on the heard reply.** -/
theorem guarded_step_of {P : Par} {t : S} (h : closeBaseB P (K9.recOf t) = true)
    (hm : t.failed = none) (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hl : rs.length = 2 + P.k) (hs : ShapedAll rs) :
    ∃ r, ((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply First.hearsReply).step ft t rs cols =
      .ok (K9.putRec t r, 0) := by
  obtain ⟨r, hr⟩ := member_step_of h hm ft rs cols hl hs
  obtain ⟨rs', gs', hd⟩ : ∃ rs' gs', rs' = rs.map noDigest ∧
      gs' = ([] : List (List (Nat × List UInt64))) ∧
      (ProofFile.guardMark (K9.closing P)).decide t rs' gs' = .ok (K9.putRec t r) := by
    refine ⟨_, _, rfl, rfl, ?_⟩
    have g : groupsOf ft (ProofFile.guardMark (K9.closing P)).rounds (rs.map (·.drawn)) = [] :=
      groups_nil ft (entries P) _
    have f : roundsFit (ProofFile.guardMark (K9.closing P)).rounds rs = true :=
      rounds_fit (Cl := ProofFile.Cl) P rs hl hs
    unfold Block.step at hr
    rw [f, g] at hr
    obtain ⟨u, hu, hv⟩ := ok_bind (show ((ProofFile.guardMark (K9.closing P)).decide t (rs.map noDigest)
      []).bind _ = _ from hr)
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
    rw [← hv.1]
    exact hu
  obtain ⟨rfl, rfl, hd⟩ := hd
  have hsame : ProofFile.sameReply t (K9.putRec t r) = true := by
    unfold ProofFile.sameReply
    rw [(putRec_keeps t r).2.2.2.1]
    exact beq_self_eq_true _
  have d : ((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply First.hearsReply).decide t
      (rs.map noDigest) [] = .ok (K9.putRec t r) := by
    show (if First.hearsReply (ProofFile.guardMark (K9.closing P)).place then
        (ProofFile.guardMark (K9.closing P)).decide t (rs.map noDigest) [] else
      ((ProofFile.guardMark (K9.closing P)).decide t (rs.map noDigest) []).bind
        (seatSame ProofFile.sameReply t)) = _
    have hp : First.hearsReply (ProofFile.guardMark (K9.closing P)).place = false := rfl
    rw [hp, if_neg (by decide), hd]
    show seatSame ProofFile.sameReply t (K9.putRec t r) = _
    unfold seatSame
    rw [if_pos hsame]
  have g : groupsOf ft ((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply
      First.hearsReply).rounds (rs.map (·.drawn)) = [] := groups_nil ft (entries P) _
  have f : roundsFit ((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply
      First.hearsReply).rounds rs = true := rounds_fit (Cl := ProofFile.Cl) P rs hl hs
  refine ⟨r, ?_⟩
  unfold Block.step
  rw [f, g]
  show (((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply First.hearsReply).decide t
    (rs.map noDigest) []).bind _ = _
  rw [d]
  rfl

namespace Toy

/-- A state of the first chain, BETWEEN SEGMENTS, with the toy's frame and statement: no mark. -/
def tS : S := { S.start default { frame := MeansToys.fr, rows := ⟨default⟩ } with st := MeansToys.S0 }

theorem tS_member : closeBaseB P (K9.recOf tS) = true := by decide +kernel

/-- `member_step_of`, called. -/
theorem member_steps (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 4)
    (hs : ShapedAll rs) :
    ∃ r, (ProofFile.guardMark (K9.closing P)).step ft tS rs cols = .ok (K9.putRec tS r, 0) :=
  member_step_of tS_member rfl ft rs cols hl hs

/-- `guarded_step_of`, called. -/
theorem guarded_steps (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hl : rs.length = 4)
    (hs : ShapedAll rs) :
    ∃ r, ((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply First.hearsReply).step ft tS rs cols =
      .ok (K9.putRec tS r, 0) :=
  guarded_step_of tS_member rfl ft rs cols hl hs

/-- A second road to one such yes, and to "no column": Lean's kernel evaluates the step of the block
under the three wrappers itself at the toy's rounds. -/
theorem guarded_step_yes :
    (((ProofFile.guardMark (K9.closing P)).guarded ProofFile.sameReply First.hearsReply).step 0 tS MeansToys.rs0
      []).toOption.map (·.2) = some 0 := by
  decide +kernel

end Toy

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closing_step_of
#print axioms ProofFile.Honest.K10.YesFree.member_step_of
#print axioms ProofFile.Honest.K10.YesFree.guarded_step_of
#print axioms ProofFile.Honest.K10.YesFree.Toy.tS_member
#print axioms ProofFile.Honest.K10.YesFree.Toy.member_steps
#print axioms ProofFile.Honest.K10.YesFree.Toy.guarded_steps
#print axioms ProofFile.Honest.K10.YesFree.Toy.guarded_step_yes
