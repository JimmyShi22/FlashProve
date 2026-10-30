--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Shape/TestSeatAsksRecord.lean: THE ASKING IN FRONT OF A PROXIMITY TEST IN
ITS SEAT OF THE KEY FILE's FIRST CHAIN (`asksOnRecord`, Johnson/Desc/Key/Ranges.lean) RETURNS, FROM
THE GUARD ON THE SHAPE AND THE PLAN (`guardK12`, Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean)
AND THE THREE MARKS ALONE: no view, and no test on the values of the test's own rounds and columns.
(Of the three marks `claimsB` reads values of the open rows in front.) At the test's own structure.

What it is beside TestSeatAsks.lean. `seat_returns` there gives the same return as its first part,
and asks the library's test on the view and the test on values besides, which that part does not
spend. The proof here is that part's text, with the three facts that it took from `OneAsks` taken
from `guard_says`.

  ★ `asks_record_of_guard`   nothing is passed in front; the guard; the statement is tidy; the rows
      taken in have no written-out factor; the front's named test on the open rows: then
      `asksOnRecord p t = .ok ()`.
  `asks_record_KR`   the same at the closed place and the written shape of the full size.

By what. Calls: `guard_says`, `testSh_front`, `testFront_of`, `batOwes_of`, `frontOwes_of`,
`planFrom_of_ok`, `combineAt_of_order`, `layout_eq`, `layoutOf_own`; `guard_KR`, `pass_of_sh`
(TestSeatAsksAtKeyRanges.lean).

Limits. All limits of TestSeatAsks.lean on the guard and the marks stand: one tree at the first
stage; the mask has come; the three marks are premises. THE PROOF SPENDS FOUR OF THE GUARD's EIGHT
CLAUSES (the door's Bool; a mask is named; the plan's test, for the stages' equation alone; the
layout is the stage's): so a group in several trees is shut out here by the guard, not by the
proof. What the seat asks of the chain's own state is not here. Nothing on completeness, on
soundness or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Shape.TestSeatAsksAtKeyRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc.Key (asksOnRecord layoutIsStage behindBatching)
open Johnson.Prover.Link
open H2K.JointK (laidS)
open H2K.Member (piKRFull)

/-- ★ **THE SEAT's ASKING RETURNS, FROM THE GUARD AND THE THREE MARKS.** -/
theorem asks_record_of_guard {p : P12} {t : T12} (hpass : t.pass = .nothing)
    (hg : guardK12 p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) : asksOnRecord p t = .ok () := by
  obtain ⟨-, g2, ⟨id, hm, -⟩, -, g5, -, g7, -⟩ := guard_says hg
  have PF := planFrom_of_ok p _ _ _ _ _ g5
  have hst : p.nums.stages = curOf p :: nxtOf p :: p.nums.stages.drop 2 := PF.2.2.1
  have hD : doorB p (curOf p) (nxtOf p) (((H2K.JointK.laidOf p).take 1).map (·.1)) (idxOf p)
      ((nextOf p).code, (nextOf p).maskCode) (testSh t) = true := by
    rw [testSh_front hpass]
    exact g2
  unfold doorB at hD
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hD
  have h4' : (match t.mask with
    | some id => cameB (curOf p) (testSh t).core t.g (idxOf p) id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 hm h4' ht hp
  have B := batOwes_of h2 H.group
  have F := frontOwes_of h3 hv H.group
  have a1 : t.mask.isSome = true := by
    rw [hm]
    rfl
  have a4 : layoutIsStage (curOf p) (layoutOf t.st G) = true := by
    unfold seatLayB at g7
    have e : (coreSh ⟨t.st, t.book, t.roots⟩).st = stSh t.st := rfl
    rw [e, grp_get, H.group] at g7
    simp only [has, Option.map_some, Option.getD_some] at g7
    rw [layoutS_eq, layoutOf_own H.group] at g7
    exact g7
  have a5 : H2K.First.gpOk p (behindBatching t G (layoutOf t.st G)) = true := (B.gp {} rfl).1
  have a6 : H2K.First.labelsOk p (behindBatching t G (layoutOf t.st G)) = true := (B.gp {} rfl).2
  unfold asksOnRecord
  rw [H.group, layout_eq t.st t.g G H.group, hst]
  simp only [a1, F.pub, combineAt_of_order t.st t.g G H.group H.order, a4, a5, a6, need, bind,
    Except.bind, if_true]

/-- At the closed place and the written shape of the full size. -/
theorem asks_record_KR (t : T12) (hsh : testSh t = frontSh shKRFull 0 (some 2))
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) : asksOnRecord piKRFull t = .ok () := by
  have ec : coreSh ⟨t.st, t.book, t.roots⟩ = shKRFull := congrArg TestSh.core hsh
  have eg : t.g = 0 := congrArg TestSh.g hsh
  have em : t.mask = some 2 := congrArg TestSh.mask hsh
  exact asks_record_of_guard (pass_of_sh (congrArg TestSh.pass hsh))
    (by rw [ec, eg, em]; exact guard_KR) ht hp hv

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.asks_record_of_guard
#print axioms ProofFile.Honest.Sh.asks_record_KR
