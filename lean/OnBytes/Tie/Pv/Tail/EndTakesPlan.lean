-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndTakesPlan.lean: the planner's lookup lays rounds with the very names of the
entries that the verifier's lookup uses up.

Theorems with their proofs, by the laws of OnBytes/Tie/Pv/Req/Names.lean (`Says x N`: wherever the
planner's routine x ends well it has added rounds with just the names N).
OnBytes/Tie/Pv/Tail/EndTakes.lean says of the verifier's `Forest.pad` that it uses up entries with
the names `forestNames (forestSize h)`.

Main names:
  `says_times`, `says_treeLevels`, `says_line`, `says_zero`, `says_join`, `says_shift`: the
    planner's steps.
  `says_forest`: `planForest z` adds rounds with the names `forestNames z`.
  `laid_forest`: so what it has laid from an idle state has these names, and as many rounds.
  `meet`: the step at one place: a call that uses up entries with the names of the planner's rounds
    S, from a context whose entries begin with those of S, uses up just these and leaves the rest.

Limits: names alone.


-/
import OnBytes.Tie.Pv.Req.Names
import OnBytes.Tie.Pv.Tail.EndTakes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Used
open OnBytes OnBytes.Params OnBytes.Tie.Pv.Req
open OnBytes.Tie.Pv.Tail (reads_setting reads_needs)

/-- A routine, n times. -/
theorem says_times {x : Planning Unit} {N : List String} (h : Says x N) :
    ∀ n, Says (times n x) ((List.replicate n N).flatten)
  | 0 => says_pure ()
  | n + 1 => by
    unfold times
    rw [List.replicate_succ, List.flatten_cons]
    exact Says.bind h fun _ => says_times h n

/-- The planner's `planLine` adds rounds with just the names of the statement. -/
theorem says_line : Says planLine ["LINE"] :=
  Says.after (says_reads reads_setting) fun _ => says_close _ _ _ _

/-- The planner's `planZero` adds rounds with just the names of the statement. -/
theorem says_zero (v : Nat) : Says (planZero v) ["ZERO"] :=
  Says.after (says_reads reads_setting) fun _ => says_close _ _ _ _

/-- The planner's `planJoin` adds rounds with just the names of the statement. -/
theorem says_join (v : Nat) : Says (planJoin v) ["JOIN"] :=
  Says.after (says_reads reads_setting) fun _ => says_close _ _ _ _

/-- The planner's `planShift` adds rounds with just the names of the statement. -/
theorem says_shift (n : Nat) : Says (planShift n) ["LKP shift"] :=
  Says.after (says_reads reads_setting) fun _ => says_close _ _ _ _

/-- The levels of a product tree. -/
theorem says_treeLevels (more : Nat) : ∀ fuel l,
    Says (planTreeLevels more fuel l) ((List.range fuel).flatMap fun i => levelNames (l + i + more))
  | 0, _ => says_pure ()
  | fuel + 1, l => by
    unfold planTreeLevels
    have e : (List.range (fuel + 1)).flatMap (fun i => levelNames (l + i + more)) =
        pscNames (l + more) true ++ (["LINE"] ++
          (List.range fuel).flatMap fun i => levelNames (l + 1 + i + more)) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [levelNames, Nat.add_zero, List.append_assoc]
      congr 2
      refine List.flatMap_congr fun i _ => ?_
      have : l + (i + 1) + more = l + 1 + i + more := by omega
      simp only [Nat.succ_eq_add_one, this]
    rw [e]
    refine Says.bind ?_ fun _ => Says.bind says_line fun _ => says_treeLevels more fuel (l + 1)
    have h := says_psc { degree := List.replicate (l + more) 3 }
    simpa [pscNames] using h

/-- **The planner's lookup lays rounds with the names `forestNames z`.** -/
theorem says_forest (z : ForestSize) : Says (planForest z) (forestNames z) := by
  unfold planForest planLookup
  refine Says.after (says_reads reads_setting) fun s => ?_
  dsimp only
  refine Says.after (says_reads (reads_needs _ _)) fun _ => ?_
  refine Says.after (says_reads (reads_needs _ _)) fun _ => ?_
  have e31 : tieNames =
      pscNames 0 true ++ ((List.replicate 30 (pscNames 0 true)).flatten ++ []) := by
    decide
  have e : forestNames z = (if z.shifted = true then ["LKP shift"] else []) ++ (["LKP"] ++
      (pscNames 0 true ++ ((List.replicate 30 (pscNames 0 true)).flatten ++ ([] ++ (["JOIN"] ++
        ((List.range z.v).flatMap levelNames ++
          ((List.range z.d).flatMap (fun l => levelNames (5 + l)) ++
            (pscNames (5 + z.d) false ++ (["ZERO"] ++ pscNames (5 + z.d) true))))))))) := by
    unfold forestNames
    rw [e31]
    simp only [pscNames, List.append_assoc, List.nil_append, List.append_nil, List.cons_append,
      if_true, Bool.false_eq_true, if_false]
  rw [e]
  split
  case' isTrue => refine Says.bind (says_shift _) fun _ => ?_
  case' isFalse =>
    rw [List.nil_append]
    refine Says.after (says_pure _) fun _ => ?_
  all_goals
    refine Says.bind (says_close _ _ _ _) fun _ => ?_
    refine Says.bind (by simpa [pscNames] using says_psc { degreeY := 3, values := 3 }) fun _ => ?_
    refine Says.bind
      (says_times (by simpa [pscNames] using says_psc { degreeY := 3, values := 2 }) 30) fun _ => ?_
    refine Says.bind (says_times (N := pscNames 0 true) (by simpa [pscNames] using says_psc {}) 0)
      fun _ => ?_
    refine Says.bind (says_join 5) fun _ => ?_
    refine Says.bind ?_ fun _ => ?_
    · unfold forEach forEach planProductTree
      refine Says.before ?_ fun _ => says_pure ()
      simpa using says_treeLevels 0 z.v 0
    refine Says.bind ?_ fun _ => ?_
    · unfold planProductTree
      have h := says_treeLevels 5 z.d 0
      have e2 : (List.range z.d).flatMap (fun i => levelNames (0 + i + 5)) =
          (List.range z.d).flatMap fun l => levelNames (5 + l) :=
        List.flatMap_congr fun i _ => by rw [Nat.zero_add, Nat.add_comm]
      rwa [e2] at h
    refine Says.bind ?_ fun _ => ?_
    · have h := says_psc { degree := List.replicate z.d 3 ++ List.replicate 5 2, withY := false }
      simpa [pscNames, Nat.add_comm] using h
    refine Says.bind (says_zero _) fun _ => ?_
    have h := says_psc { degree := List.replicate (5 + z.d) 3, degreeY := 2, values := 1 }
    simpa [pscNames] using h

/-- What the planner's lookup has laid from an idle state has the names `forestNames z`. -/
theorem laid_forest {st : Setting} {z : ForestSize} {F : List PlanRound}
    (k : LaidIdle st (planForest z) F) :
    namesOf F = forestNames z ∧ F.length = (forestNames z).length := by
  have h := laidIdle_says (says_forest z) k
  exact ⟨h, by rw [← h, namesOf, List.length_map]⟩

/-- **The step at one place.** If the entries of c are those of the planner's rounds S and then of
rest, and a call from c to c' has used up entries with the names of S, then what it has used up are
the entries of S, and the entries of c' are those of rest. -/
theorem meet {N : List String} {c c' : Ctx} {S rest : List PlanRound} (h : TookN N c c')
    (hc : c.ch.entries = (S ++ rest).map (·.entry)) (hn : namesOf S = N) :
    c'.ch.entries = rest.map (·.entry) ∧ c.ch.entries.take N.length = S.map (·.entry) := by
  have hl : N.length = (S.map (·.entry)).length := by
    rw [← hn, namesOf, List.length_map, List.length_map]
  rw [List.map_append] at hc
  exact ⟨by rw [h.drop, hc, hl, List.drop_left], by rw [hc, hl, List.take_left]⟩

end OnBytes.Tie.Pv.Tail.Used

#print axioms OnBytes.Tie.Pv.Tail.Used.says_forest
#print axioms OnBytes.Tie.Pv.Tail.Used.laid_forest
#print axioms OnBytes.Tie.Pv.Tail.Used.meet
