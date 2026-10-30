-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecStage.lean: the honest side of the kind "lookup" (K3). One
stage of a course whose summand is a job of the specification, carried to the program's elements:
the stage's summand sums as `Sums` (Honest/K3/Law/Statements.lean) says, from the job's true sum to
the job's summand at the shown end values. Theorems, with one definition of a proposition and one
abbreviation.

Terms. Honest/K3/GLOSSARY.md ("course", "job, summand", "specification", "stage").

What is shown.
  `CarriedAt R s J`: at the stage's own points the course's three functions are the job's, carried.
  `split_last`, `up_getD`, `ups_addScale`, `padTo_self`: small facts on lists.
  `call_eq`, `poly_eq`, `ends_eq`, `shown_read`: what the stage's call, polynomials and end values
    are.
  `sums_stage_ends`: conditional on the job's law: a stage with end values.
  `sums_stage_open`: conditional on the job's law: a stage without.
  `T_read`: a stage's true end value, read, is the job's.
Others: `up_downs_getD`, `withPoints_len`, `shapeAt_eq`, `tail_eq`.

Hypotheses that remain. The job's law (`hlaw`); `CarriedAt` (`C`); every hypothesis on lengths is a
hypothesis here. By name, in the two results: `hc`, `he`: the stage's call is k, with the end values
e, or with none; `hsz`: `JobSized J`; `hv`: `VarsFit` at the call's variables with the stage's
points; `hlen`: as many challenges as variables (one more with end values); in `sums_stage_ends`
besides: `hdY`: the job's degree in Y is the call's; `hn`, `hm`: the job has, and the masks are, as
many as the call's end values. `hl`: (in `poly_eq`) as many variables as the job has points. `h`:
(in `split_last`, `padTo_self`) a length.

Users. This file is imported by Honest/K3/Law/SpecValues.lean.

Limits. For every job: nothing is said here of any job of the lookup, of what its true sum is, or of
the verifier's forms.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecSums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE addE mulE)
open OnBytes.Slice (readE readE_add readE_mul readE_zero)
open OnBytes.HonestTrace.Look (Job shownL)
open ProofFile.Honest.SumLaw (SumsTo jobPoly)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)

variable {W : Type}

/-- The points that a stage's job is given: made of the challenges in front of the stage. -/
abbrev _root_.ProofFile.Honest.K3.Law.Course.ptsAt (R : Course W) (s : Stage) : Pts :=
    ptsOf R.f R.a.base (R.front s).heard

/-- **At the stage's own points the course's three functions are the job's, carried.** -/
structure CarriedAt (R : Course W) (s : Stage) (J : Job KE) : Prop where
  round : ∀ rs, (R.J.job s).round R.t.input (R.ptsAt s) rs = downs (J.round (ups rs))
  inY : ∀ rs m, (R.J.job s).inY R.t.input (R.ptsAt s) rs m = downs (J.inY (ups rs) (ups m))
  ends : ∀ rs, (R.J.job s).ends R.t.input (R.ptsAt s) rs = downs (J.ends (ups rs))

/-! ## Small facts on lists -/

/-- A list of n + 1 entries is its first n and its last. -/
theorem split_last (l : List E) (n : Nat) (h : l.length = n + 1) :
    l = l.take n ++ [l.getLastD zeroE] := by
  have hne : l ≠ [] := by
    intro e
    rw [e] at h
    simp at h
  have e1 := List.dropLast_append_getLast hne
  rw [List.dropLast_eq_take, h, Nat.add_sub_cancel] at e1
  have e2 : l.getLastD zeroE = l.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  rw [e2]
  exact e1.symm

/-- Entry j of a list, read; 0 beyond its end. -/
theorem up_getD (l : List E) (j : Nat) : up (l.getD j zeroE) = (ups l).getD j 0 := by
  unfold ups
  rw [← readE_zero, List.getD_map]

/-- Entry j of a list that was carried down, read. -/
theorem up_downs_getD (l : List KE) (j : Nat) : up ((downs l).getD j zeroE) = l.getD j 0 := by
  rw [up_getD, ups_downs]

/-- End values as they are shown, read. -/
theorem ups_addScale (beta : E) : ∀ (v m : List E), v.length = m.length →
    ups (addL v (scaleL beta m)) = shownL (up beta) (ups v) (ups m)
  | [], [], _ => rfl
  | a :: v, b :: m, h => by
    have ih := ups_addScale beta v m (by simpa using h)
    show up (addE a (mulE beta b)) :: ups (addL v (scaleL beta m)) =
      (up a + up beta * up b) :: shownL (up beta) (ups v) (ups m)
    rw [ih]
    show readE (addE a (mulE beta b)) :: _ = _
    rw [readE_add, readE_mul]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A list of just n entries is not changed by the padding. -/
theorem padTo_self (n : Nat) (a : List E) (h : a.length = n) : padTo n a = a := by
  unfold padTo
  rw [h, Nat.sub_self, List.replicate_zero, List.append_nil, ← h, List.take_length]

/-! ## The stage's call and polynomials -/

/-- Writing points in keeps the number of variables. -/
theorem withPoints_len : ∀ (vs : List Var) (zs : List E), (withPoints vs zs).length = vs.length
  | [], _ => rfl
  | .plain _ :: vs, zs => by simp [withPoints, withPoints_len vs zs]
  | .point _ _ :: vs, _ :: zs => by simp [withPoints, withPoints_len vs zs]
  | .point _ _ :: vs, [] => by simp [withPoints, withPoints_len vs []]

/-- The shape at a stage that has a call. -/
theorem shapeAt_eq (R : Course W) (s : Stage) (k : Call) (hc : s.call R.f = some k) :
    shapeAt R.a s = k := by
  unfold shapeAt
  rw [show s.call R.a.face = some k from hc]
  rfl

/-- The stage's call as it stands in the run. -/
theorem call_eq (R : Course W) (s : Stage) (k : Call) (hc : s.call R.f = some k) :
    R.call s = { k with vs := withPoints k.vs (pointsAt R.f s (R.ptsAt s)) } := by
  show ({ shapeAt R.a s with
    vs := withPoints (shapeAt R.a s).vs (pointsAt R.f s (R.ptsAt s)) } : Call) = _
  rw [shapeAt_eq R s k hc]

/-- **The stage's polynomials are the carried job's.** -/
theorem poly_eq (R : Course W) (s : Stage) (k : Call) (J : Job KE) (hc : s.call R.f = some k)
    (C : CarriedAt R s J) (hl : k.vs.length = J.zs.length) :
    R.poly s = polyOf J (R.masks s) := by
  funext rs
  show (if rs.length < (shapeAt R.a s).vs.length
    then (R.J.job s).round R.t.input (R.ptsAt s) rs
    else (R.J.job s).inY R.t.input (R.ptsAt s) rs (R.masks s)) = _
  rw [shapeAt_eq R s k hc, hl, C.round, C.inY]
  rfl

/-- The stage's true end values are the carried job's. -/
theorem ends_eq (R : Course W) (s : Stage) (k : Call) (J : Job KE) (hc : s.call R.f = some k)
    (C : CarriedAt R s J) : R.ends s = downs (J.ends (ups ((R.r s).take k.vs.length))) := by
  show (R.J.job s).ends R.t.input (R.ptsAt s) ((R.r s).take (shapeAt R.a s).vs.length) = _
  rw [shapeAt_eq R s k hc, C.ends]

/-- **A stage's true end value, read, is the job's.** -/
theorem T_read (R : Course W) (s : Stage) (k : Call) (J : Job KE) (hc : s.call R.f = some k)
    (C : CarriedAt R s J) (j : Nat) :
    rd (R.T s j) = (J.ends (ups ((R.r s).take k.vs.length))).getD j 0 := by
  show up ((R.ends s).getD j zeroE) = _
  rw [ends_eq R s k J hc C, up_downs_getD]

/-- How many end values a stage with ends has. -/
theorem tail_eq (R : Course W) (s : Stage) (k : Call) (e : Ends) (hc : s.call R.f = some k)
    (he : k.ends = some e) : s.tail R.f = e.n := by
  unfold Stage.tail
  rw [hc]
  show ((k.ends).map (·.n)).getD 0 = e.n
  rw [he]
  rfl

/-- **The end values as they are shown, read.** -/
theorem shown_read (R : Course W) (s : Stage) (k : Call) (e : Ends) (J : Job KE)
    (hc : s.call R.f = some k) (he : k.ends = some e) (C : CarriedAt R s J)
    (hn : ∀ xs, (J.ends xs).length = e.n) (hm : (R.masks s).length = e.n) :
    ups (R.shown s) = shownL (up (R.beta s)) (J.ends (ups ((R.r s).take k.vs.length)))
      (ups (R.masks s)) := by
  have hE : (R.ends s).length = e.n := by
    rw [ends_eq R s k J hc C]
    unfold downs
    rw [List.length_map, hn]
  unfold Course.shown
  rw [tail_eq R s k e hc he, padTo_self _ _ hE, padTo_self _ _ hm,
    ups_addScale _ _ _ (by rw [hE, hm]), ends_eq R s k J hc C, ups_downs]

/-! ## The two results -/

/-- **Conditional on the job's law: a stage with end values** sums from the job's true sum to the
job's summand at the shown end values. Conditional besides on `CarriedAt`, `JobSized`, `VarsFit`,
the degree in Y and the lengths that the head lists. -/
theorem sums_stage_ends (R : Course W) (s : Stage) (k : Call) (e : Ends) (J : Job KE)
    (hc : s.call R.f = some k) (he : k.ends = some e) (C : CarriedAt R s J) (hlaw : J.Lawful)
    (hsz : JobSized J) (hdY : J.dY = some e.dY)
    (hv : VarsFit (withPoints k.vs (pointsAt R.f s (R.ptsAt s))) J)
    (hn : ∀ xs, (J.ends xs).length = e.n) (hlen : (R.r s).length = k.vs.length + 1)
    (hm : (R.masks s).length = e.n) :
    Sums R s J.sum (J.S0 (ups (R.shown s))) := by
  have hl : k.vs.length = J.zs.length := by rw [← hv.1, withPoints_len]
  have key := sums_ends J hlaw hsz e.dY hdY _ hv (R.masks s) ((R.r s).take k.vs.length)
    ((R.r s).getLastD zeroE) (by rw [List.length_take, hlen, ← hl]; omega) (by rw [hm, hn])
  rw [← split_last (R.r s) k.vs.length hlen] at key
  unfold Sums
  rw [call_eq R s k hc, poly_eq R s k J hc C hl, shown_read R s k e J hc he C hn hm]
  show SumsTo gl (match k.ends with
    | none => withPoints k.vs (pointsAt R.f s (R.ptsAt s))
    | some e => withPoints k.vs (pointsAt R.f s (R.ptsAt s)) ++ [.point zeroE (e.dY + 1)]) _ _ _ _ _
  rw [he]
  exact key

/-- **Conditional on the job's law: a stage without end values** sums from the job's true sum to the
job's summand at the point of its challenges. Conditional besides on `CarriedAt`, `JobSized`,
`VarsFit` and as many challenges as variables. -/
theorem sums_stage_open (R : Course W) (s : Stage) (k : Call) (J : Job KE)
    (hc : s.call R.f = some k)
    (he : k.ends = none) (C : CarriedAt R s J) (hlaw : J.Lawful) (hsz : JobSized J)
    (hv : VarsFit (withPoints k.vs (pointsAt R.f s (R.ptsAt s))) J)
    (hlen : (R.r s).length = k.vs.length) :
    Sums R s J.sum (J.fin (ups (R.r s))) := by
  have hl : k.vs.length = J.zs.length := by rw [← hv.1, withPoints_len]
  have key := sums_open J hlaw hsz _ hv (R.masks s) (R.r s) (by rw [hlen, hl])
  unfold Sums
  rw [call_eq R s k hc, poly_eq R s k J hc C hl]
  show SumsTo gl (match k.ends with
    | none => withPoints k.vs (pointsAt R.f s (R.ptsAt s))
    | some e => withPoints k.vs (pointsAt R.f s (R.ptsAt s)) ++ [.point zeroE (e.dY + 1)]) _ _ _ _ _
  rw [he]
  exact key

#print axioms ProofFile.Honest.K3.Law.Spec.withPoints_len
#print axioms ProofFile.Honest.K3.Law.Spec.call_eq
#print axioms ProofFile.Honest.K3.Law.Spec.poly_eq
#print axioms ProofFile.Honest.K3.Law.Spec.ends_eq
#print axioms ProofFile.Honest.K3.Law.Spec.T_read
#print axioms ProofFile.Honest.K3.Law.Spec.tail_eq
#print axioms ProofFile.Honest.K3.Law.Spec.shown_read
#print axioms ProofFile.Honest.K3.Law.Spec.sums_stage_ends
#print axioms ProofFile.Honest.K3.Law.Spec.sums_stage_open
#print axioms ProofFile.Honest.K3.Law.Spec.split_last
#print axioms ProofFile.Honest.K3.Law.Spec.up_getD
#print axioms ProofFile.Honest.K3.Law.Spec.up_downs_getD
#print axioms ProofFile.Honest.K3.Law.Spec.ups_addScale
#print axioms ProofFile.Honest.K3.Law.Spec.padTo_self
#print axioms ProofFile.Honest.K3.Law.Spec.shapeAt_eq

end ProofFile.Honest.K3.Law.Spec
