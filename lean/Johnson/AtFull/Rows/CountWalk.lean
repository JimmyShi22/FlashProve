-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CountWalk.lean: THE PLANNER's COUNT OF SCALARS (`Params.scalarsOf`,
OnBytes/Params/Gate.lean) OF ROUTINES LAID ONE BEHIND THE OTHER, TAKEN PIECE BY PIECE. Definitions
and theorems. A law file; no running text imports it. Nothing on codes.

Why. `scalarsOf` runs a routine whole and then reads all the rounds that it has written. Put before
Lean's kernel so, at an arm's routine, it was dear (the figures: Johnson/AtFull/Rows/ArmCount.lean);
why, was not looked into. Here each piece is run from a plan without rounds; only a sum and the
plan's four small fields are handed on to the next piece.

  `seqP xs`: the routines of a list, one behind the other. `seqP_append`, `seqP_one`,
    `forEach_seqP`, `frP_seqP`.
  `fieldBytes`, `sentBytes`: A SECOND TEXT of `scalarsOf`'s term for one message, and its sum over a
    list of rounds. `scalars_of_walk` ties it to `scalarsOf`.
  `bareAt s q`: the plan q without its rounds, at the setting s.
  `walkS s st xs`: the walk, with code. It returns the sum and the last plan, or nothing where a
    piece refuses.
  `walkS_runs`: what a «some» of the walk says of `seqP xs`, if each piece reads no round (`FrP`,
    Johnson/AtFull/Rows/FrameP.lean) and the walk starts at the setting s, from a plan without
    rounds.
  `scalars_of_walk`: if each piece reads no round, a «some» of the walk from the empty plan gives
    `scalarsOf`'s value.

Limits. No closed fact is here. A conditional on a «some»: of a walk that returns nothing, nothing
is said. Nothing on what a round means. Nothing on soundness.

-/
import Johnson.AtFull.Rows.FrameP
import OnBytes.Params.Gate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Rows
open OnBytes OnBytes.Params VerifiableInference.Desc.LinkJoin

/-- The routines of a list, one behind the other. -/
def seqP : List (Planning Unit) → Planning Unit
  | [] => pure ()
  | x :: xs => x >>= fun _ => seqP xs

theorem seqP_append : ∀ (a b : List (Planning Unit)), seqP (a ++ b) = seqP a >>= fun _ => seqP b
  | [], b => by
    simp only [List.nil_append, seqP, pure_bind]
  | x :: a, b => by
    simp only [List.cons_append, seqP, bind_assoc, seqP_append a b]

theorem seqP_one (x : Planning Unit) : seqP [x] = x := by
  simp only [seqP, bind_pure_unit]

/-- The planner's own loop over a list is `seqP` of the list's routines. -/
theorem forEach_seqP {γ : Type} (f : γ → Planning Unit) :
    ∀ l : List γ, forEach l f = seqP (l.map f)
  | [] => by
    unfold forEach
    rfl
  | a :: t => by
    conv => lhs; unfold forEach
    rw [forEach_seqP f t]
    rfl

/-- Pieces that read no round, laid one behind the other, read no round. -/
theorem frP_seqP : ∀ xs : List (Planning Unit), (∀ y ∈ xs, FrP y) → FrP (seqP xs)
  | [], _ => by
    unfold seqP
    exact frP_pure _
  | x :: xs, h => by
    unfold seqP
    exact frP_bind (h x (by simp)) fun _ => frP_seqP xs fun y hy => h y (by simp [hy])

/-- Of a message's bytes, those that are neither roots nor sample answers: a second text of
`scalarsOf`'s term. -/
def fieldBytes (msg roots answers : Nat) : Nat := msg - 32 * roots - 24 * answers

/-- The sum of that term over a list of rounds. -/
def sentBytes (l : List PlanRound) : Nat :=
  l.foldl (fun n r => n + fieldBytes r.entry.msg r.entry.roots r.entry.answers) 0

theorem foldl_add_from {β : Type} (g : β → Nat) : ∀ (l : List β) (a : Nat),
    l.foldl (fun n r => n + g r) a = a + l.foldl (fun n r => n + g r) 0
  | [], a => by
    simp only [List.foldl_nil, Nat.add_zero]
  | x :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_add_from g l (a + g x), foldl_add_from g l (0 + g x)]
    omega

theorem sentBytes_append (a b : List PlanRound) :
    sentBytes (a ++ b) = sentBytes a + sentBytes b := by
  unfold sentBytes
  rw [List.foldl_append, foldl_add_from]

/-- The plan q without its rounds, at the setting s. -/
def bareAt (s : Setting) (q : PlanState) : PlanState :=
  { set := s, scope := q.scope, openBytes := q.openBytes, openRoots := q.openRoots,
    openAnswers := q.openAnswers }

theorem under_bareAt {s : Setting} {q : PlanState} (h : q.set = s) :
    under q.rounds (bareAt s q) = q := by
  subst h
  cases q
  simp only [under, bareAt, Array.append_empty]

theorem under_empty (p : PlanState) : under #[] p = p := by
  cases p
  simp only [under, Array.empty_append]

theorem under_under (R R' : Array PlanRound) (p : PlanState) :
    under R (under R' p) = under (R ++ R') p := by
  simp only [under, Array.append_assoc]

/-- The walk: each piece is run from a plan without rounds; the sum of `sentBytes` over what it has
written is handed on, and the plan without these rounds. Nothing where a piece refuses. -/
def walkS (s : Setting) : Nat × PlanState → List (Planning Unit) → Option (Nat × PlanState)
  | st, [] => some st
  | st, y :: ys =>
    match y.run st.2 with
    | .error _ => none
    | .ok (_, q) => walkS s (st.1 + sentBytes q.rounds.toList, bareAt s q) ys

/-- **What a «some» of the walk says of the pieces laid one behind the other.** -/
theorem walkS_runs {s : Setting} : ∀ (xs : List (Planning Unit)), (∀ y ∈ xs, FrP y) →
    ∀ st st' : Nat × PlanState, st.2.set = s → st.2.rounds = #[] → walkS s st xs = some st' →
      ∃ rs, (seqP xs).run st.2 = .ok ((), under rs st'.2) ∧ st'.1 = st.1 + sentBytes rs.toList ∧
        st'.2.rounds = #[]
  | [], _, st, st', _, hr, h => by
    unfold walkS at h
    cases h
    refine ⟨#[], ?_, rfl, hr⟩
    rw [under_empty]
    unfold seqP
    rfl
  | y :: ys, hf, st, st', hs, _, h => by
    unfold walkS at h
    cases e : y.run st.2 with
    | error m =>
      rw [e] at h
      cases h
    | ok r =>
      obtain ⟨u, q⟩ := r
      rw [e] at h
      dsimp only at h
      have hq : q.set = s := ((hf y (by simp)) _ _ _ e).1.trans hs
      have hys : ∀ z ∈ ys, FrP z := fun z hz => hf z (by simp [hz])
      obtain ⟨rs', h1, h2, h3⟩ :=
        walkS_runs (s := s) ys hys (st.1 + sentBytes q.rounds.toList, bareAt s q) st' rfl rfl h
      have g := ((frP_seqP ys hys) _ _ _ h1).2 q.rounds
      rw [under_bareAt hq, under_under] at g
      refine ⟨q.rounds ++ rs', ?_, ?_, h3⟩
      · show (y >>= fun _ => seqP ys).run st.2 = _
        rw [StateT.run_bind, e]
        exact g
      · rw [h2, Array.toList_append, sentBytes_append]
        show st.1 + sentBytes q.rounds.toList + sentBytes rs'.toList = _
        omega

/-- **If each piece reads no round, a «some» of the walk from the empty plan gives the planner's
count.** -/
theorem scalars_of_walk {s : Setting} {xs : List (Planning Unit)} (hf : ∀ y ∈ xs, FrP y) {m : Nat}
    {p : PlanState} (h : walkS s (0, { set := s }) xs = some (m, p)) :
    scalarsOf s (seqP xs) = .ok ((m + fieldBytes p.openBytes p.openRoots p.openAnswers) / 24) := by
  obtain ⟨rs, h1, h2, h3⟩ := walkS_runs (s := s) xs hf (0, { set := s }) (m, p) rfl rfl h
  have h1' : seqP xs { set := s } = .ok ((), under rs p) := h1
  have h3' : p.rounds = #[] := h3
  have e1 : (under rs p).rounds = rs := by
    show rs ++ p.rounds = rs
    rw [h3', Array.append_empty]
  have h2' : m = 0 + sentBytes rs.toList := h2
  rw [Nat.zero_add] at h2'
  unfold scalarsOf
  rw [h1']
  show (Except.ok (((under rs p).rounds.foldl
    (fun n r => n + (r.entry.msg - 32 * r.entry.roots - 24 * r.entry.answers)) 0 +
      (p.openBytes - 32 * p.openRoots - 24 * p.openAnswers)) / 24) : Except String Nat) = _
  rw [e1, ← Array.foldl_toList, h2']
  rfl

end AtFull.Rows

#print axioms AtFull.Rows.seqP_append
#print axioms AtFull.Rows.seqP_one
#print axioms AtFull.Rows.forEach_seqP
#print axioms AtFull.Rows.frP_seqP
#print axioms AtFull.Rows.foldl_add_from
#print axioms AtFull.Rows.sentBytes_append
#print axioms AtFull.Rows.under_bareAt
#print axioms AtFull.Rows.under_empty
#print axioms AtFull.Rows.under_under
#print axioms AtFull.Rows.walkS_runs
#print axioms AtFull.Rows.scalars_of_walk
