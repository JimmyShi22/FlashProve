-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Cut/Run.lean: a block's run on a view, cut at the border between two routines.

The program decides a chain by one run of the chain's block on a view (`Blk.runOn`,
OnBytes/Iop/Ground.lean). A law on one routine of such a block speaks of the two contexts between
which the routine ran, and of the rounds of the view that lie between them (`Took c rvs c'`,
OnBytes/Tie/Pv/Psc/PscView.lean). This file goes from the yes of the whole run to these contexts and
rounds. Nothing here stands under "there is" without the equation that gives it: a block is a
function of the context, so the context between two routines is what the first returns.

  `start s v`: the context from which `Blk.runOn` runs a block.
  `Ended c`: what `Blk.runOn` asks of the context that the block leaves.
  `runOn_iff`: `b.runOn s v` gives a exactly if the codes' lengths are admitted, b returns a from
    `start s v`, and the context that it leaves has ended.
  `runOn_bind_iff`: the same for `b >>= f`: b returns a and c1 from `start s v`, and `f a` returns
    from c1.
  `used c c'`, `usedColumns c c'`: the rounds, and the opened columns, that c still has and c' has
    not: as many from the front as the lists differ in length.
  `Took.eq_used`: the rounds of a `Took` are `used`: so they are a function of the two contexts.
  `took_of_suffix`: between two contexts of a run on a view with no message open, of which the
    second's rounds are an end piece of the first's, `used` was taken.
  `took_whole`: what was taken from `start s v` to a context that has ended is all the view's
    rounds.
  `cut_bind`: so where `(b >>= f).runOn s v` gives a value: whatever was taken by b and by `f a`,
    laid end to end, is the view's list of rounds.
  `Along c steps`, `Along.took`, `along_whole`: the same along a list of stretches, each with the
    context at its end.
  `trace`, `foldlM_trace`: for a block that folds a routine over a list: the values and contexts
    behind each step, as a function of the routine, the list and the beginning.
What is not claimed. That the rounds which a routine leaves are an end piece of those that it found,
and that no message is open at a border: these are premises here. A routine's border need not be a
round's border; where a message is open between two routines no `Took` can be said, and this file
says nothing of the rounds there. Nothing on what a routine tests.
-/
import OnBytes.Tie.Pv.Psc.PscView

set_option autoImplicit false

namespace OnBytes.Cut

open OnBytes
open OnBytes.PscRun (Clean Took)

/-- The context from which `Blk.runOn` runs a block: the record of `Blk.runNamed` at a run that is
not dry, the view's rounds and its opened columns. -/
def start (s : Start) (v : Fmt.View) : Ctx :=
  { ch := { dry := false, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
            left := v.rounds, opened := v.opened },
    st := s.st, book := s.book, keepNotes := false }

/-- What `Blk.runOn` asks of the context that the block leaves: no named test has failed; the plan's
entries are used up and the last round's question is answered; nothing of the view is left. -/
structure Ended (c : Ctx) : Prop where
  clean : c.failed = none
  plan_used : (c.ch.entries.isEmpty && c.ch.settled) = true
  view_used : (c.ch.cur.isNone && c.ch.opened.isEmpty && c.ch.left.isEmpty) = true

/-- A run on a whole view gives a value exactly if the block returns it from `start s v` and the
context that it leaves has ended. -/
theorem runOn_iff {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) (a : α) :
    b.runOn s v = .ok a ↔
      s.st.codes.lengthsOk = true ∧ ∃ c', b (start s v) = .ok (a, c') ∧ Ended c' := by
  unfold Blk.runOn Blk.runNamed
  constructor
  · intro h
    split at h
    · cases h
    · rename_i a' c' hr
      split at hr
      · rename_i hcodes
        split at h
        · cases h
        · rename_i hf
          split at h
          · cases h
          · rename_i hplan
            split at h
            · rename_i hview
              cases h
              refine ⟨hcodes, c', hr, hf, ?_, hview⟩
              cases hP : (c'.ch.entries.isEmpty && c'.ch.settled) with
              | true => rfl
              | false =>
                rw [hP] at hplan
                exact absurd rfl hplan
            · cases h
      · cases hr
  · rintro ⟨hcodes, c', hr, hf, hplan, hview⟩
    rw [if_pos hcodes]
    unfold start at hr
    rw [hr]
    simp only [hf, hplan, hview, Bool.not_true, Bool.false_eq_true, if_false, if_true]

/-- The same for two routines, one behind the other. -/
theorem runOn_bind_iff {α β : Type} (b : Blk α) (f : α → Blk β) (s : Start) (v : Fmt.View)
    (e : β) :
    (b >>= f).runOn s v = .ok e ↔
      s.st.codes.lengthsOk = true ∧
        ∃ a c1 c2, b (start s v) = .ok (a, c1) ∧ f a c1 = .ok (e, c2) ∧ Ended c2 := by
  rw [runOn_iff]
  constructor
  · rintro ⟨hc, c2, hr, he⟩
    obtain ⟨a, c1, h1, h2⟩ := (PscRun.bindB_ok b f _ _).1 hr
    exact ⟨hc, a, c1, c2, h1, h2, he⟩
  · rintro ⟨hc, a, c1, c2, h1, h2, he⟩
    exact ⟨hc, c2, (PscRun.bindB_ok b f _ _).2 ⟨a, c1, h1, h2⟩, he⟩

/-- The rounds that c still has and c' has not. -/
def used (c c' : Ctx) : List Fmt.RoundView := c.ch.left.take (c.ch.left.length - c'.ch.left.length)

/-- The opened columns that c still has and c' has not. -/
def usedColumns (c c' : Ctx) : List (Nat × Nat × List UInt64) :=
  c.ch.opened.take (c.ch.opened.length - c'.ch.opened.length)

/-- The rounds of a `Took` are a function of its two contexts. -/
theorem Took.eq_used {c c' : Ctx} {l : List Fmt.RoundView} (h : Took c l c') : l = used c c' := by
  unfold used
  rw [h.2.2, List.length_append, Nat.add_sub_cancel, List.take_left']
  rfl

/-- Between two contexts with no message open, of which the second's rounds are an end piece of the
first's. -/
theorem took_of_suffix {c c' : Ctx} (hc : Clean c) (hc' : Clean c')
    (h : c'.ch.left <:+ c.ch.left) : Took c (used c c') c' := by
  obtain ⟨l, hl⟩ := h
  refine ⟨hc, hc', ?_⟩
  unfold used
  rw [← hl, List.length_append, Nat.add_sub_cancel, List.take_left']
  rfl

/-- No message is open at the start of a run on a view. -/
theorem start_clean (s : Start) (v : Fmt.View) : Clean (start s v) := ⟨rfl, rfl⟩

/-- What was taken from the start to a context that has ended is all the view's rounds. -/
theorem took_whole {s : Start} {v : Fmt.View} {l : List Fmt.RoundView} {c' : Ctx}
    (h : Took (start s v) l c') (he : Ended c') : l = v.rounds := by
  have hv := he.view_used
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hv
  have h2 : v.rounds = l ++ c'.ch.left := h.2.2
  rw [h2, hv.2, List.append_nil]

/-- **The cut at a border.** Where the run of `b >>= f` on a view gives a value: b has returned a
and c1 from the start, `f a` has returned from c1 and has left a context that has ended; and
whatever was taken by the one and by the other, laid end to end, is the view's list of rounds. -/
theorem cut_bind {α β : Type} {b : Blk α} {f : α → Blk β} {s : Start} {v : Fmt.View} {e : β}
    (h : (b >>= f).runOn s v = .ok e) :
    ∃ a c1 c2, b (start s v) = .ok (a, c1) ∧ f a c1 = .ok (e, c2) ∧ Ended c2 ∧
      ∀ l1 l2, Took (start s v) l1 c1 → Took c1 l2 c2 →
        v.rounds = l1 ++ l2 ∧ l1 = used (start s v) c1 ∧ l2 = used c1 c2 := by
  obtain ⟨_, a, c1, c2, h1, h2, he⟩ := (runOn_bind_iff b f s v e).1 h
  exact ⟨a, c1, c2, h1, h2, he, fun l1 l2 t1 t2 =>
    ⟨(took_whole (t1.append t2) he).symm, Took.eq_used t1, Took.eq_used t2⟩⟩

/-- Stretches of rounds one behind the other, each with the context at its end. -/
def Along : Ctx → List (List Fmt.RoundView × Ctx) → Prop
  | _, [] => True
  | c, (l, c1) :: rest => Took c l c1 ∧ Along c1 rest

/-- The context at the end of the last stretch. -/
def endOf : Ctx → List (List Fmt.RoundView × Ctx) → Ctx
  | c, [] => c
  | _, (_, c1) :: rest => endOf c1 rest

/-- The stretches, laid end to end, were taken from the first context to the last. -/
theorem Along.took : ∀ {c : Ctx} {steps : List (List Fmt.RoundView × Ctx)}, Clean c → Along c steps →
    Took c (steps.map (·.1)).flatten (endOf c steps)
  | _, [], hc, _ => Took.nil hc
  | _, (_, _) :: _, _, h => h.1.append (Along.took h.1.2.1 h.2)

/-- Along a whole run the stretches, laid end to end, are the view's list of rounds. -/
theorem along_whole {s : Start} {v : Fmt.View} {steps : List (List Fmt.RoundView × Ctx)}
    (h : Along (start s v) steps) (he : Ended (endOf (start s v) steps)) :
    v.rounds = (steps.map (·.1)).flatten :=
  (took_whole (Along.took (start_clean s v) h) he).symm

/-- For a block that folds a routine over a list: the value and the context behind each step. -/
def trace {α β : Type} (f : β → α → Blk β) : List α → β → Ctx → List (β × Ctx)
  | [], _, _ => []
  | a :: l, x, c =>
    match f x a c with
    | .ok (y, c1) => (y, c1) :: trace f l y c1
    | .error _ => []

/-- The steps of a fold, each from what the one before has left. -/
def Steps {α β : Type} (f : β → α → Blk β) : List α → β → Ctx → List (β × Ctx) → Prop
  | [], _, _, t => t = []
  | a :: l, x, c, t => ∃ y c1 t', t = (y, c1) :: t' ∧ f x a c = .ok (y, c1) ∧ Steps f l y c1 t'

/-- What a fold returns and leaves. -/
def lastOf {β : Type} (x : β) (c : Ctx) (t : List (β × Ctx)) : β × Ctx := t.getLastD (x, c)

/-- Where a fold returns, every step has returned from what the one before has left; the values and
contexts between are `trace`; and the fold returns and leaves the last of them. -/
theorem foldlM_trace {α β : Type} (f : β → α → Blk β) : ∀ (l : List α) (x : β) (c : Ctx)
    (r : β × Ctx), (l.foldlM f x) c = .ok r →
    Steps f l x c (trace f l x c) ∧ r = lastOf x c (trace f l x c)
  | [], x, c, r, h => by
    rw [List.foldlM_nil] at h
    cases h
    exact ⟨rfl, rfl⟩
  | a :: l, x, c, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨y, c1, h1, h2⟩ := (PscRun.bindB_ok _ _ _ _).1 h
    obtain ⟨k1, k2⟩ := foldlM_trace f l y c1 r h2
    have et : trace f (a :: l) x c = (y, c1) :: trace f l y c1 := by
      show (match f x a c with
        | .ok (y, c1) => (y, c1) :: trace f l y c1
        | .error _ => []) = _
      rw [h1]
    rw [et]
    refine ⟨⟨y, c1, _, rfl, h1, k1⟩, ?_⟩
    rw [k2]
    unfold lastOf
    cases trace f l y c1 with
    | nil => rfl
    | cons p t => rfl

end OnBytes.Cut

#print axioms OnBytes.Cut.runOn_iff
#print axioms OnBytes.Cut.runOn_bind_iff
#print axioms OnBytes.Cut.cut_bind
#print axioms OnBytes.Cut.along_whole
#print axioms OnBytes.Cut.foldlM_trace
