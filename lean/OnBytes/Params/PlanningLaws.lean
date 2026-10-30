-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/PlanningLaws.lean: what a routine of the planner adds to a plan: the general laws,
and the laws of the routines that add one round or none.

A routine of the planner (`Planning`, OnBytes/Params/Planner.lean) runs on a plan that is being
written: it ends well with a value and a new state, or it refuses. What it adds depends on the state
only through the setting, the scope, and the three counts of what the prover has sent since the last
round. This file describes a round before it is added (`RoundSpec`, of three sorts: a round with a
verifier's message, with its name, the kind of its error, the bound by which it is priced, its draws
and the three counts; a silent round; the entry for a table's record), and defines `Runs`: wherever
the routine ends well from a state with a given setting, scope and counts, it returns a given value,
keeps setting and scope, adds the rounds of a given list of descriptions, and leaves given counts;
and of each round with a verifier's message the bound is not marked bad, the work is below the
target, and the work fits the nonce (of a silent round and of a record's entry this is not said). It
proves how `Runs` composes, and the laws of the routines from which all others are made. A second
relation, `Knows`, keeps what a routine's own tests (`needs`, `must`) have found.

Main definitions: `RoundSpec`, `RoundSpec.round`, `RoundSpec.Good`, `Runs`, `Knows`.
Main theorems: `runs_bind`, `runs_pure`, `runs_close`, `runs_closeNone`, `runs_scalars`,
`runs_answers`, `runs_roots`, `runs_needs`, `runs_setting`, `runs_scope`, `runs_ite`, `runs_when`,
`runs_must`, `runs_push`, `runs_times`, `runs_forEach`; `knows_fst`, `knows_snd`, `knows_needs`,
`knows_must`, `finishHeld_knows`; `finish_rounds`, `finishHeld_rounds`.
What is not claimed: that a routine ends well: of a routine that refuses, `Runs` and `Knows` say
nothing. `Runs` says which rounds are added, not which conditions held. Nothing on the routines that
plan a block. Nothing on the C++ planner, of which OnBytes/Params/ is a rendering. For proofs only;
the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import Mathlib.Tactic
import OnBytes.Params.Planner

set_option autoImplicit false

namespace OnBytes.Params

/-- A round as a routine asks for it. `said`: a round with a verifier's message, as `close` takes
it, with the bytes, roots and answers that the prover has sent since the last round. `silent`: a
round in which the verifier says nothing, as `closeNone` takes it. `record`: the entry for a table's
own sample, which `planRecord` adds and which is no round of the chain. -/
inductive RoundSpec where
  | said (name : String) (why : ErrorKind) (error : Bound) (d : Draws) (bytes roots answers : Nat)
  | silent (name : String) (bytes answers : Nat)
  | record (answers cube : Nat) (error : Bound)

namespace RoundSpec

/-- The bound that `close` prices: the routine's; or, in a request's own rounds if there are several
instances, that times their number. A silent round has the bound 0; a record's entry its own. -/
def bound (s : Setting) (c : Scope) : RoundSpec → Bound
  | said _ _ error _ _ _ _ =>
    if c == .request && 1 < s.instances then error * Bound.ofNat s.instances else error
  | silent _ _ _ => Bound.ofWord 0
  | record _ _ error => error

/-- The bits of work of the round. -/
def work (s : Setting) (c : Scope) : RoundSpec → Nat
  | said _ why _ _ _ _ _ => s.workOf why c
  | silent _ _ _ => 0
  | record _ _ _ => 0

/-- The round that is added to the plan. -/
def round (s : Setting) (c : Scope) : RoundSpec → PlanRound
  | x@(said name why _ d bytes roots answers) =>
    { entry := { name, work := s.workOf why c, msg := bytes, roots := roots, answers := answers,
                 drawE := d.drawE, drawNZ := d.drawNZ, poss := d.poss, logN := d.logN,
                 trits := d.trits, rows := d.rows },
      error := (x.bound s c).error, group := d.group, why := why, rests := d.rests, scope := c,
      wordFault := wordFaultOf d (x.bound s c).error }
  | silent name bytes answers => { entry := { name, msg := bytes, answers := answers }, scope := c }
  | record answers cube error =>
    { entry := { name := "RECORD", drawE := answers * (cube + 1), drawNZ := answers },
      error := error.error, why := .sample, scope := c }

/-- What `close` has tested of a round that it added: the bound is not marked bad; the work is below
the target; and the work, if it is not 0, and six bits more fit the nonce. Of a silent round and of
a record's entry nothing. -/
def Good (s : Setting) (c : Scope) : RoundSpec → Prop
  | x@(said _ _ _ _ _ _ _) => (x.bound s c).bad = false ∧ x.work s c < s.target ∧
      (x.work s c ≠ 0 → x.work s c + 6 ≤ 8 * s.nonceBytes)
  | silent _ _ _ => True
  | record _ _ _ => True

end RoundSpec

/-- Wherever the routine x ends well from a state with the setting s, the scope c and the open
counts b, r, a, it returns v, keeps s and c, adds the rounds of the descriptions in l, each of them
good, and leaves the open counts b', r', a'. -/
def Runs (s : Setting) (c : Scope) (b r a : Nat) {α : Type} (x : Planning α) (v : α)
    (l : List RoundSpec) (b' r' a' : Nat) : Prop :=
  ∀ (p p' : PlanState) (v' : α), p.set = s → p.scope = c → p.openBytes = b → p.openRoots = r →
    p.openAnswers = a → x p = .ok (v', p') →
    v' = v ∧ p'.set = s ∧ p'.scope = c ∧
      p'.rounds.toList = p.rounds.toList ++ l.map (·.round s c) ∧
      p'.openBytes = b' ∧ p'.openRoots = r' ∧ p'.openAnswers = a' ∧ ∀ y ∈ l, y.Good s c

section
variable {s : Setting} {c : Scope}

/-- One routine after another, on a state. -/
theorem bind_run {α β : Type} (x : Planning α) (f : α → Planning β) (p : PlanState) :
    (x >>= f) p = (match x p with
      | .ok v => f v.1 v.2
      | .error e => .error e) := by
  show StateT.bind x f p = _
  unfold StateT.bind
  show Except.bind (x p) _ = _
  unfold Except.bind
  cases x p <;> rfl

/-- If one routine after another ends well, so did the first, and then the second. -/
theorem bind_ends {α β : Type} {x : Planning α} {f : α → Planning β} {p p2 : PlanState} {b : β}
    (h : (x >>= f) p = .ok (b, p2)) : ∃ a p1, x p = .ok (a, p1) ∧ f a p1 = .ok (b, p2) := by
  rw [bind_run] at h
  cases hx : x p with
  | error e =>
    rw [hx] at h
    cases h
  | ok v =>
    rw [hx] at h
    exact ⟨v.1, v.2, rfl, h⟩

/-- One routine after another: the descriptions of the first and then those of the second. -/
theorem runs_bind {α β : Type} {x : Planning α} {f : α → Planning β} {v : α} {w : β}
    {l1 l2 : List RoundSpec} {b r a b1 r1 a1 b2 r2 a2 : Nat}
    (h1 : Runs s c b r a x v l1 b1 r1 a1) (h2 : Runs s c b1 r1 a1 (f v) w l2 b2 r2 a2) :
    Runs s c b r a (x >>= f) w (l1 ++ l2) b2 r2 a2 := by
  intro p p' v' hs hc hb hr ha h
  obtain ⟨u, p1, e1, e2⟩ := bind_ends h
  obtain ⟨rfl, s1, c1, q1, ob, or1, oa, g1⟩ := h1 p p1 u hs hc hb hr ha e1
  obtain ⟨rfl, s2, c2, q2, ob2, or2, oa2, g2⟩ := h2 p1 p' v' s1 c1 ob or1 oa e2
  refine ⟨rfl, s2, c2, ?_, ob2, or2, oa2, ?_⟩
  · rw [q2, q1, List.map_append, List.append_assoc]
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact g1 y hy
    · exact g2 y hy

/-- The same list under another name. -/
theorem Runs.cast {α : Type} {x : Planning α} {v : α} {l l' : List RoundSpec}
    {b r a b' r' a' : Nat} (h : Runs s c b r a x v l b' r' a') (e : l = l') :
    Runs s c b r a x v l' b' r' a' := e ▸ h

/-- A value alone adds nothing. -/
theorem runs_pure {α : Type} (v : α) (b r a : Nat) :
    Runs s c b r a (pure v : Planning α) v [] b r a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok (v, p) : Except String (α × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨rfl, hs, hc, by simp, hb, hr, ha, by simp⟩

/-- The setting, read. -/
theorem runs_setting (b r a : Nat) : Runs s c b r a theSetting s [] b r a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok (p.set, p) : Except String (Setting × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨hs, hs, hc, by simp, hb, hr, ha, by simp⟩

/-- The scope, read. -/
theorem runs_scope (b r a : Nat) : Runs s c b r a theScope c [] b r a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok (p.scope, p) : Except String (Scope × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨hc, hs, hc, by simp, hb, hr, ha, by simp⟩

/-- A test adds nothing. That it passed is kept by `knows_needs`, not here. -/
theorem runs_needs (t : Bool) (why : String) (b r a : Nat) :
    Runs s c b r a (needs t why) () [] b r a := by
  intro p p' v' hs hc hb hr ha h
  unfold needs at h
  cases t
  · cases h
  · exact runs_pure () b r a p p' v' hs hc hb hr ha h

/-- The prover sends n elements: no round; 24 n bytes more are open. -/
theorem runs_scalars (n b r a : Nat) : Runs s c b r a (planScalars n) () [] (b + 24 * n) r a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok ((), { p with openBytes := p.openBytes + 24 * n }) :
      Except String (Unit × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨rfl, hs, hc, by simp, by show p.openBytes + 24 * n = _; rw [hb], hr, ha, by simp⟩

/-- The prover sends n answers: no round; 24 n bytes and n answers more are open. -/
theorem runs_answers (n b r a : Nat) :
    Runs s c b r a (planAnswers n) () [] (b + 24 * n) r (a + n) := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok ((), ({ p with
      openBytes := p.openBytes + 24 * n, openAnswers := p.openAnswers + n } : PlanState)) :
      Except String (Unit × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨rfl, hs, hc, by simp, by show p.openBytes + 24 * n = _; rw [hb], hr,
    by show p.openAnswers + n = _; rw [ha], by simp⟩

/-- The prover sends n roots: no round; 32 n bytes and n roots more are open. -/
theorem runs_roots (n b r a : Nat) :
    Runs s c b r a (planRoots n) () [] (b + 32 * n) (r + n) a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok ((), ({ p with
      openBytes := p.openBytes + 32 * n, openRoots := p.openRoots + n } : PlanState)) :
      Except String (Unit × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨rfl, hs, hc, by simp, by show p.openBytes + 32 * n = _; rw [hb],
    by show p.openRoots + n = _; rw [hr], ha, by simp⟩

/-- `close`, with the round under its name. -/
theorem close_run (name : String) (why : ErrorKind) (error : Bound) (d : Draws) (p : PlanState) :
    close name why error d p =
      (if (((RoundSpec.said name why error d p.openBytes p.openRoots p.openAnswers).bound p.set
            p.scope).bad || decide (p.set.target ≤ p.set.workOf why p.scope) ||
          (p.set.workOf why p.scope != 0 &&
            decide (8 * p.set.nonceBytes < p.set.workOf why p.scope + 6))) = true then
        .error notAdmitted
      else
        .ok ((), { p with
          rounds := p.rounds.push
            ((RoundSpec.said name why error d p.openBytes p.openRoots p.openAnswers).round p.set
              p.scope),
          openBytes := 0, openRoots := 0, openAnswers := 0 })) := rfl

/-- `close` adds one round, and leaves nothing open. -/
theorem runs_close (name : String) (why : ErrorKind) (error : Bound) (d : Draws) (b r a : Nat) :
    Runs s c b r a (close name why error d) () [.said name why error d b r a] 0 0 0 := by
  intro p p' v' hs hc hb hr ha h
  rw [close_run] at h
  split at h
  · cases h
  · rename_i hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_le] at hn
    have h3 : p.set.workOf why p.scope ≠ 0 →
        p.set.workOf why p.scope + 6 ≤ 8 * p.set.nonceBytes := by
      intro h0
      by_contra hlt
      have ht : (p.set.workOf why p.scope != 0 &&
          decide (8 * p.set.nonceBytes < p.set.workOf why p.scope + 6)) = true := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        exact ⟨h0, by omega⟩
      rw [ht] at hn
      exact absurd hn.2 (by decide)
    cases h
    subst hs hc hb hr ha
    refine ⟨rfl, rfl, rfl, Array.toList_push, rfl, rfl, rfl, ?_⟩
    intro y hy
    rw [List.mem_singleton.1 hy]
    exact ⟨hn.1.1, hn.1.2, h3⟩

/-- `closeNone` adds one silent round, if no root is open, and leaves nothing open. -/
theorem runs_closeNone (name : String) (b r a : Nat) :
    Runs s c b r a (closeNone name) () [.silent name b a] 0 0 0 := by
  intro p p' v' hs hc hb hr ha h
  unfold closeNone at h
  split at h
  · cases h
  · rename_i hn
    have h0 : p.openRoots = 0 := by simpa using hn
    cases h
    subst hs hc hb ha
    refine ⟨rfl, rfl, rfl, Array.toList_push, rfl, h0, rfl, ?_⟩
    intro y hy
    rw [List.mem_singleton.1 hy]
    trivial

/-- A choice between two routines. -/
theorem runs_ite {α : Type} {P : Prop} [Decidable P] {x y : Planning α} {v w : α}
    {l1 l2 : List RoundSpec} {b r a b' r' a' : Nat} (h1 : P → Runs s c b r a x v l1 b' r' a')
    (h2 : ¬ P → Runs s c b r a y w l2 b' r' a') :
    Runs s c b r a (if P then x else y) (if P then v else w) (if P then l1 else l2) b' r' a' := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp, if_pos hp]
    exact h1 hp
  · rw [if_neg hp, if_neg hp, if_neg hp]
    exact h2 hp

/-- A routine that is run or left out, and what follows in both cases. The routine leaves the open
counts as they were. -/
theorem runs_when {β : Type} {P : Prop} [Decidable P] {x : Planning PUnit} {k : PUnit → Planning β}
    {w : β} {l1 l2 : List RoundSpec} {b r a b' r' a' : Nat} (h1 : Runs s c b r a x () l1 b r a)
    (h2 : Runs s c b r a (k ()) w l2 b' r' a') :
    Runs s c b r a (if P then x >>= k else pure PUnit.unit >>= k) w
      ((if P then l1 else []) ++ l2) b' r' a' := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp]
    exact runs_bind h1 h2
  · rw [if_neg hp, if_neg hp]
    exact runs_bind (runs_pure () b r a) h2

/-- A routine that refuses runs as anything: it never ends well. -/
theorem runs_refuse {α : Type} (why : String) (v : α) (l : List RoundSpec) (b r a b' r' a' : Nat) :
    Runs s c b r a (refusePlan why : Planning α) v l b' r' a' := by
  intro p p' v' _ _ _ _ _ h
  cases h

/-- A value that must be there, and what follows. Where it is not there the routine refuses; the
list is then written as empty. -/
theorem runs_must {α : Type} {x : Option α} {why : String} {f : α → Planning Unit}
    {L : α → List RoundSpec} {b r a b' r' a' : Nat}
    (h : ∀ v, Runs s c b r a (f v) () (L v) b' r' a') :
    Runs s c b r a (must x why >>= f) () ((x.map L).getD []) b' r' a' := by
  cases x with
  | none =>
    intro p p' v' _ _ _ _ _ hh
    obtain ⟨_, _, e1, _⟩ := bind_ends hh
    cases e1
  | some v => exact runs_bind (runs_pure v b r a) (h v)

/-- A round that is added as it stands. -/
theorem runs_push (x : RoundSpec) (hx : x.Good s c) (b r a : Nat) :
    Runs s c b r a (modify fun p => { p with rounds := p.rounds.push (x.round s c) } :
      Planning PUnit) () [x] b r a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok ((), ({ p with rounds := p.rounds.push (x.round s c) } : PlanState)) :
      Except String (Unit × PlanState)) = .ok (v', p') := h
  cases h'
  refine ⟨rfl, hs, hc, Array.toList_push, hb, hr, ha, ?_⟩
  intro y hy
  rw [List.mem_singleton.1 hy]
  exact hx

/-- A routine n times, from nothing open to nothing open. -/
theorem runs_times {x : Planning Unit} {l : List RoundSpec} (h : Runs s c 0 0 0 x () l 0 0 0) :
    ∀ n : Nat, Runs s c 0 0 0 (times n x) () (List.replicate n l).flatten 0 0 0
  | 0 => runs_pure () 0 0 0
  | n + 1 => by
      have := runs_bind h (f := fun _ => times n x) (runs_times h n)
      rw [List.replicate_succ, List.flatten_cons]
      exact this

/-- A routine on each member of a list, from nothing open to nothing open. -/
theorem runs_forEach {α : Type} {f : α → Planning Unit} {L : α → List RoundSpec}
    (h : ∀ x, Runs s c 0 0 0 (f x) () (L x) 0 0 0) :
    ∀ l : List α, Runs s c 0 0 0 (forEach l f) () (l.map L).flatten 0 0 0
  | [] => runs_pure () 0 0 0
  | x :: t => by
      have := runs_bind (h x) (f := fun _ => forEach t f) (runs_forEach h t)
      rw [List.map_cons, List.flatten_cons]
      exact this

/-! ## What a routine's own tests have found -/

/-- Wherever the routine x ends well from a state with the setting s, the scope c and the open
counts b, r, a, the proposition F holds. -/
def Knows (s : Setting) (c : Scope) (b r a : Nat) {α : Type} (x : Planning α) (F : Prop) : Prop :=
  ∀ (p p' : PlanState) (v' : α), p.set = s → p.scope = c → p.openBytes = b → p.openRoots = r →
    p.openAnswers = a → x p = .ok (v', p') → F

/-- What follows from what is known is known. -/
theorem Knows.mono {α : Type} {x : Planning α} {F G : Prop} {b r a : Nat}
    (h : Knows s c b r a x F) (hi : F → G) : Knows s c b r a x G :=
  fun p p' v' hs hc hb hr ha e => hi (h p p' v' hs hc hb hr ha e)

/-- Two things that are known. -/
theorem Knows.and {α : Type} {x : Planning α} {F G : Prop} {b r a : Nat}
    (h : Knows s c b r a x F) (g : Knows s c b r a x G) : Knows s c b r a x (F ∧ G) :=
  fun p p' v' hs hc hb hr ha e => ⟨h p p' v' hs hc hb hr ha e, g p p' v' hs hc hb hr ha e⟩

/-- What the first of two routines knows. -/
theorem knows_fst {α β : Type} {x : Planning α} {f : α → Planning β} {F : Prop} {b r a : Nat}
    (h : Knows s c b r a x F) : Knows s c b r a (x >>= f) F := by
  intro p p' v' hs hc hb hr ha e
  obtain ⟨u, p1, e1, _⟩ := bind_ends e
  exact h p p1 u hs hc hb hr ha e1

/-- What the second of two routines knows. -/
theorem knows_snd {α β : Type} {x : Planning α} {f : α → Planning β} {v : α} {F : Prop}
    {l : List RoundSpec} {b r a b1 r1 a1 : Nat} (h1 : Runs s c b r a x v l b1 r1 a1)
    (h2 : Knows s c b1 r1 a1 (f v) F) : Knows s c b r a (x >>= f) F := by
  intro p p' v' hs hc hb hr ha e
  obtain ⟨u, p1, e1, e2⟩ := bind_ends e
  obtain ⟨rfl, s1, c1, _, ob, or1, oa, _⟩ := h1 p p1 u hs hc hb hr ha e1
  exact h2 p1 p' v' s1 c1 ob or1 oa e2

/-- A test that ends well has passed. -/
theorem knows_needs (t : Bool) (why : String) (b r a : Nat) :
    Knows s c b r a (needs t why) (t = true) := by
  intro p p' v' _ _ _ _ _ e
  cases t
  · cases e
  · rfl

/-- A value that must be there was there, and what follows knows what it knows. -/
theorem knows_must {α β : Type} {x : Option α} {why : String} {f : α → Planning β} {F : α → Prop}
    {b r a : Nat} (h : ∀ v, Knows s c b r a (f v) (F v)) :
    Knows s c b r a (must x why >>= f) (∃ v, x = some v ∧ F v) := by
  cases x with
  | none =>
    intro p p' v' _ _ _ _ _ e
    obtain ⟨_, _, e1, _⟩ := bind_ends e
    cases e1
  | some v =>
    exact (knows_snd (runs_pure v b r a) (h v)).mono fun hF => ⟨v, rfl, hF⟩

/-- `True` is known of every routine. -/
theorem knows_true {α : Type} (x : Planning α) (b r a : Nat) : Knows s c b r a x True :=
  fun _ _ _ _ _ _ _ _ _ => trivial

/-- What the routine of a finished plan that holds knows is so. The verdict is not used. -/
theorem finishHeld_knows {x : Planning Unit} {F : Prop} {P : Planned}
    (hx : Knows s c 0 0 0 x F) (h : finishHeld s c x = .ok P) : F := by
  unfold finishHeld at h
  cases hf : finish s c x with
  | error e =>
    rw [hf] at h
    cases h
  | ok Q =>
    unfold finish at hf
    split at hf
    · cases hf
    · rename_i u p hp
      exact hx _ p u rfl rfl rfl rfl rfl hp

/-! ## Finished plans -/

/-- A finished plan has the rounds of the routine's list, each of them good. -/
theorem finish_rounds {x : Planning Unit} {l : List RoundSpec} {b' r' a' : Nat} {P : Planned}
    (hx : Runs s c 0 0 0 x () l b' r' a') (h : finish s c x = .ok P) :
    P.set = s ∧ P.rounds = l.map (·.round s c) ∧ ∀ y ∈ l, y.Good s c := by
  unfold finish at h
  split at h
  · cases h
  · rename_i u p hp
    obtain ⟨_, _, _, q, _, _, _, g⟩ := hx _ p u rfl rfl rfl rfl rfl hp
    split at h
    · cases h
    · cases h
      exact ⟨rfl, by simpa using q, g⟩

/-- A finished plan that holds: the same, and each round holds in the planner's reckoning. -/
theorem finishHeld_rounds {x : Planning Unit} {l : List RoundSpec} {b' r' a' : Nat} {P : Planned}
    (hx : Runs s c 0 0 0 x () l b' r' a') (h : finishHeld s c x = .ok P) :
    P.set = s ∧ P.rounds = l.map (·.round s c) ∧ (∀ y ∈ l, y.Good s c) ∧
      ∀ y ∈ l, roundHolds s (capped s) (y.round s c) = true := by
  unfold finishHeld at h
  cases hf : finish s c x with
  | error e =>
    rw [hf] at h
    cases h
  | ok Q =>
    rw [hf] at h
    have h' : (if Q.holds = true then (Except.ok Q : Except String Planned)
        else .error notAdmitted) = .ok P := h
    split at h'
    · rename_i hh
      cases h'
      obtain ⟨e1, e2, g⟩ := finish_rounds hx hf
      refine ⟨e1, e2, g, ?_⟩
      intro y hy
      unfold Planned.holds Planned.roundsHold at hh
      simp only [Bool.and_eq_true, List.all_eq_true] at hh
      have := hh.1.1 (y.round s c) (by rw [e2]; exact List.mem_map_of_mem hy)
      rw [e1] at this
      exact this
    · cases h'

end

end OnBytes.Params

#print axioms OnBytes.Params.knows_must
#print axioms OnBytes.Params.finishHeld_knows
#print axioms OnBytes.Params.finish_rounds
#print axioms OnBytes.Params.finishHeld_rounds
#print axioms OnBytes.Params.runs_bind
#print axioms OnBytes.Params.runs_close
#print axioms OnBytes.Params.runs_closeNone
#print axioms OnBytes.Params.runs_times
#print axioms OnBytes.Params.runs_forEach
