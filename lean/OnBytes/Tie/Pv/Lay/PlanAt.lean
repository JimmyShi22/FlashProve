-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lay/PlanAt.lean: how the planner's small routines act on a plan's state, and the list
of rounds that it lays for the row products' stretch of a layers' sub-proof.

The planner (OnBytes/Params/) is a program in a state monad: a routine adds bytes to the open
message or closes a round. To say which rounds a routine lays, for all sizes, its action on a state
is described.

Main names:
  `At s b p`: the state p is in a request's scope, under the setting s, with b bytes in the open
    message.
  `scalars_at`, `close_at`, `none_at`, `rounds_at`: what planScalars, close, closeNone and
    planPscRounds do to such a state, and which entry (Fmt.Entry) the closed round has.
  `rowProductsL`, `stretch`, `rowProducts_at`, `rowProducts_shapes`: three neighbouring lines of
    Params.planLayerOwn as one routine; the list of entries that it lays, as a closed function of
    four numbers; that this is the list, from any such state, and for a whole plan that finish
    accepts.
  `stretch_length`, `stretch_scalars`, `stretch_kinds`: the list's length; the messages' scalars;
    the kinds that the format gives the rounds' names.

What is compared of a round is its whole entry: the name and eleven numbers.

Limits: nothing is said on whether finish accepts, nor on the rounds' errors.

-/
import OnBytes.Params.SubRounds
import OnBytes.Params.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params

/-- The port's own three lines for the stretch (SubRounds.lean:148-150). -/
def rowProductsL (lt NI NP NO : Nat) : Planning Unit := do
  planScalars (NP * NI)
  planBatSigma (NP * NI)
  planTokenSumcheck lt 2 (NO * NI)

/-- What is compared of a round: the planner's whole entry. -/
abbrev Shape := Fmt.Entry

def shapeOf (r : PlanRound) : Shape := r.entry

/-- THE LIST, closed. w: the work of a round whose error is of the field's kind, in a request's
scope. -/
def stretch (w lt NI NP NO : Nat) : List Shape :=
  [{ name := "BAT-sigma", work := w, msg := 24 * (NP * NI), drawE := 1, rows := NP * NI },
   { name := "PSC epsilon", work := w, msg := 48, drawE := 1 }] ++
  List.replicate lt { name := "PSC round", work := w, msg := 48, drawE := 1 } ++
  [{ name := "PSC Y", work := w, msg := 48, drawE := 1, drawNZ := 1 },
   { name := "PSC values", msg := 24 * (NO * NI) }]

/-- what a state must be like for the lemmas below -/
structure At (s : Setting) (b : Nat) (p : PlanState) : Prop where
  set : p.set = s
  scope : p.scope = .request
  bytes : p.openBytes = b
  roots : p.openRoots = 0
  answers : p.openAnswers = 0

theorem scalars_at {s : Setting} {b : Nat} {p : PlanState} (h : At s b p) (n : Nat) :
    ∃ q, planScalars n p = .ok ((), q) ∧ At s (b + 24 * n) q ∧ q.rounds = p.rounds :=
  ⟨{ p with openBytes := p.openBytes + 24 * n }, rfl,
    ⟨h.set, h.scope, by show p.openBytes + 24 * n = b + 24 * n; rw [h.bytes], h.roots, h.answers⟩,
        rfl⟩

/-- the entry of a round that is closed with b bytes open, no root and no answer, and the draws d -/
def entryOf (name : String) (w b : Nat) (d : Draws) : Fmt.Entry where
  name := name
  work := w
  msg := b
  drawE := d.drawE
  drawNZ := d.drawNZ
  poss := d.poss
  logN := d.logN
  trits := d.trits
  rows := d.rows

theorem close_at {s : Setting} {b : Nat} {p q : PlanState} (h : At s b p) (name : String)
    (e : Bound) (d : Draws) (hq : close name .field e d p = .ok ((), q)) :
    At s 0 q ∧ ∃ r : PlanRound, q.rounds = p.rounds.push r ∧
      shapeOf r = entryOf name (s.workOf .field .request) b d := by
  unfold close at hq
  simp only at hq
  split at hq
  · split at hq
    · cases hq
    · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      exact ⟨⟨h.set, h.scope, rfl, rfl, rfl⟩, _, rfl, by simp only [shapeOf, entryOf, h.set,
          h.scope, h.bytes, h.roots, h.answers]⟩
  · split at hq
    · cases hq
    · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      exact ⟨⟨h.set, h.scope, rfl, rfl, rfl⟩, _, rfl, by simp only [shapeOf, entryOf, h.set,
          h.scope, h.bytes, h.roots, h.answers]⟩

theorem none_at {s : Setting} {b : Nat} {p q : PlanState} (h : At s b p) (name : String)
    (hq : closeNone name p = .ok ((), q)) :
    At s 0 q ∧ ∃ r : PlanRound, q.rounds = p.rounds.push r ∧
      shapeOf r = { name := name, msg := b } := by
  unfold closeNone at hq
  split at hq
  · cases hq
  · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
    subst e1
    refine ⟨⟨h.set, h.scope, rfl, h.roots, rfl⟩, _, rfl, ?_⟩
    simp only [shapeOf, h.bytes, h.answers]

/-- a bind of two routines that ends well: both do -/
theorem bind_ok {α : Type} {x : Planning α} {f : α → Planning Unit} {p q : PlanState}
    (h : (x >>= f) p = .ok ((), q)) : ∃ a m, x p = .ok (a, m) ∧ f a m = .ok ((), q) := by
  have h' : (match x p with | .ok (a, m) => f a m | .error e => .error e) = .ok ((), q) := by
    rw [← h]
    show _ = (x p >>= fun y => f y.1 y.2)
    cases x p <;> rfl
  cases hx : x p with
  | error e => rw [hx] at h'; exact absurd h' (by simp)
  | ok y => rw [hx] at h'; exact ⟨y.1, y.2, rfl, h'⟩

/-- the rounds of the variables -/
theorem rounds_at {s : Setting} : ∀ (n : Nat) {p q : PlanState}, At s 0 p →
    planPscRounds s (List.replicate n 3) p = .ok ((), q) →
    At s 0 q ∧ ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      l.map shapeOf = List.replicate n
        { name := "PSC round", work := s.workOf .field .request, msg := 48, drawE := 1 }
  | 0, p, q, h, hq => by
    have e : q = p := ((Prod.mk.inj (Except.ok.inj hq)).2).symm
    subst e
    exact ⟨h, [], by simp, rfl⟩
  | n + 1, p, q, h, hq => by
    have hq' : (planScalars (3 - 1) >>= fun _ =>
        close "PSC round" .field (fieldError s (3 - 1)) { drawE := 1, priced := .roundItself } >>=
            fun _ =>
        planPscRounds s (List.replicate n 3)) p = .ok ((), q) := hq
    obtain ⟨_, m1, h1, hq1⟩ := bind_ok hq'
    obtain ⟨m1', e1, a1, r1⟩ := scalars_at h (3 - 1)
    rw [e1] at h1
    have em : m1' = m1 := (Prod.mk.inj (Except.ok.inj h1)).2
    subst em
    obtain ⟨_, m2, h2, hq2⟩ := bind_ok hq1
    obtain ⟨a2, r, er, sr⟩ := close_at a1 _ _ _ h2
    obtain ⟨a3, l, el, sl⟩ := rounds_at n a2 hq2
    refine ⟨a3, r :: l, ?_, ?_⟩
    · rw [el, er, r1]
      simp
    · rw [List.map_cons, sl, sr]
      rfl

/-- the kinds that the format gives the five names -/
theorem kinds : kindOf "BAT-sigma" = some .elems ∧ kindOf "PSC epsilon" = some .join ∧
    kindOf "PSC round" = some .elems ∧ kindOf "PSC Y" = some .elems ∧
    kindOf "PSC values" = some .nothing := by decide

/-- THE LIST, from any state at which no message is open. -/
theorem rowProducts_at {s : Setting} (lt NI NP NO : Nat) {p q : PlanState} (h : At s 0 p)
    (hq : rowProductsL lt NI NP NO p = .ok ((), q)) :
    At s 0 q ∧ ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      l.map shapeOf = stretch (s.workOf .field .request) lt NI NP NO := by
  have hq' : (planScalars (NP * NI) >>= fun _ =>
      (theSetting >>= fun s' => close "BAT-sigma" .field (powersError s' (NP * NI))
        { drawE := 1, rows := NP * NI, priced := .asSaid }) >>= fun _ =>
      planScalars 1 >>= fun _ =>
      theSetting >>= fun s' =>
      planScalars 1 >>= fun _ =>
      close "PSC epsilon" .field (fieldError s' 1) { drawE := 1, priced := .settingAlone } >>= fun
          _ =>
      planPscRounds s' (List.replicate lt 3) >>= fun _ =>
      planScalars 2 >>= fun _ =>
      close "PSC Y" .field (fieldErrorNonzero s' 2)
          { drawE := 1, drawNZ := 1, priced := .roundItself } >>= fun _ =>
      planScalars (NO * NI) >>= fun _ =>
      closeNone "PSC values") p = .ok ((), q) := hq
  -- the products' scalars
  obtain ⟨_, m1, h1, k1⟩ := bind_ok hq'
  obtain ⟨n1, e1, a1, r1⟩ := scalars_at h (NP * NI)
  rw [e1] at h1
  obtain rfl : n1 = m1 := (Prod.mk.inj (Except.ok.inj h1)).2
  -- BAT-sigma
  obtain ⟨_, m2, h2, k2⟩ := bind_ok k1
  obtain ⟨s2, m2', g2, h2'⟩ := bind_ok h2
  obtain ⟨rfl, rfl⟩ : n1.set = s2 ∧ n1 = m2' := Prod.mk.inj (Except.ok.inj g2)
  obtain ⟨a2, x2, er2, sh2⟩ := close_at a1 _ _ _ h2'
  -- the scalar of the claimed sum
  obtain ⟨_, m3, h3, k3⟩ := bind_ok k2
  obtain ⟨n3, e3, a3, r3⟩ := scalars_at a2 1
  rw [e3] at h3
  obtain rfl : n3 = m3 := (Prod.mk.inj (Except.ok.inj h3)).2
  -- the setting
  obtain ⟨s4, m4, g4, k4⟩ := bind_ok k3
  obtain ⟨rfl, rfl⟩ : n3.set = s4 ∧ n3 = m4 := Prod.mk.inj (Except.ok.inj g4)
  -- the sum of the hiding polynomial
  obtain ⟨_, m5, h5, k5⟩ := bind_ok k4
  obtain ⟨n5, e5, a5, r5⟩ := scalars_at a3 1
  rw [e5] at h5
  obtain rfl : n5 = m5 := (Prod.mk.inj (Except.ok.inj h5)).2
  -- PSC epsilon
  obtain ⟨_, m6, h6, k6⟩ := bind_ok k5
  obtain ⟨a6, x6, er6, sh6⟩ := close_at a5 _ _ _ h6
  -- the rounds
  obtain ⟨_, m7, h7, k7⟩ := bind_ok k6
  rw [a3.set] at h7
  obtain ⟨a7, l7, el7, sl7⟩ := rounds_at lt a6 h7
  -- Y
  obtain ⟨_, m8, h8, k8⟩ := bind_ok k7
  obtain ⟨n8, e8, a8, r8⟩ := scalars_at a7 2
  rw [e8] at h8
  obtain rfl : n8 = m8 := (Prod.mk.inj (Except.ok.inj h8)).2
  obtain ⟨_, m9, h9, k9⟩ := bind_ok k8
  obtain ⟨a9, x9, er9, sh9⟩ := close_at a8 _ _ _ h9
  -- the values
  obtain ⟨_, m10, h10, k10⟩ := bind_ok k9
  obtain ⟨n10, e10, a10, r10⟩ := scalars_at a9 (NO * NI)
  rw [e10] at h10
  obtain rfl : n10 = m10 := (Prod.mk.inj (Except.ok.inj h10)).2
  obtain ⟨a11, x11, er11, sh11⟩ := none_at a10 _ k10
  refine ⟨a11, [x2, x6] ++ l7 ++ [x9, x11], ?_, ?_⟩
  · rw [er11, r10, er9, r8, el7, er6, r5, r3, er2, r1]
    simp
  · simp only [List.map_append, List.map_cons, List.map_nil, sl7, sh2, sh6, sh9, sh11, stretch,
      entryOf]
    simp

/-- The entries of the plan that the planner's finish makes of the three lines. -/
theorem rowProducts_shapes (s : Setting) (lt NI NP NO : Nat) (P : Planned)
    (h : finish s .request (rowProductsL lt NI NP NO) = .ok P) :
    P.set = s ∧ P.rounds.map shapeOf = stretch (s.workOf .field .request) lt NI NP NO := by
  unfold finish at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      obtain ⟨_, l, el, sl⟩ := rowProducts_at lt NI NP NO
        (p := { set := s, scope := .request }) ⟨rfl, rfl, rfl, rfl, rfl⟩ hq
      refine ⟨rfl, ?_⟩
      show q.rounds.toList.map shapeOf = _
      rw [el, ← sl]
      simp

theorem stretch_length (w lt NI NP NO : Nat) : (stretch w lt NI NP NO).length = lt + 4 := by
  simp [stretch]

/-- such a plan has lt + 4 rounds -/
theorem rowProducts_length (s : Setting) (lt NI NP NO : Nat) (P : Planned)
    (h : finish s .request (rowProductsL lt NI NP NO) = .ok P) : P.rounds.length = lt + 4 := by
  have e := congrArg List.length (rowProducts_shapes s lt NI NP NO P h).2
  rw [List.length_map, stretch_length] at e
  exact e

/-- the scalars sent, round for round: every message is a whole number of scalars of 24 bytes -/
theorem stretch_scalars (w lt NI NP NO : Nat) :
    (stretch w lt NI NP NO).map (·.msg) =
      ([NP * NI, 2] ++ List.replicate lt 2 ++ [2, NO * NI]).map (24 * ·) := by
  simp [stretch]

/-- the kinds that the format gives the names of the list -/
theorem stretch_kinds (w lt NI NP NO : Nat) :
    (stretch w lt NI NP NO).map (fun e => kindOf e.name) =
      [some .elems, some .join] ++ List.replicate lt (some .elems) ++ [some .elems, some .nothing]
          := by
  obtain ⟨kb, ke, kr, ky, kv⟩ := kinds
  simp [stretch, kb, ke, kr, ky, kv]

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.rowProducts_shapes
#print axioms OnBytes.Tie.Pv.Lay.rowProducts_at
#print axioms OnBytes.Tie.Pv.Lay.rowProducts_length
#print axioms OnBytes.Tie.Pv.Lay.stretch_scalars
#print axioms OnBytes.Tie.Pv.Lay.stretch_kinds
