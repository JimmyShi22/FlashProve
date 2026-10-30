-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/PlanCalc.lean: which rounds the planner's routines for scalars, a batch, a zero
point and a sumcheck add to a plan, with every field of each round.

The planner is that of the verifier on bytes (OnBytes/Params/Planner.lean). A routine there changes
a plan that is being written, or refuses. This file has a small calculus for "this routine adds just
these rounds" and applies it to planScalars, planBatSigma, planZero and planPsc.
OnBytes/Tie/Pv/Att/PlanOwnW.lean uses it for the rounds of an attention sub-proof.

Main names:
  `At s b p`: the state p has the setting s, a request's scope, b bytes of an open message, no root
    and no answer.
  `roundOf`, `quietOf`: the whole round that close, for an error of the kind field, or closeNone
    adds from such a state.
  `AddsW s b b' r L`: from a state with At s b the routine r ends well only in a state with
    At s b', and it has then added just the rounds L.
  `addsW_scalars`: planScalars n adds no round. It raises the open bytes by 24 n.
  `addsW_bat`, `addsW_zero`, `addsW_psc`: the rounds of planBatSigma, planZero and planPsc, the last
    for every PscSize.
Limits: no statement says that a routine ends well, that a round's bound holds of the protocol, or
what the planner's arithmetic on bounds computes.
-/
import OnBytes.Params.SubRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att.Plan

open OnBytes OnBytes.Params

/-- A state of a request's scope with the setting s, b bytes of an open message, no root and no
answer. -/
structure At (s : Setting) (b : Nat) (p : PlanState) : Prop where
  set : p.set = s
  scope : p.scope = .request
  bytes : p.openBytes = b
  roots : p.openRoots = 0
  answers : p.openAnswers = 0

/-- If a bind of two routines ends well, both do. -/
theorem bind_ok {α : Type} {x : Planning α} {f : α → Planning Unit} {p q : PlanState}
    (h : (x >>= f) p = .ok ((), q)) : ∃ a m, x p = .ok (a, m) ∧ f a m = .ok ((), q) := by
  have h' : (match x p with | .ok (a, m) => f a m | .error e => .error e) = .ok ((), q) := by
    rw [← h]
    show _ = (x p >>= fun y => f y.1 y.2)
    cases x p <;> rfl
  cases hx : x p with
  | error e => rw [hx] at h'; exact absurd h' (by simp)
  | ok y => rw [hx] at h'; exact ⟨y.1, y.2, rfl, h'⟩

/-- The entry of a round that is closed with b bytes open, no root and no answer, and the draws
d. w is the round's work. -/
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

/-- A bound as close counts it in a request's scope: times the instances, if there are more than
one. -/
def scaled (s : Setting) (e : Bound) : Bound :=
  if 1 < s.instances then e * Bound.ofNat s.instances else e

/-- The round that close adds for an error of the kind field. -/
def roundOf (s : Setting) (name : String) (b : Nat) (e : Bound) (d : Draws) : PlanRound where
  entry := entryOf name (s.workOf .field .request) b d
  error := (scaled s e).error
  group := d.group
  why := .field
  rests := d.rests
  scope := .request
  wordFault := wordFaultOf d (scaled s e).error

/-- The round that closeNone adds. -/
def quietOf (name : String) (b : Nat) : PlanRound where
  entry := { name := name, msg := b }
  scope := .request

theorem closeW_at {s : Setting} {b : Nat} {p q : PlanState} (h : At s b p) (name : String)
    (e : Bound) (d : Draws) (hq : close name .field e d p = .ok ((), q)) :
    At s 0 q ∧ q.rounds = p.rounds.push (roundOf s name b e d) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold close at hq
  simp only [h1, h2, h3, h4, h5] at hq
  have hb : (Scope.request == Scope.request) = true := rfl
  by_cases hi : 1 < s.instances
  · simp only [hb, hi, decide_true, Bool.and_self, if_true] at hq
    split at hq
    · cases hq
    · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [roundOf, scaled, entryOf, hi, if_true]⟩
  · simp only [hb, hi, decide_false, Bool.and_false, Bool.false_eq_true, if_false] at hq
    split at hq
    · cases hq
    · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [roundOf, scaled, entryOf, hi, if_false]⟩

theorem noneW_at {s : Setting} {b : Nat} {p q : PlanState} (h : At s b p) (name : String)
    (hq : closeNone name p = .ok ((), q)) :
    At s 0 q ∧ q.rounds = p.rounds.push (quietOf name b) := by
  unfold closeNone at hq
  split at hq
  · cases hq
  · have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
    subst e1
    exact ⟨⟨h.set, h.scope, rfl, h.roots, rfl⟩,
      by simp only [quietOf, h.bytes, h.answers, h.scope]⟩

/-- From b open bytes the routine r ends well only with b' open bytes, and it has then added just
the rounds L. -/
def AddsW (s : Setting) (b b' : Nat) (r : Planning Unit) (L : List PlanRound) : Prop :=
  ∀ p q, At s b p → r p = .ok ((), q) → At s b' q ∧ q.rounds = p.rounds ++ L.toArray

theorem AddsW.bind {s : Setting} {b b' b'' : Nat} {x y : Planning Unit} {L L' : List PlanRound}
    (hx : AddsW s b b' x L) (hy : AddsW s b' b'' y L') :
    AddsW s b b'' (x >>= fun _ => y) (L ++ L') :=
  fun p q hp h => by
    obtain ⟨_, r, h1, h2⟩ := bind_ok h
    obtain ⟨a1, e1⟩ := hx p r hp h1
    obtain ⟨a2, e2⟩ := hy r q a1 h2
    exact ⟨a2, by rw [e2, e1]; simp⟩

theorem AddsW.pure (s : Setting) (b : Nat) : AddsW s b b (pure ()) [] := fun p q hp h => by
  obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨hp, by simp⟩

theorem AddsW.ite {s : Setting} {b b' : Nat} {c : Prop} [Decidable c] {x y : Planning Unit}
    {L L' : List PlanRound} (hx : AddsW s b b' x L) (hy : AddsW s b b' y L') :
    AddsW s b b' (if c then x else y) (if c then L else L') := by
  split
  · exact hx
  · exact hy

theorem AddsW.cast {s : Setting} {b b' c c' : Nat} {x : Planning Unit} {L L' : List PlanRound}
    (h : AddsW s b b' x L) (e1 : b = c) (e2 : b' = c') (e3 : L = L') : AddsW s c c' x L' := by
  subst e1 e2 e3
  exact h

/-- A routine that first reads the setting. -/
theorem AddsW.withSetting {s : Setting} {b b' : Nat} {f : Setting → Planning Unit}
    {L : List PlanRound} (h : AddsW s b b' (f s) L) : AddsW s b b' (theSetting >>= f) L :=
  fun p q hp hq => by
    obtain ⟨s2, m2, g2, h2⟩ := bind_ok hq
    obtain ⟨rfl, rfl⟩ : p.set = s2 ∧ p = m2 := Prod.mk.inj (Except.ok.inj g2)
    rw [hp.set] at h2
    exact h p q hp h2

/-- planScalars adds no round. -/
theorem addsW_scalars (s : Setting) (b n : Nat) : AddsW s b (b + 24 * n) (planScalars n) [] :=
  fun p q hp h => by
    obtain rfl : ({ p with openBytes := p.openBytes + 24 * n } : PlanState) = q :=
      (Prod.mk.inj (Except.ok.inj h)).2
    exact ⟨⟨hp.set, hp.scope, by show p.openBytes + 24 * n = b + 24 * n; rw [hp.bytes], hp.roots,
      hp.answers⟩, by simp⟩

theorem addsW_close (s : Setting) (b : Nat) (name : String) (e : Bound) (d : Draws) :
    AddsW s b 0 (close name .field e d) [roundOf s name b e d] := fun p q hp h => by
  obtain ⟨a, er⟩ := closeW_at hp _ _ _ h
  exact ⟨a, by rw [er]; simp⟩

theorem addsW_none (s : Setting) (b : Nat) (name : String) :
    AddsW s b 0 (closeNone name) [quietOf name b] := fun p q hp h => by
  obtain ⟨a, er⟩ := noneW_at hp _ h
  exact ⟨a, by rw [er]; simp⟩

/-! ### The rounds in closed form -/

/-- ZERO: v elements are drawn; the bound is v / cardE. -/
def rZero (s : Setting) (b v : Nat) : PlanRound :=
  roundOf s "ZERO" b (fieldError s v) { drawE := v, priced := .roundItself }

/-- BAT-sigma: one element is drawn; the bound is (rows - 1) / cardE. -/
def rBat (s : Setting) (b rows : Nat) : PlanRound :=
  roundOf s "BAT-sigma" b (powersError s rows) { drawE := 1, rows := rows, priced := .asSaid }

/-- PSC epsilon: the message has planPsc's one scalar and b more bytes. The plan does not say in
which order they come. The bound is 1 / cardE. -/
def rEps (s : Setting) (b : Nat) : PlanRound :=
  roundOf s "PSC epsilon" (b + 24) (fieldError s 1) { drawE := 1, priced := .settingAlone }

/-- PSC round, for a variable whose member of PscSize.degree is g: g - 1 scalars; the bound is
(g - 1) / cardE. -/
def rVar (s : Setting) (g : Nat) : PlanRound :=
  roundOf s "PSC round" (24 * (g - 1)) (fieldError s (g - 1)) { drawE := 1, priced := .roundItself }

/-- PSC Y: dy scalars; one element is drawn, which is never 0; the bound is dy / (cardE - 1). -/
def rY (s : Setting) (dy : Nat) : PlanRound :=
  roundOf s "PSC Y" (24 * dy) (fieldErrorNonzero s dy)
    { drawE := 1, drawNZ := 1, priced := .roundItself }

/-- The rounds of planPsc, for every size. b: the bytes that are open when planPsc is called. -/
def wPsc (s : Setting) (b : Nat) (x : PscSize) : List PlanRound :=
  [rEps s b] ++ x.degree.map (rVar s) ++
    (if x.withY then [rY s x.degreeY, quietOf "PSC values" (24 * x.values)] else [])

theorem addsW_zero (s : Setting) (b v : Nat) : AddsW s b 0 (planZero v) [rZero s b v] :=
  AddsW.withSetting
    (f := fun s' => close "ZERO" .field (fieldError s' v) { drawE := v, priced := .roundItself })
    (addsW_close s b _ _ _)

theorem addsW_bat (s : Setting) (b rows : Nat) :
    AddsW s b 0 (planBatSigma rows) [rBat s b rows] :=
  AddsW.withSetting
    (f := fun s' => close "BAT-sigma" .field (powersError s' rows)
      { drawE := 1, rows := rows, priced := .asSaid })
    (addsW_close s b _ _ _)

theorem addsW_vars (s : Setting) :
    ∀ gs : List Nat, AddsW s 0 0 (planPscRounds s gs) (gs.map (rVar s))
  | [] => AddsW.pure s 0
  | g :: gs =>
    (AddsW.bind (addsW_scalars s 0 (g - 1))
      (AddsW.bind
        (addsW_close s (0 + 24 * (g - 1)) "PSC round" (fieldError s (g - 1))
          { drawE := 1, priced := .roundItself })
        (addsW_vars s gs))).cast rfl rfl (by simp [rVar])

theorem addsW_psc (s : Setting) (b : Nat) (x : PscSize) :
    AddsW s b 0 (planPsc x) (wPsc s b x) := by
  unfold planPsc
  refine AddsW.withSetting ?_
  refine (AddsW.bind (addsW_scalars s b 1)
    (AddsW.bind
      (addsW_close s (b + 24 * 1) "PSC epsilon" (fieldError s 1)
        { drawE := 1, priced := .settingAlone })
      (AddsW.bind (addsW_vars s x.degree) (AddsW.ite
        (AddsW.bind (addsW_scalars s 0 x.degreeY)
          (AddsW.bind
            (addsW_close s (0 + 24 * x.degreeY) "PSC Y" (fieldErrorNonzero s x.degreeY)
              { drawE := 1, drawNZ := 1, priced := .roundItself })
            (AddsW.bind (addsW_scalars s 0 x.values)
              (addsW_none s (0 + 24 * x.values) "PSC values"))))
        (AddsW.pure s 0))))).cast rfl rfl ?_
  simp [wPsc, rEps, rY]

end OnBytes.Tie.Pv.Att.Plan

#print axioms OnBytes.Tie.Pv.Att.Plan.addsW_psc
#print axioms OnBytes.Tie.Pv.Att.Plan.addsW_bat
#print axioms OnBytes.Tie.Pv.Att.Plan.addsW_zero
