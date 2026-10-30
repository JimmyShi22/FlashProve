-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/Plan.lean: the round that the planner lays for the matrix of a smallness test,
as a theorem on the planner's own functions.

Each sub-proof of a request ends with a smallness test. The verifier draws a matrix with entries in
{-1, 0, 1}; the round is named RNG. The planner (OnBytes/Params/) lists every round of a chain with
a bound on its error. This file says what the planner adds for the draw of the matrix, for every
record of sizes and every setting. The statements are about the imported functions planSmall,
layerRounds, attentionRounds, headRounds and finish. The round is written out here once more
(`scaled`, `rngDraws`, `rngRound`); the theorems hold what is written out to the planner's own
routines. Definitions, statements and proofs.

Main names:
  `Idle s p`: the state p of a plan in writing has the setting s, a request's scope, and no open
    message.
  `rngRound s x`: the round, whole: its entry (the name and eleven numbers), its bound, and what
    else a round of a plan holds. The entry draws x.columns * x.tau matrix entries and nothing
    else, and no byte is sent.
  `small_adds`: from an idle state planSmall x 0 ends well only in an idle state and adds just
    rngRound s x. `small_asks`: it ends well only if the number of combinations that follows
    from the setting is x.tau, the round's work is below the target and fits the nonce, and the
    number of drawn entries is within the planner's limit (`Asked`). `tau_pos`: x.tau is then
    at least 1. `room_lt`: x.columns * x.tau + 31 is below 2 ^ 64.
  `small_finish`: the same of the planner's finish: the plan is the one round.
  `layer_adds`, `attention_adds`, `head_adds`: the rounds of each of the three kinds of sub-proof
    after moment 1 are that one round.
  `rngRound_entry`: the entry written out.
  `rngRound_error`: with one instance the bound is the number 1 * 2 ^ -x.tau, exactly.
  `rngRound_word`: with one instance and x.tau at least 1 the round's mark wordFault is false.
  `settingOf_instances`: every setting that is read from a parameter file has one instance.
  `small_ok`, `small_ok_work`: the premise is not empty: the planner's finish accepts, at the
    default setting, and at a setting in which the round has work.

Limits: nothing here says that the bound is true of the protocol. The planner does not derive it:
it is the price that the routine planRng sets for entries that are 0 with probability 1/2 and 1 or
-1 with probability 1/4 each. With several instances the bound is that price times their number,
in the planner's arithmetic, which rounds; no theorem here evaluates it. Nothing is said on the
lookup on the digits (planSmall x 1), nor on the round of the sub-proof's batching element, which
counts the test's equations. That the routine of a whole chain calls planSmall from an idle state
is not shown here.
-/
import OnBytes.Params.SubRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Params

/-- The state of a plan in writing: the setting s, a request's scope, no open message. -/
structure Idle (s : Setting) (p : PlanState) : Prop where
  set : p.set = s
  scope : p.scope = .request
  bytes : p.openBytes = 0
  roots : p.openRoots = 0
  answers : p.openAnswers = 0

/-- A bound as the planner counts it in a request's scope: once for each instance. -/
def scaled (s : Setting) (e : Bound) : Bound :=
  if 1 < s.instances then e * Bound.ofNat s.instances else e

/-- What the planner says beside the round. -/
def rngDraws (x : SmallSize) : Draws :=
  { trits := x.columns * x.tau, combinations := x.tau, priced := .asSaid }

/-- The bound of the round. -/
def rngError (s : Setting) (x : SmallSize) : Binary :=
  (scaled s (Bound.exact (Binary.twoTo (-(x.tau : Int))))).error

/-- The round of the matrix, whole. Two fields have the value that the structure gives by itself,
as in the planner: no group is said beside the round (group := none), and the field rests, which
is read of a round with a closeness term only, is .johnson. -/
def rngRound (s : Setting) (x : SmallSize) : PlanRound where
  entry := { name := "RNG", work := s.workOf .small .request, trits := x.columns * x.tau }
  error := rngError s x
  why := .small
  scope := .request
  wordFault := wordFaultOf (rngDraws x) (rngError s x)

/-- If two routines of the planner in a row end well, each does. -/
theorem plan_bind {α β : Type} {x : Planning α} {f : α → Planning β} {p q : PlanState} {b : β}
    (h : (x >>= f) p = .ok (b, q)) : ∃ a m, x p = .ok (a, m) ∧ f a m = .ok (b, q) := by
  have h' : (match x p with | .ok (a, m) => f a m | .error e => .error e) = .ok (b, q) := by
    rw [← h]
    show _ = (x p >>= fun y => f y.1 y.2)
    cases x p <;> rfl
  cases hx : x p with
  | error e => rw [hx] at h'; exact absurd h' (by simp)
  | ok y => rw [hx] at h'; exact ⟨y.1, y.2, rfl, h'⟩

/-- A condition that ends well holds, and leaves the state as it was. -/
theorem needs_ok {c : Bool} {why : String} {p q : PlanState} (h : needs c why p = .ok ((), q)) :
    c = true ∧ p = q := by
  unfold needs at h
  split at h
  · rename_i hc
    exact ⟨hc, (Prod.mk.inj (Except.ok.inj h)).2⟩
  · cases h

/-- The round that the planner's close adds for the matrix, from an idle state; it ends well only
if the round's work is below the target and, with six bits more, fits the nonce. -/
theorem close_rng {s : Setting} {x : SmallSize} {p q : PlanState} (h : Idle s p)
    (hq : close "RNG" .small (Bound.exact (Binary.twoTo (-(x.tau : Int)))) (rngDraws x) p =
      .ok ((), q)) :
    Idle s q ∧ q.rounds = p.rounds.push (rngRound s x) ∧
      s.workOf .small .request < s.target ∧
      (s.workOf .small .request = 0 ∨ s.workOf .small .request + 6 ≤ 8 * s.nonceBytes) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold close at hq
  simp only [h1, h2, h3, h4, h5] at hq
  have hb : (Scope.request == Scope.request) = true := rfl
  by_cases hi : 1 < s.instances
  · simp only [hb, hi, decide_true, Bool.and_self, if_true] at hq
    split at hq
    · cases hq
    · rename_i hn
      have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp only [rngRound, rngError, rngDraws, scaled, hi, if_true], ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or,
        not_and] at hn
      refine ⟨by omega, ?_⟩
      by_cases h0 : s.workOf .small .request = 0
      · exact Or.inl h0
      · exact Or.inr (Nat.le_of_not_lt (hn.2 h0))
  · simp only [hb, hi, decide_false, Bool.and_false, Bool.false_eq_true, if_false] at hq
    split at hq
    · cases hq
    · rename_i hn
      have e1 := (Prod.mk.inj (Except.ok.inj hq)).2
      subst e1
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp only [rngRound, rngError, rngDraws, scaled, hi, if_false], ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or,
        not_and] at hn
      refine ⟨by omega, ?_⟩
      by_cases h0 : s.workOf .small .request = 0
      · exact Or.inl h0
      · exact Or.inr (Nat.le_of_not_lt (hn.2 h0))

/-- What planSmall x 0 asks of the setting and the sizes. One more condition of the planner is not
among the fields: that the round's bound is not marked bad. -/
structure Asked (s : Setting) (x : SmallSize) : Prop where
  /-- the number of combinations that follows from the setting is the sub-proof's -/
  tau : rngCombinations s .request = x.tau
  /-- the round's work is below the target -/
  work : s.workOf .small .request < s.target
  /-- the round's work, if there is any, fits the nonce with six bits to spare -/
  nonce : s.workOf .small .request = 0 ∨ s.workOf .small .request + 6 ≤ 8 * s.nonceBytes
  /-- the number of drawn entries is within the planner's limit -/
  room : x.tau = 0 ∨ x.columns ≤ (2 ^ 64 - 1 - 31) / x.tau

/-- The round of the matrix, with what is asked. -/
theorem small_runs (s : Setting) (x : SmallSize) (p q : PlanState) (hp : Idle s p)
    (h : planSmall x 0 p = .ok ((), q)) :
    (Idle s q ∧ q.rounds = p.rounds.push (rngRound s x)) ∧ Asked s x := by
  have h' : (theSetting >>= fun s1 => theScope >>= fun c1 =>
      needs (rngCombinations s1 c1 == x.tau) "plan-tau" >>= fun _ =>
      theSetting >>= fun s2 => theScope >>= fun c2 =>
      needs (rngCombinations s2 c2 == 0 ||
        decide (x.columns ≤ (2 ^ 64 - 1 - 31) / rngCombinations s2 c2)) >>= fun _ =>
      close "RNG" .small (Bound.exact (Binary.twoTo (-(rngCombinations s2 c2 : Int))))
        { trits := x.columns * rngCombinations s2 c2, combinations := rngCombinations s2 c2,
          priced := .asSaid }) p = .ok ((), q) := h
  obtain ⟨s1, m1, g1, k1⟩ := plan_bind h'
  obtain ⟨rfl, rfl⟩ : p.set = s1 ∧ p = m1 := Prod.mk.inj (Except.ok.inj g1)
  obtain ⟨c1, m2, g2, k2⟩ := plan_bind k1
  obtain ⟨rfl, rfl⟩ : p.scope = c1 ∧ p = m2 := Prod.mk.inj (Except.ok.inj g2)
  obtain ⟨_, m3, g3, k3⟩ := plan_bind k2
  obtain ⟨ht, rfl⟩ := needs_ok g3
  obtain ⟨s2, m4, g4, k4⟩ := plan_bind k3
  obtain ⟨rfl, rfl⟩ : p.set = s2 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  obtain ⟨c2, m5, g5, k5⟩ := plan_bind k4
  obtain ⟨rfl, rfl⟩ : p.scope = c2 ∧ p = m5 := Prod.mk.inj (Except.ok.inj g5)
  obtain ⟨_, m6, g6, k6⟩ := plan_bind k5
  obtain ⟨hr, rfl⟩ := needs_ok g6
  have ht' : rngCombinations p.set p.scope = x.tau := by simpa using ht
  rw [ht'] at k6 hr
  obtain ⟨a, r, w, n⟩ := close_rng hp k6
  refine ⟨⟨a, r⟩, ?_, w, n, by simpa using hr⟩
  rw [← hp.set, ← hp.scope]
  exact ht'

/-- The round of the matrix. From an idle state the planner's planSmall x 0 ends well only in an
idle state, and it adds just the round rngRound s x. -/
theorem small_adds (s : Setting) (x : SmallSize) (p q : PlanState) (hp : Idle s p)
    (h : planSmall x 0 p = .ok ((), q)) :
    Idle s q ∧ q.rounds = p.rounds.push (rngRound s x) := (small_runs s x p q hp h).1

/-- What it asks. -/
theorem small_asks (s : Setting) (x : SmallSize) (p q : PlanState) (hp : Idle s p)
    (h : planSmall x 0 p = .ok ((), q)) : Asked s x := (small_runs s x p q hp h).2

/-- There is at least one combination. -/
theorem tau_pos {s : Setting} {x : SmallSize} (h : Asked s x) : 1 ≤ x.tau := by
  have h1 := h.tau
  have h2 := h.work
  unfold rngCombinations at h1
  omega

/-- The number of drawn entries, and 31 more, is below 2 ^ 64. -/
theorem room_lt {s : Setting} {x : SmallSize} (h : Asked s x) :
    x.columns * x.tau + 31 < 2 ^ 64 := by
  have ht := tau_pos h
  rcases h.room with h0 | h1
  · omega
  · have := (Nat.le_div_iff_mul_le (by omega)).1 h1
    omega

/-- The same of the planner's finish: the plan that it makes of planSmall x 0 is the one round. -/
theorem small_finish (s : Setting) (x : SmallSize) (P : Planned)
    (h : finish s .request (planSmall x 0) = .ok P) :
    P.set = s ∧ P.rounds = [rngRound s x] ∧ Asked s x := by
  unfold finish at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      obtain ⟨⟨_, r⟩, t⟩ :=
        small_runs s x { set := s, scope := .request } q ⟨rfl, rfl, rfl, rfl, rfl⟩ hq
      refine ⟨rfl, ?_, t⟩
      show q.rounds.toList = _
      rw [r]
      rfl

/-- A group of layers: the rounds after moment 1 are the round of the matrix. -/
theorem layer_adds (s : Setting) (look : ForestSize) (y : LayerRounds) (x : SmallSize)
    (claims : Nat) (p q : PlanState) (hp : Idle s p)
    (h : layerRounds look y x claims 1 p = .ok ((), q)) :
    (Idle s q ∧ q.rounds = p.rounds.push (rngRound s x)) ∧ Asked s x := by
  have h' : (planSmall x 0 >>= fun _ => (pure () : Planning Unit)) p = .ok ((), q) := h
  obtain ⟨_, m, g, k⟩ := plan_bind h'
  obtain rfl : m = q := (Prod.mk.inj (Except.ok.inj k)).2
  exact small_runs s x p m hp g

/-- Attention: the rounds after moment 1 are the round of the matrix. -/
theorem attention_adds (s : Setting) (look : ForestSize) (y : AttentionRounds) (x : SmallSize)
    (p q : PlanState) (hp : Idle s p) (h : attentionRounds look y x 1 p = .ok ((), q)) :
    (Idle s q ∧ q.rounds = p.rounds.push (rngRound s x)) ∧ Asked s x := by
  have h' : ((pure () : Planning Unit) >>= fun _ => planSmall x 0 >>= fun _ =>
      (pure () : Planning Unit)) p = .ok ((), q) := h
  obtain ⟨_, m0, g0, k0⟩ := plan_bind h'
  obtain rfl : p = m0 := (Prod.mk.inj (Except.ok.inj g0)).2
  obtain ⟨_, m, g, k⟩ := plan_bind k0
  obtain rfl : m = q := (Prod.mk.inj (Except.ok.inj k)).2
  exact small_runs s x p m hp g

/-- The output head: the rounds after moment 1 are the round of the matrix. -/
theorem head_adds (s : Setting) (look : ForestSize) (y : HeadRounds) (x : SmallSize)
    (p q : PlanState) (hp : Idle s p) (h : headRounds look y x 1 p = .ok ((), q)) :
    (Idle s q ∧ q.rounds = p.rounds.push (rngRound s x)) ∧ Asked s x := by
  have h' : ((pure () : Planning Unit) >>= fun _ => planSmall x 0 >>= fun _ =>
      (pure () : Planning Unit)) p = .ok ((), q) := h
  obtain ⟨_, m0, g0, k0⟩ := plan_bind h'
  obtain rfl : p = m0 := (Prod.mk.inj (Except.ok.inj g0)).2
  obtain ⟨_, m, g, k⟩ := plan_bind k0
  obtain rfl : m = q := (Prod.mk.inj (Except.ok.inj k)).2
  exact small_runs s x p m hp g

/-- With one instance the bound is the number 1 * 2 ^ -x.tau, exactly. -/
theorem rngRound_error (s : Setting) (x : SmallSize) (h : s.instances ≤ 1) :
    (rngRound s x).error = ⟨1, -(x.tau : Int)⟩ := by
  have hi : ¬ 1 < s.instances := Nat.not_lt.mpr h
  simp only [rngRound, rngError, scaled, hi, if_false]
  rfl

/-- With one instance and a combination or more the round's mark wordFault is false. -/
theorem rngRound_word (s : Setting) (x : SmallSize) (h : s.instances ≤ 1) (ht : 1 ≤ x.tau) :
    (rngRound s x).wordFault = false := by
  have he : rngError s x = ⟨1, -(x.tau : Int)⟩ := rngRound_error s x h
  have h0 : (x.tau != 0) = true := by
    simp only [bne_iff_ne, ne_eq]
    omega
  show wordFaultOf (rngDraws x) (rngError s x) = false
  rw [he]
  simp [wordFaultOf, rngDraws, Binary.isZero, h0]

/-- The entry of the round: the name and eleven numbers. -/
theorem rngRound_entry (s : Setting) (x : SmallSize) :
    (rngRound s x).entry =
      { name := "RNG", count := 1, work := s.workOf .small .request, msg := 0, roots := 0,
        answers := 0, drawE := 0, drawNZ := 0, poss := 0, logN := 0, trits := x.columns * x.tau,
        rows := 0 } := rfl

/-- Every setting that is read from a parameter file has one instance. -/
theorem settingOf_instances (l : Lines) : (settingOf l).instances = 1 := rfl

/-- The premise is not empty: at the planner's default setting its finish accepts a test with 3
columns. -/
theorem small_ok :
    (finish {} .request (planSmall { columns := 3, tau := 128, digits := default } 0)).isOk =
      true := by
  decide

/-- The same at a setting in which the round has 20 bits of work. -/
theorem small_ok_work :
    (finish { workSmall := ⟨20, 0, 0⟩ } .request
      (planSmall { columns := 3, tau := 108, digits := default } 0)).isOk = true := by
  decide

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.small_runs
#print axioms OnBytes.Tie.Pv.Tail.tau_pos
#print axioms OnBytes.Tie.Pv.Tail.room_lt
#print axioms OnBytes.Tie.Pv.Tail.small_finish
#print axioms OnBytes.Tie.Pv.Tail.layer_adds
#print axioms OnBytes.Tie.Pv.Tail.attention_adds
#print axioms OnBytes.Tie.Pv.Tail.head_adds
#print axioms OnBytes.Tie.Pv.Tail.rngRound_error
#print axioms OnBytes.Tie.Pv.Tail.rngRound_word
#print axioms OnBytes.Tie.Pv.Tail.small_ok
#print axioms OnBytes.Tie.Pv.Tail.small_ok_work
