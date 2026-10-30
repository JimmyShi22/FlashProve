-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscRun.lean: how the routines of the sub-proofs' masked sumcheck
(OnBytes/Model/Psc.lean) follow each other: what a run that returns has read, drawn and left.

Definitions, and theorems with their proofs. A routine (`SubM`, OnBytes/Model/Hide.lean) is run from
a state F of the sub-proof and a context c of the channel, and returns a value, a state and a
context, or fails. Every theorem here has the form: if the run returns, then it was made of these
calls of the channel's own routines (`trSum`, `trAnswer`, `trRead`, `trAnswerNotZero`, `trEmpty`,
OnBytes/Model/Rounds.lean; `Ev` has `trPoint` too, which callers of these routines use and none of
the six does), with these results, and the value and the state that it leaves are these.

Main names:
  `Ev`: one call of a routine of the channel, with its result. `Ev.At e c c'`: that call, run from
    the context c, returns that result and leaves c'. `Evs l c c'`: the calls of the list l, one
    after the other, lead from c to c'.
  `bind_ok`, `lift_ok`, `must_ok`, `get_ok`, `take_ok`, `ask_ok`, `change_ok`, `pure_ok`: a run of
    each way in which routines are put together.
  `pscBeginAt_ok`, `pscBegin_ok`, `pscRound_ok`, `roundIn_ok`, `pscEnds_ok`, `pscRow_ok`: the six
    routines.

Limits: nothing is said where a routine fails, and nothing on what the channel's routines do to a
context. Nothing on soundness, on an honest prover or on hiding.



-/
import OnBytes.Model.Psc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

/-- One call of a routine of the channel, with its result. -/
inductive Ev where
  /-- the sum of a hiding polynomial is received -/
  | sum (x : E)
  /-- a round is closed and one element drawn -/
  | ans (r : RoundName) (x : E)
  /-- a round is closed and one element drawn by the rule that never gives 0 -/
  | ansNZ (r : RoundName) (x : E)
  /-- n elements are received -/
  | read (n : Nat) (v : Array E)
  /-- a round is closed in which nothing is drawn -/
  | empty (r : RoundName)
  /-- a round is closed and n elements are drawn -/
  | point (r : RoundName) (n : Nat) (v : Array E)

/-- The call, run from c, returns its result and leaves c'. -/
def Ev.At : Ev → Ctx → Ctx → Prop
  | .sum x, c, c' => trSum c = .ok (x, c')
  | .ans r x, c, c' => trAnswer r c = .ok (x, c')
  | .ansNZ r x, c, c' => trAnswerNotZero r c = .ok (x, c')
  | .read n v, c, c' => trRead n c = .ok (v, c')
  | .empty r, c, c' => trEmpty r c = .ok ((), c')
  | .point r n v, c, c' => trPoint r n c = .ok (v, c')

/-- The calls of a list, one after the other. -/
def Evs : List Ev → Ctx → Ctx → Prop
  | [], c, c' => c' = c
  | e :: l, c, c' => ∃ c1, e.At c c1 ∧ Evs l c1 c'

/-- Calls after calls. -/
theorem Evs.append : ∀ {l m : List Ev} {c c1 c2 : Ctx}, Evs l c c1 → Evs m c1 c2 → Evs (l ++ m) c c2
  | [], _, _, _, _, h, h' => by
    obtain rfl : _ = _ := h
    exact h'
  | _ :: _, _, _, _, _, ⟨d, h0, h1⟩, h' => ⟨d, h0, Evs.append h1 h'⟩

/-- One call as a list of calls. -/
theorem Evs.one {e : Ev} {c c' : Ctx} (h : e.At c c') : Evs [e] c c' := ⟨c', h, rfl⟩

section Ways
variable {α β : Type}

/-- A run of «x, then f» returns exactly if a run of x returns and f's run from there does. -/
theorem bind_ok (x : SubM α) (f : α → SubM β) (F : Fork) (c : Ctx) (r : (β × Fork) × Ctx) :
    (x >>= f) F c = .ok r ↔ ∃ a G c1, x F c = .ok ((a, G), c1) ∧ f a G c1 = .ok r := by
  show (x F c >>= fun p => f p.1.1 p.1.2 p.2) = .ok r ↔ _
  cases h : x F c with
  | error e =>
    show (Except.error e : Except Failure _) = .ok r ↔ _
    simp
  | ok y =>
    obtain ⟨⟨a, G⟩, c1⟩ := y
    show f a G c1 = .ok r ↔ _
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h'
      exact ⟨a, G, c1, ⟨⟨rfl, rfl⟩, rfl⟩, h'⟩
    · rintro ⟨_, _, _, ⟨⟨rfl, rfl⟩, rfl⟩, h'⟩
      exact h'

/-- A routine that only returns a value leaves state and context. -/
theorem pure_ok (a : α) (F : Fork) (c : Ctx) (r : (α × Fork) × Ctx) :
    (pure a : SubM α) F c = .ok r ↔ r = ((a, F), c) := by
  show (Except.ok ((a, F), c) : Except Failure _) = .ok r ↔ _
  simp [eq_comm]

/-- A lifted call of the channel leaves the state. -/
theorem lift_ok (b : Blk α) (F : Fork) (c : Ctx) (r : (α × Fork) × Ctx) :
    (StateT.lift b : SubM α) F c = .ok r ↔ ∃ a c1, b c = .ok (a, c1) ∧ r = ((a, F), c1) := by
  show (b c >>= fun p => (Except.ok ((p.1, F), p.2) : Except Failure _)) = .ok r ↔ _
  cases h : b c with
  | error e =>
    show (Except.error e : Except Failure _) = .ok r ↔ _
    simp
  | ok y =>
    obtain ⟨a, c1⟩ := y
    show (Except.ok ((a, F), c1) : Except Failure _) = .ok r ↔ _
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h'
      exact ⟨a, c1, ⟨rfl, rfl⟩, h'.symm⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h'⟩
      exact h'.symm

/-- A public condition returns exactly if it is true, and leaves state and context. -/
theorem must_ok (b : Bool) (F : Fork) (c : Ctx) (r : (Unit × Fork) × Ctx) :
    SubM.must b F c = .ok r ↔ b = true ∧ r = (((), F), c) := by
  unfold SubM.must
  rw [lift_ok]
  cases b with
  | false =>
    constructor
    · rintro ⟨_, _, h, _⟩
      exact absurd h (by simp [Blk.must])
    · rintro ⟨h, _⟩
      cases h
  | true =>
    constructor
    · rintro ⟨a, c1, h, rfl⟩
      have e : (((), c) : Unit × Ctx) = (a, c1) := Except.ok.inj h
      cases e
      exact ⟨rfl, rfl⟩
    · rintro ⟨_, rfl⟩
      exact ⟨(), c, rfl, rfl⟩

/-- Unwrapping a value returns exactly if it is there, and leaves state and context. -/
theorem get_ok (x : Option α) (F : Fork) (c : Ctx) (r : (α × Fork) × Ctx) :
    SubM.get x F c = .ok r ↔ ∃ a, x = some a ∧ r = ((a, F), c) := by
  unfold SubM.get
  rw [lift_ok]
  cases x with
  | none => simp [Blk.get]
  | some a =>
    simp only [Blk.get, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨_, rfl, rfl⟩
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩

/-- A step on the state that returns a value leaves the context. -/
theorem take_ok (f : Fork → Option (α × Fork)) (F : Fork) (c : Ctx) (r : (α × Fork) × Ctx) :
    SubM.take f F c = .ok r ↔ ∃ y, f F = some y ∧ r = (y, c) := by
  simp only [SubM.take]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm]

/-- Reading a value off the state leaves state and context. -/
theorem ask_ok (f : Fork → Option α) (F : Fork) (c : Ctx) (r : (α × Fork) × Ctx) :
    SubM.ask f F c = .ok r ↔ ∃ a, f F = some a ∧ r = ((a, F), c) := by
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm]

/-- A step on the state leaves the context. -/
theorem change_ok (f : Fork → Option Fork) (F : Fork) (c : Ctx) (r : (Unit × Fork) × Ctx) :
    SubM.change f F c = .ok r ↔ ∃ G, f F = some G ∧ r = (((), G), c) := by
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm]

end Ways

/-- The state with n more slots taken. -/
def took (F : Fork) (n : Nat) : Fork := { F with next := F.next + n }

/-- Taking n slots returns the next slot and always succeeds. -/
theorem takeSlots_ok (n : Nat) (F : Fork) (c : Ctx) (r : (Nat × Fork) × Ctx) :
    SubM.takeSlots n F c = .ok r ↔ r = ((F.next, took F n), c) := by
  unfold SubM.takeSlots
  rw [take_ok]
  simp [took]

/-- The beginning: one slot is taken; the sum is received; eps is drawn. -/
theorem pscBeginAt_ok (target : E) (F G : Fork) (c c' : Ctx) (p : Psc)
    (h : pscBeginAt target F c = .ok ((p, G), c')) :
    ∃ mu eps, Evs [.sum mu, .ans .pscEpsilon eps] c c' ∧ G = took F 1 ∧
      p = { target := target, first := F.next, eps := eps,
            claim := addE mu (mulE eps target) } := by
  unfold pscBeginAt at h
  rw [bind_ok] at h
  obtain ⟨first, F1, c1, h1, h⟩ := h
  rw [takeSlots_ok] at h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (first = F.next ∧ F1 = took F 1) ∧ c1 = c := by
    simpa [Prod.ext_iff] using h1
  rw [bind_ok] at h
  obtain ⟨mu, F2, c2, h2, h⟩ := h
  unfold SubM.readSum at h2
  rw [lift_ok] at h2
  obtain ⟨mu', c2', h2, e2⟩ := h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (mu = mu' ∧ F2 = took F 1) ∧ c2 = c2' := by
    simpa [Prod.ext_iff] using e2
  rw [bind_ok] at h
  obtain ⟨eps, F3, c3, h3, h⟩ := h
  unfold SubM.answer at h3
  rw [lift_ok] at h3
  obtain ⟨eps', c3', h3, e3⟩ := h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (eps = eps' ∧ F3 = took F 1) ∧ c3 = c3' := by
    simpa [Prod.ext_iff] using e3
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨mu, eps, ⟨_, h2, _, h3, rfl⟩, rfl, rfl⟩

/-- The beginning, from the form C of the sum: the target is C's public part at the state before. -/
theorem pscBegin_ok (C : Aff) (F G : Fork) (c c' : Ctx) (p : Psc)
    (h : pscBegin C F c = .ok ((p, G), c')) :
    ∃ target mu eps, F.publicPart C = some target ∧ Evs [.sum mu, .ans .pscEpsilon eps] c c' ∧
      G = took F 1 ∧
      p = { start := C, started := true, target := target, first := F.next, eps := eps,
            claim := addE mu (mulE eps target) } := by
  unfold pscBegin at h
  rw [bind_ok] at h
  obtain ⟨target, F1, c1, h1, h⟩ := h
  unfold SubM.publicPart at h1
  rw [ask_ok] at h1
  obtain ⟨t', ht, e1⟩ := h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨p0, F2, c2, h2, h⟩ := h
  obtain ⟨mu, eps, hev, rfl, rfl⟩ := pscBeginAt_ok _ _ _ _ _ _ h2
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨_, mu, eps, ht, hev, rfl, rfl⟩

/-- One round: d - 1 elements are received, the challenge is drawn, d - 1 slots are taken. -/
theorem pscRound_ok (p : Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) (F G : Fork) (c c' : Ctx)
    (r : E) (p' : Psc) (h : pscRound p w draw F c = .ok (((r, p'), G), c')) :
    ∃ sent c1, (w.fits && weightHeld w) = true ∧ trRead (w.d - 1) c = .ok (sent, c1) ∧
      sent.size + 1 = w.d ∧ draw c1 = .ok (r, c') ∧ G = took F (w.d - 1) ∧
      p' = { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) r,
                    vars := p.vars.push w, r := p.r.push r } := by
  unfold pscRound at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨hw, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨sent, F2, c2, h2, h⟩ := h
  unfold SubM.read at h2
  rw [lift_ok] at h2
  obtain ⟨sent', c2', h2, e2⟩ := h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  rw [bind_ok] at h
  obtain ⟨_, F3, c3, h3, h⟩ := h
  rw [must_ok] at h3
  obtain ⟨hs, e3⟩ := h3
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  rw [bind_ok] at h
  obtain ⟨r0, F4, c4, h4, h⟩ := h
  rw [lift_ok] at h4
  obtain ⟨r0', c4', h4, e4⟩ := h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e4
  rw [bind_ok] at h
  obtain ⟨_, F5, c5, h5, h⟩ := h
  rw [takeSlots_ok] at h5
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h5
  rw [pure_ok] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨_, _, hw, h2, by simpa using hs, h4, rfl, rfl⟩

/-- One round of a given form. -/
theorem roundIn_ok (form : RoundForm) (p : Psc) (z : E) (degree : Nat) (F G : Fork) (c c' : Ctx)
    (r : E) (p' : Psc) (h : roundIn form p z degree F c = .ok (((r, p'), G), c')) :
    ∃ w sent, p.ended = false ∧ form.weight z degree = some w ∧
      (w.fits && weightHeld w) = true ∧ sent.size + 1 = w.d ∧
      Evs [.read (w.d - 1) sent, .ans .pscRound r] c c' ∧ G = took F (w.d - 1) ∧
      p' = { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) r,
                    vars := p.vars.push w, r := p.r.push r } := by
  unfold roundIn at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨he, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨w, F2, c2, h2, h⟩ := h
  rw [get_ok] at h2
  obtain ⟨w', hw, e2⟩ := h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  obtain ⟨sent, c3, hf, hr, hs, hd, rfl, rfl⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ h
  exact ⟨_, sent, by simpa using he, hw, hf, hs, ⟨_, hr, _, hd, rfl⟩, rfl, rfl⟩

/-- The round in the further variable Y, and the round of the n end values: degreeInY elements are
received, beta is drawn by the rule that never gives 0, degreeInY slots are taken; n elements are
received and their round is closed; n slots are taken, from e on, and the n elements are put under
them with the factor beta. -/
theorem pscEnds_ok (p : Psc) (degreeInY n : Nat) (F G : Fork) (c c' : Ctx) (e : Nat) (p' : Psc)
    (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) :
    ∃ sent beta v, p.ended = false ∧ 1 ≤ degreeInY ∧ 1 ≤ n ∧ sent.size = degreeInY ∧ v.size = n ∧
      Evs [.read degreeInY sent, .ansNZ .pscY beta, .read n v, .empty .pscValues] c c' ∧
      e = F.next + degreeInY ∧
      (took F (degreeInY + n)).hideRun e v beta = some G ∧
      p' = { p with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.atZero (degreeInY + 1)).complete sent.toList p.claim) beta,
        vars := p.vars.push (OnBytes.Psc.Weight.atZero (degreeInY + 1)), r := p.r.push beta,
        ended := true } := by
  unfold pscEnds at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨hm, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨⟨beta, p1⟩, F2, c2, h2, h⟩ := h
  obtain ⟨sent, c3, -, hr, hs, hd, rfl, rfl⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ h2
  simp only [] at h
  rw [bind_ok] at h
  obtain ⟨v, F3, c4, h3, h⟩ := h
  unfold SubM.read at h3
  rw [lift_ok] at h3
  obtain ⟨v', c4', h3, e3⟩ := h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  rw [bind_ok] at h
  obtain ⟨_, F4, c5, h4, h⟩ := h
  rw [must_ok] at h4
  obtain ⟨hv, e4⟩ := h4
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e4
  rw [bind_ok] at h
  obtain ⟨_, F5, c6, h5, h⟩ := h
  unfold SubM.empty at h5
  rw [lift_ok] at h5
  obtain ⟨_, c6', h5, e5⟩ := h5
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
  rw [bind_ok] at h
  obtain ⟨e0, F6, c7, h6, h⟩ := h
  rw [takeSlots_ok] at h6
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h6
  rw [bind_ok] at h
  obtain ⟨_, F7, c8, h7, h⟩ := h
  rw [change_ok] at h7
  obtain ⟨G', hG, e7⟩ := h7
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e7
  rw [pure_ok] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm
  have hd1 : (OnBytes.Psc.Weight.atZero (degreeInY + 1)).d - 1 = degreeInY := rfl
  rw [hd1] at hr
  refine ⟨sent, beta, v, hm.1.1, hm.1.2, hm.2, ?_, by simpa using hv,
    ⟨_, hr, _, hd, _, h3, _, h5, rfl⟩, rfl, ?_, rfl⟩
  · have : sent.size + 1 = degreeInY + 1 := hs
    omega
  · have ht : took (took F ((OnBytes.Psc.Weight.atZero (degreeInY + 1)).d - 1)) n =
        took F (degreeInY + n) := by
      simp only [took, hd1, Nat.add_assoc]
    rw [← ht]
    exact hG

/-- The claim that a sumcheck leaves: nothing is received or drawn; the coefficients of the hiding
polynomial are put under the slots from p.first on: 0 shown, the factor -1. -/
theorem pscRow_ok (p : Psc) (S0 : E) (kept : Aff) (F G : Fork) (c c' : Ctx) (row : Aff) (p' : Psc)
    (h : pscRow p S0 kept F c = .ok (((row, p'), G), c')) :
    p.rowMade = false ∧ p.started = true ∧ p.vars.isEmpty = false ∧ p.r.size = p.vars.size ∧
      c' = c ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G ∧
      row = p.rowForm S0 kept ∧ p' = { p with rowMade := true } := by
  unfold pscRow at h
  rw [bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨hm, e1⟩ := h1
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  rw [change_ok] at h2
  obtain ⟨G', hG, e2⟩ := h2
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  rw [pure_ok] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
  exact ⟨hm.1.1.1, hm.1.1.2, hm.1.2, hm.2, rfl, hG, rfl, rfl⟩

end OnBytes.PscRun

#print axioms OnBytes.PscRun.pscBegin_ok
#print axioms OnBytes.PscRun.roundIn_ok
#print axioms OnBytes.PscRun.pscEnds_ok
#print axioms OnBytes.PscRun.pscRow_ok
