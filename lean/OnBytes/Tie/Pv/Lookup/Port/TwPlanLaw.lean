-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwPlanLaw.lean.
What the planner's lookup writes into a plan, as a pure list: a theorem on the function
OnBytes.Params.planLookup itself.

The planner (OnBytes/Params/Planner.lean) is a routine on a plan that is being written: it may
refuse, and else it adds rounds. This file says which rounds the lookup's routine adds, for every
setting, every scope and all six fields of its argument (v, d, mu, shifted, live, parts).

Main definitions.
  errOf s sc (a, kind): the planner's error of a round whose chance of failure is a quotient: kind
    1: a of |E|; kind 2: a of |E| - 1; kind 0: a round without a verifier's message. Here |E| is
    s.cardE. It is the planner's own Bound.ratio, times the number of instances in a request's own
    rounds, cut to the Binary that the plan's verdict reads.
  Step s sc x a b L: wherever the routine x does not refuse, on a plan with setting s and scope sc
    in which a bytes are open and no root or answer: setting and scope stay, b bytes are open and no
    root or answer, and the plan's rounds grow by exactly the list L: each round's entry, in all
    twelve fields, and its error. A round's other fields (group, why, rests, scope, wordFault) are
    not read.
  lookI: the lookup's list, in the planner's own letters.
Main statement. planLookup_step: Step s sc (planLookup x) 0 0 (lookI ...).
What is not claimed: that the planner does not refuse: where it refuses the statement says nothing.
Nor that the binary number errOf s sc (a, kind) is at least the quotient for which it stands.

-/
import OnBytes.Params.SubRounds
import OnBytes.Tie.Pv.Lookup.Lists.TwPlan
import Cb.Pv.Lookup.Lists.TwErr

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params TwPlan

/-- the planner's error of a round whose ratio is (a, kind): kind 1: a of |E|; 2: a of |E| − 1; 0:
no verifier's message. In a request's own rounds it counts once for each instance, as in `close`
(OnBytes/Params/Planner.lean). -/
def errOf (s : Setting) (sc : Scope) (r : Nat × Nat) : Binary :=
  if r.2 = 0 then {}
  else
    let b := Bound.ratio r.1 (if r.2 = 1 then s.cardE else s.cardE - 1)
    (if sc == .request && 1 < s.instances then b * Bound.ofNat s.instances else b).error

abbrev Item : Type := Fmt.Entry × (Nat × Nat)

def seen (r : PlanRound) : Fmt.Entry × Binary := (r.entry, r.error)
def said (s : Setting) (sc : Scope) (x : Item) : Fmt.Entry × Binary := (x.1, errOf s sc x.2)
def view (p : PlanState) : List (Fmt.Entry × Binary) := p.rounds.toList.map seen

def Step (s : Setting) (sc : Scope) (x : Planning Unit) (a b : Nat) (L : List Item) : Prop :=
  ∀ p p', p.set = s → p.scope = sc → p.openBytes = a → p.openRoots = 0 → p.openAnswers = 0 → x p =
      .ok ((), p') →
    p'.set = s ∧ p'.scope = sc ∧ p'.openBytes = b ∧ p'.openRoots = 0 ∧ p'.openAnswers = 0 ∧ view p'
        = view p ++ L.map (said s sc)

section
variable {s : Setting} {sc : Scope}

theorem bind_ok {α β : Type} {x : Planning α} {f : α → Planning β} {p : PlanState}
    {r : β × PlanState}
    (h : (x >>= f) p = .ok r) : ∃ a p1, x p = .ok (a, p1) ∧ f a p1 = .ok r := by
  have h' : (match x p with | .ok (a, p1) => f a p1 | .error e => .error e) = Except.ok r := by
    cases hx : x p with
    | error e => simp [bind, StateT.bind, Except.bind, hx] at h
    | ok v => simpa [bind, StateT.bind, Except.bind, hx] using h
  cases hx : x p with
  | error e => rw [hx] at h'; cases h'
  | ok v => rw [hx] at h'; exact ⟨v.1, v.2, rfl, h'⟩

theorem step_pure (a : Nat) : Step s sc (pure ()) a a [] := by
  intro p p' h1 h2 h3 h4 h5 h
  cases h
  exact ⟨h1, h2, h3, h4, h5, by simp⟩

theorem step_seq {x y : Planning Unit} {a b c : Nat} {L₁ L₂ : List Item} (hx : Step s sc x a b L₁)
    (hy : Step s sc y b c L₂) :
    Step s sc (do x; y) a c (L₁ ++ L₂) := by
  intro p p' h1 h2 h3 h4 h5 h
  obtain ⟨_, p1, e1, e2⟩ := bind_ok h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx p p1 h1 h2 h3 h4 h5 e1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hy p1 p' a1 a2 a3 a4 a5 e2
  exact ⟨b1, b2, b3, b4, b5, by rw [b6, a6, List.map_append, List.append_assoc]⟩

theorem step_set {f : Setting → Planning Unit} {a b : Nat} {L : List Item}
    (h : Step s sc (f s) a b L) :
    Step s sc (do let t ← theSetting; f t) a b L := by
  intro p p' h1 h2 h3 h4 h5 hh
  obtain ⟨t, p1, e1, e2⟩ := bind_ok hh
  cases e1
  rw [h1] at e2
  exact h p p' h1 h2 h3 h4 h5 e2

/-- a test: what follows may use that it was true -/
theorem step_needs {c : Bool} {why : String} {y : Planning Unit} {a b : Nat} {L : List Item}
    (h : c = true → Step s sc y a b L) :
    Step s sc (do needs c why; y) a b L := by
  intro p p' h1 h2 h3 h4 h5 hh
  obtain ⟨_, p1, e1, e2⟩ := bind_ok hh
  cases c with
  | true =>
    cases e1
    exact h rfl p p' h1 h2 h3 h4 h5 e2
  | false => cases e1

theorem step_scalars (k : Nat) : Step s sc (planScalars k) 0 (24 * k) [] := by
  intro p p' h1 h2 h3 h4 h5 h
  have e : planScalars k p = .ok ((), { p with openBytes := p.openBytes + 24 * k }) := rfl
  rw [e] at h
  cases h
  exact ⟨h1, h2, by
      show p.openBytes + 24 * k = 24 * k; rw [h3, Nat.zero_add], h4, h5, by simp [view]⟩

/-- what close does where it does not refuse -/
theorem close_ok {name : String} {why : ErrorKind} {err : Bound} {d : Draws} {p p' : PlanState}
    (h : close name why err d p = .ok ((), p')) :
    p' = { p with
      rounds := p.rounds.push
        { entry := { name, work := p.set.workOf why p.scope, msg := p.openBytes,
                     roots := p.openRoots,
                     answers := p.openAnswers, drawE := d.drawE, drawNZ := d.drawNZ,
                     poss := d.poss, logN := d.logN, trits := d.trits, rows := d.rows },
          error :=
            (if p.scope == .request && 1 < p.set.instances then err * Bound.ofNat p.set.instances
                else err).error,
          group := d.group, why := why, rests := d.rests, scope := p.scope,
          wordFault :=
            wordFaultOf d (if p.scope == .request && 1 < p.set.instances then err * Bound.ofNat
                p.set.instances else err).error },
      openBytes := 0, openRoots := 0, openAnswers := 0 } := by
  unfold close at h
  dsimp only at h
  generalize (if (p.scope == .request && decide (1 < p.set.instances)) = true then err * Bound.ofNat
      p.set.instances else err) = e at h ⊢
  split at h
  · cases h
  · cases h
    rfl

/-- a round with a verifier's message, priced at a field quotient, after k scalars -/
theorem step_close (name : String) (k a kind : Nat) (hk : kind = 1 ∨ kind = 2) (d : Draws)
    (hd : d.poss = 0 ∧ d.logN = 0 ∧ d.trits = 0 ∧ d.rows = 0) :
    Step s sc (close name .field (Bound.ratio a (if kind = 1 then s.cardE else s.cardE - 1)) d)
        (24 * k) 0
      [(rd (s.workOf .field sc) name k d.drawE d.drawNZ, (a, kind))] := by
  intro p p' h1 h2 h3 h4 h5 h
  obtain ⟨d1, d2, d3, d4⟩ := hd
  have hz : kind ≠ 0 := by rcases hk with h | h <;> omega
  subst h1 h2
  rw [close_ok h]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [view, Array.toList_push, List.map_append, List.map_cons, List.map_nil, seen, said,
      errOf, rd, h3, h4, h5, d1, d2, d3, d4, if_neg hz]

theorem step_closeE (name : String) (k a : Nat) (d : Draws)
    (hd : d.poss = 0 ∧ d.logN = 0 ∧ d.trits = 0 ∧ d.rows = 0) :
    Step s sc (close name .field (Bound.ratio a s.cardE) d) (24 * k) 0
        [(rd (s.workOf .field sc) name k d.drawE d.drawNZ, (a, 1))] :=
  step_close name k a 1 (.inl rfl) d hd
theorem step_closeNZ (name : String) (k a : Nat) (d : Draws)
    (hd : d.poss = 0 ∧ d.logN = 0 ∧ d.trits = 0 ∧ d.rows = 0) :
    Step s sc (close name .field (Bound.ratio a (s.cardE - 1)) d) (24 * k) 0
        [(rd (s.workOf .field sc) name k d.drawE d.drawNZ, (a, 2))] :=
  step_close name k a 2 (.inr rfl) d hd

/-- a round in which the verifier says nothing, after k scalars -/
theorem step_none (name : String) (k : Nat) : Step s sc (closeNone name) (24 * k) 0
    [(rdNone name k, (0, 0))] := by
  intro p p' h1 h2 h3 h4 h5 h
  unfold closeNone at h
  split at h
  · cases h
  · cases h
    refine ⟨h1, h2, rfl, h4, rfl, ?_⟩
    simp [view, seen, said, errOf, rdNone, h3, h5]

end

/-! ### the lists -/

/-- TwPlan.pscN and TwErr.pscR, zipped by construction -/
def pscI (wk : Nat) (degs : List Nat) (withY : Bool) (gY vals : Nat) : List Item :=
  [(rd wk "PSC epsilon" 1 1, (1, 1))] ++ degs.map (fun g => (rd wk "PSC round" g 1, (g, 1))) ++
    if withY then [(rd wk "PSC Y" gY 1 1, (gY, 2)), (rdNone "PSC values" vals, (0, 0))] else []

def lineI (wk : Nat) : Item := (rd wk "LINE" 0 1, (1, 1))
def shiftI (wk d : Nat) : Item := (shiftN wk, (2 ^ d, 1))

/-- the levels l, l + 1, .. of a product tree, as many as the fuel -/
def levelsI (wk more : Nat) : Nat → Nat → List Item
  | 0, _ => []
  | fuel + 1, l => pscI wk (List.replicate (l + more) 2) true 2 2 ++ [lineI wk] ++ levelsI wk more
      fuel (l + 1)

def timesI (L : List Item) : Nat → List Item
  | 0 => []
  | k + 1 => L ++ timesI L k

def eachI (f : Nat → List Item) : List Nat → List Item
  | [] => []
  | a :: t => f a ++ eachI f t

/-- The lookup's list, in the planner's own letters. -/
def lookI (wk : Nat) (shifted : Bool) (keys w : Nat) (parts : List Nat) (d mu : Nat) : List Item :=
  (if shifted then [shiftI wk d] else []) ++ ([(rd wk "LKP" 0 1, (keys - 1, 1))] ++
      (pscI wk [] true 3 3 ++ (timesI (pscI wk [] true 3 2) (w - 2) ++
    (timesI (pscI wk [] true 2 2) (parts.length - 1) ++
        ([(rd wk "JOIN" 0 mu, (mu, 1))] ++ (eachI (fun v => levelsI wk 0 v 0) parts ++
            (levelsI wk mu d 0 ++
      (pscI wk (List.replicate d 2 ++ List.replicate mu 1) false 2 2 ++
          ([(rd wk "ZERO" 0 (mu + d), (mu + d, 1))] ++ pscI wk (List.replicate (mu + d) 2) true 2
              1)))))))))

section
variable {s : Setting} {sc : Scope}

theorem step_rounds : ∀ gs : List Nat, Step s sc (planPscRounds s gs) 0 0
    ((gs.map (· - 1)).map fun g => (rd (s.workOf .field sc) "PSC round" g 1, (g, 1)))
  | [] => step_pure 0
  | g :: gs => step_seq (step_scalars (g - 1)) (step_seq
      (step_closeE "PSC round" (g - 1) (g - 1) _ ⟨rfl, rfl, rfl, rfl⟩) (step_rounds gs))

theorem step_psc (x : PscSize) : Step s sc (planPsc x) 0 0
    (pscI (s.workOf .field sc) (x.degree.map (· - 1)) x.withY x.degreeY x.values) := by
  unfold planPsc
  refine step_set ?_
  have tail : Step s sc (if x.withY = true then (do
      planScalars x.degreeY
      close "PSC Y" .field (fieldErrorNonzero s x.degreeY)
          { drawE := 1, drawNZ := 1, priced := .roundItself }
      planScalars x.values
      closeNone "PSC values") else pure ()) 0 0
      (if x.withY then [(rd (s.workOf .field sc) "PSC Y" x.degreeY 1 1, (x.degreeY, 2)),
          (rdNone "PSC values" x.values, (0, 0))] else []) := by
    cases x.withY with
    | false => exact step_pure 0
    | true =>
      exact step_seq (step_scalars _) (step_seq (step_closeNZ "PSC Y" _ _ _ ⟨rfl, rfl, rfl, rfl⟩)
          (step_seq (step_scalars _) (step_none _ _)))
  have h :=
    step_seq (step_scalars (s := s) (sc := sc) 1) (step_seq
        (step_closeE "PSC epsilon" 1 1 { drawE := 1, priced := .settingAlone } ⟨rfl, rfl, rfl, rfl⟩)
    (step_seq (step_rounds x.degree) tail))
  simpa [pscI, List.append_assoc] using h

theorem step_line : Step s sc planLine 0 0 [lineI (s.workOf .field sc)] :=
  step_set (step_closeE "LINE" 0 1 { drawE := 1, priced := .settingAlone } ⟨rfl, rfl, rfl, rfl⟩)
theorem step_join (k : Nat) : Step s sc (planJoin k) 0 0
    [(rd (s.workOf .field sc) "JOIN" 0 k, (k, 1))] :=
  step_set (step_closeE "JOIN" 0 k { drawE := k, priced := .roundItself } ⟨rfl, rfl, rfl, rfl⟩)
theorem step_zero (k : Nat) : Step s sc (planZero k) 0 0
    [(rd (s.workOf .field sc) "ZERO" 0 k, (k, 1))] :=
  step_set (step_closeE "ZERO" 0 k { drawE := k, priced := .roundItself } ⟨rfl, rfl, rfl, rfl⟩)
theorem step_shift (d : Nat) : Step s sc (planShift (2 ^ d)) 0 0 [shiftI (s.workOf .field sc) d] :=
  step_set (step_closeE "LKP shift" 0 (2 ^ d) { drawE := 1, priced := .callersWord }
      ⟨rfl, rfl, rfl, rfl⟩)

theorem rep3 (k : Nat) : (List.replicate k 3).map (· - 1) = List.replicate k 2 := by simp
theorem rep2 (k : Nat) : (List.replicate k 2).map (· - 1) = List.replicate k 1 := by simp

theorem step_levels (more : Nat) : ∀ fuel l, Step s sc (planTreeLevels more fuel l) 0 0
    (levelsI (s.workOf .field sc) more fuel l)
  | 0, _ => step_pure 0
  | fuel + 1, l => by
    have h1 := step_psc (s := s) (sc := sc) { degree := List.replicate (l + more) 3 }
    rw [show ({ degree := List.replicate (l + more) 3 } : PscSize).degree.map (· - 1) =
        List.replicate (l + more) 2 from rep3 _] at h1
    have h := step_seq h1 (step_seq step_line (step_levels more fuel (l + 1)))
    simpa [levelsI, List.append_assoc] using h

theorem step_times {x : Planning Unit} {L : List Item} (h : Step s sc x 0 0 L) : ∀ n,
    Step s sc (times n x) 0 0 (timesI L n)
  | 0 => step_pure 0
  | n + 1 => step_seq h (step_times h n)

theorem step_each {f : Nat → Planning Unit} {g : Nat → List Item}
    (h : ∀ a, Step s sc (f a) 0 0 (g a)) : ∀ l, Step s sc (forEach l f) 0 0 (eachI g l)
  | [] => step_pure 0
  | a :: t => step_seq (h a) (step_each h t)

/-- What the planner's lookup adds to a plan, in the planner's own letters. -/
theorem planLookup_step (x : LookupSize) :
    Step s sc (planLookup x) 0 0
      (lookI (s.workOf .field sc) x.shifted (sumT ((if x.parts.isEmpty then [x.v] else x.parts).map
          (2 ^ ·)))
        (if x.live != 0 then x.live else 2 ^ min x.mu 6)
            (if x.parts.isEmpty then [x.v] else x.parts) x.d x.mu) := by
  unfold planLookup
  refine step_set (step_needs fun _ => step_needs fun _ => ?_)
  have p1 := step_psc (s := s) (sc := sc) { degreeY := 3, values := 3 }
  have p2 := step_psc (s := s) (sc := sc) { degreeY := 3, values := 2 }
  have p3 := step_psc (s := s) (sc := sc) {}
  have p4 :=
    step_psc (s := s) (sc := sc) { degree := List.replicate x.d 3 ++ List.replicate x.mu 2,
                                   withY := false }
  have p5 :=
    step_psc (s := s) (sc := sc) { degree := List.replicate (x.mu + x.d) 3, degreeY := 2,
                                   values := 1 }
  rw [show ({ degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false } :
      PscSize).degree.map (· - 1) = List.replicate x.d 2 ++ List.replicate x.mu 1 by
    show (List.replicate x.d 3 ++ List.replicate x.mu 2).map (· - 1) = _
    rw [List.map_append, rep3, rep2]] at p4
  rw [show ({ degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 } :
      PscSize).degree.map (· - 1) = List.replicate (x.mu + x.d) 2 from rep3 _] at p5
  have rest :=
    step_seq (step_closeE (s := s) (sc := sc) "LKP" 0
        (sumT ((if x.parts.isEmpty then [x.v] else x.parts).map (2 ^ ·)) - 1)
            { drawE := 1, priced := .callersWord } ⟨rfl, rfl, rfl, rfl⟩)
    (step_seq p1 (step_seq (step_times p2 ((if x.live != 0 then x.live else 2 ^ min x.mu 6) - 2))
    (step_seq (step_times p3 ((if x.parts.isEmpty then [x.v] else x.parts).length - 1))
        (step_seq (step_join x.mu)
      (step_seq (step_each (fun v => step_levels 0 v 0)
          (if x.parts.isEmpty then [x.v] else x.parts)) (step_seq (step_levels x.mu x.d 0)
      (step_seq p4 (step_seq (step_zero (x.mu + x.d)) p5))))))))
  cases x.shifted with
  | true => exact step_seq (step_shift x.d) rest
  | false => exact step_seq (step_pure 0) rest

end
end TwLaw
