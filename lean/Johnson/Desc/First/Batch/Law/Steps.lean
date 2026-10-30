-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Steps.lean
(kind K9's soundness lemma): THEOREMS: THE HYPOTHESES OF K9's ROW ON ITS MOVES, BROUGHT DOWN TO ONE
DUTY A RUN: so that what a kind's files prove of ITS run of claims goes into the row as it stands.
K9's place is the draw and then STEPS OF ADDING: each gathers the claims of a list of runs, adds
them, and makes one quiet move behind.
  Step, Step.moves, movesOf, runsOf   a step (windows, the order's cut, its runs with their terms,
                the quiet move behind); its two moves; the moves and the runs of a list of steps.
  steps_moveOk  hms: MoveOk of every move, FROM RunOk of every run and QuietOk of every quiet move.
  gather_door, steps_door   hkd: the door's duty of every move, FROM the like of every run and quiet
                move.
  termsOf_append, terms_steps   the row's terms are the runs' terms in a row.
  steps_termsOk hok: the exponents differ and are at most plan + ties - 1, FROM the discipline of
                every run (Law/ExpsOk.lean: DiscFrom over the runs, their windows laid end to end).
  steps_isMoves, steps_drawMoves   hbm: the draw joined with the steps' blocks (K9.addsStep) is a
                draw with these moves.
Not claimed: RunOk, QuietOk, the door's duty or the discipline of any run (Law/K8Run.lean,
Law/K8Step.lean, Law/K8Disc.lean hold them for the smallness test's).

-/
import Johnson.Desc.First.Batch.Law.MovesRow
import Johnson.Desc.First.Batch.Law.MovesDoor
import Johnson.Desc.First.Batch.Law.ExpsRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where RunOf Window gather addsStep drawAlone)

variable {T P K : Type}

/-- A step of adding, its runs with their terms. -/
structure Step (T P K : Type) where
  ws : T → List Window
  cut : List (Nat × String)
  runs : List (TermedRun T P K)
  behind : T → Except String T

/-- Its two moves. -/
def Step.moves (s : Step T P K) : List (Termed T P K) :=
  [⟨.add (gather s.ws s.cut (s.runs.map (·.run))), fun n q y => termsRuns q y s.runs n,
      fun q => lenRuns q s.runs⟩,
   ⟨.quiet s.behind, fun _ _ _ => [], fun _ => 0⟩]

/-- The moves of a list of steps. -/
def movesOf (l : List (Step T P K)) : List (Termed T P K) := l.flatMap Step.moves

/-- Their runs, in a row. -/
def runsOf (l : List (Step T P K)) : List (TermedRun T P K) := l.flatMap (·.runs)

/-- **hms, from one duty a run.** -/
theorem steps_moveOk [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K)
    (Fx : P → T → Prop) (p : Where) (H : FitsM X O Fx p) (l : List (Step T P K))
    (hr : ∀ r ∈ runsOf l, RunOk ρ X O Fx r.run.2 r.tm r.len)
    (hq : ∀ s ∈ l, QuietOk X O Fx s.behind) : ∀ m ∈ movesOf l, MoveOk ρ X O Fx m := by
  intro m hm
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.1 hm
  simp only [Step.moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · exact gather_addOk ρ X O Fx p H s.ws s.cut s.runs fun r hr' =>
      hr r (List.mem_flatMap.2 ⟨s, hs, hr'⟩)
  · exact ⟨hq s hs, fun _ _ _ => rfl, fun _ => rfl⟩

/-- A gathering keeps the door if each of its runs does. -/
theorem gather_door (X : Lens T) (ws : T → List Window) (cut : List (Nat × String)) :
    ∀ (runs : List (RunOf T)),
      (∀ r ∈ runs, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → KeepsDoor X e e₁) →
      ∀ x x' : List Claim × T, runs.foldlM (gstep ws cut) x = .ok x' → KeepsDoor X x.2 x'.2
  | [], _, x, x', h => by
    have e : x = x' := Except.ok.inj h
    subst e
    exact fun a ha => ⟨a, ha, rfl, rfl⟩
  | r :: l, hr, x, x', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hz
    exact keepsDoor_trans X (hr r List.mem_cons_self _ _ _ _ hc)
      (gather_door X ws cut l (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) _ _ h)

/-- **hkd, from one duty a run.** -/
theorem steps_door (X : Lens T) (l : List (Step T P K))
    (hr : ∀ r ∈ runsOf l, ∀ n e c e₁, r.run.2 n e = .ok (c, e₁) → KeepsDoor X e e₁)
    (hq : ∀ s ∈ l, ∀ e e₁, s.behind e = .ok e₁ → KeepsDoor X e e₁) :
    ∀ m ∈ movesOf l, MoveDoor X m.move := by
  intro m hm
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.1 hm
  simp only [Step.moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · intro e c e₁ h
    rw [gather_eq] at h
    exact gather_door X s.ws s.cut (s.runs.map (·.run)) (fun r hr' => by
      obtain ⟨r0, h0, rfl⟩ := List.mem_map.1 hr'
      exact hr r0 (List.mem_flatMap.2 ⟨s, hs, h0⟩)) ([], e) (c, e₁) h
  · exact hq s hs

/-- The number of claims of a row of moves. -/
def lenM (p : P) : List (Termed T P K) → ℕ
  | [] => 0
  | m :: l => m.len p + lenM p l

theorem termsOf_append (p : P) (y : Bound K) : ∀ (a b : List (Termed T P K)) (n : ℕ),
    termsOf p y (a ++ b) n = termsOf p y a n ++ termsOf p y b (n + lenM p a)
  | [], _, _ => rfl
  | m :: a, b, n => by
    simp only [List.cons_append, termsOf, lenM, termsOf_append p y a b, List.append_assoc,
      Nat.add_assoc]

theorem lenM_runs (p : P) : ∀ rl : List (TermedRun T P K), lenM p (rl.map asMove) = lenRuns p rl
  | [] => rfl
  | r :: l => by
    simp only [List.map_cons, lenM, lenRuns, lenM_runs p l]
    rfl

/-- **The row's terms are the runs' terms in a row.** -/
theorem terms_steps (p : P) (y : Bound K) : ∀ (l : List (Step T P K)) (n : ℕ),
    termsOf p y (movesOf l) n = termsOf p y ((runsOf l).map asMove) n
  | [], _ => rfl
  | s :: l, n => by
    have e1 : movesOf (s :: l) = s.moves ++ movesOf l := rfl
    have e2 : runsOf (s :: l) = s.runs ++ runsOf l := rfl
    rw [e1, e2, List.map_append, termsOf_append, termsOf_append, terms_steps p y l, lenM_runs]
    simp only [Step.moves, termsOf, lenM, List.append_nil, Nat.add_zero, termsRuns_eq]

/-- **hok, from the discipline of every run.** ties: the runs, each with its number of equations. -/
theorem steps_termsOk [Field K] (p : P) (y : Bound K) (plan : ℕ) (l : List (Step T P K))
    (ties : List (TermedRun T P K × ℕ)) (he : ties.map (·.1) = runsOf l)
    (h : DiscFrom p y plan (ties.map fun r => (asMove r.1, r.2)) 0 0)
    (hp : lenAll p (ties.map fun r => (asMove r.1, r.2)) ≤ plan) :
    Desc.TermsOk K (termsOf p y (movesOf l) 0)
      (plan + tieAll (ties.map fun r => (asMove r.1, r.2)) - 1) := by
  have e : (runsOf l).map asMove = (ties.map fun r => (asMove r.1, r.2)).map (·.1) := by
    rw [← he, List.map_map, List.map_map]
    rfl
  rw [terms_steps, e]
  exact termsOk_of_disc p y plan _ h hp

/-- A step's block is its two moves. -/
theorem steps_isMoves {Cl : Type} (X : Lens T) (p : Where) (what : String)
    (counts : List (String × (T → Bool))) (s : Step T P K) :
    IsMoves X (s.moves.map (·.move))
      (addsStep (Cl := Cl) X p what counts s.ws s.cut (s.runs.map (·.run)) s.behind) := by
  show IsMoves X [.add (gather s.ws s.cut (s.runs.map (·.run))), .quiet s.behind] _
  exact isMoves_addsStep X p what counts s.ws s.cut (s.runs.map (·.run)) s.behind

/-- **hbm: the draw joined with the steps' blocks is a draw with these moves.** dress: each step's
name and its counts in front. -/
theorem steps_drawMoves {Cl : Type} (X : Lens T) (p : Where) (name : String)
    (l : List (Step T P K × Where × String × List (String × (T → Bool)))) :
    DrawMoves X p ((movesOf (l.map (·.1))).map (·.move))
      ((l.map fun s => addsStep (Cl := Cl) X s.2.1 s.2.2.1 s.2.2.2 s.1.ws s.1.cut
        (s.1.runs.map (·.run)) s.1.behind).foldl (fun acc x => acc.andThen name x)
        (drawAlone X p)) := by
  have h := drawMoves_joined (Cl := Cl) X p name (drawAlone X p) rfl rfl
    (l.map fun s => (addsStep (Cl := Cl) X s.2.1 s.2.2.1 s.2.2.2 s.1.ws s.1.cut
      (s.1.runs.map (·.run)) s.1.behind, s.1.moves.map (·.move)))
    (fun q hq => by
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 hq
      exact steps_isMoves X s.2.1 s.2.2.1 s.2.2.2 s.1)
  have e1 : ((l.map fun s => (addsStep (Cl := Cl) X s.2.1 s.2.2.1 s.2.2.2 s.1.ws s.1.cut
      (s.1.runs.map (·.run)) s.1.behind, s.1.moves.map (·.move))).flatMap (·.2)) =
      (movesOf (l.map (·.1))).map (·.move) := by
    simp only [movesOf, List.flatMap_map, List.map_flatMap]
  rw [e1, List.map_map] at h
  exact h

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.steps_moveOk
#print axioms VerifiableInference.Desc.K9L.steps_door
#print axioms VerifiableInference.Desc.K9L.terms_steps
#print axioms VerifiableInference.Desc.K9L.steps_termsOk
#print axioms VerifiableInference.Desc.K9L.steps_drawMoves
