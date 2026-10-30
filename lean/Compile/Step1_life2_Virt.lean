-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_life2_Virt.lean: renumbering of tokens (words of this library: lean/GLOSSARY.md).

The compiled prover is a token program (`Step`, Rom/Defer.lean), in which a secret string is a
token, and a token is a number: the index of its string in the list of all strings sampled so far.
The stateless prover of the scheme starts every session from the list of the setup's strings, so
that the first new token of every session has the same number N₀. The experiment of deferred
programming keeps one list for the whole run, which only grows. A program may compute with a number
as it likes, so "the same program at other numbers behaves alike" is false in general.

This file avoids the question. `virt N₀ δ c` is the program c under a renumbering: c is shown the
numbers that it would see if the δ strings after the first N₀ did not exist. The theorem `run_virt`
is not in this file but in Compile/Step1_life2_VirtMany.lean. It says, for every program c and for
both modes of Rom/Defer.lean: the run of virt N₀ δ c from a state D with WF N₀ δ D, mapped by `view`
(which forgets those δ strings and the marked queries charged to them; marked queries:
`Step.marked`, marked evaluations in Rom/Defer.lean), is the run of c from view D.
-/
import Rom.Defer
noncomputable section -- Lean tags what it cannot compile

namespace Compile
namespace Life2
open Rom

/-! ## Part 1. Numbers and lists -/

section Numbers

variable (N₀ δ : ℕ)

/-- A number is visible if it is not one of the δ numbers from N₀ on. -/
def vis (t : ℕ) : Bool := decide (t < N₀) || decide (N₀ + δ ≤ t)
/-- from the numbers that the program sees to the numbers of the experiment -/
def up (v : ℕ) : ℕ := if v < N₀ then v else v + δ
/-- and back -/
def down (t : ℕ) : ℕ := if t < N₀ then t else t - δ

theorem vis_iff (t : ℕ) : vis N₀ δ t = true ↔ t < N₀ ∨ N₀ + δ ≤ t := by simp [vis]

theorem vis_up (v : ℕ) : vis N₀ δ (up N₀ δ v) = true := by
  rw [vis_iff]
  unfold up
  split <;> omega

theorem down_up (v : ℕ) : down N₀ δ (up N₀ δ v) = v := by
  unfold down up
  split_ifs <;> omega

theorem up_down {t : ℕ} (h : vis N₀ δ t = true) : up N₀ δ (down N₀ δ t) = t := by
  rw [vis_iff] at h
  unfold up down
  split_ifs <;> omega

theorem up_injective : Function.Injective (up N₀ δ) := fun a b h => by
  have h1 := congrArg (down N₀ δ) h
  rwa [down_up, down_up] at h1

theorem down_eq_iff {t : ℕ} (h : vis N₀ δ t = true) (v : ℕ) : down N₀ δ t = v ↔ t = up N₀ δ v :=
  ⟨fun h1 => by rw [← h1, up_down N₀ δ h], fun h1 => by rw [h1, down_up]⟩

/-- the strings without the δ strings from index N₀ on -/
def viewVals (l : List Bits) : List Bits := l.take N₀ ++ l.drop (N₀ + δ)

variable {N₀ δ}

theorem length_viewVals {l : List Bits} (h : N₀ + δ ≤ l.length) :
    (viewVals N₀ δ l).length + δ = l.length := by
  simp only [viewVals, List.length_append, List.length_take, List.length_drop]
  omega

theorem viewVals_append {l : List Bits} (h : N₀ + δ ≤ l.length) (x : Bits) :
    viewVals N₀ δ (l ++ [x]) = viewVals N₀ δ l ++ [x] := by
  unfold viewVals
  rw [List.take_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega), List.append_assoc]

theorem getD_viewVals {l : List Bits} (h : N₀ + δ ≤ l.length) (v : ℕ) :
    (viewVals N₀ δ l).getD v [] = l.getD (up N₀ δ v) [] := by
  unfold viewVals up
  simp only [List.getD_eq_getElem?_getD]
  by_cases hv : v < N₀
  · rw [if_pos hv, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hv]
  · rw [if_neg hv, List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    congr 2
    simp only [List.length_take]
    omega

variable (N₀ δ)

/-- the visible ones among a list of numbers, as the program sees them -/
def viewShown (l : List ℕ) : List ℕ := (l.filter (vis N₀ δ)).map (down N₀ δ)

theorem contains_viewShown (l : List ℕ) (v : ℕ) :
    (viewShown N₀ δ l).contains v = l.contains (up N₀ δ v) := by
  rw [Bool.eq_iff_iff]
  simp only [viewShown, List.contains_iff_mem, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hv⟩, rfl⟩
    rwa [up_down N₀ δ hv]
  · intro h
    exact ⟨_, ⟨h, vis_up N₀ δ v⟩, down_up N₀ δ v⟩

theorem viewShown_append_up (l ts : List ℕ) :
    viewShown N₀ δ (l ++ ts.map (up N₀ δ)) = viewShown N₀ δ l ++ ts := by
  unfold viewShown
  rw [List.filter_append, List.map_append]
  congr 1
  rw [List.filter_eq_self.2 (by
    intro t ht
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ht
    exact vis_up N₀ δ v), List.map_map]
  conv_rhs => rw [← List.map_id ts]
  exact List.map_congr_left fun v _ => down_up N₀ δ v

end Numbers

/-! ## Part 2. Releases -/

section View

variable {S : OSpec} (N₀ δ : ℕ)




variable {N₀ δ}


/-- what the release of one marked query does to the table -/
def wr (m : Bool) (T : Table S) (o : S.ι) (pt : S.Dom o) (ans : S.Rng o) : Table S :=
  if m then (match T o pt with | none => T.set o pt ans | some _ => T) else T

theorem releaseAll_cons_pos {m : Bool} {shown : List ℕ} {e : Ev S}
    (h : (!e.released && shown.contains e.charged) = true) (es : List (Ev S)) (T : Table S) :
    releaseAll m shown (e :: es) T =
      ({ e with released := true } :: (releaseAll m shown es (wr m T e.o e.pt e.ans)).1,
        (releaseAll m shown es (wr m T e.o e.pt e.ans)).2) := by
  rw [releaseAll, if_pos h]
  cases hT : T e.o e.pt <;> simp only [wr, hT]

theorem releaseAll_cons_neg {m : Bool} {shown : List ℕ} {e : Ev S}
    (h : ¬ (!e.released && shown.contains e.charged) = true) (es : List (Ev S)) (T : Table S) :
    releaseAll m shown (e :: es) T =
      (e :: (releaseAll m shown es T).1, (releaseAll m shown es T).2) := by
  rw [releaseAll, if_neg h]

theorem not_cond {e : Ev S} {shown : List ℕ}
    (h : e.released = true ∨ shown.contains e.charged = false) :
    ¬ (!e.released && shown.contains e.charged) = true := by
  rcases h with h | h <;> rw [h] <;> simp

/-- What a release does to the list: it sets flags, and only of marked queries that are charged to
shown tokens. -/
theorem mem_releaseAll {m : Bool} {shown : List ℕ} {evs : List (Ev S)} {T : Table S} {x : Ev S}
    (hx : x ∈ (releaseAll m shown evs T).1) :
    ∃ e ∈ evs, (x = e ∧ ¬ (!e.released && shown.contains e.charged) = true)
      ∨ (x = { e with released := true } ∧ (!e.released && shown.contains e.charged) = true) := by
  induction evs generalizing T with
  | nil => exact absurd hx (by simp [releaseAll])
  | cons e es ih =>
    by_cases hcond : (!e.released && shown.contains e.charged) = true
    · rw [releaseAll_cons_pos hcond, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨e, List.mem_cons_self, Or.inr ⟨rfl, hcond⟩⟩
      · obtain ⟨e', he', h⟩ := ih hx
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · rw [releaseAll_cons_neg hcond, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨x, List.mem_cons_self, Or.inl ⟨rfl, hcond⟩⟩
      · obtain ⟨e', he', h⟩ := ih hx
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩


end View

/-! ## Part 3. The program under the renumbering -/

section Virt

variable {S : OSpec} {sp : Split S} {α : Type} (N₀ δ : ℕ)

/-- The program c under the renumbering. c is shown the number t - δ for a new token t, and where c
names the token v the experiment is given up v. -/
def virt : Step S sp α → Step S sp α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => virt (k r)
  | .plain o q k => .plain o q fun r => virt (k r)
  | .fresh ℓ k => .fresh ℓ fun t => virt (k (t - δ))
  | .marked o t us pt inj k => .marked o (up N₀ δ t) (us.map (up N₀ δ)) pt inj fun v t' => virt (k v (t' - δ))
  | .reveal ts k => .reveal (ts.map (up N₀ δ)) fun vs => virt (k vs)


variable {N₀ δ}




end Virt

/-! ## Part 4. For what the renumbered program leaves as it was (`Many.frame_virt`,
Compile/Step1_life2_VirtMany.lean) -/

section Frame

variable {S : OSpec} {sp : Split S} {α : Type} {N₀ δ : ℕ}

/-- the marked queries that are charged to one of the δ strings -/
def deadEvs (N₀ δ : ℕ) (l : List (Ev S)) : List (Ev S) := l.filter fun e => !vis N₀ δ e.charged

theorem deadEvs_releaseAll (m : Bool) (shown : List ℕ) (evs : List (Ev S))
    (hin : ∀ e ∈ evs,
      vis N₀ δ e.charged = false → e.released = true ∨ shown.contains e.charged = false)
    (T : Table S) :
    deadEvs N₀ δ (releaseAll m shown evs T).1 = deadEvs N₀ δ evs := by
  induction evs generalizing T with
  | nil => rfl
  | cons e es ih =>
    have ih' := fun T => ih (fun x hx => hin x (List.mem_cons_of_mem _ hx)) T
    by_cases hcond : (!e.released && shown.contains e.charged) = true
    · have hv : vis N₀ δ e.charged = true := by
        by_contra hv
        rw [Bool.not_eq_true] at hv
        exact not_cond (hin e List.mem_cons_self hv) hcond
      rw [releaseAll_cons_pos hcond]
      simp only [deadEvs, List.filter_cons, hv, Bool.not_true, Bool.false_eq_true, if_false]
      exact ih' _
    · rw [releaseAll_cons_neg hcond]
      simp only [deadEvs, List.filter_cons]
      rw [show List.filter (fun e => !vis N₀ δ e.charged) (releaseAll m shown es T).1 =
              deadEvs N₀ δ (releaseAll m shown es T).1 from rfl, ih']
      rfl



end Frame

/-! ## Part 5. Two general facts on runs -/

section General

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- The run of "first c, then g". -/
theorem run_bind (m : Bool) (c : Step S sp α) (g : α → Step S sp β) :
    ∀ D : DSt S, (c.bind g).run m D = (c.run m D).bind fun x => (g x.1).run m x.2 := by
  induction c with
  | pure a => intro D; simp only [Step.bind, Step.run, PMF.pure_bind]
  | sample n k ih => intro D; simp only [Step.bind, Step.run, PMF.bind_bind, ih]
  | plain o q k ih => intro D; simp only [Step.bind, Step.run, PMF.bind_bind, ih]
  | fresh ℓ k ih => intro D; simp only [Step.bind, Step.run, PMF.bind_bind, ih]
  | marked o t us pt inj k ih =>
    intro D
    cases m
      <;> simp only [Step.bind, Step.run, PMF.bind_bind, ih, if_true, Bool.false_eq_true, if_false]
  | reveal ts k ih => intro D; simp only [Step.bind, Step.run, ih]

/-- The list of strings only grows. -/
theorem vals_prefix (m : Bool) (c : Step S sp α) :
    ∀ D : DSt S, ∀ x ∈ (c.run m D).support, D.vals <+: x.2.vals := by
  induction c with
  | pure a =>
    intro D x hx
    simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | sample n k ih =>
    intro D x hx
    simp only [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    exact ih r D x hx
  | plain o q k ih =>
    intro D x hx
    simp only [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨p, -, hx⟩ := hx
    have h := ih p.1 _ x hx
    exact h
  | fresh ℓ k ih =>
    intro D x hx
    simp only [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨u, -, hx⟩ := hx
    exact (List.prefix_append _ _).trans (ih _ _ x hx)
  | marked o t us pt inj k ih =>
    intro D x hx
    cases m with
    | true =>
      simp only [Step.run, if_true, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact (List.prefix_append _ _).trans (ih _ _ _ x hx)
    | false =>
      simp only [Step.run, Bool.false_eq_true, if_false, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact (List.prefix_append _ _).trans (ih _ _ _ x hx)
  | reveal ts k ih =>
    intro D x hx
    simp only [Step.run] at hx
    have h := ih _ _ x hx
    exact h

end General

end Life2
end Compile
