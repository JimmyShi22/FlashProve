-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/Runs.lean: tools on a list that is written as records and runs ("how often, which
record"), at any type, so that a test on a list of some ten thousand members is settled by a test on
its distinct records, or by one walk along its runs.

The library's written lists of rounds (Johnson/G/DryKeyLit.lean, Johnson/G/DryProofLit.lean) and of
priced rounds (Johnson/G/PricedKeyLit.lean) stand as records and runs, and Lean's kernel is to
evaluate tests on them.

All that is here are tools. They hold of all lists; they name no file, no plan and no description of
the protocol. No row is to be laid on any of them.

Definitions.
  `unrunG recs runs`: the list of a list of runs. It has the text of `Johnson.G.unrunR`, at any
    type.
  `expand l`: the list of a list of runs "how often, which value". `valRuns recs runs`: the runs
    with each index replaced by its record; a run whose index names no record is dropped.
  `cntG q a l`: a plus the number of members with q, counted along the runs, each step forced
    (`force`, Johnson/G/Eager.lean).
  `sameBy r k A B`: one walk along two lists of runs, which need not be cut alike. It says yes if r
    says yes of the two values at every place and the two lists end together. k bounds the steps;
    with too small a k it says no.
Statements and proofs.
  `unrunG_eq`: the two ways of writing the list agree.
  `mem_unrunG`: a member is a record. `mem_unrunG_of`: a record that a run names, not 0 times, is a
    member.
  `all_of_recs`, `all_of_runs`: a test that every record passes, or every record that a run names,
    is passed by every member. `not_all_of_run`: a record that fails and that a run names, not 0
    times, makes the test on the list say no.
  `map_unrunG`, `filter_expand`, `filter_unrunG`, `cntG_eq`, `count_unrunG`: a function, a filter
    and a count, along the runs.
  `sameBy_sound`: a yes of the walk gives the relation place by place (`List.Forall₂`).
  `map_eq_of_walk`, `map_eq_of_same`: so two lists have the same image under two functions.
  `eq_of_forall2`, `expand_ones`: for a walk of a plain list against a list of runs.

The definitions `unrunG`, `valRuns` and `sameBy` have moved, unturned, into
Johnson/G/RunsDefs.lean, a file of definitions alone, which this file imports.

Limits. `sameBy` is sound. That it says yes wherever the relation holds is not shown: a run of 0
members can make it say no, and which k is enough is not shown. That the kernel gets through a given
list is seen where a theorem is checked.
-/
import Mathlib.Data.List.Forall2
import Johnson.G.Eager
import Johnson.G.RunsDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.Runs
open Johnson.G (force force_eq)

variable {α β γ : Type}

/-- The list of a list of runs: how often, which value. -/
def expand : List (Nat × α) → List α
  | [] => []
  | x :: xs => List.replicate x.1 x.2 ++ expand xs

/-! ## The two ways of writing the list -/

theorem unrunG_eq (recs : List α) (runs : List (Nat × Nat)) :
    unrunG recs runs = expand (valRuns recs runs) := by
  induction runs with
  | nil => rfl
  | cons x xs ih =>
    have e : unrunG recs (x :: xs) =
        (recs[x.2]?).elim [] (List.replicate x.1) ++ unrunG recs xs := by
      simp [unrunG, List.flatMap_cons]
    rw [e, ih]
    cases h : recs[x.2]? with
    | none => simp [valRuns, h]
    | some r => simp [valRuns, h, expand]

/-! ## Members -/

theorem mem_expand {l : List (Nat × α)} {x : α} (h : x ∈ expand l) : ∃ n, (n, x) ∈ l := by
  induction l with
  | nil => simp [expand] at h
  | cons y ys ih =>
    simp only [expand, List.mem_append] at h
    rcases h with h | h
    · obtain rfl := (List.mem_replicate.1 h).2
      exact ⟨y.1, List.mem_cons.2 (Or.inl rfl)⟩
    · obtain ⟨n, hn⟩ := ih h
      exact ⟨n, List.mem_cons_of_mem _ hn⟩

theorem mem_expand_of {l : List (Nat × α)} {n : Nat} {x : α} (h : (n + 1, x) ∈ l) :
    x ∈ expand l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [expand, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (List.mem_replicate.2 ⟨Nat.succ_ne_zero n, rfl⟩)
    · exact Or.inr (ih h)

theorem mem_valRuns {recs : List α} {runs : List (Nat × Nat)} {p : Nat × α}
    (h : p ∈ valRuns recs runs) : p.2 ∈ recs := by
  induction runs with
  | nil => simp [valRuns] at h
  | cons x xs ih =>
    cases hr : recs[x.2]? with
    | none =>
      simp only [valRuns, hr, Option.elim] at h
      exact ih h
    | some r =>
      simp only [valRuns, hr, Option.elim, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_of_getElem? hr
      · exact ih h

theorem mem_valRuns_of {recs : List α} {runs : List (Nat × Nat)} {c i : Nat} {r : α}
    (h : (c, i) ∈ runs) (hr : recs[i]? = some r) : (c, r) ∈ valRuns recs runs := by
  induction runs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp only [valRuns, hr, Option.elim]
      exact List.mem_cons.2 (Or.inl rfl)
    · cases hx : recs[x.2]? with
      | none =>
        simp only [valRuns, hx, Option.elim]
        exact ih h
      | some s =>
        simp only [valRuns, hx, Option.elim]
        exact List.mem_cons_of_mem _ (ih h)

/-- A member is a record. -/
theorem mem_unrunG {recs : List α} {runs : List (Nat × Nat)} {x : α}
    (h : x ∈ unrunG recs runs) : x ∈ recs := by
  rw [unrunG_eq] at h
  obtain ⟨n, hn⟩ := mem_expand h
  exact mem_valRuns hn

/-- A record that a run names, not 0 times, is a member. -/
theorem mem_unrunG_of {recs : List α} {runs : List (Nat × Nat)} {n i : Nat} {r : α}
    (h : (n + 1, i) ∈ runs) (hr : recs[i]? = some r) : r ∈ unrunG recs runs := by
  rw [unrunG_eq]
  exact mem_expand_of (mem_valRuns_of h hr)

/-! ## A test on all members -/

/-- A test that holds of all members of a list holds of all members of a list of its members. -/
theorem all_of_mem {f : α → Bool} {l l' : List α} (hs : ∀ x ∈ l', x ∈ l) (h : l.all f = true) :
    l'.all f = true :=
  List.all_eq_true.2 fun x hx => List.all_eq_true.1 h x (hs x hx)

/-- **Every record passes: every member passes.** -/
theorem all_of_recs {f : α → Bool} {recs : List α} (runs : List (Nat × Nat))
    (h : recs.all f = true) : (unrunG recs runs).all f = true :=
  all_of_mem (fun _ hx => mem_unrunG hx) h

/-- **Every record that a run names passes: every member passes.** -/
theorem all_of_runs {f : α → Bool} {recs : List α} {runs : List (Nat × Nat)}
    (h : (valRuns recs runs).all (fun x => f x.2) = true) : (unrunG recs runs).all f = true := by
  rw [unrunG_eq]
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨n, hn⟩ := mem_expand hx
  exact List.all_eq_true.1 h (n, x) hn

/-- A record that fails and that a run names, not 0 times: the test on the list says no. -/
theorem not_all_of_run {f : α → Bool} {recs : List α} {runs : List (Nat × Nat)} {n i : Nat} {r : α}
    (h : (n + 1, i) ∈ runs) (hr : recs[i]? = some r) (hf : f r = false) :
    (unrunG recs runs).all f = false := by
  cases hc : (unrunG recs runs).all f with
  | false => rfl
  | true =>
    have t := List.all_eq_true.1 hc r (mem_unrunG_of h hr)
    rw [hf] at t
    cases t

/-! ## A function, a filter, a count -/

theorem expand_map (f : α → β) (l : List (Nat × α)) :
    (expand l).map f = expand (l.map fun x => (x.1, f x.2)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [expand, List.map_cons, List.map_append, List.map_replicate, ih]

theorem valRuns_map (f : α → β) (recs : List α) (runs : List (Nat × Nat)) :
    (valRuns recs runs).map (fun x => (x.1, f x.2)) = valRuns (recs.map f) runs := by
  induction runs with
  | nil => rfl
  | cons x xs ih =>
    cases h : recs[x.2]? with
    | none =>
      have h' : (recs.map f)[x.2]? = none := by simp [h]
      simp only [valRuns, h, h', Option.elim]
      exact ih
    | some r =>
      have h' : (recs.map f)[x.2]? = some (f r) := by simp [h]
      simp only [valRuns, h, h', Option.elim, List.map_cons, ih]

/-- The image of the list is the list of the records' images. -/
theorem map_unrunG (f : α → β) (recs : List α) (runs : List (Nat × Nat)) :
    (unrunG recs runs).map f = unrunG (recs.map f) runs := by
  rw [unrunG_eq, unrunG_eq, expand_map, valRuns_map]

/-- A filter, along the runs. -/
theorem filter_expand (q : α → Bool) (l : List (Nat × α)) :
    (expand l).filter q = expand (l.filter fun x => q x.2) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hq : q x.2 <;> simp [expand, List.filter_append, hq, ih]

/-- The like for a list that is written as records and runs. -/
theorem filter_unrunG (q : α → Bool) (recs : List α) (runs : List (Nat × Nat)) :
    (unrunG recs runs).filter q = expand ((valRuns recs runs).filter fun x => q x.2) := by
  rw [unrunG_eq, filter_expand]

/-- a plus the number of members with q, counted along the runs. -/
def cntG (q : α → Bool) : Nat → List (Nat × α) → Nat
  | a, [] => a
  | a, x :: xs => force (a + if q x.2 then x.1 else 0) fun v => cntG q v xs

theorem cntG_eq (q : α → Bool) (l : List (Nat × α)) :
    ∀ a, cntG q a l = a + ((expand l).filter q).length := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    have c : ((List.replicate x.1 x.2).filter q).length = if q x.2 then x.1 else 0 := by
      cases hq : q x.2 <;> simp [hq]
    simp only [cntG, force_eq, ih, expand]
    rw [List.filter_append, List.length_append, c]
    omega

/-- The number of members with q of a list that is written as records and runs. -/
theorem count_unrunG (q : α → Bool) (recs : List α) (runs : List (Nat × Nat)) :
    ((unrunG recs runs).filter q).length = cntG q 0 (valRuns recs runs) := by
  rw [cntG_eq, unrunG_eq, Nat.zero_add]

/-! ## One walk along two lists of runs -/

theorem rep_add (n m : Nat) (a : α) :
    List.replicate (n + m) a = List.replicate n a ++ List.replicate m a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_right_comm n 1 m, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

theorem f2_app {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β} {m₁ : List α} {m₂ : List β},
    List.Forall₂ R l₁ l₂ → List.Forall₂ R m₁ m₂ → List.Forall₂ R (l₁ ++ m₁) (l₂ ++ m₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a t, h => .cons a (f2_app t h)

theorem f2_rep {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ∀ n : Nat, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => .cons h (f2_rep h n)

/-- **A yes of the walk gives the relation place by place.** -/
theorem sameBy_sound (r : α → β → Bool) :
    ∀ (k : Nat) (A : List (Nat × α)) (B : List (Nat × β)), sameBy r k A B = true →
      List.Forall₂ (fun a b => r a b = true) (expand A) (expand B)
  | 0, _, _, h => by simp [sameBy] at h
  | _ + 1, [], [], _ => .nil
  | _ + 1, [], _ :: _, h => by simp [sameBy] at h
  | _ + 1, _ :: _, [], h => by simp [sameBy] at h
  | k + 1, x :: xs, y :: ys, h => by
    have h' : (if r x.2 y.2 = true then
        (if x.1 = y.1 then sameBy r k xs ys
          else if x.1 < y.1 then sameBy r k xs ((y.1 - x.1, y.2) :: ys)
          else sameBy r k ((x.1 - y.1, x.2) :: xs) ys)
        else false) = true := h
    show List.Forall₂ _ (List.replicate x.1 x.2 ++ expand xs)
      (List.replicate y.1 y.2 ++ expand ys)
    by_cases hr : r x.2 y.2 = true
    · rw [if_pos hr] at h'
      by_cases e1 : x.1 = y.1
      · rw [if_pos e1] at h'
        rw [e1]
        exact f2_app (f2_rep (R := fun a b => r a b = true) hr y.1) (sameBy_sound r k _ _ h')
      · rw [if_neg e1] at h'
        by_cases lt : x.1 < y.1
        · rw [if_pos lt] at h'
          have ih : List.Forall₂ (fun a b => r a b = true) (expand xs)
              (List.replicate (y.1 - x.1) y.2 ++ expand ys) := sameBy_sound r k _ _ h'
          have hn : x.1 + (y.1 - x.1) = y.1 := by omega
          have e : List.replicate y.1 y.2 =
              List.replicate x.1 y.2 ++ List.replicate (y.1 - x.1) y.2 := by
            rw [← rep_add, hn]
          rw [e, List.append_assoc]
          exact f2_app (f2_rep (R := fun a b => r a b = true) hr x.1) ih
        · rw [if_neg lt] at h'
          have ih : List.Forall₂ (fun a b => r a b = true)
              (List.replicate (x.1 - y.1) x.2 ++ expand xs) (expand ys) :=
            sameBy_sound r k _ _ h'
          have hn : y.1 + (x.1 - y.1) = x.1 := by omega
          have e : List.replicate x.1 x.2 =
              List.replicate y.1 x.2 ++ List.replicate (x.1 - y.1) x.2 := by
            rw [← rep_add, hn]
          rw [e, List.append_assoc]
          exact f2_app (f2_rep (R := fun a b => r a b = true) hr y.1) ih
    · rw [if_neg hr] at h'
      cases h'

theorem map_eq_of_forall2 {f : α → γ} {g : β → γ} : ∀ {l : List α} {m : List β},
    List.Forall₂ (fun a b => f a = g b) l m → l.map f = m.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => congrArg₂ List.cons h (map_eq_of_forall2 t)

theorem eq_of_forall2 : ∀ {l m : List α}, List.Forall₂ (fun a b => a = b) l m → l = m
  | _, _, .nil => rfl
  | _, _, .cons h t => congrArg₂ List.cons h (eq_of_forall2 t)

/-- **Two lists of runs have the same image under two functions**, by one walk. -/
theorem map_eq_of_walk [DecidableEq γ] (f : α → γ) (g : β → γ) {A : List (Nat × α)}
    {B : List (Nat × β)} (k : Nat) (h : sameBy (fun a b => decide (f a = g b)) k A B = true) :
    (expand A).map f = (expand B).map g :=
  map_eq_of_forall2 ((sameBy_sound _ k _ _ h).imp fun _ _ H => of_decide_eq_true H)

/-- The like for two lists that are written as records and runs. -/
theorem map_eq_of_same [DecidableEq γ] (f : α → γ) (g : β → γ) {recsA : List α} {recsB : List β}
    {runsA runsB : List (Nat × Nat)} (k : Nat)
    (h : sameBy (fun a b => decide (f a = g b)) k (valRuns recsA runsA) (valRuns recsB runsB) =
      true) : (unrunG recsA runsA).map f = (unrunG recsB runsB).map g := by
  rw [unrunG_eq, unrunG_eq]
  exact map_eq_of_walk f g k h

/-- A plain list, as runs of one. -/
theorem expand_ones (l : List α) : expand (l.map fun x => (1, x)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

end Johnson.G.Runs

#print axioms Johnson.G.Runs.unrunG_eq
#print axioms Johnson.G.Runs.mem_expand
#print axioms Johnson.G.Runs.mem_expand_of
#print axioms Johnson.G.Runs.mem_valRuns
#print axioms Johnson.G.Runs.mem_valRuns_of
#print axioms Johnson.G.Runs.mem_unrunG
#print axioms Johnson.G.Runs.mem_unrunG_of
#print axioms Johnson.G.Runs.all_of_mem
#print axioms Johnson.G.Runs.all_of_recs
#print axioms Johnson.G.Runs.all_of_runs
#print axioms Johnson.G.Runs.not_all_of_run
#print axioms Johnson.G.Runs.expand_map
#print axioms Johnson.G.Runs.valRuns_map
#print axioms Johnson.G.Runs.map_unrunG
#print axioms Johnson.G.Runs.filter_expand
#print axioms Johnson.G.Runs.filter_unrunG
#print axioms Johnson.G.Runs.cntG_eq
#print axioms Johnson.G.Runs.count_unrunG
#print axioms Johnson.G.Runs.rep_add
#print axioms Johnson.G.Runs.f2_app
#print axioms Johnson.G.Runs.f2_rep
#print axioms Johnson.G.Runs.sameBy_sound
#print axioms Johnson.G.Runs.map_eq_of_forall2
#print axioms Johnson.G.Runs.eq_of_forall2
#print axioms Johnson.G.Runs.map_eq_of_walk
#print axioms Johnson.G.Runs.map_eq_of_same
#print axioms Johnson.G.Runs.expand_ones
