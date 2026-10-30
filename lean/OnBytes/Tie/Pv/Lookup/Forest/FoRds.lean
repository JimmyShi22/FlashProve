-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoRds.lean.
From the calls of a run to the rounds of a view, once, for any run.

* `Rds l`: the list of calls l is a row of rounds, each of one of six kinds: elements are received
and
  one element is drawn; the same with the draw that never gives 0; elements are received and nothing
    is
  drawn; the sum of a hiding polynomial is received and one element is drawn; one element is drawn;
    a
  point is drawn. `Rds.append`, `Rds.closed`.
* `rds_took`: if such a list of calls runs from a context on a view with no message open, then it
takes
  some rounds off the view, leaves no message open, and these rounds, read as plain data, are the
    calls
  read as plain data.
* `HCout2V`: the statement that the lookup's routine returns the flat function's end values, over
the view:
  from a context on a view with no message open. `hcOut2V_of`: it follows from the statement over
    the
  calls of a run, `HCout2R`, in which the calls are a row of rounds. Both say
  also how many scalars each round sends and how many elements it draws: the numbers of `Fo.planF`
    at
  the record's shape. Without this no typed transcript could be named that has these plain data.
  Both also ask that the state before the run fits (Sized). Their proofs are hcOut2R and hcOut2V
  (OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean).

-/
import OnBytes.Tie.Pv.Lookup.Port.FoHeard

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

/-- The calls are a row of rounds. -/
inductive Rds : List Ev → Prop
  | nil : Rds []
  | read (n : ℕ) (v : Array OnBytes.E) (r : RoundName) (x : OnBytes.E) {l : List Ev} :
      Rds l → Rds (.read n v :: .ans r x :: l)
  | readNZ (n : ℕ) (v : Array OnBytes.E) (r : RoundName) (x : OnBytes.E) {l : List Ev} :
      Rds l → Rds (.read n v :: .ansNZ r x :: l)
  | values (n : ℕ) (v : Array OnBytes.E) (r : RoundName) {l : List Ev} :
      Rds l → Rds (.read n v :: .empty r :: l)
  | sum (mu : OnBytes.E) (r : RoundName) (x : OnBytes.E) {l : List Ev} :
      Rds l → Rds (.sum mu :: .ans r x :: l)
  | ans (r : RoundName) (x : OnBytes.E) {l : List Ev} : Rds l → Rds (.ans r x :: l)
  | point (r : RoundName) (n : ℕ) (v : Array OnBytes.E) {l : List Ev} :
      Rds l → Rds (.point r n v :: l)

theorem Rds.append {l₁ l₂ : List Ev} (h1 : Rds l₁) (h2 : Rds l₂) : Rds (l₁ ++ l₂) := by
  induction h1 with
  | nil => exact h2
  | read n v r x _ ih => exact .read n v r x ih
  | readNZ n v r x _ ih => exact .readNZ n v r x ih
  | values n v r _ ih => exact .values n v r ih
  | sum mu r x _ ih => exact .sum mu r x ih
  | ans r x _ ih => exact .ans r x ih
  | point r n v _ ih => exact .point r n v ih

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem Rds.closed {l : List Ev} (h : Rds l) : Closed ρ l := by
  induction h with
  | nil => rfl
  | read _ _ _ _ _ ih => exact ih
  | readNZ _ _ _ _ _ ih => exact ih
  | values _ _ _ _ ih => exact ih
  | sum _ _ _ _ ih => exact ih
  | ans _ _ _ ih => exact ih
  | point _ _ _ _ ih => exact ih

theorem took_nil {c : Ctx} (h : Clean c) : Took c [] c := ⟨h, h, rfl⟩

theorem took_cons {c c₁ c' : Ctx} {rv : Fmt.RoundView} {rvs : List Fmt.RoundView} (h1 : Round c rv c₁)
    (h2 : Took c₁ rvs c') : Took c (rv :: rvs) c' :=
  ⟨h1.1, h2.2.1, by rw [h1.2.2, h2.2.2]; rfl⟩

/-- Two calls, then the rest. -/
theorem evs_two {e₁ e₂ : Ev} {l : List Ev} {c c' : Ctx} (h : Evs (e₁ :: e₂ :: l) c c') :
    ∃ c₁, Evs [e₁, e₂] c c₁ ∧ Evs l c₁ c' :=
  (evs_append [e₁, e₂] l c c').1 h

theorem evs_head {e : Ev} {l : List Ev} {c c' : Ctx} (h : Evs (e :: l) c c') :
    ∃ c₁, Evs [e] c c₁ ∧ Evs l c₁ c' :=
  (evs_append [e] l c c').1 h

/-- A row of rounds takes its rounds off the view. -/
theorem rds_took {l : List Ev} (hl : Rds l) : ∀ {c c' : Ctx}, Clean c → Evs l c c' →
    ∃ rv, Took c rv c' ∧ flEv ρ l = rv.map (rdRV ρ) := by
  induction hl with
  | nil =>
    intro c c' hc h
    obtain rfl : c' = c := h
    exact ⟨[], took_nil hc, rfl⟩
  | read n v r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_read n v r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ v.toList.map ρ.val, [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | readNZ n v r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_readNZ n v r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ v.toList.map ρ.val, [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | values n v r _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_values n v r c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ v.toList.map ρ.val, []) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | sum mu r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_sum mu r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ [ρ.val mu], [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | ans r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_head h
    obtain ⟨rv, hr, hs, hd⟩ := round_ans r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([], [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | point r n v _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_head h
    obtain ⟨rv, hr, hs, hd, _⟩ := round_point r n v c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([], v.toList.map ρ.val) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl

end

/-- Over the calls of a run, which are a row of rounds. -/
def HCout2R : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (F F' : Fork) (c c' : Ctx) (g : Forest.Heard),
    Forest.pad calls pub lid F c = .ok ((g, F'), c') → Sized F → Clean c →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    ∃ l : List Ev, Evs l c c' ∧ Rds l ∧
      (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = planF g.shape ∧
      HeardIs ρ g F' (endsOf g.shape lm F.next (flEv ρ l))

/-- Over the view, from a context on a view with no message open. -/
def HCout2V : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (F F' : Fork) (c c' : Ctx) (g : Forest.Heard),
    Forest.pad calls pub lid F c = .ok ((g, F'), c') → Sized F → Clean c →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    ∃ rv : List Fmt.RoundView, Took c rv c' ∧
      rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      HeardIs ρ g F' (endsOf g.shape lm F.next (rv.map (rdRV ρ)))

theorem hcOut2V_of (h : HCout2R) : HCout2V := by
  intro K _ ρ calls pub lid lm F F' c c' g hr hF hc
  obtain ⟨h1, h2, l, hl, hR, hs, hH⟩ := h K ρ calls pub lid lm F F' c c' g hr hF hc
  obtain ⟨rv, ht, he⟩ := rds_took ρ hR hc hl
  refine ⟨h1, h2, rv, ht, ?_, he ▸ hH⟩
  rw [he, List.map_map] at hs
  rw [← hs]
  refine List.map_congr_left fun r _ => ?_
  simp [rdRV]

/-- HCout2 (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean), in which the rounds taken are given, follows.
-/
theorem hcOut2_of (h : HCout2V) : HCout2 := by
  intro K _ ρ calls pub lid lm F F' c c' g rv hr hF ht
  obtain ⟨h1, h2, rv', ht', _, hH⟩ := h K ρ calls pub lid lm F F' c c' g hr hF ht.1
  have e : rv' = rv := List.append_cancel_right (ht'.2.2.symm.trans ht.2.2)
  exact ⟨h1, h2, e ▸ hH⟩

end Fo
