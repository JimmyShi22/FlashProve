-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_life2_VirtMany.lean: the run of a program under a renumbering of its tokens, for
programs whose marked queries hold several tokens (marked queries: `Step.marked`, marked evaluations
in Rom/Defer.lean; words of this library: lean/GLOSSARY.md).

Compile/Step1_life2_Virt.lean defines `virt N₀ δ c`, the token program c (`Step`, Rom/Defer.lean)
under a renumbering: c is shown the numbers that it would see if the δ strings after the first N₀
did not exist. Here it is shown for every program c that the run of `virt N₀ δ c` from a state with
`WF`, mapped by `view`, is the run of c from the mapped state. A marked query may hold further
tokens beside the one to which it is charged (in a batch: the right child in a node of a request
tree, the last shared chaining value in the first local query after the shared rounds; these words:
the head of Compile/Batch/Oracles.lean). Among what `WF` asks of the state: a marked query that
`view` keeps holds only tokens that it keeps, and one that it forgets only tokens that it forgets
(`vis`, Compile/Step1_life2_Virt.lean).

  `Many.view`        The state without the δ strings and the marked queries charged to them; the
                     further tokens of a marked query are renumbered too.
  `Many.run_virt`    ((virt N₀ δ c).run m D).map (id × view) = c.run m (view D), for both modes,
                     every program c and every state D with `WF`.
  `Many.frame_virt`  What the renumbered program leaves as it was: every state that a run of
                     `virt N₀ δ c` reaches from a state D with `WF` has `Frame N₀ δ D` (both modes).

Of Compile/Step1_life2_Virt.lean, Part 1, `virt`, `deadEvs` and the lemmas on releases are used.
-/
import Compile.Step1_life2_Virt

namespace Compile
namespace Life2
namespace Many
open Rom

/-! ## Part 1. Lists of numbers -/

section Lists

variable (N₀ δ : ℕ)

theorem map_down_map_up (l : List ℕ) : (l.map (up N₀ δ)).map (down N₀ δ) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun v _ => down_up N₀ δ v

theorem contains_map_up (l : List ℕ) (t : ℕ) :
    (l.map (up N₀ δ)).contains (up N₀ δ t) = l.contains t := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact List.mem_map_of_injective (up_injective N₀ δ)

variable {N₀ δ}

theorem contains_map_down {l : List ℕ} (h : ∀ u ∈ l, vis N₀ δ u = true) (t : ℕ) :
    (l.map (down N₀ δ)).contains t = l.contains (up N₀ δ t) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [up_down N₀ δ (h u hu)]
  · intro ht
    exact ⟨_, ht, down_up N₀ δ t⟩

theorem contains_up_of_unseen {l : List ℕ} (h : ∀ u ∈ l, vis N₀ δ u = false) (t : ℕ) :
    l.contains (up N₀ δ t) = false := by
  rw [Bool.eq_false_iff]
  intro ht
  have h1 := h _ (List.contains_iff_mem.1 ht)
  rw [vis_up] at h1
  exact Bool.noConfusion h1

theorem all_map_down {l : List ℕ} (h : ∀ u ∈ l, vis N₀ δ u = true) (shown : List ℕ) :
    (l.map (down N₀ δ)).all (viewShown N₀ δ shown).contains = l.all shown.contains := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    rw [List.map_cons, List.all_cons, List.all_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx),
      contains_viewShown, up_down N₀ δ (h u List.mem_cons_self)]

end Lists

/-! ## Part 2. States without the δ strings -/

section View

variable {S : OSpec} (N₀ δ : ℕ)

/-- the record of a marked query, with the numbers that the program sees -/
def ren (e : Ev S) : Ev S :=
  { e with
    charged := down N₀ δ e.charged, others := e.others.map (down N₀ δ), tail := down N₀ δ e.tail }

/-- the marked queries that are charged to visible tokens -/
def viewEvs (l : List (Ev S)) : List (Ev S) := (l.filter fun e => vis N₀ δ e.charged).map (ren N₀ δ)

/-- The state as the program sees it: without the δ strings from index N₀ on and without the
marked queries charged to them. -/
def view (D : DSt S) : DSt S :=
  { table := D.table, vals := viewVals N₀ δ D.vals, shown := viewShown N₀ δ D.shown,
    evs := viewEvs N₀ δ D.evs, nPlain := D.nPlain, viol := D.viol }

theorem viewEvs_cons_vis {e : Ev S} (h : vis N₀ δ e.charged = true) (l : List (Ev S)) :
    viewEvs N₀ δ (e :: l) = ren N₀ δ e :: viewEvs N₀ δ l := by
  simp [viewEvs, h]

theorem viewEvs_cons_dead {e : Ev S} (h : vis N₀ δ e.charged = false) (l : List (Ev S)) :
    viewEvs N₀ δ (e :: l) = viewEvs N₀ δ l := by
  simp [viewEvs, h]

theorem viewEvs_append (l l' : List (Ev S)) :
    viewEvs N₀ δ (l ++ l') = viewEvs N₀ δ l ++ viewEvs N₀ δ l' := by
  simp [viewEvs]

/-- What the marked queries must be like, for a given list of shown tokens. One that `view` keeps
has a tail that it keeps and holds only tokens that it keeps. One that is forgotten holds only
forgotten tokens; it can no longer be released; and if it was released, its tail and its further
tokens were shown. -/
structure EvsOK (shown : List ℕ) (evs : List (Ev S)) : Prop where
  tail : ∀ e ∈ evs, vis N₀ δ e.charged = true → vis N₀ δ e.tail = true
  seen : ∀ e ∈ evs, vis N₀ δ e.charged = true → ∀ u ∈ e.others, vis N₀ δ u = true
  unseen : ∀ e ∈ evs, vis N₀ δ e.charged = false → ∀ u ∈ e.others, vis N₀ δ u = false
  inert : ∀ e ∈ evs,
    vis N₀ δ e.charged = false → e.released = true ∨ shown.contains e.charged = false
  closed : ∀ e ∈ evs, vis N₀ δ e.charged = false → e.released = true →
    shown.contains e.tail = true ∧ e.others.all shown.contains = true

variable {N₀ δ}

theorem EvsOK.of_cons {shown : List ℕ} {e : Ev S}
    {evs : List (Ev S)} (h : EvsOK N₀ δ shown (e :: evs)) : EvsOK N₀ δ shown evs :=
  ⟨fun x hx => h.tail x (List.mem_cons_of_mem _ hx),
    fun x hx => h.seen x (List.mem_cons_of_mem _ hx),
    fun x hx => h.unseen x (List.mem_cons_of_mem _ hx),
    fun x hx => h.inert x (List.mem_cons_of_mem _ hx),
    fun x hx => h.closed x (List.mem_cons_of_mem _ hx)⟩

/-- Showing further visible tokens keeps `EvsOK`. -/
theorem EvsOK.show_up {shown : List ℕ} {evs : List (Ev S)}
    (h : EvsOK N₀ δ shown evs) (ts : List ℕ) :
    EvsOK N₀ δ (shown ++ ts.map (up N₀ δ)) evs := by
  refine ⟨h.tail, h.seen, h.unseen, fun e he hd => ?_, fun e he hd hr => ?_⟩
  · rcases h.inert e he hd with h1 | h1
    · exact Or.inl h1
    · right
      rw [Bool.eq_false_iff] at h1 ⊢
      intro h2
      rw [List.contains_iff_mem, List.mem_append] at h2
      rcases h2 with h2 | h2
      · exact h1 (List.contains_iff_mem.2 h2)
      · obtain ⟨v, -, hv⟩ := List.mem_map.1 h2
        rw [← hv, vis_up] at hd
        exact Bool.noConfusion hd
  · obtain ⟨h1, h2⟩ := h.closed e he hd hr
    refine ⟨?_, ?_⟩
    · rw [List.contains_iff_mem] at h1 ⊢
      exact List.mem_append_left _ h1
    · rw [List.all_eq_true] at h2 ⊢
      intro u hu
      have h3 := h2 u hu
      rw [List.contains_iff_mem] at h3 ⊢
      exact List.mem_append_left _ h3

/-- `EvsOK` after a new marked query, all of whose tokens are visible. -/
theorem EvsOK.snoc {shown : List ℕ} {evs : List (Ev S)} (h : EvsOK N₀ δ shown evs)
    {e : Ev S} (h1 : ∀ u ∈ e.others, vis N₀ δ u = true)
    (h2 : vis N₀ δ e.charged = true) (h3 : vis N₀ δ e.tail = true) :
    EvsOK N₀ δ shown (evs ++ [e]) := by
  refine ⟨fun x hx hv => ?_, fun x hx hv => ?_, fun x hx hd => ?_,
      fun x hx hd => ?_, fun x hx hd hr => ?_⟩ <;>
    rcases List.mem_append.1 hx with hx | hx
  · exact h.tail x hx hv
  · rw [List.mem_singleton.1 hx]; exact h3
  · exact h.seen x hx hv
  · rw [List.mem_singleton.1 hx]; exact h1
  · exact h.unseen x hx hd
  · rw [List.mem_singleton.1 hx, h2] at hd; exact Bool.noConfusion hd
  · exact h.inert x hx hd
  · rw [List.mem_singleton.1 hx, h2] at hd; exact Bool.noConfusion hd
  · exact h.closed x hx hd hr
  · rw [List.mem_singleton.1 hx, h2] at hd; exact Bool.noConfusion hd

/-- A release commutes with `viewEvs` and `viewShown`, under `hin`. -/
theorem releaseAll_view (m : Bool) (shown : List ℕ) (evs : List (Ev S))
    (hin : ∀ e ∈ evs,
      vis N₀ δ e.charged = false → e.released = true ∨ shown.contains e.charged = false)
    (T : Table S) :
    releaseAll m (viewShown N₀ δ shown) (viewEvs N₀ δ evs) T =
      (viewEvs N₀ δ (releaseAll m shown evs T).1, (releaseAll m shown evs T).2) := by
  induction evs generalizing T with
  | nil => rfl
  | cons e es ih =>
    have ih' := fun T => ih (fun x hx => hin x (List.mem_cons_of_mem _ hx)) T
    by_cases hv : vis N₀ δ e.charged = true
    · rw [viewEvs_cons_vis N₀ δ hv]
      have hc : (viewShown N₀ δ shown).contains (ren N₀ δ e).charged =
          shown.contains e.charged := by
        rw [contains_viewShown]
        show shown.contains (up N₀ δ (down N₀ δ e.charged)) = _
        rw [up_down N₀ δ hv]
      by_cases hcond : (!e.released && shown.contains e.charged) = true
      · have hcond' : (!(ren N₀ δ e).released &&
              (viewShown N₀ δ shown).contains (ren N₀ δ e).charged) = true := by
          rw [hc]; exact hcond
        rw [releaseAll_cons_pos hcond, releaseAll_cons_pos hcond',
          show wr m T (ren N₀ δ e).o (ren N₀ δ e).pt (ren N₀ δ e).ans = wr m T e.o e.pt e.ans
            from rfl,
          ih', viewEvs_cons_vis N₀ δ (e := { e with released := true }) hv]
        rfl
      · have hcond' : ¬ (!(ren N₀ δ e).released &&
              (viewShown N₀ δ shown).contains (ren N₀ δ e).charged) = true := by
          rw [hc]; exact hcond
        rw [releaseAll_cons_neg hcond, releaseAll_cons_neg hcond', ih', viewEvs_cons_vis N₀ δ hv]
    · rw [Bool.not_eq_true] at hv
      have hcond := not_cond (hin e List.mem_cons_self hv)
      rw [viewEvs_cons_dead N₀ δ hv, releaseAll_cons_neg hcond, ih', viewEvs_cons_dead N₀ δ hv]

theorem EvsOK.release {shown : List ℕ} {evs : List (Ev S)} (h : EvsOK N₀ δ shown evs)
    (m : Bool) (T : Table S) :
    EvsOK N₀ δ shown (releaseAll m shown evs T).1 := by
  have key : ∀ x ∈ (releaseAll m shown evs T).1, ∃ e ∈ evs,
      x.others = e.others ∧
      x.charged = e.charged ∧
      x.tail = e.tail ∧
      (vis N₀ δ e.charged = false → x.released = e.released) := by
    intro x hx
    obtain ⟨e, he, ⟨rfl, -⟩ | ⟨rfl, hc⟩⟩ := mem_releaseAll hx
    · exact ⟨x, he, rfl, rfl, rfl, fun _ => rfl⟩
    · refine ⟨e, he, rfl, rfl, rfl, fun hd => ?_⟩
      exact absurd hc (not_cond (h.inert e he hd))
  refine ⟨fun x hx hv => ?_, fun x hx hv => ?_, fun x hx hd => ?_,
      fun x hx hd => ?_, fun x hx hd hr => ?_⟩ <;>
    obtain ⟨e, he, h1, h2, h3, h4⟩ := key x hx
  · rw [h3]; rw [h2] at hv; exact h.tail e he hv
  · rw [h1]; rw [h2] at hv; exact h.seen e he hv
  · rw [h1]; rw [h2] at hd; exact h.unseen e he hd
  · rw [h2] at hd ⊢; rw [h4 hd]; exact h.inert e he hd
  · rw [h2] at hd; rw [h4 hd] at hr; rw [h3, h1]; exact h.closed e he hd hr

theorem closedUnder_view {shown : List ℕ} {evs : List (Ev S)} (h : EvsOK N₀ δ shown evs) :
    closedUnder (viewShown N₀ δ shown) (viewEvs N₀ δ evs) = closedUnder shown evs := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    have ih' := ih h.of_cons
    unfold closedUnder at ih' ⊢
    by_cases hv : vis N₀ δ e.charged = true
    · rw [viewEvs_cons_vis N₀ δ hv, List.all_cons, List.all_cons, ih']
      congr 1
      have ht := h.tail e List.mem_cons_self hv
      show (!e.released || ((viewShown N₀ δ shown).contains (down N₀ δ e.tail) &&
        (e.others.map (down N₀ δ)).all (viewShown N₀ δ shown).contains)) = _
      rw [contains_viewShown, up_down N₀ δ ht, all_map_down (h.seen e List.mem_cons_self hv)]
    · rw [Bool.not_eq_true] at hv
      rw [viewEvs_cons_dead N₀ δ hv, List.all_cons, ih']
      have h1 : (!e.released || (shown.contains e.tail && e.others.all shown.contains)) = true := by
        cases hr : e.released with
        | false => simp
        | true =>
          obtain ⟨h2, h3⟩ := h.closed e List.mem_cons_self hv hr
          rw [h2, h3]
          rfl
      rw [h1, Bool.true_and]

theorem any_view {shown : List ℕ} {evs : List (Ev S)} (h : EvsOK N₀ δ shown evs) (o : S.ι) (t : ℕ) :
    ((viewEvs N₀ δ evs).any fun e => decide (e.o = o) && (e.charged == t || e.others.contains t)) =
      evs.any fun e =>
        decide (e.o = o) && (e.charged == up N₀ δ t || e.others.contains (up N₀ δ t)) := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    have ih' := ih h.of_cons
    by_cases hv : vis N₀ δ e.charged = true
    · rw [viewEvs_cons_vis N₀ δ hv, List.any_cons, List.any_cons, ih']
      congr 1
      show (decide (e.o = o) &&
          (down N₀ δ e.charged == t || (e.others.map (down N₀ δ)).contains t)) = _
      rw [contains_map_down (h.seen e List.mem_cons_self hv)]
      congr 2
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact down_eq_iff N₀ δ hv t
    · rw [Bool.not_eq_true] at hv
      rw [viewEvs_cons_dead N₀ δ hv, List.any_cons, ih']
      have h1 : (e.charged == up N₀ δ t) = false := by
        rw [beq_eq_false_iff_ne]
        intro h2
        rw [h2, vis_up] at hv
        exact Bool.noConfusion hv
      rw [h1, contains_up_of_unseen (h.unseen e List.mem_cons_self hv)]
      simp

end View

/-! ## Part 3. The program under the renumbering -/

section Virt

variable {S : OSpec} {sp : Split S} {α : Type} (N₀ δ : ℕ)

/-- The states for which `run_virt` holds. -/
structure WF (D : DSt S) : Prop where
  len : N₀ + δ ≤ D.vals.length
  evs : EvsOK N₀ δ D.shown D.evs

variable {N₀ δ}

theorem length_view {D : DSt S} (h : WF N₀ δ D) :
    (view N₀ δ D).vals.length = D.vals.length - δ := by
  have h1 := length_viewVals h.len
  show (viewVals N₀ δ D.vals).length = _
  omega

theorem val_view {D : DSt S} (h : WF N₀ δ D) (v : ℕ) : (view N₀ δ D).val v = D.val (up N₀ δ v) :=
  getD_viewVals h.len v

theorem map_val_view {D : DSt S} (h : WF N₀ δ D) (l : List ℕ) :
    (l.map (up N₀ δ)).map D.val = l.map (view N₀ δ D).val := by
  rw [List.map_map]
  exact List.map_congr_left fun v _ => (val_view h v).symm

theorem decide_le_up {D : DSt S} (h : WF N₀ δ D) (v : ℕ) :
    decide (D.vals.length ≤ up N₀ δ v) = decide ((view N₀ δ D).vals.length ≤ v) := by
  have h1 := h.len
  rw [length_view h, decide_eq_decide]
  unfold up
  split_ifs <;> omega

theorem any_le_up {D : DSt S} (h : WF N₀ δ D) (l : List ℕ) :
    ((l.map (up N₀ δ)).any fun u => decide (D.vals.length ≤ u)) =
      l.any fun u => decide ((view N₀ δ D).vals.length ≤ u) := by
  rw [List.any_map]
  exact congrArg (fun f => l.any f) (funext fun v => decide_le_up h v)

theorem down_length {D : DSt S} (h : WF N₀ δ D) : down N₀ δ D.vals.length = D.vals.length - δ := by
  have h1 := h.len
  unfold down
  rw [if_neg (by omega)]

theorem vis_length {D : DSt S} (h : WF N₀ δ D) : vis N₀ δ D.vals.length = true :=
  (vis_iff _ _ _).2 (Or.inr h.len)

theorem vis_of_mem_map_up {l : List ℕ} : ∀ u ∈ l.map (up N₀ δ), vis N₀ δ u = true := by
  intro u hu
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
  exact vis_up N₀ δ v

/-- the state after a marked query of the renumbered program has `WF` again -/
theorem WF.mark {D : DSt S} (h : WF N₀ δ D) (o : S.ι) (P : S.Dom o) (r : S.Rng o) (t : ℕ)
    (us : List ℕ) (T : Table S) (x : Bits) (b : Bool) :
    WF N₀ δ (⟨T, D.vals ++ [x], D.shown,
        D.evs ++ [⟨o, P, r, up N₀ δ t, us.map (up N₀ δ), D.vals.length, false⟩],
        D.nPlain, b⟩ : DSt S) :=
  ⟨by have := h.len; simp only [List.length_append]; omega,
    h.evs.snoc vis_of_mem_map_up (vis_up N₀ δ t) (vis_length h)⟩

/-- From a state with `WF`, the run of the renumbered program, mapped by `view`, is the run of the
program from the mapped state. -/
theorem run_virt (m : Bool) (c : Step S sp α) :
    ∀ D : DSt S, WF N₀ δ D →
      ((virt N₀ δ c).run m D).map (fun x => (x.1, view N₀ δ x.2)) = c.run m (view N₀ δ D) := by
  induction c with
  | pure a =>
    intro D _
    simp only [virt, Step.run, PMF.pure_map]
  | sample n k ih =>
    intro D h
    simp only [virt, Step.run, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r D h)
  | plain o q k ih =>
    intro D h
    simp only [virt, Step.run, PMF.map_bind]
    exact congrArg _ (funext fun p => ih p.1 _ ⟨h.len, h.evs⟩)
  | fresh ℓ k ih =>
    intro D h
    simp only [virt, Step.run, PMF.map_bind]
    refine congrArg _ (funext fun u => ?_)
    rw [length_view h, ih (D.vals.length - δ) { D with vals := D.vals ++ [List.ofFn u] }
      ⟨by have := h.len; simp only [List.length_append]; omega, h.evs⟩]
    congr 1
    simp only [view, viewVals_append h.len]
  | marked o t us pt inj k ih =>
    intro D h
    have hgo : ∀ (r : S.Rng o) (T : Table S) (b : Bool),
        ((virt N₀ δ (k (sp.split o r).1 (D.vals.length - δ))).run m
              ⟨T, D.vals ++ [List.ofFn (sp.split o r).2],
                D.shown,
                D.evs ++ [⟨o, pt (D.val (up N₀ δ t)) (us.map (view N₀ δ D).val), r, up N₀ δ t,
                    us.map (up N₀ δ), D.vals.length, false⟩],
                D.nPlain, b⟩).map
            (fun x => (x.1, view N₀ δ x.2)) =
          (k (sp.split o r).1 (view N₀ δ D).vals.length).run m
            ⟨T, (view N₀ δ D).vals ++ [List.ofFn (sp.split o r).2],
              (view N₀ δ D).shown,
              (view N₀ δ D).evs ++
                [⟨o, pt (D.val (up N₀ δ t)) (us.map (view N₀ δ D).val), r, t, us,
                  (view N₀ δ D).vals.length, false⟩],
              (view N₀ δ D).nPlain,
              b⟩ := by
      intro r T b
      rw [ih _ _ _ (h.mark o _ r t us T _ b), length_view h]
      congr 1
      simp only [view, viewVals_append h.len, viewEvs_append]
      congr 2
      rw [viewEvs_cons_vis N₀ δ (vis_up N₀ δ t)]
      simp only [ren, down_up, down_length h, map_down_map_up]
      rfl
    have hbad : (decide (D.vals.length ≤ up N₀ δ t) ||
          (us.map (up N₀ δ)).any (fun u => decide (D.vals.length ≤ u)) ||
          (us.map (up N₀ δ)).contains (up N₀ δ t) || D.shown.contains (up N₀ δ t) ||
          D.evs.any fun e =>
            decide (e.o = o) && (e.charged == up N₀ δ t || e.others.contains (up N₀ δ t))) =
        (decide ((view N₀ δ D).vals.length ≤ t) ||
          us.any (fun u => decide ((view N₀ δ D).vals.length ≤ u)) ||
          us.contains t || (view N₀ δ D).shown.contains t ||
          (view N₀ δ D).evs.any fun e =>
            decide (e.o = o) && (e.charged == t || e.others.contains t)) := by
      rw [decide_le_up h, any_le_up h, contains_map_up,
        show (view N₀ δ D).shown = viewShown N₀ δ D.shown from rfl, contains_viewShown,
        show (view N₀ δ D).evs = viewEvs N₀ δ D.evs from rfl, any_view h.evs]
    simp only [virt, Step.run, val_view h, map_val_view h]
    rw [hbad]
    cases m with
    | true =>
      simp only [if_true, PMF.map_bind]
      exact congrArg _ (funext fun r => hgo r _ _)
    | false =>
      simp only [Bool.false_eq_true, if_false, PMF.map_bind]
      exact congrArg _ (funext fun p => hgo p.1 p.2 _)
  | reveal ts k ih =>
    intro D h
    have hs := h.evs.show_up ts
    have hr := hs.release m D.table
    simp only [virt, Step.run]
    rw [ih _ ⟨(releaseAll m (D.shown ++ ts.map (up N₀ δ)) D.evs D.table).2,
          D.vals,
          D.shown ++ ts.map (up N₀ δ),
          (releaseAll m (D.shown ++ ts.map (up N₀ δ)) D.evs D.table).1,
          D.nPlain, _⟩ ⟨h.len, hr⟩]
    have h3 := releaseAll_view m (D.shown ++ ts.map (up N₀ δ)) D.evs hs.inert D.table
    rw [viewShown_append_up] at h3
    rw [map_val_view h]
    congr 1
    simp only [view]
    rw [h3, any_le_up h, ← closedUnder_view hr, viewShown_append_up]
    rfl

end Virt

/-! ## Part 4. What the renumbered program leaves as it was -/

section Frame

variable {S : OSpec} {sp : Split S} {α : Type} {N₀ δ : ℕ}

/-- What holds of a state D' that the renumbered program can reach from a D with `WF`
(`frame_virt`): it has `WF` again; the strings up to index N₀ + δ, the marked queries that are not
seen (`deadEvs`), and which of the unseen tokens (`vis` false) are shown, are as they were; and what
was shown is shown. -/
structure Frame (N₀ δ : ℕ) (D D' : DSt S) : Prop where
  wf : WF N₀ δ D'
  vals : D'.vals.take (N₀ + δ) = D.vals.take (N₀ + δ)
  dead : deadEvs N₀ δ D'.evs = deadEvs N₀ δ D.evs
  shown : ∀ t, vis N₀ δ t = false → D'.shown.contains t = D.shown.contains t
  sub : ∀ t ∈ D.shown, t ∈ D'.shown

theorem Frame.refl {D : DSt S} (h : WF N₀ δ D) : Frame N₀ δ D D :=
  ⟨h, rfl, rfl, fun _ _ => rfl, fun _ h => h⟩

theorem Frame.trans {D D' D'' : DSt S} (h : Frame N₀ δ D D') (h' : Frame N₀ δ D' D'') :
    Frame N₀ δ D D'' :=
  ⟨h'.wf, h'.vals.trans h.vals, h'.dead.trans h.dead,
    fun t ht => (h'.shown t ht).trans (h.shown t ht), fun t ht => h'.sub t (h.sub t ht)⟩

theorem frame_virt (m : Bool) (c : Step S sp α) :
    ∀ D : DSt S, WF N₀ δ D → ∀ x ∈ ((virt N₀ δ c).run m D).support, Frame N₀ δ D x.2 := by
  induction c with
  | pure a =>
    intro D h x hx
    simp only [virt, Step.run, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact Frame.refl h
  | sample n k ih =>
    intro D h x hx
    simp only [virt, Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    exact ih r D h x hx
  | plain o q k ih =>
    intro D h x hx
    simp only [virt, Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨p, -, hx⟩ := hx
    refine Frame.trans ?_ (ih p.1 _ ?_ x hx)
    · exact ⟨⟨h.len, h.evs⟩, rfl, rfl, fun _ _ => rfl, fun _ h => h⟩
    · exact ⟨h.len, h.evs⟩
  | fresh ℓ k ih =>
    intro D h x hx
    simp only [virt, Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨u, -, hx⟩ := hx
    have hw : WF N₀ δ ({ D with vals := D.vals ++ [List.ofFn u] } : DSt S) :=
      ⟨by have := h.len; simp only [List.length_append]; omega, h.evs⟩
    exact (Frame.mk (D := D) hw (List.take_append_of_le_length h.len) rfl
        (fun _ _ => rfl) fun _ h => h).trans (ih _ _ hw x hx)
  | marked o t us pt inj k ih =>
    intro D h x hx
    have hgo : ∀ (P : S.Dom o) (r : S.Rng o) (T : Table S) (b : Bool), x ∈
      ((virt N₀ δ (k (sp.split o r).1 (D.vals.length - δ))).run m
        ⟨T, D.vals ++ [List.ofFn (sp.split o r).2], D.shown,
          D.evs ++ [⟨o, P, r, up N₀ δ t, us.map (up N₀ δ), D.vals.length, false⟩], D.nPlain,
          b⟩).support →
          Frame N₀ δ D x.2 := by
      intro P r T b hx
      have hw := h.mark o P r t us T (List.ofFn (sp.split o r).2) b
      refine (Frame.mk (D := D) hw (List.take_append_of_le_length h.len) ?_
          (fun _ _ => rfl) fun _ h => h).trans
        (ih _ _ _ hw x hx)
      simp [deadEvs, vis_up]
    simp only [virt, Step.run] at hx
    cases m with
    | true =>
      simp only [if_true, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact hgo _ r _ _ hx
    | false =>
      simp only [Bool.false_eq_true, if_false, PMF.mem_support_bind_iff] at hx
      obtain ⟨p, -, hx⟩ := hx
      exact hgo _ p.1 p.2 _ hx
  | reveal ts k ih =>
    intro D h x hx
    have hs := h.evs.show_up ts
    have hr := hs.release m D.table
    simp only [virt, Step.run] at hx
    refine Frame.trans ?_ (ih _ _ ?_ x hx)
    rotate_left
    · exact ⟨h.len, hr⟩
    refine ⟨⟨h.len, hr⟩, rfl, deadEvs_releaseAll m _ _ hs.inert _,
      fun t ht => ?_, fun t ht => List.mem_append_left _ ht⟩
    show (D.shown ++ ts.map (up N₀ δ)).contains t = D.shown.contains t
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_append]
    refine ⟨fun h1 => h1.resolve_right fun h2 => ?_, Or.inl⟩
    obtain ⟨v, -, hv⟩ := List.mem_map.1 h2
    rw [← hv, vis_up] at ht
    exact Bool.noConfusion ht

end Frame

end Many
end Life2
end Compile
