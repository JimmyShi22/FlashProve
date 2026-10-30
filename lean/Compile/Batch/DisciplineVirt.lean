-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineVirt.lean: orderly states (`TidyO`) and the translation of token numbers,
for marked queries that hold several tokens. Generic in the family of oracles.

The challenger of the compiled scheme runs the prover's program behind a translation of token
numbers (`virt`, Compile/Step1_life2_Virt.lean; Compile/Step1_life2_VirtMany.lean): a batch sees the
first N₀ tokens, those of the setup, and its own, not those of earlier batches. The rules
(Compile/Batch/SpecDiscipline.lean) are about what the program sees (words of this library:
lean/GLOSSARY.md). Here:

  `wf_start`, `tidy_view_start`, `closed_view_start`  Under `TidyO`, `MidO`: what a batch sees at
                                                      its start is orderly, and tokens of the setup
                                                      that can be revealed together can be revealed
                                                      there. (`wf_start` concludes `WF`: see its
                                                      statement)
  `tidy_of_view`, `closed_of_view`, `mid_of_view`  If its start was orderly, what it sees at its end
                                                   is orderly, and it has left alone what it does
                                                   not see, the whole state is orderly again.
                                                   (not all hypotheses are named here, and
                                                   `closed_of_view` concludes `ClosedO`,
                                                   `mid_of_view` concludes `MidO`: see their
                                                   statements)
  `nEv_split`  The marked queries that a batch sees, and the others.

`MidO` is what a state between two batches has beside being orderly: it has at least N₀ tokens
(`len`), a query charged to a token of the setup holds only tokens of the setup and has its tail
among them, and one charged to a later token holds none of them.
-/
import Compile.Step1_life2_WorldsX
import Compile.Step1_life2_VirtMany
import Compile.Batch.DisciplineKit

namespace Compile.Batch.Disc.VirtO
open Rom
open Compile.Life2 (vis up down vis_iff vis_up down_up up_down viewShown deadEvs)
open Compile.Life2.Many
  (ren viewEvs view WF EvsOK Frame length_view val_view viewEvs_cons_vis viewEvs_cons_dead)
open Compile.Life2.WorldsX
  (mem_viewShown mem_deadEvs not_vis_iff down_lt down_of_lt lt_of_down_lt dummy gap getD_of_take_eq)
open Compile.Disc (Rules nEv)

variable {S : OSpec} {Rl : Rules S} {N₀ δ : ℕ}

theorem mem_viewEvs {l : List (Ev S)} {x : Ev S} :
    x ∈ viewEvs N₀ δ l ↔ ∃ e ∈ l, vis N₀ δ e.charged = true ∧ ren N₀ δ e = x := by
  simp only [viewEvs, List.mem_map, List.mem_filter, and_assoc]

theorem tidy_dummy {D : DSt S} (h : TidyO Rl D) : TidyO Rl (dummy D) := h.fresh []

/-- what a state between two batches has beside being orderly -/
structure MidO (N₀ : ℕ) (D : DSt S) : Prop where
  len : N₀ ≤ D.vals.length
  tails : ∀ e ∈ D.evs, e.charged < N₀ → e.tail < N₀
  low : ∀ e ∈ D.evs, e.charged < N₀ → ∀ u ∈ e.others, u < N₀
  high : ∀ e ∈ D.evs, N₀ ≤ e.charged → ∀ u ∈ e.others, N₀ ≤ u

theorem gap_len {D : DSt S} (h : MidO N₀ D) : N₀ + gap N₀ D = (dummy D).vals.length := by
  have := h.len
  have hg : gap N₀ D = D.vals.length + 1 - N₀ := rfl
  simp only [List.length_append, List.length_singleton]
  omega

/-- among the tokens that exist at the start of a batch, the visible ones are the first N₀ (under
`MidO`) -/
theorem vis_start {D : DSt S} (h : MidO N₀ D) {t : ℕ} (ht : t < D.vals.length) :
    vis N₀ (gap N₀ D) t = true ↔ t < N₀ := by
  have := h.len
  have hg : gap N₀ D = D.vals.length + 1 - N₀ := rfl
  rw [vis_iff]
  omega

/-- Under `TidyO`, `MidO`: the start of a batch is well formed for the translation of token numbers.
-/
theorem wf_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) : WF N₀ (gap N₀ D) (dummy D) where
  len := le_of_eq (gap_len h)
  evs :=
    { tail := fun e he hv =>
        (vis_start h (ht.tail_lt e he)).2 (h.tails e he ((vis_start h (ht.charged_lt e he)).1 hv))
      seen := fun e he hv u hu =>
        (vis_start h (ht.others_lt e he u hu)).2
          (h.low e he ((vis_start h (ht.charged_lt e he)).1 hv) u hu)
      unseen := fun e he hv u hu => by
        have h1 : ¬ e.charged < N₀ := fun hc => by
          rw [(vis_start h (ht.charged_lt e he)).2 hc] at hv
          cases hv
        have h2 := h.high e he (Nat.le_of_not_lt h1) u hu
        rw [Bool.eq_false_iff]
        exact fun hvu => absurd ((vis_start h (ht.others_lt e he u hu)).1 hvu) (Nat.not_lt.2 h2)
      inert := fun e he _ => by
        by_cases hs : e.charged ∈ D.shown
        · exact Or.inl (ht.released e he hs)
        · right
          rw [Bool.eq_false_iff]
          exact fun hc => hs (List.contains_iff_mem.1 hc)
      closed := fun e he _ hr => ⟨List.contains_iff_mem.2 (ht.closed_tail e he hr),
        List.all_eq_true.2 fun u hu => List.contains_iff_mem.2 (ht.closed_others e he hr u hu)⟩ }

theorem length_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) :
    (view N₀ (gap N₀ D) (dummy D)).vals.length = N₀ := by
  rw [length_view (wf_start ht h), ← gap_len h]; omega

/-- what a new batch sees of the queries (under `TidyO`, `MidO`): those charged to tokens of the
setup, with their own numbers -/
theorem ev_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) {x : Ev S}
    (hx : x ∈ (view N₀ (gap N₀ D) (dummy D)).evs) :
    ∃ e ∈ D.evs, e.charged < N₀ ∧ e.tail < N₀ ∧ (∀ u ∈ e.others, u < N₀) ∧
      x.o = e.o ∧ HEq x.pt e.pt ∧ x.charged = e.charged ∧ x.tail = e.tail ∧
      x.others = e.others ∧ x.released = e.released := by
  obtain ⟨e, he, hv, rfl⟩ := mem_viewEvs.1 hx
  have hc := (vis_start h (ht.charged_lt e he)).1 hv
  have hl := h.low e he hc
  refine ⟨e, he, hc, h.tails e he hc, hl, rfl, HEq.rfl, down_of_lt hc,
    down_of_lt (h.tails e he hc), ?_, rfl⟩
  show e.others.map (down N₀ (gap N₀ D)) = e.others
  conv_rhs => rw [← List.map_id e.others]
  exact List.map_congr_left fun u hu => down_of_lt (hl u hu)

theorem shown_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) (v : ℕ) :
    v ∈ (view N₀ (gap N₀ D) (dummy D)).shown ↔ v < N₀ ∧ v ∈ D.shown := by
  constructor
  · intro hv
    have h1 : up N₀ (gap N₀ D) v ∈ D.shown := mem_viewShown.1 hv
    have h2 := ht.shown_lt _ h1
    have h3 := (vis_start h h2).1 (vis_up _ _ _)
    have h4 : v < N₀ := by
      unfold up at h3
      split_ifs at h3 <;> omega
    have h5 : up N₀ (gap N₀ D) v = v := if_pos h4
    rw [h5] at h1
    exact ⟨h4, h1⟩
  · rintro ⟨h4, h1⟩
    refine mem_viewShown.2 ?_
    have h5 : up N₀ (gap N₀ D) v = v := if_pos h4
    rw [h5]; exact h1

/-- Under `TidyO`, `MidO`: what a new batch sees is orderly. -/
theorem tidy_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) :
    TidyO Rl (view N₀ (gap N₀ D) (dummy D)) := by
  have hwf := wf_start ht h
  have hlen := length_view_start ht h
  refine ⟨ht.viol, fun t hts => by rw [hlen]; exact ((shown_view_start ht h t).1 hts).1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, -, hc, -, -, -, -, h1, -⟩ := ev_view_start ht h hx
    rw [hlen, h1]; exact hc
  · intro x hx
    obtain ⟨e, -, -, htl, -, -, -, -, h1, -⟩ := ev_view_start ht h hx
    rw [hlen, h1]; exact htl
  · intro x hx u hu
    obtain ⟨e, -, -, -, hl, -, -, -, -, h1, -⟩ := ev_view_start ht h hx
    rw [hlen]; exact hl u (h1 ▸ hu)
  · intro x hx hs
    obtain ⟨e, he, -, -, -, -, -, h1, -, -, h2⟩ := ev_view_start ht h hx
    rw [h2]
    exact ht.released e he ((shown_view_start ht h _).1 (h1 ▸ hs)).2
  · intro x hx hr
    obtain ⟨e, he, -, htl, -, -, -, -, h1, -, h2⟩ := ev_view_start ht h hx
    rw [h1]
    exact (shown_view_start ht h _).2 ⟨htl, ht.closed_tail e he (h2 ▸ hr)⟩
  · intro x hx hr u hu
    obtain ⟨e, he, -, -, hl, -, -, -, -, h1, h2⟩ := ev_view_start ht h hx
    exact (shown_view_start ht h _).2 ⟨hl u (h1 ▸ hu), ht.closed_others e he (h2 ▸ hr) u (h1 ▸ hu)⟩
  · intro x hx
    obtain ⟨e, he, hv, rfl⟩ := mem_viewEvs.1 hx
    show Rl.bits e.o ≤ ((view N₀ (gap N₀ D) (dummy D)).val (down N₀ (gap N₀ D) e.charged)).length
    rw [val_view hwf, up_down _ _ hv]
    exact (tidy_dummy ht).bits e he
  · intro x hx
    obtain ⟨e, he, -, rfl⟩ := mem_viewEvs.1 hx
    exact ht.point e he

/-- The end of a batch is orderly, if its start was, if what the batch has seen is orderly at the
end, if it has left alone what it did not see (`hf`: `Frame`, which also asks `WF` of the end), and
if N₀ + δ = D₁.vals.length (`hl`). -/
theorem tidy_of_view {D₁ D' : DSt S} (h1 : TidyO Rl D₁) (hl : N₀ + δ = D₁.vals.length)
    (hf : Frame N₀ δ D₁ D') (hv : TidyO Rl (view N₀ δ D')) : TidyO Rl D' := by
  have hlenV : (view N₀ δ D').vals.length = D'.vals.length - δ := length_view hf.wf
  have hle : N₀ + δ ≤ D'.vals.length := hf.wf.len
  have seen : ∀ e ∈ D'.evs, vis N₀ δ e.charged = true → ren N₀ δ e ∈ (view N₀ δ D').evs :=
    fun e he hvis => mem_viewEvs.2 ⟨e, he, hvis, rfl⟩
  have dead : ∀ e ∈ D'.evs, vis N₀ δ e.charged = false → e ∈ D₁.evs := fun e he hd =>
    (mem_deadEvs.1 (hf.dead ▸ mem_deadEvs.2 ⟨he, hd⟩)).1
  have shownV : ∀ t,
      vis N₀ δ t = true → (down N₀ δ t ∈ (view N₀ δ D').shown ↔ t ∈ D'.shown) := fun t hvis => by
    show down N₀ δ t ∈ viewShown N₀ δ D'.shown ↔ _
    rw [mem_viewShown, up_down _ _ hvis]
  have cases_vis : ∀ t, vis N₀ δ t = true ∨ vis N₀ δ t = false :=
    fun t => by cases vis N₀ δ t <;> simp
  have memO : ∀ (e : Ev S) (u : ℕ), u ∈ e.others → down N₀ δ u ∈ (ren N₀ δ e).others :=
    fun e u hu => List.mem_map_of_mem hu
  refine ⟨hv.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases cases_vis t with hvis | hd
    · have h2 := hv.shown_lt _ ((shownV t hvis).2 ht)
      rw [hlenV] at h2
      exact (down_lt hvis hle).1 h2
    · exact lt_of_lt_of_le ((not_vis_iff t).1 hd).2 hle
  · intro e he
    rcases cases_vis e.charged with hvis | hd
    · have h2 : down N₀ δ e.charged < _ := hv.charged_lt _ (seen e he hvis)
      rw [hlenV] at h2
      exact (down_lt hvis hle).1 h2
    · exact lt_of_lt_of_le ((not_vis_iff _).1 hd).2 hle
  · intro e he
    rcases cases_vis e.charged with hvis | hd
    · have h2 : down N₀ δ e.tail < _ := hv.tail_lt _ (seen e he hvis)
      rw [hlenV] at h2
      exact (down_lt (hf.wf.evs.tail e he hvis) hle).1 h2
    · exact lt_of_lt_of_le (h1.tail_lt e (dead e he hd)) (hl ▸ hle)
  · intro e he u hu
    rcases cases_vis e.charged with hvis | hd
    · have h2 := hv.others_lt _ (seen e he hvis) _ (memO e u hu)
      rw [hlenV] at h2
      exact (down_lt (hf.wf.evs.seen e he hvis u hu) hle).1 h2
    · exact lt_of_lt_of_le (h1.others_lt e (dead e he hd) u hu) (hl ▸ hle)
  · intro e he hs
    rcases cases_vis e.charged with hvis | hd
    · exact hv.released (ren N₀ δ e) (seen e he hvis) ((shownV _ hvis).2 hs)
    · refine h1.released e (dead e he hd) ?_
      have h2 := hf.shown _ hd
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem] at h2
      exact h2.1 hs
  · intro e he hr
    rcases cases_vis e.charged with hvis | hd
    · exact (shownV _ (hf.wf.evs.tail e he hvis)).1
        (hv.closed_tail (ren N₀ δ e) (seen e he hvis) hr)
    · exact hf.sub _ (h1.closed_tail e (dead e he hd) hr)
  · intro e he hr u hu
    rcases cases_vis e.charged with hvis | hd
    · exact (shownV _ (hf.wf.evs.seen e he hvis u hu)).1
        (hv.closed_others (ren N₀ δ e) (seen e he hvis) hr _ (memO e u hu))
    · exact hf.sub _ (h1.closed_others e (dead e he hd) hr u hu)
  · intro e he
    rcases cases_vis e.charged with hvis | hd
    · have h2 : Rl.bits e.o ≤ ((view N₀ δ D').val (down N₀ δ e.charged)).length :=
        hv.bits _ (seen e he hvis)
      rwa [val_view hf.wf, up_down _ _ hvis] at h2
    · have h2 : D'.val e.charged = D₁.val e.charged :=
        getD_of_take_eq hf.vals ((not_vis_iff _).1 hd).2
      rw [h2]
      exact h1.bits e (dead e he hd)
  · intro e he
    rcases cases_vis e.charged with hvis | hd
    · exact hv.point (ren N₀ δ e) (seen e he hvis)
    · exact h1.point e (dead e he hd)

/-- Between two batches again, under the hypotheses below: a batch whose new queries hold only new
tokens keeps the tokens of the setup and the later ones apart. -/
theorem mid_of_view {D₁ D' : DSt S} {R : Tok → Prop} {e M : S.ι → ℕ} (hf : Frame N₀ δ D₁ D')
    (hhigh : ∀ x ∈ D₁.evs, N₀ ≤ x.charged → ∀ u ∈ x.others, N₀ ≤ u) (hV₁ : TidyO Rl (view N₀ δ D₁))
    (hlen : (view N₀ δ D₁).vals.length = N₀)
    (hg : GrowsO (fun _ => False) R e M (view N₀ δ D₁) (view N₀ δ D')) : MidO N₀ D' := by
  have hwf := hf.wf
  -- a query charged to a token of the setup is an old one
  have old : ∀ x ∈ D'.evs, x.charged < N₀ →
      ∃ e₀ ∈ (view N₀ δ D₁).evs, e₀.others = (ren N₀ δ x).others ∧ e₀.tail = (ren N₀ δ x).tail := by
    intro x hx hc
    have hvis : vis N₀ δ x.charged = true := (vis_iff _ _ _).2 (Or.inl hc)
    rcases hg.evs _
      (mem_viewEvs.2 ⟨x, hx, hvis, rfl⟩) with ⟨e₀, he₀, -, -, ho, ht⟩ | ⟨-, hn | hn, -⟩
    · exact ⟨e₀, he₀, ho, ht⟩
    · exact hn.elim
    · have h3 : (view N₀ δ D₁).vals.length ≤ down N₀ δ x.charged := hn
      rw [hlen, down_of_lt hc] at h3
      exact absurd hc (not_lt.2 h3)
  refine ⟨le_trans (Nat.le_add_right _ _) hwf.len, fun x hx hc => ?_,
    fun x hx hc u hu => ?_, fun x hx hc u hu => ?_⟩
  · have hvis : vis N₀ δ x.charged = true := (vis_iff _ _ _).2 (Or.inl hc)
    obtain ⟨e₀, he₀, -, ht⟩ := old x hx hc
    have h2 := hV₁.tail_lt e₀ he₀
    rw [hlen, ht] at h2
    exact lt_of_down_lt (hwf.evs.tail x hx hvis) h2
  · have hvis : vis N₀ δ x.charged = true := (vis_iff _ _ _).2 (Or.inl hc)
    obtain ⟨e₀, he₀, ho, -⟩ := old x hx hc
    have h2 := hV₁.others_lt e₀ he₀ (down N₀ δ u) (ho ▸ List.mem_map_of_mem hu)
    rw [hlen] at h2
    exact lt_of_down_lt (hwf.evs.seen x hx hvis u hu) h2
  · by_cases hvis : vis N₀ δ x.charged = true
    · rcases hg.evs _ (mem_viewEvs.2 ⟨x, hx, hvis, rfl⟩) with ⟨e₀, he₀, -, hc₀, -, -⟩ | ⟨-, -, hn⟩
      · have h2 := hV₁.charged_lt e₀ he₀
        rw [hlen, hc₀] at h2
        exact absurd (lt_of_down_lt hvis h2) (not_lt.2 hc)
      · rcases hn (down N₀ δ u) (List.mem_map_of_mem hu) with h3 | h3
        · exact h3.elim
        · rw [hlen] at h3
          by_contra hlt
          rw [down_of_lt (not_le.1 hlt)] at h3
          exact hlt h3
    · have hd : vis N₀ δ x.charged = false := by simpa using hvis
      exact hhigh x (mem_deadEvs.1 (hf.dead ▸ mem_deadEvs.2 ⟨hx, hd⟩)).1 hc u hu

/-- the marked queries of o: those that a batch sees, and the others -/
theorem nEv_split (D : DSt S) (o : S.ι) :
    nEv D o =
      nEv (view N₀ δ D) o + ((deadEvs N₀ δ D.evs).filter fun v => decide (v.o = o)).length := by
  have key : ∀ l : List (Ev S), (l.filter fun v => decide (v.o = o)).length =
      ((viewEvs N₀ δ l).filter fun v => decide (v.o = o)).length +
        ((deadEvs N₀ δ l).filter fun v => decide (v.o = o)).length := by
    intro l
    induction l with
    | nil => rfl
    | cons e es ih =>
      by_cases hvis : vis N₀ δ e.charged = true
      · have hd : deadEvs N₀ δ (e :: es) = deadEvs N₀ δ es := by simp [deadEvs, hvis]
        rw [viewEvs_cons_vis _ _ hvis, hd]
        by_cases ho : e.o = o
        · have ho' : (ren N₀ δ e).o = o := ho
          simp only [List.filter_cons, ho, ho', decide_true, if_true, List.length_cons, ih]
          omega
        · have ho' : ¬ (ren N₀ δ e).o = o := ho
          simp only [List.filter_cons, ho, ho', decide_false, Bool.false_eq_true, if_false, ih]
      · have hvis' : vis N₀ δ e.charged = false := by simpa using hvis
        have hd : deadEvs N₀ δ (e :: es) = e :: deadEvs N₀ δ es := by simp [deadEvs, hvis']
        rw [viewEvs_cons_dead _ _ hvis', hd]
        by_cases ho : e.o = o
        · simp only [List.filter_cons, ho, decide_true, if_true, List.length_cons, ih]
          omega
        · simp only [List.filter_cons, ho, decide_false, Bool.false_eq_true, if_false, ih]
  exact key D.evs

/-- tokens of the setup that can be revealed together (under `TidyO`, `MidO`), at the start of a
batch as it sees them -/
theorem closed_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) {ts : List Tok}
    (hc : ClosedO D ts) (hts : ∀ t ∈ ts, t < N₀) :
    ClosedO (view N₀ (gap N₀ D) (dummy D)) ts where
  lt := fun t htm => by rw [length_view_start ht h]; exact hts t htm
  tail := fun x hx hcx => by
    obtain ⟨e, he, -, htl, -, -, -, h1, h2, -, -⟩ := ev_view_start ht h hx
    rw [h2]
    exact (hc.tail e he (h1 ▸ hcx)).imp_right fun hs => (shown_view_start ht h _).2 ⟨htl, hs⟩
  others := fun x hx hcx u hu => by
    obtain ⟨e, he, -, -, hl, -, -, h1, -, h3, -⟩ := ev_view_start ht h hx
    exact (hc.others e he (h1 ▸ hcx) u (h3 ▸ hu)).imp_right fun hs =>
      (shown_view_start ht h _).2 ⟨hl u (h3 ▸ hu), hs⟩

/-- and at its end, from what it sees (under `WF`) -/
theorem closed_of_view {D' : DSt S} (hwf : WF N₀ δ D') {ts : List Tok}
    (hc : ClosedO (view N₀ δ D') ts) (hts : ∀ t ∈ ts, t < N₀) :
    ClosedO D' ts := by
  have key : ∀ u, vis N₀ δ u = true →
      (down N₀ δ u ∈ ts ∨ down N₀ δ u ∈ (view N₀ δ D').shown) → u ∈ ts ∨ u ∈ D'.shown := by
    intro u hu h
    rcases h with h | h
    · have h3 := lt_of_down_lt hu (hts _ h)
      rw [down_of_lt h3] at h
      exact Or.inl h
    · have h2 : up N₀ δ (down N₀ δ u) ∈ D'.shown := mem_viewShown.1 h
      rw [up_down _ _ hu] at h2
      exact Or.inr h2
  have chg : ∀ e : Ev S,
      e.charged ∈ ts → vis N₀ δ e.charged = true ∧ (ren N₀ δ e).charged ∈ ts := fun e hce => by
    have hch := hts _ hce
    refine ⟨(vis_iff _ _ _).2 (Or.inl hch), ?_⟩
    show down N₀ δ e.charged ∈ ts
    rw [down_of_lt hch]; exact hce
  refine ⟨fun t htm => lt_of_lt_of_le (hts t htm) (le_trans (Nat.le_add_right _ _) hwf.len),
    fun e he hce => ?_,
    fun e he hce u hu => ?_⟩
  · obtain ⟨hvis, h1⟩ := chg e hce
    exact key _ (hwf.evs.tail e he hvis)
      (hc.tail (ren N₀ δ e) (mem_viewEvs.2 ⟨e, he, hvis, rfl⟩) h1)
  · obtain ⟨hvis, h1⟩ := chg e hce
    exact key _ (hwf.evs.seen e he hvis u hu)
      (hc.others (ren N₀ δ e) (mem_viewEvs.2 ⟨e, he, hvis, rfl⟩) h1 _ (List.mem_map_of_mem hu))

end Compile.Batch.Disc.VirtO
