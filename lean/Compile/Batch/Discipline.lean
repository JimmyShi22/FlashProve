-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Discipline.lean: the rules of deferred programming (`Step`, `Step.run`,
Rom/Defer.lean) for marked queries that hold several tokens: the generic part.

Definitions and statements: Compile/Batch/SpecDiscipline.lean (words of this library:
lean/GLOSSARY.md). `SafeO Rl c d Q`: from the state d the program c obeys the rules Rl and ends in
Q, whatever the coins, the answers and the tables are. Here: `SafeO` is monotone and closed under
sequential composition, and under it every outcome of `Rom.Step.run`, in both modes, satisfies Q
(`safeRunO`); the four kinds of action keep `TidyO`, the well-formedness of a state (under `SafeO`'s
conditions).

Notation:
  `S`: an `OSpec` (Rom/OSpec.lean): a family of oracles: names, and for each name a domain and a
    finite, non-empty range;
  `sp`: a `Split S` (Rom/Defer.lean): how the answers of each oracle split into a visible part and
    a tail;
  `Rl`: a `Rules S` (Compile/SpecDiscipline.lean): the parameters of the rules;
  `d`: a `DSt` (Rom/Defer.lean): the state of the experiment beside the challenger's own;
  charged, others, tail (fields of `Ev`, Rom/Defer.lean): every marked evaluation is charged to
    one token; it may hold further tokens; the tail of its answer is a new token;
  `FreeAt d o t` (Compile/Batch/SpecDiscipline.lean): a marked query to the oracle o can be
    charged to the token t;
  `markBad`, `markDue` (Compile/SpecDiscipline.lean): the check of `Rom.Step.run` at a marked
    query; what a release does to the record of one query;
  `P`, `r`, `T` (`afterMark`, Compile/SpecDiscipline.lean): the marked query P to o with the
    answer r; T is the new table.
-/
import Compile.Batch.SpecDiscipline
import Compile.Discipline

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules markBad markDue afterPlain afterFresh afterMark afterReveal nEv releaseAll_fst
    val_of_prefix val_new markDue_o markDue_charged markDue_tail markDue_others markDue_point
    markDue_released nEv_map_markDue length_afterFresh length_afterMark mem_evs_afterMark cnt1)

section Generic
variable {S : OSpec} {sp : Split S} {α β : Type} {Rl : Rules S}

/-! ### SafeO -/

theorem SafeO.mono {Q Q' : α → DSt S → Prop} (h : ∀ a d', Q a d' → Q' a d') (c : Step S sp α) :
    ∀ d, SafeO Rl c d Q → SafeO Rl c d Q' := by
  induction c with
  | pure a => exact fun d hd => h a d hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd => ⟨hd.1, fun r T => ih r _ (hd.2 r T)⟩
  | fresh ℓ k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih =>
      exact fun d hd =>
        ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, fun r T => ih _ _ _ (hd.2.2.2.2.2 r T)⟩
  | reveal ts k ih => exact fun d hd => ⟨hd.1, fun T => ih _ _ (hd.2 T)⟩

/-- Sequential composition. -/
theorem SafeO.bind {Q : β → DSt S → Prop} (c : Step S sp α) (g : α → Step S sp β) :
    ∀ d, SafeO Rl c d (fun a d' => SafeO Rl (g a) d' Q) → SafeO Rl (c.bind g) d Q := by
  induction c with
  | pure a => exact fun d hd => hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd => ⟨hd.1, fun r T => ih r _ (hd.2 r T)⟩
  | fresh ℓ k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih =>
      exact fun d hd =>
        ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, fun r T => ih _ _ _ (hd.2.2.2.2.2 r T)⟩
  | reveal ts k ih => exact fun d hd => ⟨hd.1, fun T => ih _ _ (hd.2 T)⟩

/-- `Spec.safeRunO`: if `SafeO Rl c d Q`, every outcome of a run of c from d satisfies Q, in both
modes. -/
theorem safeRunO : Spec.safeRunO := by
  intro S sp α Rl c d Q m
  induction c generalizing d with
  | pure a =>
      intro h x hx
      rw [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
  | sample n k ih =>
      intro h x hx
      rw [Step.run, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, _, hr⟩ := hx
      exact ih r d (h r) x hr
  | plain o q k ih =>
      intro h x hx
      rw [Step.run, PMF.mem_support_bind_iff] at hx
      obtain ⟨pr, _, hr⟩ := hx
      exact ih pr.1 _ (h.2 pr.1 pr.2) x hr
  | fresh ℓ k ih =>
      intro h x hx
      rw [Step.run, PMF.mem_support_bind_iff] at hx
      obtain ⟨u, _, hr⟩ := hx
      exact ih _ _ (h u) x hr
  | marked o t us pt inj k ih =>
      intro h x hx
      rw [Step.run] at hx
      cases m with
      | true =>
          simp only [if_true] at hx
          rw [PMF.mem_support_bind_iff] at hx
          obtain ⟨r, _, hr⟩ := hx
          exact ih _ _ _ (h.2.2.2.2.2 r d.table) x hr
      | false =>
          simp only [Bool.false_eq_true, if_false] at hx
          rw [PMF.mem_support_bind_iff] at hx
          obtain ⟨pr, _, hr⟩ := hx
          exact ih _ _ _ (h.2.2.2.2.2 pr.1 pr.2) x hr
  | reveal ts k ih =>
      intro h x hx
      rw [Step.run] at hx
      simp only [releaseAll_fst] at hx
      exact ih _ _ (h.2 _) x hx

/-! ### The four kinds of action and TidyO -/

theorem TidyO.init : TidyO Rl (DSt.init S) where
  viol := rfl
  shown_lt := fun _ h => absurd h (List.not_mem_nil)
  charged_lt := fun _ h => absurd h (List.not_mem_nil)
  tail_lt := fun _ h => absurd h (List.not_mem_nil)
  others_lt := fun _ h => absurd h (List.not_mem_nil)
  released := fun _ h => absurd h (List.not_mem_nil)
  closed_tail := fun _ h => absurd h (List.not_mem_nil)
  closed_others := fun _ h => absurd h (List.not_mem_nil)
  bits := fun _ h => absurd h (List.not_mem_nil)
  point := fun _ h => absurd h (List.not_mem_nil)

/-- TidyO does not depend on the table (so a query of the adversary keeps it). -/
theorem TidyO.table {d : DSt S} (h : TidyO Rl d) (T : Table S) : TidyO Rl { d with table := T } :=
  ⟨h.viol, h.shown_lt, h.charged_lt, h.tail_lt, h.others_lt, h.released, h.closed_tail,
    h.closed_others, h.bits, h.point⟩

theorem TidyO.plain {d : DSt S} (h : TidyO Rl d) (o : S.ι) (T : Table S) :
    TidyO Rl (afterPlain d o T) :=
  ⟨h.viol, h.shown_lt, h.charged_lt, h.tail_lt, h.others_lt, h.released, h.closed_tail,
    h.closed_others, h.bits, h.point⟩

theorem TidyO.fresh {d : DSt S} (h : TidyO Rl d) (v : Bits) : TidyO Rl (afterFresh d v) where
  viol := h.viol
  shown_lt := fun t ht => by rw [length_afterFresh]; exact Nat.lt_succ_of_lt (h.shown_lt t ht)
  charged_lt := fun e he => by rw [length_afterFresh]; exact Nat.lt_succ_of_lt (h.charged_lt e he)
  tail_lt := fun e he => by rw [length_afterFresh]; exact Nat.lt_succ_of_lt (h.tail_lt e he)
  others_lt :=
    fun e he u hu => by rw [length_afterFresh]; exact Nat.lt_succ_of_lt (h.others_lt e he u hu)
  released := h.released
  closed_tail := h.closed_tail
  closed_others := h.closed_others
  bits := fun e he => by
    rw [val_of_prefix (d := d) (d' := afterFresh d v) (List.prefix_append _ _) (h.charged_lt e he)]
    exact h.bits e he
  point := h.point

theorem markBad_eq_false {d : DSt S} {o : S.ι} {t : Tok} {us : List Tok}
    (hus : ∀ u ∈ us, u < d.vals.length) (htu : t ∉ us) (ht : FreeAt d o t) :
    markBad d o t us = false := by
  unfold markBad
  have h1 : decide (d.vals.length ≤ t) = false := decide_eq_false (Nat.not_le.mpr ht.lt)
  have h2 : d.shown.contains t = false := by
    rw [Bool.eq_false_iff]
    exact fun hc => ht.not_shown (List.contains_iff_mem.mp hc)
  have h3 : (d.evs.any fun e => decide (e.o = o) && (e.charged == t || e.others.contains t)) =
      false := by
    rw [List.any_eq_false]
    intro e he
    by_cases ho : e.o = o
    · have h4 : (e.charged == t) = false := beq_eq_false_iff_ne.mpr (ht.fresh e he ho).1
      have h5 : e.others.contains t = false := by
        rw [Bool.eq_false_iff]
        exact fun hc => (ht.fresh e he ho).2 (List.contains_iff_mem.mp hc)
      rw [h4, h5]
      simp
    · simp [ho]
  have h6 : (us.any fun u => decide (d.vals.length ≤ u)) = false := by
    rw [List.any_eq_false]
    intro u hu
    simpa using hus u hu
  have h7 : us.contains t = false := by
    rw [Bool.eq_false_iff]
    exact fun hc => htu (List.contains_iff_mem.mp hc)
  rw [h1, h2, h3, h6, h7]
  rfl

theorem TidyO.mark {d : DSt S} (h : TidyO Rl d) {o : S.ι} {t : Tok} {us : List Tok}
    (hus : ∀ u ∈ us, u < d.vals.length) (htu : t ∉ us) (ht : FreeAt d o t) (P : S.Dom o)
    (hb : Rl.bits o ≤ (d.val t).length) (hP : Rl.Mk o P) (r : S.Rng o) (T : Table S) :
    TidyO Rl (afterMark sp d o t us P r T) where
  viol := by
    show (d.viol || markBad d o t us) = false
    rw [h.viol, markBad_eq_false hus htu ht]
    rfl
  shown_lt := fun u hu => by rw [length_afterMark]; exact Nat.lt_succ_of_lt (h.shown_lt u hu)
  charged_lt := fun e he => by
    rw [length_afterMark]
    rcases mem_evs_afterMark he with he | rfl
    · exact Nat.lt_succ_of_lt (h.charged_lt e he)
    · exact Nat.lt_succ_of_lt ht.lt
  tail_lt := fun e he => by
    rw [length_afterMark]
    rcases mem_evs_afterMark he with he | rfl
    · exact Nat.lt_succ_of_lt (h.tail_lt e he)
    · exact Nat.lt_succ_self _
  others_lt := fun e he u hu => by
    rw [length_afterMark]
    rcases mem_evs_afterMark he with he | rfl
    · exact Nat.lt_succ_of_lt (h.others_lt e he u hu)
    · exact Nat.lt_succ_of_lt (hus u hu)
  released := fun e he hs => by
    rcases mem_evs_afterMark he with he | rfl
    · exact h.released e he hs
    · exact absurd hs ht.not_shown
  closed_tail := fun e he hr => by
    rcases mem_evs_afterMark he with he | rfl
    · exact h.closed_tail e he hr
    · exact absurd hr (by simp)
  closed_others := fun e he hr => by
    rcases mem_evs_afterMark he with he | rfl
    · exact h.closed_others e he hr
    · exact absurd hr (by simp)
  bits := fun e he => by
    have hp : d.vals <+: (afterMark sp d o t us P r T).vals := List.prefix_append _ _
    rcases mem_evs_afterMark he with he | rfl
    · rw [val_of_prefix hp (h.charged_lt e he)]
      exact h.bits e he
    · rw [val_of_prefix hp ht.lt]
      exact hb
  point := fun e he => by
    rcases mem_evs_afterMark he with he | rfl
    · exact h.point e he
    · exact hP

theorem TidyO.reveal {d : DSt S} (h : TidyO Rl d) {ts : List Tok}
    (hc : ClosedO d ts) (T : Table S) :
    TidyO Rl (afterReveal d ts T) := by
  have htail : ∀ e ∈ d.evs,
      (markDue (d.shown ++ ts) e).released = true → e.tail ∈ d.shown ++ ts := by
    intro e he hr
    rcases (markDue_released _ e).mp hr with hr | hr
    · exact List.mem_append_left _ (h.closed_tail e he hr)
    · rcases List.mem_append.mp hr with hs | hs
      · exact List.mem_append_left _ (h.closed_tail e he (h.released e he hs))
      · exact List.mem_append.mpr (hc.tail e he hs).symm
  have hoth : ∀ e ∈ d.evs,
      (markDue (d.shown ++ ts) e).released = true → ∀ u ∈ e.others, u ∈ d.shown ++ ts := by
    intro e he hr u hu
    rcases (markDue_released _ e).mp hr with hr | hr
    · exact List.mem_append_left _ (h.closed_others e he hr u hu)
    · rcases List.mem_append.mp hr with hs | hs
      · exact List.mem_append_left _ (h.closed_others e he (h.released e he hs) u hu)
      · exact List.mem_append.mpr (hc.others e he hs u hu).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : closedUnder (d.shown ++ ts) (d.evs.map (markDue (d.shown ++ ts))) = true := by
      unfold closedUnder
      rw [List.all_eq_true]
      intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      by_cases hr : (markDue (d.shown ++ ts) e).released = true
      · have h3 : (d.shown ++ ts).contains (markDue (d.shown ++ ts) e).tail = true := by
          rw [markDue_tail]
          exact List.contains_iff_mem.mpr (htail e he hr)
        have h5 : (markDue (d.shown ++ ts) e).others.all (d.shown ++ ts).contains = true := by
          rw [markDue_others, List.all_eq_true]
          exact fun u hu => List.contains_iff_mem.mpr (hoth e he hr u hu)
        rw [h3, h5]
        simp
      · simp [hr]
    have h4 : (ts.any fun u => decide (d.vals.length ≤ u)) = false := by
      rw [List.any_eq_false]
      intro u hu
      simpa using hc.lt u hu
    show (d.viol || !closedUnder (d.shown ++ ts) (d.evs.map (markDue (d.shown ++ ts))) ||
      ts.any fun u => decide (d.vals.length ≤ u)) = false
    rw [h.viol, h1, h4]
    rfl
  · intro t ht
    rcases List.mem_append.mp (show t ∈ d.shown ++ ts from ht) with ht | ht
    · exact h.shown_lt t ht
    · exact hc.lt t ht
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_charged]
    exact h.charged_lt e he
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_tail]
    exact h.tail_lt e he
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_others]
    exact h.others_lt e he
  · intro e' he' hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_charged] at hs
    exact (markDue_released _ e).mpr (Or.inr hs)
  · intro e' he' hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_tail]
    exact htail e he hr
  · intro e' he' hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_others]
    exact hoth e he hr
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    rw [markDue_o, markDue_charged]
    exact h.bits e he
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    exact (markDue_point _ e Rl.Mk).mpr (h.point e he)


end Generic

end Compile.Batch.Disc
