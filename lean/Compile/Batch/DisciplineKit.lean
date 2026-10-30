-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineKit.lean: the rules of deferred programming for marked queries that hold
several tokens (the charged one and the others): what a run adds, and what is known about a token
(tokens and marked queries: `Step`, `Ev`, Rom/Defer.lean; `GrowsO`, `ClosedO`:
Compile/Batch/SpecDiscipline.lean; words of this library: lean/GLOSSARY.md).

Generic in the family of oracles. `GrowsO` is reflexive, two runs compose (`GrowsO.trans`, under its
hypotheses: the counts add), and each of the four kinds of action is an instance. Three kinds of
knowledge about a token, `Untouched` (it may be a tail), `Deps` (of a token that exists) and `Len`,
each survive a run that does not touch the token. `ClosedO` follows from `Deps`, for tokens that
exist and whose dependencies are among them or shown (`ClosedO.of_deps`).
-/
import Compile.Batch.Discipline

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules markBad markDue afterPlain afterFresh afterMark afterReveal nEv val_of_prefix val_new
    markDue_o markDue_charged markDue_tail markDue_others nEv_map_markDue length_afterFresh
    length_afterMark mem_evs_afterMark cnt1 val_afterFresh val_afterMark)

section Kit
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {Ch R Ch₂ R₂ : Tok → Prop}
  {e M e₁ M₁ e₂ M₂ : S.ι → ℕ} {d d' d'' : DSt S}

/-! ### GrowsO
`GrowsO Ch R e M d d'` (Compile/Batch/SpecDiscipline.lean): what a run may have added on the way
from d to d'. Ch: the tokens of d that its marked queries may hold (charged or among the others); e
o and M o: how many ordinary and marked queries to o it may have added (R: see its doc comment). -/

theorem GrowsO.refl (d : DSt S) : GrowsO Ch R e M d d where
  vals := List.prefix_refl _
  shown_old := fun _ h => h
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => Or.inl ⟨e', he', rfl, rfl, rfl, rfl⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun _ => Nat.le_add_right _ _

theorem GrowsO.length_le (h : GrowsO Ch R e M d d') : d.vals.length ≤ d'.vals.length :=
  h.vals.length_le

theorem GrowsO.trans (h₁ : GrowsO Ch R e₁ M₁ d d') (h₂ : GrowsO Ch₂ R₂ e₂ M₂ d' d'')
    (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t) (hR : ∀ t, R₂ t → R t ∨ d.vals.length ≤ t)
    (he : ∀ o, e₁ o + e₂ o ≤ e o) (hM : ∀ o, M₁ o + M₂ o ≤ M o) : GrowsO Ch R e M d d'' where
  vals := h₁.vals.trans h₂.vals
  shown_old := fun t ht => h₂.shown_old t (h₁.shown_old t ht)
  shown := fun t ht => by
    rcases h₂.shown t ht with h | h | h
    · exact h₁.shown t h
    · exact Or.inr (hR t h)
    · exact Or.inr (Or.inr (le_trans h₁.length_le h))
  evs := fun e'' he'' => by
    rcases h₂.evs e'' he'' with ⟨e', he', ho, hc, hu, ht⟩ | ⟨ht, hc, hu⟩
    · rcases h₁.evs e' he' with ⟨e₀, he₀, ho', hc', hu', ht'⟩ | ⟨ht', hc', hu'⟩
      · exact Or.inl ⟨e₀, he₀, ho'.trans ho, hc'.trans hc, hu'.trans hu, ht'.trans ht⟩
      · exact Or.inr ⟨ht ▸ ht', hc ▸ hc', hu ▸ hu'⟩
    · refine Or.inr ⟨le_trans h₁.length_le ht, ?_, fun u hu' => ?_⟩
      · rcases hc with hc | hc
        · exact hCh _ hc
        · exact Or.inr (le_trans h₁.length_le hc)
      · rcases hu u hu' with hc | hc
        · exact hCh _ hc
        · exact Or.inr (le_trans h₁.length_le hc)
  plain := fun o => by
    have a := h₁.plain o
    have b := h₂.plain o
    have c := he o
    omega
  marked := fun o => by
    have a := h₁.marked o
    have b := h₂.marked o
    have c := hM o
    omega

theorem GrowsO.mono (h : GrowsO Ch₂ R₂ e₂ M₂ d d') (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t)
    (hR : ∀ t, R₂ t → R t ∨ d.vals.length ≤ t) (he : ∀ o, e₂ o ≤ e o) (hM : ∀ o, M₂ o ≤ M o) :
    GrowsO Ch R e M d d' :=
  (GrowsO.refl (Ch := Ch) (R := R) (e := fun _ => 0) (M := fun _ => 0) d).trans h hCh hR
    (fun o => by rw [Nat.zero_add]; exact he o) (fun o => by rw [Nat.zero_add]; exact hM o)

theorem GrowsO.ofPlain (d : DSt S) (o : S.ι) (T : Table S) :
    GrowsO Ch R (cnt1 o 1) M d (afterPlain d o T) where
  vals := List.prefix_refl _
  shown_old := fun _ h => h
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => Or.inl ⟨e', he', rfl, rfl, rfl, rfl⟩
  plain := fun o' => by
    show Function.update d.nPlain o (d.nPlain o + 1) o' ≤ d.nPlain o' + cnt1 o 1 o'
    unfold cnt1
    by_cases h : o' = o
    · subst h
      rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne h, if_neg h]
      exact Nat.le_add_right _ _
  marked := fun _ => Nat.le_add_right _ _

theorem GrowsO.ofFresh (d : DSt S) (v : Bits) : GrowsO Ch R e M d (afterFresh d v) where
  vals := List.prefix_append _ _
  shown_old := fun _ h => h
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => Or.inl ⟨e', he', rfl, rfl, rfl, rfl⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun _ => Nat.le_add_right _ _

theorem GrowsO.ofMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    GrowsO (fun t' => t' = t ∨ t' ∈ us) R e (cnt1 o 1) d (afterMark sp d o t us P r T) where
  vals := List.prefix_append _ _
  shown_old := fun _ h => h
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => by
    rcases mem_evs_afterMark he' with h | rfl
    · exact Or.inl ⟨e', h, rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨le_rfl, Or.inl (Or.inl rfl), fun u hu => Or.inl (Or.inr hu)⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun o' => by
    show ((d.evs ++ [(⟨o, P, r, t, us, d.vals.length, false⟩ : Ev S)]).filter fun v =>
        decide (v.o = o')).length ≤
      nEv d o' + cnt1 o 1 o'
    rw [List.filter_append, List.length_append]
    refine Nat.add_le_add_left ?_ _
    unfold cnt1
    by_cases h : o' = o
    · rw [if_pos h]
      exact le_trans (List.length_filter_le _ _) (le_of_eq rfl)
    · rw [if_neg h, List.filter_cons_of_neg (by simpa using fun hh : o = o' => h hh.symm)]
      exact le_rfl

theorem GrowsO.ofReveal (d : DSt S) (ts : List Tok) (T : Table S) :
    GrowsO Ch (fun t => t ∈ ts) e M d (afterReveal d ts T) where
  vals := List.prefix_refl _
  shown_old := fun _ h => List.mem_append_left _ h
  shown := fun t ht => by
    rcases List.mem_append.mp (show t ∈ d.shown ++ ts from ht) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  evs := fun e' he' => by
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    exact Or.inl
      ⟨e₀, he₀, (markDue_o _ _).symm, (markDue_charged _ _).symm,
        (markDue_others _ _).symm, (markDue_tail _ _).symm⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun o => by
    show ((d.evs.map (markDue (d.shown ++ ts))).filter fun v => decide (v.o = o)).length ≤
      nEv d o + M o
    rw [nEv_map_markDue]
    exact Nat.le_add_right _ _

/-! ### What is known about a token -/

/-- The tail and the others of every query that is charged to u are in l. -/
def Deps (d : DSt S) (u : Tok) (l : List Tok) : Prop :=
  ∀ e ∈ d.evs, e.charged = u → e.tail ∈ l ∧ ∀ v ∈ e.others, v ∈ l

/-- The token exists, is not shown, and no query holds it. -/
structure Untouched (d : DSt S) (t : Tok) : Prop where
  lt : t < d.vals.length
  not_shown : t ∉ d.shown
  not_held : ∀ e ∈ d.evs, e.charged ≠ t ∧ t ∉ e.others

/-- The token exists and its value has n bits. -/
def Len (d : DSt S) (t : Tok) (n : ℕ) : Prop := t < d.vals.length ∧ (d.val t).length = n

theorem Untouched.freeAt {t : Tok} (h : Untouched d t) (o : S.ι) : FreeAt d o t :=
  ⟨h.lt, h.not_shown, fun e he _ => h.not_held e he⟩

theorem Untouched.deps {t : Tok} (h : Untouched d t) (l : List Tok) : Deps d t l := fun e he hc =>
  absurd hc (h.not_held e he).1

theorem Deps.mono {u : Tok} {l l' : List Tok} (h : Deps d u l) (hl : ∀ v ∈ l, v ∈ l') :
    Deps d u l' :=
  fun e he hc => ⟨hl _ (h e he hc).1, fun v hv => hl _ ((h e he hc).2 v hv)⟩

theorem Untouched.grows {t : Tok} (hf : Untouched d t) (h : GrowsO Ch R e M d d')
    (hc : ¬ Ch t) (hr : ¬ R t) : Untouched d' t where
  lt := lt_of_lt_of_le hf.lt h.length_le
  not_shown := fun hs => by
    rcases h.shown t hs with h1 | h1 | h1
    · exact hf.not_shown h1
    · exact hr h1
    · exact absurd hf.lt (Nat.not_lt.mpr h1)
  not_held := fun e' he' => by
    rcases h.evs e' he' with ⟨e₀, he₀, _, hc₀, hu₀, _⟩ | ⟨_, h1, h2⟩
    · exact ⟨hc₀ ▸ (hf.not_held e₀ he₀).1, hu₀ ▸ (hf.not_held e₀ he₀).2⟩
    · refine ⟨fun hce => ?_, fun hu => ?_⟩
      · rcases h1 with h1 | h1
        · exact hc (hce ▸ h1)
        · exact absurd hf.lt (Nat.not_lt.mpr (hce ▸ h1))
      · rcases h2 t hu with h1 | h1
        · exact hc h1
        · exact absurd hf.lt (Nat.not_lt.mpr h1)

theorem FreeAt.grows {o : S.ι} {t : Tok} (hf : FreeAt d o t) (h : GrowsO Ch R e M d d')
    (hc : ¬ Ch t) (hr : ¬ R t) : FreeAt d' o t where
  lt := lt_of_lt_of_le hf.lt h.length_le
  not_shown := fun hs => by
    rcases h.shown t hs with h1 | h1 | h1
    · exact hf.not_shown h1
    · exact hr h1
    · exact absurd hf.lt (Nat.not_lt.mpr h1)
  fresh := fun e' he' ho => by
    rcases h.evs e' he' with ⟨e₀, he₀, ho₀, hc₀, hu₀, _⟩ | ⟨_, h1, h2⟩
    · exact ⟨hc₀ ▸ (hf.fresh e₀ he₀ (ho₀.trans ho)).1, hu₀ ▸ (hf.fresh e₀ he₀ (ho₀.trans ho)).2⟩
    · refine ⟨fun hce => ?_, fun hu => ?_⟩
      · rcases h1 with h1 | h1
        · exact hc (hce ▸ h1)
        · exact absurd hf.lt (Nat.not_lt.mpr (hce ▸ h1))
      · rcases h2 t hu with h1 | h1
        · exact hc h1
        · exact absurd hf.lt (Nat.not_lt.mpr h1)

theorem Deps.grows {u : Tok} {l : List Tok} (hd : Deps d u l) (hlt : u < d.vals.length)
    (h : GrowsO Ch R e M d d') (hc : ¬ Ch u) : Deps d' u l :=
  fun e' he' hce => by
    rcases h.evs e' he' with ⟨e₀, he₀, _, hc₀, hu₀, ht₀⟩ | ⟨_, h1, _⟩
    · exact ⟨ht₀ ▸ (hd e₀ he₀ (hc₀.trans hce)).1, hu₀ ▸ (hd e₀ he₀ (hc₀.trans hce)).2⟩
    · rcases h1 with h1 | h1
      · exact absurd (hce ▸ h1) hc
      · exact absurd hlt (Nat.not_lt.mpr (hce ▸ h1))

theorem Len.grows {t : Tok} {n : ℕ} (hl : Len d t n) (h : GrowsO Ch R e M d d') : Len d' t n :=
  ⟨lt_of_lt_of_le hl.1 h.length_le, by rw [val_of_prefix h.vals hl.1]; exact hl.2⟩

/-- Tokens that exist and whose dependencies are among them, or shown, can be revealed together. -/
theorem ClosedO.of_deps {ts : List Tok} (hlt : ∀ t ∈ ts, t < d.vals.length)
    (h : ∀ u ∈ ts, ∃ l, Deps d u l ∧ ∀ v ∈ l, v ∈ ts ∨ v ∈ d.shown) : ClosedO d ts where
  lt := hlt
  tail := fun e he hc => by
    obtain ⟨l, hl, hsub⟩ := h _ hc
    exact hsub _ (hl e he rfl).1
  others := fun e he hc v hv => by
    obtain ⟨l, hl, hsub⟩ := h _ hc
    exact hsub _ ((hl e he rfl).2 v hv)

/-- Tokens that can be revealed together can still be revealed after a run whose queries do not hold
them. -/
theorem ClosedO.grows {ts : List Tok} (hc : ClosedO d ts)
    (h : GrowsO Ch R e M d d') (hch : ∀ t ∈ ts, ¬ Ch t) : ClosedO d' ts where
  lt := fun t ht => lt_of_lt_of_le (hc.lt t ht) h.length_le
  tail := fun e' he' hce => by
    rcases h.evs e' he' with ⟨e₀, he₀, _, hc₀, _, ht₀⟩ | ⟨_, h1 | h1, _⟩
    · exact ht₀ ▸ (hc.tail e₀ he₀ (hc₀ ▸ hce)).imp_right (h.shown_old _)
    · exact absurd h1 (hch _ hce)
    · exact absurd (hc.lt _ hce) (Nat.not_lt.mpr h1)
  others := fun e' he' hce v hv => by
    rcases h.evs e' he' with ⟨e₀, he₀, _, hc₀, hu₀, _⟩ | ⟨_, h1 | h1, _⟩
    · exact (hc.others e₀ he₀ (hc₀ ▸ hce) v (hu₀ ▸ hv)).imp_right (h.shown_old _)
    · exact absurd h1 (hch _ hce)
    · exact absurd (hc.lt _ hce) (Nat.not_lt.mpr h1)

/-! ### New tokens -/

theorem Untouched.of_fresh (h : TidyO Rl d) (v : Bits) :
    Untouched (afterFresh d v) d.vals.length where
  lt := by rw [length_afterFresh]; exact Nat.lt_succ_self _
  not_shown := fun hs => absurd (h.shown_lt _ hs) (lt_irrefl _)
  not_held := fun e₀ he₀ =>
    ⟨fun hc => absurd (hc ▸ h.charged_lt e₀ he₀) (lt_irrefl _),
      fun hu => absurd (h.others_lt e₀ he₀ _ hu) (lt_irrefl _)⟩

theorem Len.of_fresh (d : DSt S) {ℓ : ℕ} (u : Fin ℓ → Bool) :
    Len (afterFresh d (List.ofFn u)) d.vals.length ℓ :=
  ⟨by rw [length_afterFresh]; exact Nat.lt_succ_self _,
    by rw [val_afterFresh]; exact List.length_ofFn⟩

/-- Under the hypotheses below: the tail of a new query is untouched. -/
theorem Untouched.of_tail (h : TidyO Rl d) {o : S.ι} {t : Tok} {us : List Tok}
    (ht : t < d.vals.length) (hus : ∀ u ∈ us, u < d.vals.length) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Untouched (afterMark sp d o t us P r T) d.vals.length where
  lt := by rw [length_afterMark]; exact Nat.lt_succ_self _
  not_shown := fun hs => absurd (h.shown_lt _ hs) (lt_irrefl _)
  not_held := fun e₀ he₀ => by
    rcases mem_evs_afterMark he₀ with he₀ | rfl
    · exact ⟨fun hc => absurd (hc ▸ h.charged_lt e₀ he₀) (lt_irrefl _),
        fun hu => absurd (h.others_lt e₀ he₀ _ hu) (lt_irrefl _)⟩
    · exact ⟨fun hc => absurd (show t = d.vals.length from hc) (Nat.ne_of_lt ht),
        fun hu => absurd (hus _ hu) (lt_irrefl _)⟩

theorem Len.of_tail (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Len (afterMark sp d o t us P r T) d.vals.length (sp.tl o) :=
  ⟨by rw [length_afterMark]; exact Nat.lt_succ_self _,
    by rw [val_afterMark]; exact List.length_ofFn⟩

/-- What the token that has just been charged depends on. -/
theorem Deps.of_mark {o : S.ι} {t : Tok} {us l : List Tok} (h : Deps d t l) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Deps (afterMark sp d o t us P r T) t (d.vals.length :: (us ++ l)) := fun e₀ he₀ hc => by
  rcases mem_evs_afterMark he₀ with he₀ | rfl
  · exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ (h e₀ he₀ hc).1),
      fun v hv => List.mem_cons_of_mem _ (List.mem_append_right _ ((h e₀ he₀ hc).2 v hv))⟩
  · exact ⟨List.mem_cons_self, fun v hv => List.mem_cons_of_mem _ (List.mem_append_left _ hv)⟩

end Kit

end Compile.Batch.Disc
