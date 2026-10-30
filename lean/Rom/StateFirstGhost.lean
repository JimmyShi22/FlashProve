-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstGhost.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): the relation `Ghost` at each step of a run.

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). A mixed program (over `mixSpec`) makes typed queries (the honest side's, to the first
family) and raw queries (an adversary's, to the second). The ideal interpretations (`ideal`) are
programs over the first family, in which a reduction answers the raw expansion queries from a table
(`Book`). (`Link`, `stSpec`: Rom/StateFirst.lean; `mixSpec`, `ideal`, `Book`:
Rom/StateFirstMix.lean.)

For the step's main lemma (`Spec.mixClose`, Rom/StateFirstMix.lean) it is shown that the relation
`Ghost` (Rom/StateFirstHitDef.lean) is preserved by each step of a run (at a new query: if the
answer is fine; and under hR: see Limits), and that under `Ghost`, where the tables bT and bF
(below) differ at a query to dr, its state is the state of T's answer at a hidden query
(`ghost_hit`; hidden query: Rom/StateFirstHitDef.lean). Counting lemmas (`cnt_mem_le`,
`pr_not_fine_plain`, `pr_not_fine`); otherwise no probability.

`Ghost T bT bF H` relates the lazily sampled table T of the first family, the reduction's table bF,
a ghost table bT of all chain answers, which exists only in the proof, and the hidden queries H. An
answer is fine (`Link.fine`) if its state is not among the states that bT knows (`stL`); by
`good_of_fine` it is then `Link.good` (Rom/StateFirstColl.lean).

Limits: nothing on runs or programs: each lemma is on one step (the induction is in
Rom/StateFirstMain.lean). That an answer is fine is a hypothesis of the lemmas on new queries. So is
hR in `ghost_typed_new`, `ghost_raw_new` and `ghost_raw_old`: at a chain oracle bT holds at the
query what T holds (`Rel.made`, Rom/StateFirstColl.lean, gives it). Nothing on how often a hidden
state is met (`Spec.psiLe`).
-/
import Rom.StateFirstAvg
import Rom.StateFirstFind

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))

/-! ## The states that a `Book` knows -/

/-- the states of the entered answers, and the first components of the queries for which the `Book`
has itself sampled answers -/
def stL (b : Book S lam) : List (Dg lam × Dg lam) :=
  (b.made.filterMap fun e => (C e.1).stateOf e.2.2) ++ b.loose.map fun x => x.1.1

theorem length_stL_le (b : Book S lam) : (stL C b).length ≤ b.made.length + b.loose.length := by
  unfold stL
  rw [List.length_append, List.length_map]
  exact Nat.add_le_add_right (List.length_filterMap_le _ _) _

theorem mem_stL_of_made {b : Book S lam} {e : QA S} (he : e ∈ b.made)
    {σ : Dg lam × Dg lam} (hs : (C e.1).stateOf e.2.2 = some σ) : σ ∈ stL C b :=
  List.mem_append_left _ (List.mem_filterMap.mpr ⟨e, he, hs⟩)

theorem mem_stL_of_drVal {b : Book S lam} {σ : Dg lam × Dg lam}
    {j : ℕ} (hj : drVal C b (σ, j) ≠ none) : σ ∈ stL C b := by
  unfold stL
  rw [List.mem_append]
  unfold drVal at hj
  cases hl : b.loose.lookup (σ, j) with
  | some v =>
    right
    exact List.mem_map.mpr ⟨((σ, j), v), mem_of_lookup _ hl, rfl⟩
  | none =>
    left
    rw [hl] at hj
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hj
    unfold findBlock at hv
    obtain ⟨e, he, hev⟩ := List.exists_of_findSome?_eq_some hv
    split at hev
    · rename_i hs
      exact List.mem_filterMap.mpr ⟨e, he, hs⟩
    · cases hev

namespace Link
variable {R : Type}
/-- the state of the answer is not in the list (an answer of an unchanged oracle has no state: it is
fine) -/
def fine (c : Link lam R) (L : List (Dg lam × Dg lam)) (r : R) : Prop :=
  ∀ σ, c.stateOf r = some σ → σ ∉ L
end Link

theorem good_of_fine {o : S.ι} {b : Book S lam} {r : S.Rng o} (h : (C o).fine (stL C b) r) :
    (C o).good (drVal C b) r := fun σ hs j _ => by
  by_contra hn
  exact h σ hs (mem_stL_of_drVal C hn)

theorem pr_not_fine_plain {R : Type} [Fintype R] [Nonempty R] (c : Link lam R)
    (hc : c.isPlain = true) (L : List (Dg lam × Dg lam)) :
    pr (unif R) {r | ¬ c.fine L r} = 0 := by
  have : {r : R | ¬ c.fine L r} = ∅ :=
    Set.eq_empty_of_forall_notMem fun r h =>
      h fun σ hs => by rw [isPlain_of_stateOf c hs] at hc; cases hc
  rw [this]
  simp [pr]

theorem cnt_mem_le {γ : Type} [Finite γ] (L : List γ) :
    Prob.cnt (fun σ : γ => σ ∈ L) ≤ L.length := by
  classical
  exact cnt_le_of_forall_finset fun Y hY =>
    le_trans (Finset.card_le_card fun σ hσ => List.mem_toFinset.mpr (hY σ hσ))
      (List.toFinset_card_le _)

/-- A uniform answer is not fine with probability at most (length of L) / 2^(2 lam) (R nonempty). -/
theorem pr_not_fine {R : Type} [Fintype R] [Nonempty R]
    (c : Link lam R) (L : List (Dg lam × Dg lam)) :
    pr (unif R) {r | ¬ c.fine L r} ≤ (L.length : ℝ≥0∞) * wSt lam := by
  cases c with
  | plain => rw [pr_not_fine_plain Link.plain rfl]; exact zero_le _
  | chain K e =>
    have hR : unif R = (unif ((Fin K → Dg lam) × Dg lam × Dg lam)).map e.symm :=
      (map_unif_equiv e.symm).symm
    rw [hR, pr_map]
    have hsub : (e.symm ⁻¹' {r | ¬ (Link.chain K e).fine L r}) ⊆
        {x : (Fin K → Dg lam) × Dg lam × Dg lam | x.2 ∈ L} := fun x hx => by
      by_contra hn
      refine hx fun σ hs => ?_
      have h' : some (e (e.symm x)).2 = some σ := hs
      rw [Equiv.apply_symm_apply] at h'
      rw [← Option.some.inj h']
      exact hn
    refine le_trans (pr_mono _ hsub) ?_
    have h2 : pr (unif ((Fin K → Dg lam) × Dg lam × Dg lam)) {x | x.2 ∈ L} =
        pr (unif (Dg lam × Dg lam)) {σ | σ ∈ L} := by
      rw [unif_prod, ← map_snd_prod (unif (Fin K → Dg lam)) (unif (Dg lam × Dg lam)), pr_map,
        map_snd_prod]
      rfl
    rw [h2]
    refine le_trans (pr_unif_le_of_cnt_le (cnt_mem_le L)) (le_of_eq ?_)
    rw [card_state, div_eq_mul_inv]
    rfl

/-! ## Searches -/

theorem entryAt_ne {o o' : S.ι} {q : S.Dom o} {q' : S.Dom o'}
    (h : (⟨o', q'⟩ : PtS S) ≠ ⟨o, q⟩) (r : S.Rng o) :
    entryAt (⟨o, q, r⟩ : QA S) o' q' = none := by
  by_cases ho : o' = o
  · subst ho
    exact entryAt_ne_point o' (fun e => h (by rw [e])) r
  · exact entryAt_ne_oracle ho q r q'

/-- where the states of the entries are pairwise different, the search finds a hash block if and
only if some entry with the state has it -/
theorem findBlock_iff {made : List (QA S)}
    (hinj : ∀ e ∈ made,
      ∀ e' ∈ made, ∀ σ, (C e.1).stateOf e.2.2 = some σ → (C e'.1).stateOf e'.2.2 = some σ → e = e')
    (σ : Dg lam × Dg lam) (j : ℕ) (v : Dg lam) :
    findBlock C made σ j = some v ↔
    ∃ e ∈ made, (C e.1).stateOf e.2.2 = some σ ∧ (C e.1).blockOf e.2.2 j = some v := by
  have fwd : ∀ w, findBlock C made σ j = some w →
      ∃ e ∈ made, (C e.1).stateOf e.2.2 = some σ ∧ (C e.1).blockOf e.2.2 j = some w := fun w h => by
    unfold findBlock at h
    obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
    split at hf
    · rename_i hs
      exact ⟨e, he, hs, hf⟩
    · cases hf
  refine ⟨fwd v, ?_⟩
  rintro ⟨e, he, hs, hb⟩
  cases hfb : findBlock C made σ j with
  | none =>
    unfold findBlock at hfb
    have := List.findSome?_eq_none_iff.1 hfb e he
    rw [if_pos hs, hb] at this
    cases this
  | some w =>
    obtain ⟨e', he', hs', hb'⟩ := fwd w hfb
    have := hinj e he e' he' σ hs hs'
    subst this
    rw [← hb, ← hb']

/-! ## `Ghost` is preserved -/

variable {C}
variable {T : Table S} {bT bF : Book S lam} {H : List (PtS S)}

theorem Ghost.pt_ne (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o} (hT : T o q = none) :
    ∀ e ∈ bT.made, (⟨e.1, e.2.1⟩ : PtS S) ≠ ⟨o, q⟩ := by
  rintro ⟨o', q', r'⟩ he h
  cases h
  have := hG.true _ he
  rw [hT] at this
  cases this

theorem Ghost.not_mem (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o} (hT : T o q = none) :
    (⟨o, q⟩ : PtS S) ∉ H :=
  fun h => hG.live _ h hT

/-- a new entry of T at an unchanged oracle -/
theorem ghost_set_plain (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o} (hp : (C o).isPlain = true)
    (hT : T o q = none) (r : S.Rng o) :
    Ghost C (T.set o q r) bT bF H where
  loose := hG.loose
  sub := hG.sub
  cover := hG.cover
  hid := hG.hid
  madeF := fun o' q' hn hc => by
    rw [Table.set_ne T (fun e => by cases e; rw [hp] at hc; cases hc) r]
    exact hG.madeF o' q' hn hc
  true := fun e he => by
    rw [Table.set_ne T (hG.pt_ne hT e he) r]
    exact hG.true e he
  inj := hG.inj
  nodup := hG.nodup
  live := fun h hh => by
    rw [Table.set_ne T (fun e => hG.not_mem hT (e ▸ hh)) r]
    exact hG.live h hh
  chain := hG.chain

theorem true_new (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o}
    (hT : T o q = none) (r : S.Rng o) :
    ∀ e ∈ bT.made ++ [(⟨o, q, r⟩ : QA S)], (T.set o q r) e.1 e.2.1 = some e.2.2 := fun e he => by
  rcases List.mem_append.1 he with h | h
  · rw [Table.set_ne T (hG.pt_ne hT e h) r]
    exact hG.true e h
  · rw [List.mem_singleton.1 h]
    exact Table.set_self T o q r

theorem inj_new (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (hf : (C o).fine (stL C bT) r) :
    ∀ e ∈ bT.made ++ [(⟨o, q, r⟩ : QA S)], ∀ e' ∈ bT.made ++ [(⟨o, q, r⟩ : QA S)], ∀ σ,
      (C e.1).stateOf e.2.2 = some σ → (C e'.1).stateOf e'.2.2 = some σ →
      e = e' := fun e he e' he' σ hs hs' => by
  rcases List.mem_append.1 he with h | h
  · rcases List.mem_append.1 he' with h' | h'
    · exact hG.inj e h e' h' σ hs hs'
    · rw [List.mem_singleton.1 h'] at hs'
      exact absurd (mem_stL_of_made C h hs) (hf σ hs')
  · rcases List.mem_append.1 he' with h' | h'
    · rw [List.mem_singleton.1 h] at hs
      exact absurd (mem_stL_of_made C h' hs') (hf σ hs)
    · rw [List.mem_singleton.1 h, List.mem_singleton.1 h']

/-- A new typed query with a fine answer: at a chain oracle the answer is entered in bT, not in bF,
and the query becomes hidden. Also assumed: hR (at a chain oracle bT has no answer at the query). -/
theorem ghost_typed_new (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o}
    (hR : (C o).isPlain = false → findMade bT.made o q = none) (hT : T o q = none)
    {r : S.Rng o} (hf : (C o).fine (stL C bT) r) :
    Ghost C (T.set o q r) (bT.note C o q r) bF
      (if (C o).isPlain = true then H else ⟨o, q⟩ :: H) := by
  have hnH := hG.not_mem hT
  by_cases hp : (C o).isPlain = true
  · rw [if_pos hp, note_plain C bT o q r hp]
    exact ghost_set_plain hG hp hT r
  · have hp' : (C o).isPlain = false := by simpa using hp
    rw [if_neg hp, note_new C bT o q r hp' (hR hp')]
    exact {
      loose := hG.loose
      sub := fun e he => List.mem_append_left _ (hG.sub e he)
      cover := fun e he => by
        rcases List.mem_append.1 he with h | h
        · exact (hG.cover e h).imp id (List.mem_cons_of_mem _)
        · rw [List.mem_singleton.1 h]
          exact Or.inr List.mem_cons_self
      hid := fun h hh => by
        rcases List.mem_cons.1 hh with rfl | hh
        · exact (hG.madeF o q hnH hp').trans hT
        · exact hG.hid h hh
      madeF := fun o' q' hn hc => by
        rw [Table.set_ne T (fun e => hn (e ▸ List.mem_cons_self)) r]
        exact hG.madeF o' q' (fun h => hn (List.mem_cons_of_mem _ h)) hc
      true := true_new hG hT r
      inj := inj_new hG hf
      nodup := List.nodup_cons.2 ⟨hnH, hG.nodup⟩
      live := fun h hh => by
        rcases List.mem_cons.1 hh with rfl | hh
        · rw [Table.set_self]
          exact Option.some_ne_none _
        · rw [Table.set_ne T (fun e => hnH (e ▸ hh)) r]
          exact hG.live h hh
      chain := fun h hh => by
        rcases List.mem_cons.1 hh with rfl | hh
        · exact hp'
        · exact hG.chain h hh }

/-- A new raw query for a state, with a fine answer: at a chain oracle the answer is entered in both
tables. Also assumed: hR (at a chain oracle bT has no answer at the query). -/
theorem ghost_raw_new (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o}
    (hR : (C o).isPlain = false → findMade bT.made o q = none) (hT : T o q = none)
    {r : S.Rng o} (hf : (C o).fine (stL C bT) r) :
    Ghost C (T.set o q r) (bT.note C o q r) (bF.note C o q r) H := by
  have hnH := hG.not_mem hT
  by_cases hp : (C o).isPlain = true
  · rw [note_plain C bT o q r hp, note_plain C bF o q r hp]
    exact ghost_set_plain hG hp hT r
  · have hp' : (C o).isPlain = false := by simpa using hp
    have hbF : findMade bF.made o q = none := (hG.madeF o q hnH hp').trans hT
    rw [note_new C bT o q r hp' (hR hp'), note_new C bF o q r hp' hbF]
    exact {
      loose := hG.loose
      sub := fun e he => by
        rcases List.mem_append.1 he with h | h
        · exact List.mem_append_left _ (hG.sub e h)
        · exact List.mem_append_right _ h
      cover := fun e he => by
        rcases List.mem_append.1 he with h | h
        · exact (hG.cover e h).imp (List.mem_append_left _) id
        · exact Or.inl (List.mem_append_right _ h)
      hid := fun h hh => by
        show findMade (bF.made ++ [⟨o, q, r⟩]) h.1 h.2 = none
        rw [findMade_append, hG.hid h hh,
          entryAt_ne (fun e => hnH (by have : h = ⟨o, q⟩ := e; exact this ▸ hh)) r]
        rfl
      madeF := fun o' q' hn hc => by
        show findMade (bF.made ++ [⟨o, q, r⟩]) o' q' = _
        by_cases e : (⟨o', q'⟩ : PtS S) = ⟨o, q⟩
        · cases e
          rw [findMade_append, hbF, entryAt_self, Table.set_self]
          rfl
        · rw [findMade_append, entryAt_ne e, Option.or_none, Table.set_ne T e r]
          exact hG.madeF o' q' hn hc
      true := true_new hG hT r
      inj := inj_new hG hf
      nodup := hG.nodup
      live := fun h hh => by
        rw [Table.set_ne T (fun e => hnH (e ▸ hh)) r]
        exact hG.live h hh
      chain := hG.chain }

/-- A raw query for a state that was made before: bT stays, the answer is entered in bF if the query
was hidden, and the query is no longer hidden. Also assumed: hR (at a chain oracle bT has T's answer
at the query). -/
theorem ghost_raw_old [DecidableEq (PtS S)] (hG : Ghost C T bT bF H) {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (hT : T o q = some r)
    (hR : (C o).isPlain = false → findMade bT.made o q = some r) :
    Ghost C T bT (bF.note C o q r) (H.erase ⟨o, q⟩) := by
  by_cases hH : (⟨o, q⟩ : PtS S) ∈ H
  · have hp' : (C o).isPlain = false := hG.chain _ hH
    have hbF : findMade bF.made o q = none := hG.hid _ hH
    have hmem : (⟨o, q, r⟩ : QA S) ∈ bT.made := findMade_mem (hR hp')
    rw [note_new C bF o q r hp' hbF]
    exact {
      loose := hG.loose
      sub := fun e he => by
        rcases List.mem_append.1 he with h | h
        · exact hG.sub e h
        · rw [List.mem_singleton.1 h]
          exact hmem
      cover := fun e he => by
        rcases hG.cover e he with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · by_cases e1 : (⟨e.1, e.2.1⟩ : PtS S) = ⟨o, q⟩
          · obtain ⟨o', q', r'⟩ := e
            cases e1
            have h3 := hG.true _ he
            rw [hT] at h3
            cases h3
            exact Or.inl (List.mem_append_right _ (List.mem_singleton.2 rfl))
          · exact Or.inr ((List.mem_erase_of_ne e1).2 h)
      hid := fun h hh => by
        obtain ⟨hne, hh'⟩ := (hG.nodup.mem_erase_iff).1 hh
        show findMade (bF.made ++ [⟨o, q, r⟩]) h.1 h.2 = none
        rw [findMade_append, hG.hid h hh', entryAt_ne (fun e => hne e) r]
        rfl
      madeF := fun o' q' hn hc => by
        show findMade (bF.made ++ [⟨o, q, r⟩]) o' q' = _
        by_cases e : (⟨o', q'⟩ : PtS S) = ⟨o, q⟩
        · cases e
          rw [findMade_append, hbF, entryAt_self, hT]
          rfl
        · rw [findMade_append, entryAt_ne e, Option.or_none]
          exact hG.madeF o' q' (fun h => hn ((List.mem_erase_of_ne e).2 h)) hc
      true := hG.true
      inj := hG.inj
      nodup := hG.nodup.erase _
      live := fun h hh => hG.live h (List.mem_of_mem_erase hh)
      chain := fun h hh => hG.chain h (List.mem_of_mem_erase hh) }
  · rw [List.erase_of_not_mem hH]
    by_cases hp : (C o).isPlain = true
    · rw [note_plain C bF o q r hp]
      exact hG
    · rw [note_old C bF o q r r ((hG.madeF o q hH (by simpa using hp)).trans hT)]
      exact hG

/-- the same sampled answer for dr is stored in both tables -/
theorem ghost_loose (hG : Ghost C T bT bF H) (x : ((Dg lam × Dg lam) × ℕ) × Dg lam) :
    Ghost C T { bT with loose := x :: bT.loose } { bF with loose := x :: bF.loose } H where
  loose := by
    show x :: bT.loose = x :: bF.loose
    rw [hG.loose]
  sub := hG.sub
  cover := hG.cover
  hid := hG.hid
  madeF := hG.madeF
  true := hG.true
  inj := hG.inj
  nodup := hG.nodup
  live := hG.live
  chain := hG.chain

/-- Under `Ghost`: where bT and bF differ at a query to dr, its state is the state of T's answer at
a hidden query. -/
theorem ghost_hit (hG : Ghost C T bT bF H)
    (p : (Dg lam × Dg lam) × ℕ) (hd : drVal C bT p ≠ drVal C bF p) : hitAt C T H p.1 := by
  by_contra hn
  apply hd
  unfold drVal
  rw [hG.loose]
  cases bF.loose.lookup p with
  | some v => rfl
  | none =>
    show findBlock C bT.made p.1 p.2 = findBlock C bF.made p.1 p.2
    refine Option.ext fun v => ?_
    rw [findBlock_iff C hG.inj,
      findBlock_iff C fun e he e' he' => hG.inj e (hG.sub e he) e' (hG.sub e' he')]
    constructor
    · rintro ⟨e, he, hs, hb⟩
      refine ⟨e, ?_, hs, hb⟩
      rcases hG.cover e he with h | h
      · exact h
      · exact absurd ⟨⟨e.1, e.2.1⟩, h, e.2.2, hG.true e he, hs⟩ hn
    · rintro ⟨e, he, hs, hb⟩
      exact ⟨e, hG.sub e he, hs, hb⟩

end Rom
