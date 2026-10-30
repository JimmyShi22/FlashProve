-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstRel.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): the relation `Rel` along a run. Book-keeping: no probability occurs.

After the step, from the first family S to the second, `stSpec S lam C`, a chain oracle returns only
a state: the chaining value and the last block, hid, of its old answer; the other hash blocks are
answers of an added oracle dr to expansion queries (state, counter). (`Link`, `stSpec`:
Rom/StateFirst.lean.)

`Rel` (Rom/StateFirstColl.lean) says that the lazily sampled tables of the two families and a table
b of all chain answers (a `Book`, Rom/StateFirstMix.lean) are consistent. Under `Rel`, at a query
that was made before, b does not change (`rel_old`); `Rel` is preserved at a new answer if it is
good (`rel_new`; `Link.good`, Rom/StateFirstColl.lean), and at an expansion query at which b has no
answer (`rel_loose`). Other lemmas are on a table after a write, on a `Book` after an entry and on
its size.
-/
import Rom.StateFirstColl
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open Prob

theorem Table.set_ne_oracle {S : OSpec} (T : Table S) {o o' : S.ι} (h : o' ≠ o)
    (q : S.Dom o) (r : S.Rng o) : (T.set o q r) o' = T o' := by
  unfold Table.set
  exact Function.update_of_ne h _ _

theorem Table.set_ne_point {S : OSpec} (T : Table S) (o : S.ι) {q q' : S.Dom o}
    (h : q' ≠ q) (r : S.Rng o) :
    (T.set o q r) o q' = T o q' := by
  unfold Table.set
  rw [Function.update_self]
  exact Function.update_of_ne h _ _

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))

/-- what one entry says about the query (o, q) -/
def entryAt (e : QA S) (o : S.ι) (q : S.Dom o) : Option (S.Rng o) :=
  if h : e.1 = o then (if h ▸ e.2.1 = q then some (h ▸ e.2.2) else none) else none

theorem entryAt_self (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    entryAt (⟨o, q, r⟩ : QA S) o q = some r := by
  unfold entryAt
  rw [dif_pos rfl, if_pos rfl]

theorem entryAt_ne_point (o : S.ι) {q q' : S.Dom o} (h : q' ≠ q) (r : S.Rng o) :
    entryAt (⟨o, q, r⟩ : QA S) o q' = none := by
  unfold entryAt
  rw [dif_pos rfl, if_neg (fun e => h e.symm)]

theorem entryAt_ne_oracle {o o' : S.ι} (h : o' ≠ o) (q : S.Dom o) (r : S.Rng o) (q' : S.Dom o') :
    entryAt (⟨o, q, r⟩ : QA S) o' q' = none := by
  unfold entryAt
  rw [dif_neg (fun e => h e.symm)]

theorem findMade_append (made : List (QA S)) (e : QA S) (o : S.ι) (q : S.Dom o) :
    findMade (made ++ [e]) o q = (findMade made o q).or (entryAt e o q) := by
  unfold findMade
  rw [List.findSome?_append]
  congr 1
  show [e].findSome? (fun e => entryAt e o q) = entryAt e o q
  simp only [List.findSome?_cons, List.findSome?_nil]
  cases entryAt e o q <;> rfl

theorem findBlock_append (made : List (QA S)) (o : S.ι) (q : S.Dom o) (r : S.Rng o)
    (σ : Dg lam × Dg lam) (j : ℕ) :
    findBlock C (made ++ [⟨o, q, r⟩]) σ j = (findBlock C made σ j).or ((C o).own r (σ, j)) := by
  unfold findBlock
  rw [List.findSome?_append]
  congr 1
  show [(⟨o, q, r⟩ : QA S)].findSome? (fun e => (C e.1).own e.2.2 (σ, j)) = (C o).own r (σ, j)
  simp only [List.findSome?_cons, List.findSome?_nil]
  cases (C o).own r (σ, j) <;> rfl

theorem note_plain (b : Book S lam) (o : S.ι) (q : S.Dom o)
    (r : S.Rng o) (h : (C o).isPlain = true) : b.note C o q r = b := by
  unfold Book.note
  rw [if_pos h]

theorem note_old (b : Book S lam) (o : S.ι) (q : S.Dom o)
    (r r' : S.Rng o) (h : findMade b.made o q = some r') : b.note C o q r = b := by
  unfold Book.note
  split
  · rfl
  · rw [h]

theorem note_new (b : Book S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o)
    (hp : (C o).isPlain = false) (h : findMade b.made o q = none) :
    b.note C o q r = { b with made := b.made ++ [⟨o, q, r⟩] } := by
  unfold Book.note
  rw [if_neg (by rw [hp]; simp), h]

theorem own_plain {R : Type} (c : Link lam R) (h : c.isPlain = true)
    (r : R) (p : (Dg lam × Dg lam) × ℕ) : c.own r p = none := by
  cases c with
  | plain => rfl
  | chain K e => cases h

theorem isPlain_of_stateOf {R : Type} (c : Link lam R) {r : R}
    {σ : Dg lam × Dg lam} (h : c.stateOf r = some σ) : c.isPlain = false := by
  cases c with
  | plain => cases h
  | chain K e => rfl

theorem lt_of_blockOf {R : Type} (c : Link lam R) {r : R} {j : ℕ}
    {v : Dg lam} (h : c.blockOf r j = some v) : j < c.nK := by
  cases c with
  | plain => cases h
  | chain K e =>
    by_contra hn
    have : (Link.chain K e).blockOf r j = none := dif_neg hn
    rw [this] at h
    cases h

/-- the table's answers of dr after a new entry -/
theorem drVal_note (b : Book S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o)
    (h : findMade b.made o q = none) (p : (Dg lam × Dg lam) × ℕ) :
    drVal C (b.note C o q r) p = (drVal C b p).or ((C o).own r p) := by
  by_cases hp : (C o).isPlain = true
  · rw [note_plain C b o q r hp, own_plain (C o) hp, Option.or_none]
  · rw [note_new C b o q r (by simpa using hp) h]
    unfold drVal
    show (match b.loose.lookup p with
      | some x => some x
      | none => findBlock C (b.made ++ [(⟨o, q, r⟩ : QA S)]) p.1 p.2) = _
    cases b.loose.lookup p with
    | some x => rfl
    | none => exact findBlock_append C b.made o q r p.1 p.2

theorem drVal_loose (b : Book S lam) (p : (Dg lam × Dg lam) × ℕ)
    (v : Dg lam) (p' : (Dg lam × Dg lam) × ℕ) :
    drVal C { b with loose := (p, v) :: b.loose } p' = if p' = p then some v else drVal C b p' := by
  unfold drVal
  show (match ((p, v) :: b.loose).lookup p' with
    | some x => some x
    | none => findBlock C b.made p'.1 p'.2) = _
  rw [List.lookup_cons]
  by_cases h : p' = p
  · subst h
    simp
  · rw [if_neg h]
    have : (p' == p) = false := by simpa using h
    rw [this]
    rfl

variable {C}

/-- Under `Rel`, entering again the answer of an earlier query does not change b. -/
theorem rel_old {Tp : Table (stSpec S lam C)} {T : Table S} {b : Book S lam} (h : Rel C Tp T b)
    {o : S.ι} {q : S.Dom o} {r : S.Rng o} (hT : T o q = some r) (r' : S.Rng o) :
    b.note C o q r' = b := by
  by_cases hp : (C o).isPlain = true
  · exact note_plain C b o q r' hp
  · exact note_old C b o q r' r ((h.made o q (by simpa using hp)).trans hT)

/-- Under `Rel`, after a new answer of the first family whose state has no entry at dr yet (`good`),
`Rel` holds again: the hash blocks are written on one side, the answer is entered in b on the other.
(The four goals of the proof are the fields `st`, `made`, `dr`, `blk` of `Rel`,
Rom/StateFirstColl.lean, in this order.) -/
theorem rel_new {Tp : Table (stSpec S lam C)} {T : Table S} {b : Book S lam} (h : Rel C Tp T b)
    {o : S.ι} {q : S.Dom o} (hT : T o q = none) (r : S.Rng o) (hg : (C o).good (drVal C b) r) :
    Rel C (after C (C o) (Tp.set (S := stSpec S lam C) (.inl o) q ((C o).toAns r)) r)
      (T.set o q r) (b.note C o q r) := by
  have hfm : findMade b.made o q = none ∨ (C o).isPlain = true := by
    by_cases hp : (C o).isPlain = true
    · exact Or.inr hp
    · exact Or.inl ((h.made o q (by simpa using hp)).trans hT)
  -- the table's answers of dr afterwards
  have hdv : ∀ p, drVal C (b.note C o q r) p = (drVal C b p).or ((C o).own r p) := fun p => by
    rcases hfm with h1 | h1
    · exact drVal_note C b o q r h1 p
    · rw [note_plain C b o q r h1, own_plain (C o) h1, Option.or_none]
  have hown : ∀ p v, (C o).own r p = some v → drVal C b p = none := fun p v hv => by
    unfold Link.own at hv
    split at hv
    · rename_i hs
      exact hg p.1 hs p.2 (lt_of_blockOf (C o) hv)
    · cases hv
  refine ⟨fun o' q' => ?_, fun o' q' hp' => ?_, fun p => ?_, fun o' q' r' hr' σ hs j v hv => ?_⟩
  · rw [after_inl]
    by_cases ho : o' = o
    · subst ho
      by_cases hq : q' = q
      · subst hq
        rw [Table.set_self, Table.set_self]
        rfl
      · rw [Table.set_ne_point T o' hq, Table.set_ne_point (S := stSpec S lam C) Tp (.inl o') hq]
        exact h.st o' q'
    · rw [Table.set_ne_oracle T ho,
        Table.set_ne_oracle (S := stSpec S lam C) Tp
          (show (Sum.inl o' : S.ι ⊕ Unit) ≠ Sum.inl o from fun e => ho (Sum.inl.inj e))]
      exact h.st o' q'
  · by_cases ho : o' = o
    · subst ho
      have h1 : findMade b.made o' q = none := (h.made o' q hp').trans hT
      rw [note_new C b o' q r hp' h1]
      show findMade (b.made ++ [⟨o', q, r⟩]) o' q' = _
      rw [findMade_append]
      by_cases hq : q' = q
      · subst hq
        rw [h1, entryAt_self, Table.set_self]
        rfl
      · rw [entryAt_ne_point o' hq, Option.or_none, Table.set_ne_point T o' hq]
        exact h.made o' q' hp'
    · rw [Table.set_ne_oracle T ho]
      rcases hfm with h1 | h1
      · by_cases hp : (C o).isPlain = true
        · rw [note_plain C b o q r hp]
          exact h.made o' q' hp'
        · rw [note_new C b o q r (by simpa using hp) h1]
          show findMade (b.made ++ [⟨o, q, r⟩]) o' q' = _
          rw [findMade_append, entryAt_ne_oracle ho, Option.or_none]
          exact h.made o' q' hp'
      · rw [note_plain C b o q r h1]
        exact h.made o' q' hp'
  · rw [after_dr, hdv]
    have e1 : (Tp.set (S := stSpec S lam C) (.inl o) q ((C o).toAns r)) (.inr ()) p =
        drVal C b p := by
      rw [Table.set_ne_oracle (S := stSpec S lam C) Tp
          (show (Sum.inr () : S.ι ⊕ Unit) ≠ Sum.inl o from fun e => by cases e)]
      exact h.dr p
    rw [e1]
    cases ho : (C o).own r p with
    | none => rw [Option.or_none]
    | some v => rw [hown p v ho]; rfl
  · rw [hdv]
    by_cases ho : o' = o
    · subst ho
      by_cases hq : q' = q
      · subst hq
        rw [Table.set_self] at hr'
        have e0 : r = r' := Option.some.inj hr'
        subst e0
        have e : (C o').own r (σ, j) = some v := by
          unfold Link.own
          rw [if_pos hs]
          exact hv
        rw [hown _ v e, e]
        rfl
      · rw [Table.set_ne_point T o' hq] at hr'
        rw [h.blk o' q' r' hr' σ hs j v hv]
        rfl
    · rw [Table.set_ne_oracle T ho] at hr'
      rw [h.blk o' q' r' hr' σ hs j v hv]
      rfl

/-- Under `Rel`, after an expansion query at which b has no answer, `Rel` holds again. -/
theorem rel_loose {Tp : Table (stSpec S lam C)} {T : Table S} {b : Book S lam} (h : Rel C Tp T b)
    {p : (Dg lam × Dg lam) × ℕ} (hp : drVal C b p = none) (v : Dg lam) :
    Rel C (Tp.set (S := stSpec S lam C) (.inr ()) p v) T { b with loose := (p, v) :: b.loose } := by
  refine ⟨fun o q => ?_, h.made, fun p' => ?_, fun o q r hr σ hs j v' hv => ?_⟩
  · rw [set_dr_inl]
    exact h.st o q
  · rw [drVal_loose]
    split_ifs with e
    · subst e
      exact set_dr_self C Tp _ v
    · rw [set_dr_ne C Tp _ _ v e]
      exact h.dr p'
  · rw [drVal_loose]
    have h1 := h.blk o q r hr σ hs j v' hv
    rw [if_neg (fun e => by rw [e, hp] at h1; cases h1)]
    exact h1

theorem mem_of_lookup {κ ν : Type} [BEq κ] [LawfulBEq κ] {a : κ} {v : ν} :
    ∀ (l : List (κ × ν)), l.lookup a = some v → (a, v) ∈ l
  | [], h => by cases h
  | (k, w) :: l, h => by
    rw [List.lookup_cons] at h
    cases e : (a == k) with
    | true =>
      rw [e] at h
      have e' : a = k := eq_of_beq e
      subst e'
      cases h
      exact List.mem_cons_self
    | false =>
      rw [e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l h)

variable (C)

/-- the states at which a `Book` answers some expansion query are at most as many as its entries -/
theorem cnt_drVal_le (b : Book S lam) :
    Prob.cnt (fun σ : Dg lam × Dg lam => ∃ j, drVal C b (σ, j) ≠ none) ≤
      b.made.length + b.loose.length := by
  classical
  refine cnt_le_of_forall_finset fun Y hY => ?_
  have hsub : Y ⊆
      ((b.made.filterMap fun e => (C e.1).stateOf e.2.2) ++
        b.loose.map fun x => x.1.1).toFinset := fun σ hσ => by
    obtain ⟨j, hj⟩ := hY σ hσ
    rw [List.mem_toFinset, List.mem_append]
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
  refine le_trans (Finset.card_le_card hsub) (le_trans (List.toFinset_card_le _) ?_)
  rw [List.length_append, List.length_map]
  exact Nat.add_le_add_right (List.length_filterMap_le _ _) _

theorem size_note (b : Book S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    (b.note C o q r).made.length + (b.note C o q r).loose.length ≤
      b.made.length + b.loose.length + 1 := by
  unfold Book.note
  split
  · omega
  · split
    · omega
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega

end Rom
