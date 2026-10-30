-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Faith.lean: pieces for proving that a read's words, looked up
in what has been produced (Honest/Law/Rule/Session.lean: `Before.wordsAt`, `colsOff`), are the words
that `fillCols` (Honest/Frame.lean) fills in, where what has been produced is what rounds as played
show (Honest/Law/Rule/Shown.lean: `shownBy`) and the stored columns are those of `storedShown`.
No lemma of this file states that whole. `colsOff_fill` takes "each read's words are found in what
has been produced" as its hypothesis; `cols_at`, `find_col`, `find_stored`, `filter_same` and
`filter_other` are pieces toward that hypothesis. They are joined in `treeCols_at` and `faith_one`
(Honest/Law/Rule/Words.lean). No coin, no part and no run of a protocol occurs here.

  1  `allTabs`, `cols_at`, `tables_tabs`   the trees of rounds as played, by their numbers; the
     columns that `shownBy` lists of tree number i
  2  `filter_same`, `filter_other`   the rounds of `shownBy` carry their chain's number
  3  `find_col`, `find_stored`   a position that is listed is found, with its table's column; the
     same for a stored column
  4  `colsOff_fill`   where each read's words are found in what has been produced, `colsOff` returns
     the columns of `fillCols`
  5  `roundsOff_by`, `seen_by`   the rounds as a view shows them

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Shown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place OpenedColumn)

/-! ## 1 The trees of rounds as played -/

/-- The tables of rounds as played, in the order of sending; `none` where no prover's side sent one.
-/
def allTabs (l : List Played) : List (Option Table) := l.flatMap (·.tables)

/-- **The columns that `shownBy` lists of tree number i of these rounds.** -/
theorem cols_at (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (n i : Nat),
    ((shownBy ch tree l n).flatMap (·.2.1.cols))[i]? =
      ((allTabs l)[i]?).map fun T => colsOfT T (tree (n + i))
  | [], _, _ => rfl
  | p :: l, n, i => by
    have ih := cols_at ch tree l (n + p.tables.length)
    have hlen : ((List.range p.tables.length).map fun i =>
        colsOfT (p.tables[i]?).join (tree (n + i))).length = p.tables.length := by simp
    show (((List.range p.tables.length).map fun i =>
        colsOfT (p.tables[i]?).join (tree (n + i))) ++
      (shownBy ch tree l (n + p.tables.length)).flatMap (·.2.1.cols))[i]? =
        ((p.tables ++ allTabs l)[i]?).map fun T => colsOfT T (tree (n + i))
    by_cases hi : i < p.tables.length
    · rw [List.getElem?_append_left (by rw [hlen]; exact hi), List.getElem?_append_left hi,
        List.getElem?_map, List.getElem?_range hi]
      cases ht : p.tables[i]? with
      | none =>
        have := List.getElem?_eq_none_iff.1 ht
        omega
      | some T =>
        show some (colsOfT (p.tables[i]?).join (tree (n + i))) = some (colsOfT T (tree (n + i)))
        rw [ht]
        rfl
    · have hi' : p.tables.length ≤ i := Nat.le_of_not_lt hi
      rw [List.getElem?_append_right (by rw [hlen]; exact hi'), List.getElem?_append_right hi',
        hlen, ih (i - p.tables.length)]
      have e : n + p.tables.length + (i - p.tables.length) = n + i := by omega
      rw [e]

/-- `tablesOf`, without the senders' places. -/
theorem tables_tabs (l : List Played) (j : Nat) :
    (((tablesOf l)[j]?).bind id).map (·.2) = ((allTabs l)[j]?).join := by
  have e : (tablesOf l).map (fun t => t.map (·.2)) = allTabs l := by
    unfold tablesOf allTabs
    rw [List.map_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    rw [List.map_map]
    refine Eq.trans (List.map_congr_left fun t _ => ?_) (List.map_id _)
    cases t <;> rfl
  rw [← e, List.getElem?_map]
  cases (tablesOf l)[j]? with
  | none => rfl
  | some t => cases t <;> rfl

/-! ## 2 The chain's number -/

theorem filter_same (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    ((shownBy ch tree l n).filter fun r => r.1 == ch) = shownBy ch tree l n
  | [], _ => rfl
  | p :: l, n => by
    show ((ch, p.shownBy tree n, p.drawn) :: shownBy ch tree l (n + p.tables.length)).filter
      (fun r => r.1 == ch) = _
    rw [List.filter_cons_of_pos (by simp), filter_same ch tree l (n + p.tables.length)]
    rfl

theorem filter_other {ch c : Nat} (h : ch ≠ c) (tree : Nat → List Nat) :
    ∀ (l : List Played) (n : Nat), ((shownBy ch tree l n).filter fun r => r.1 == c) = []
  | [], _ => rfl
  | p :: l, n => by
    show ((ch, p.shownBy tree n, p.drawn) :: shownBy ch tree l (n + p.tables.length)).filter
      (fun r => r.1 == c) = _
    rw [List.filter_cons_of_neg (by simpa using h)]
    exact filter_other h tree l (n + p.tables.length)

/-! ## 3 What is listed is found -/

theorem find_col (T : Table) (x : Nat) : ∀ xs : List Nat, x ∈ xs →
    ((colsOfT (some T) xs).find? fun c => c.1 == x).map (·.2) = some (T.col x)
  | [], h => by cases h
  | y :: xs, h => by
    show (((y, T.col y) :: colsOfT (some T) xs).find? fun c => c.1 == x).map (·.2) = _
    by_cases hy : y = x
    · subst hy
      rw [List.find?_cons_of_pos (by simp)]
      rfl
    · rw [List.find?_cons_of_neg (by simpa using hy)]
      refine find_col T x xs ?_
      rcases List.mem_cons.1 h with e | e
      · exact absurd e.symm hy
      · exact e

theorem find_stored (stored : Nat → Nat → Option (List UInt64)) (i x : Nat) (w : List UInt64)
    (hw : stored i x = some w) : ∀ asked : List (Nat × Nat), (i, x) ∈ asked →
    ((storedShown stored asked).find? fun c => c.1 == i && c.2.1 == x).map (·.2.2) = some w
  | [], h => by cases h
  | q :: asked, h => by
    by_cases hq : q = (i, x)
    · subst hq
      have e : storedShown stored ((i, x) :: asked) = (i, x, w) :: storedShown stored asked := by
        unfold storedShown
        rw [List.filterMap_cons]
        simp only [hw, Option.map_some]
      rw [e, List.find?_cons_of_pos (by simp)]
      rfl
    · have hm : (i, x) ∈ asked := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm hq
        · exact e
      have ih := find_stored stored i x w hw asked hm
      cases hs : stored q.1 q.2 with
      | none =>
        have e : storedShown stored (q :: asked) = storedShown stored asked := by
          unfold storedShown
          rw [List.filterMap_cons]
          simp only [hs, Option.map_none]
        rw [e]
        exact ih
      | some u =>
        have e : storedShown stored (q :: asked) = (q.1, q.2, u) :: storedShown stored asked := by
          unfold storedShown
          rw [List.filterMap_cons]
          simp only [hs, Option.map_some]
        have hne : ¬ ((q.1 == i && q.2 == x) = true) := by
          intro hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact hq (Prod.ext hb.1 hb.2)
        rw [e, List.find?_cons_of_neg
          (p := fun c : Nat × Nat × List UInt64 => c.1 == i && c.2.1 == x) hne]
        exact ih

/-! ## 4 The columns -/

/-- **Where each read's words are found in what has been produced, `colsOff` returns the columns of
`fillCols`.** -/
theorem colsOff_fill (f : Before) : ∀ (qs : List Read) (cols : List OpenedColumn),
    fillCols qs [] = .ok cols → (∀ q ∈ qs, ∀ w, q.words = some w → f.wordsAt q.bare = some w) →
    colsOff f (qs.map Read.bare) = some cols
  | [], cols, h, _ => by
    simp only [fillCols] at h
    cases h
    rfl
  | q :: qs, cols, h, hf => by
    cases hw : q.words with
    | none => simp [fillCols, hw] at h
    | some w =>
      simp only [fillCols, hw] at h
      split at h
      · cases h
      cases hrec : fillCols qs ([] : List OpenedColumn).tail with
      | error e =>
        rw [hrec] at h
        cases h
      | ok l =>
        rw [hrec] at h
        cases h
        have ih := colsOff_fill f qs l hrec fun q' hq' => hf q' (List.mem_cons_of_mem _ hq')
        show ((f.wordsAt q.bare).bind fun w =>
          (colsOff f (qs.map Read.bare)).map fun l => (q.bare.key, q.bare.pos, w) :: l) = _
        rw [hf q (List.mem_cons.2 (Or.inl rfl)) w hw, ih]
        rfl

/-! ## 5 The rounds -/

theorem roundsOff_by (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    roundsOff (shownBy ch tree l n) = roundsOf l
  | [], _ => rfl
  | p :: l, n =>
    congrArg ((⟨p.vals, p.drawn⟩ : Fmt.RoundView) :: ·) (roundsOff_by ch tree l (n + p.tables.length))

/-- What a part is given of rounds that are listed in this way. -/
theorem seen_by (l : List (Nat × Shown × Fmt.Drawn)) (st : List (Nat × Nat × List UInt64)) :
    (⟨l, st⟩ : Before).seen = roundsOff l := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.cols_at
#print axioms ProofFile.Honest.tables_tabs
#print axioms ProofFile.Honest.filter_same
#print axioms ProofFile.Honest.filter_other
#print axioms ProofFile.Honest.find_col
#print axioms ProofFile.Honest.find_stored
#print axioms ProofFile.Honest.colsOff_fill
#print axioms ProofFile.Honest.roundsOff_by
#print axioms ProofFile.Honest.seen_by
