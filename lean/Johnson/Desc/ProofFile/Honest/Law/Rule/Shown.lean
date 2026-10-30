-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Shown.lean: what rounds as played show (Honest/Side.lean:
`shownIn`, `shownOf`), written once more as one function, `shownBy`. Its arguments are the rounds'
own tables and a function that gives, for each tree of the chain by its number, the positions that
are read of it. The two functions of Honest/Side.lean are this one (`shownOf_by`, `shownIn_by`). No
coin, no part and no run of a protocol occurs here.

  1  `zipIdx_range`, `zipIdx_shift`, `getD_range`   three lemmas on lists
  2  `colsOfT`, `Played.shownBy`, `shownBy`, `shownBy_append`, `shownBy_length`   the function; over
     two consecutive lists
  3  `shownOf_cons`, `shownOf_by`   `shownOf` at the positions that `asksFrom`
     (Honest/Law/Rule/Session.lean) lists is `shownBy`
  4  `colsBy`, `shownIn_by`   `shownIn` is `shownBy`, where the reads show of each tree of these
     rounds its table's columns

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-! ## 1 Lists -/

/-- A list with its entries' numbers, compared with the numbers alone. -/
theorem zipIdx_range {α β : Type} (f : Option α → Nat → β) : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).map (fun y => f (some y.1) y.2) =
      (List.range l.length).map fun i => f l[i]? (k + i)
  | [], _ => rfl
  | a :: l, k => by
    have ih := zipIdx_range f l (k + 1)
    rw [List.zipIdx_cons, List.map_cons, ih, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    refine congrArg₂ List.cons rfl (List.map_congr_left fun i _ => ?_)
    show f l[i]? (k + 1 + i) = f (a :: l)[i + 1]? (k + (i + 1))
    rw [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 i]

/-- The numbers from k + 1 on are those from k on, each raised by 1. -/
theorem zipIdx_shift {α : Type} : ∀ (l : List α) (k : Nat),
    l.zipIdx (k + 1) = (l.zipIdx k).map fun y => (y.1, y.2 + 1)
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.zipIdx_cons, List.map_cons, zipIdx_shift l (k + 1)]

theorem getD_range {β : Type} (g : Nat → List β) {r i : Nat} (h : i < r) :
    (((List.range r).map g)[i]?).getD [] = g i := by
  simp [h]

/-! ## 2 The function -/

/-- A table's columns at given positions; nothing where no table is available. -/
def colsOfT : Option Table → List Nat → List (Nat × List UInt64)
  | some T, xs => xs.map fun x => (x, T.col x)
  | none, _ => []

/-- What one round shows. `tree`: the positions read of a tree, by its number in the chain. `n`: the
number of the round's first tree. -/
def Played.shownBy (p : Played) (tree : Nat → List Nat) (n : Nat) : Shown :=
  ⟨p.vals, (List.range p.tables.length).map fun i => colsOfT (p.tables[i]?).join (tree (n + i))⟩

/-- **What rounds as played show**, each with the chain's number and its challenge, as
`Before.rounds` lists rounds. -/
def shownBy (ch : Nat) (tree : Nat → List Nat) :
    List Played → Nat → List (Nat × Shown × Fmt.Drawn)
  | [], _ => []
  | p :: ps, n => (ch, p.shownBy tree n, p.drawn) :: shownBy ch tree ps (n + p.tables.length)

theorem shownBy_append (ch : Nat) (tree : Nat → List Nat) (l₂ : List Played) :
    ∀ (l₁ : List Played) (n : Nat), shownBy ch tree (l₁ ++ l₂) n =
      shownBy ch tree l₁ n ++ shownBy ch tree l₂ (n + (l₁.map (·.tables.length)).sum)
  | [], n => by simp [shownBy]
  | p :: l₁, n => by
    have ih := shownBy_append ch tree l₂ l₁ (n + p.tables.length)
    simp only [List.cons_append, shownBy, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem shownBy_length (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    (shownBy ch tree l n).length = l.length
  | [], _ => rfl
  | p :: l, n => congrArg (· + 1) (shownBy_length ch tree l (n + p.tables.length))

/-! ## 3 A part played alone -/

theorem shownOf_cons (p : Played) (ps : List Played) (a : List (List Nat))
    (as : List (List (List Nat))) :
    shownOf (p :: ps) (a :: as) =
      ⟨p.vals, p.tables.zipIdx.map fun y => colsOfT y.1 ((a[y.2]?).getD [])⟩ :: shownOf ps as := by
  unfold shownOf
  rw [List.zipIdx_cons, List.map_cons, zipIdx_shift, List.map_map]
  refine congrArg₂ List.cons ?_ (List.map_congr_left fun x _ => ?_)
  · refine congrArg (Shown.mk p.vals) (List.map_congr_left fun y _ => ?_)
    obtain ⟨t, i⟩ := y
    cases t <;> rfl
  · obtain ⟨q, i⟩ := x
    rfl

/-- **`shownOf` at the positions that `asksFrom` lists is `shownBy`.** -/
theorem shownOf_by (ch : Nat) (tree : Nat → List Nat) : ∀ (ps : List Played) (n : Nat),
    (shownBy ch tree ps n).map (·.2.1) =
      shownOf ps (asksFrom tree (ps.map (·.tables.length)) n)
  | [], _ => rfl
  | p :: ps, n => by
    have ih := shownOf_by ch tree ps (n + p.tables.length)
    show p.shownBy tree n :: (shownBy ch tree ps (n + p.tables.length)).map (·.2.1) =
      shownOf (p :: ps) (((List.range p.tables.length).map fun i => tree (n + i)) ::
        asksFrom tree (ps.map (·.tables.length)) (n + p.tables.length))
    rw [shownOf_cons, ih]
    refine congrArg₂ List.cons ?_ rfl
    unfold Played.shownBy
    refine congrArg (Shown.mk p.vals) ?_
    have h := zipIdx_range (fun (t : Option (Option Table)) (i : Nat) =>
      colsOfT t.join ((((List.range p.tables.length).map fun i => tree (n + i))[i]?).getD []))
      p.tables 0
    refine Eq.trans (List.map_congr_left fun i hi => ?_) h.symm
    show colsOfT (p.tables[i]?).join (tree (n + i)) = colsOfT (p.tables[i]?).join
      ((((List.range p.tables.length).map fun i => tree (n + i))[0 + i]?).getD [])
    rw [Nat.zero_add, getD_range (fun i => tree (n + i)) (List.mem_range.1 hi)]

/-! ## 4 A chain's rounds in a run -/

/-- The columns that reads show of the tree number j of the chain number ch. -/
def colsBy (ch : Nat) (qs : List Read) (j : Nat) : List (Nat × List UInt64) :=
  (qs.filter fun q => q.src == some (ch, j)).filterMap fun q => q.words.map fun w => (q.pos, w)

/-- **`shownIn` is `shownBy`**, where the reads show of each tree of these rounds its table's
columns at the positions that `tree` lists; and nothing of a tree whose table is not available. The
left side is the body of `shownIn` written out, from any first number `n`, with the chain's number
and the round's challenge beside what is shown; `shown_is` (Honest/Law/Rule/Reads.lean) states it
with `shownIn` by name. -/
theorem shownIn_by (ch : Nat) (tree : Nat → List Nat) (qs : List Read) :
    ∀ (l : List Played) (n : Nat),
    (∀ (l₁ : List Played) (p : Played) (l₂ : List Played), l = l₁ ++ p :: l₂ →
      ∀ i, i < p.tables.length →
        colsBy ch qs (n + (l₁.map (·.tables.length)).sum + i) =
          colsOfT (p.tables[i]?).join (tree (n + (l₁.map (·.tables.length)).sum + i))) →
    ((numbered l n).map fun x => (ch, (⟨x.1.vals, (List.range x.1.tables.length).map fun i =>
        colsBy ch qs (x.2 + i)⟩ : Shown), x.1.drawn)) = shownBy ch tree l n
  | [], _, _ => rfl
  | p :: l, n, h => by
    have ih := shownIn_by ch tree qs l (n + p.tables.length) fun l₁ q l₂ hl i hi => by
      have := h (p :: l₁) q l₂ (congrArg (List.cons p) hl) i hi
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using this
    show (ch, (⟨p.vals, (List.range p.tables.length).map fun i => colsBy ch qs (n + i)⟩ : Shown),
        p.drawn) :: ((numbered l (n + p.tables.length)).map fun x =>
          (ch, (⟨x.1.vals, (List.range x.1.tables.length).map fun i =>
            colsBy ch qs (x.2 + i)⟩ : Shown), x.1.drawn)) =
      (ch, p.shownBy tree n, p.drawn) :: shownBy ch tree l (n + p.tables.length)
    rw [ih]
    refine congrArg₂ List.cons ?_ rfl
    unfold Played.shownBy
    refine congrArg (fun c => (ch, (⟨p.vals, c⟩ : Shown), p.drawn)) ?_
    refine List.map_congr_left fun i hi => ?_
    have := h [] p l rfl i (List.mem_range.1 hi)
    simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using this

end ProofFile.Honest

#print axioms ProofFile.Honest.zipIdx_range
#print axioms ProofFile.Honest.zipIdx_shift
#print axioms ProofFile.Honest.getD_range
#print axioms ProofFile.Honest.shownBy_append
#print axioms ProofFile.Honest.shownBy_length
#print axioms ProofFile.Honest.shownOf_cons
#print axioms ProofFile.Honest.shownOf_by
#print axioms ProofFile.Honest.shownIn_by
