-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/Fits34OfOpens.lean: two clauses of the makers' test on three lists of rounds
(`fits3`, `fits4`, OnBytes/Maker/OkOfTop.lean) from a condition on the openings of each list.

What is proved. Let every opening of the three lists whose name stands for a tree (the others are
left out, as `Three.opensOf` leaves them out) name a tree of its own chain or of an earlier one,
among the trees that this chain sends, under the one shape `Sh` of that tree, whose number in the
label is the format's; and let a chain open a tree of its own no earlier than in the round that
sends its root. That is `OpensFit` of each list. Then every opened tree stands in the table of
`Three.Whole.of`, was sent no later than it is opened and has the table's shape (`fits3`), and the
number in the label of every opened tree of the table is the one that the test asks for (`fits4`).

How. The table's row at a tree's number over the whole file is written out, by induction along a
chain's rounds. `Three.wholeNo` is one to one on the trees that their chains send: each chain has a
stretch of the table of its own. So the first opening that `Three.shapeAt` finds under a tree's
number is an opening of that tree, and has its one shape.

Main names:
  `fits34_of_opens_pre`, `fits34_of_opens_sent`: `Three.sentBefore` by recursion along the list.
  `fits34_of_opens_row`, `fits34_of_opens_chain_get`, `fits34_of_opens_table_get`: a tree's row, in
    a chain's rows, in the chain's part of the table, in the table.
  `fits34_of_opens_place`, `fits34_of_opens_inj`: every place of the table is the number of one
    tree.
  `fits34_of_opens_Good`, `fits34_of_opens_good`: the premises, said of the list of all openings.
  `fits34_of_opens_shape`: the table's shape of an opened tree.
  `fits34_of_opens_three`, `fits34_of_opens_four`, `fits34_of_opens`: the two clauses.

What is not claimed. `OpensFit` is a premise: it is shown of no lists here. Nothing on the other
clauses of `Three.Whole.fits`. The proofs go by the text of OnBytes/Three/Data.lean: if that turns,
they break. Nothing on soundness.
-/
import OnBytes.Tie.Pv.Keeps.Fits34Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.OkOf.Proved

open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open OnBytes.Tie.Pv.Keeps.OkOf.Rows

/-! ### The trees sent before a round -/

/-- The numbers of trees sent before each round, by recursion. s: sent before the first round. -/
def fits34_of_opens_pre : ℕ → Rounds → List ℕ
  | _, [] => []
  | s, r :: R => s :: fits34_of_opens_pre (s + r.1.items.countP (· == .root)) R

/-- The fold of Three.sentBefore, from any start. -/
theorem fits34_of_opens_fold (R : Rounds) : ∀ (s : ℕ) (acc : Array ℕ),
    (R.foldl (fun (a : ℕ × Array ℕ) r => (a.1 + r.1.items.countP (· == .root), a.2.push a.1))
      (s, acc)).2.toList = acc.toList ++ fits34_of_opens_pre s R := by
  induction R with
  | nil => intro s acc; simp [fits34_of_opens_pre]
  | cons r R ih =>
    intro s acc
    rw [List.foldl_cons, ih]
    simp [fits34_of_opens_pre]

/-- Three.sentBefore is the list by recursion. -/
theorem fits34_of_opens_sent (R : Rounds) : Three.sentBefore R = fits34_of_opens_pre 0 R := by
  unfold Three.sentBefore
  rw [fits34_of_opens_fold]
  simp

/-- The roots of a list with one more round. -/
theorem fits34_of_opens_roots_cons (r : Fmt.Round × List Fmt.Stored) (R : Rounds) :
    Three.rootsIn (r :: R) = r.1.items.countP (· == .root) + Three.rootsIn R := by
  simp [Three.rootsIn]

/-! ### One chain's rows of the table -/

section Chain
variable (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)

/-- The rows of a chain's trees: the round, the place among the round's roots, the shape. s: the
trees sent before the first round. n: the first round's number. -/
def fits34_of_opens_rows (s n : ℕ) (R : Rounds) : List (ℕ × ℕ × Fmt.Shape) :=
  ((List.zipWith (Three.rdOf all t₁ t₂ here base first) R
    (fits34_of_opens_pre s R)).zipIdx n).flatMap
      fun d => d.1.trees.zipIdx.map fun q => (d.2, q.2, q.1)

/-- The rows of a list with one more round. -/
theorem fits34_of_opens_rows_cons (s n : ℕ) (r : Fmt.Round × List Fmt.Stored) (R : Rounds) :
    fits34_of_opens_rows all t₁ t₂ here base first s n (r :: R) =
      ((List.range (r.1.items.countP (· == .root))).map fun k =>
        (n, k, Three.shapeAt all (base + s + k) (Three.bareShape first (s + k)))) ++
      fits34_of_opens_rows all t₁ t₂ here base first (s + r.1.items.countP (· == .root))
        (n + 1) R := by
  unfold fits34_of_opens_rows
  rw [fits34_of_opens_pre, List.zipWith_cons_cons, List.zipIdx_cons, List.flatMap_cons]
  congr 1
  refine List.ext_getElem (by simp [Three.rdOf]) fun i h₁ h₂ => ?_
  simp [Three.rdOf]

/-- A chain has as many rows as roots. -/
theorem fits34_of_opens_rows_length (R : Rounds) : ∀ (s n : ℕ),
    (fits34_of_opens_rows all t₁ t₂ here base first s n R).length = Three.rootsIn R := by
  induction R with
  | nil => intro s n; simp [fits34_of_opens_rows, fits34_of_opens_pre, Three.rootsIn]
  | cons r R ih =>
    intro s n
    rw [fits34_of_opens_rows_cons, List.length_append, List.length_map, List.length_range, ih,
      fits34_of_opens_roots_cons]

/-- The row number j: its shape is that of the tree number s + j, and its round is no later than
any round behind which more than s + j trees are sent. -/
theorem fits34_of_opens_row (R : Rounds) : ∀ (s n j : ℕ), j < Three.rootsIn R →
    ∃ i k, (fits34_of_opens_rows all t₁ t₂ here base first s n R)[j]? =
        some (n + i, k, Three.shapeAt all (base + (s + j)) (Three.bareShape first (s + j))) ∧
      ∀ i₂ r₂, R[i₂]? = some r₂ →
        s + j < (fits34_of_opens_pre s R).getD i₂ 0 + r₂.1.items.countP (· == .root) →
          i ≤ i₂ := by
  induction R with
  | nil => intro s n j h; simp [Three.rootsIn] at h
  | cons r R ih =>
    intro s n j h
    rw [fits34_of_opens_rows_cons]
    rw [fits34_of_opens_roots_cons] at h
    by_cases hj : j < r.1.items.countP (· == .root)
    · refine ⟨0, j, ?_, fun _ _ _ _ => Nat.zero_le _⟩
      rw [List.getElem?_append_left (by simpa using hj)]
      simp [hj, Nat.add_assoc]
    · obtain ⟨i, k, e, m⟩ := ih (s + r.1.items.countP (· == .root)) (n + 1)
        (j - r.1.items.countP (· == .root)) (by omega)
      have e₁ : s + r.1.items.countP (· == .root) + (j - r.1.items.countP (· == .root)) =
          s + j := by
        omega
      rw [e₁] at e m
      refine ⟨i + 1, k, ?_, ?_⟩
      · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hj), List.length_map,
          List.length_range, e, Nat.add_assoc n 1 i, Nat.add_comm 1 i]
      · intro i₂ r₂ h₂ l
        cases i₂ with
        | zero =>
          rw [List.getElem?_cons_zero] at h₂
          cases h₂
          rw [fits34_of_opens_pre, List.getD_cons_zero] at l
          omega
        | succ i₃ =>
          rw [List.getElem?_cons_succ] at h₂
          rw [fits34_of_opens_pre, List.getD_cons_succ] at l
          exact Nat.succ_le_succ (m i₃ r₂ h₂ l)

/-- A chain's part of the table, by the rows. -/
theorem fits34_of_opens_chain (R : Rounds) :
    Three.treesOfChain all here base (Three.rdsFromL all t₁ t₂ here base first R) =
      (fits34_of_opens_rows all t₁ t₂ here base first 0 0 R).zipIdx.map fun x =>
        (⟨here, x.1.1, x.1.2.1, x.1.2.2, (all.filter (·.1 == base + x.2)).map (·.2.2)⟩ :
          Three.Tree) := by
  unfold Three.treesOfChain Three.rdsFromL fits34_of_opens_rows
  rw [fits34_of_opens_sent]

/-- A chain's part of the table has as many trees as the chain has roots. -/
theorem fits34_of_opens_chain_length (R : Rounds) :
    (Three.treesOfChain all here base (Three.rdsFromL all t₁ t₂ here base first R)).length =
      Three.rootsIn R := by
  rw [fits34_of_opens_chain, List.length_map, List.length_zipIdx, fits34_of_opens_rows_length]

/-- The tree number j of a chain's part of the table. -/
theorem fits34_of_opens_chain_get (R : Rounds) (j : ℕ) (h : j < Three.rootsIn R) :
    ∃ i k, (Three.treesOfChain all here base (Three.rdsFromL all t₁ t₂ here base first R))[j]? =
        some ⟨here, i, k, Three.shapeAt all (base + j) (Three.bareShape first j),
          (all.filter (·.1 == base + j)).map (·.2.2)⟩ ∧
      ∀ i₂ r₂, R[i₂]? = some r₂ →
        j < (Three.sentBefore R).getD i₂ 0 + r₂.1.items.countP (· == .root) → i ≤ i₂ := by
  obtain ⟨i, k, e, m⟩ := fits34_of_opens_row all t₁ t₂ here base first R 0 0 j h
  refine ⟨i, k, ?_, ?_⟩
  · rw [fits34_of_opens_chain, List.getElem?_map, List.getElem?_zipIdx, e]
    simp
  · intro i₂ r₂ h₂ l
    rw [fits34_of_opens_sent] at l
    exact m i₂ r₂ h₂ (by omega)

end Chain

/-! ### The whole table -/

section Whole
variable (R₁ R₂ R₃ : Rounds)

/-- The list of a chain. -/
def fits34_of_opens_list : ℕ → Rounds
  | 0 => R₁
  | 1 => R₂
  | _ => R₃

/-- The table, chain by chain. -/
theorem fits34_of_opens_table :
    (Three.Whole.of R₁ R₂ R₃).table =
      Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
          (Three.rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂)
            0 0 0 R₁) ++
        (Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (Three.rootsIn R₁)
          (Three.rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂)
            1 (Three.rootsIn R₁) 0 R₂) ++
        Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2
          (Three.rootsIn R₁ + Three.rootsIn R₂)
          (Three.rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂)
            2 (Three.rootsIn R₁ + Three.rootsIn R₂) (Three.first₃ (Three.rootsIn R₁)) R₃)) :=
  rfl

/-- The table has as many trees as the three chains have roots. -/
theorem fits34_of_opens_table_length :
    (Three.Whole.of R₁ R₂ R₃).table.length =
      Three.rootsIn R₁ + (Three.rootsIn R₂ + Three.rootsIn R₃) := by
  rw [fits34_of_opens_table, List.length_append, List.length_append,
    fits34_of_opens_chain_length, fits34_of_opens_chain_length, fits34_of_opens_chain_length]

/-- The table's row at the number over the whole file of a tree that its chain sends. -/
theorem fits34_of_opens_table_get (y : ℕ × ℕ) (h2 : y.1 ≤ 2) (lt : y.2 < treesIn R₁ R₂ R₃ y.1) :
    ∃ i k, (Three.Whole.of R₁ R₂ R₃).table[
          Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y]? =
        some ⟨y.1, i, k,
          Three.shapeAt (Three.Whole.of R₁ R₂ R₃).opens
            (Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y)
            (Three.bareShape (firstOf (Three.rootsIn R₁) y.1) y.2),
          ((Three.Whole.of R₁ R₂ R₃).opens.filter
            (·.1 == Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y)).map (·.2.2)⟩ ∧
      ∀ i₂ r₂, (fits34_of_opens_list R₁ R₂ R₃ y.1)[i₂]? = some r₂ →
        y.2 < (Three.sentBefore (fits34_of_opens_list R₁ R₂ R₃ y.1)).getD i₂ 0 +
          r₂.1.items.countP (· == .root) → i ≤ i₂ := by
  obtain ⟨c, j⟩ := y
  rw [fits34_of_opens_table]
  generalize (Three.Whole.of R₁ R₂ R₃).opens = all
  have l₁ := fits34_of_opens_chain_length all (Three.rootsIn R₁) (Three.rootsIn R₂) 0 0 0 R₁
  have l₂ := fits34_of_opens_chain_length all (Three.rootsIn R₁) (Three.rootsIn R₂) 1
    (Three.rootsIn R₁) 0 R₂
  match c, h2, lt with
  | 0, _, lt =>
    have lt' : j < Three.rootsIn R₁ := lt
    obtain ⟨i, k, e, m⟩ := fits34_of_opens_chain_get all (Three.rootsIn R₁) (Three.rootsIn R₂)
      0 0 0 R₁ j lt'
    refine ⟨i, k, Eq.trans ?_ e, m⟩
    have w : Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (0, j) = j := Nat.zero_add j
    rw [w, List.getElem?_append_left (by omega)]
  | 1, _, lt =>
    have lt' : j < Three.rootsIn R₂ := lt
    obtain ⟨i, k, e, m⟩ := fits34_of_opens_chain_get all (Three.rootsIn R₁) (Three.rootsIn R₂)
      1 (Three.rootsIn R₁) 0 R₂ j lt'
    refine ⟨i, k, Eq.trans ?_ e, m⟩
    have w : Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (1, j) = Three.rootsIn R₁ + j :=
      rfl
    rw [w, List.getElem?_append_right (by omega), l₁, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
  | 2, _, lt =>
    have lt' : j < Three.rootsIn R₃ := lt
    obtain ⟨i, k, e, m⟩ := fits34_of_opens_chain_get all (Three.rootsIn R₁) (Three.rootsIn R₂)
      2 (Three.rootsIn R₁ + Three.rootsIn R₂) (Three.first₃ (Three.rootsIn R₁)) R₃ j lt'
    refine ⟨i, k, Eq.trans ?_ e, m⟩
    have w : Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (2, j) =
      Three.rootsIn R₁ + Three.rootsIn R₂ + j := rfl
    have u : Three.rootsIn R₁ + Three.rootsIn R₂ + j - Three.rootsIn R₁ - Three.rootsIn R₂ = j := by
      omega
    rw [w, List.getElem?_append_right (by omega), l₁, List.getElem?_append_right (by omega), l₂, u]
  | c + 3, h2, _ =>
    have h2' : c + 3 ≤ 2 := h2
    omega

/-- Every place of the table is the number over the whole file of a tree that its chain sends. -/
theorem fits34_of_opens_place (n : ℕ)
    (h : n < Three.rootsIn R₁ + (Three.rootsIn R₂ + Three.rootsIn R₃)) :
    ∃ y : ℕ × ℕ, y.1 ≤ 2 ∧ y.2 < treesIn R₁ R₂ R₃ y.1 ∧
      Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y = n := by
  by_cases h₁ : n < Three.rootsIn R₁
  · exact ⟨(0, n), Nat.zero_le _, h₁, Nat.zero_add n⟩
  · by_cases h₂ : n < Three.rootsIn R₁ + Three.rootsIn R₂
    · refine ⟨(1, n - Three.rootsIn R₁), Nat.le_succ 1, ?_, ?_⟩
      · show n - Three.rootsIn R₁ < Three.rootsIn R₂
        omega
      · show Three.rootsIn R₁ + (n - Three.rootsIn R₁) = n
        omega
    · refine ⟨(2, n - (Three.rootsIn R₁ + Three.rootsIn R₂)), Nat.le_refl _, ?_, ?_⟩
      · show n - (Three.rootsIn R₁ + Three.rootsIn R₂) < Three.rootsIn R₃
        omega
      · show Three.rootsIn R₁ + Three.rootsIn R₂ + (n - (Three.rootsIn R₁ + Three.rootsIn R₂)) = n
        omega

/-- Two trees that their chains send have two numbers over the whole file. -/
theorem fits34_of_opens_inj (y z : ℕ × ℕ) (hy : y.1 ≤ 2) (hz : z.1 ≤ 2)
    (ly : y.2 < treesIn R₁ R₂ R₃ y.1) (lz : z.2 < treesIn R₁ R₂ R₃ z.1)
    (e : Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y =
      Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) z) : y = z := by
  obtain ⟨c, j⟩ := y
  obtain ⟨d, k⟩ := z
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by
    have hy' : c ≤ 2 := hy
    omega
  have hd : d = 0 ∨ d = 1 ∨ d = 2 := by
    have hz' : d ≤ 2 := hz
    omega
  have w₀ : ∀ n, Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (0, n) = 0 + n :=
    fun _ => rfl
  have w₁ : ∀ n, Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (1, n) =
    Three.rootsIn R₁ + n := fun _ => rfl
  have w₂ : ∀ n, Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (2, n) =
    Three.rootsIn R₁ + Three.rootsIn R₂ + n := fun _ => rfl
  have s₀ : treesIn R₁ R₂ R₃ 0 = Three.rootsIn R₁ := rfl
  have s₁ : treesIn R₁ R₂ R₃ 1 = Three.rootsIn R₂ := rfl
  have s₂ : treesIn R₁ R₂ R₃ 2 = Three.rootsIn R₃ := rfl
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    simp only [w₀, w₁, w₂, s₀, s₁, s₂] at e ly lz <;> rw [Prod.mk.injEq] <;> omega

/-- The number in the label as the table's test has it. -/
theorem fits34_of_opens_label (t₁ t₂ : ℕ) (y : ℕ × ℕ) (hy : y.1 ≤ 2) :
    firstOf t₁ y.1 + y.2 = (match y.1 with
      | 0 => Three.wholeNo t₁ t₂ y
      | 1 => Three.wholeNo t₁ t₂ y - t₁
      | _ => Three.first₃ t₁ + (Three.wholeNo t₁ t₂ y - (t₁ + t₂))) := by
  obtain ⟨c, j⟩ := y
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by
    have hy' : c ≤ 2 := hy
    omega
  rcases hc with rfl | rfl | rfl
  · rfl
  · show 0 + j = t₁ + j - t₁
    omega
  · show Three.first₃ t₁ + j = Three.first₃ t₁ + (t₁ + t₂ + j - (t₁ + t₂))
    omega

/-! ### The openings -/

variable (Sh : ℕ × ℕ → Fmt.Shape)

/-- What the premises say of a member of the list of all openings. -/
def fits34_of_opens_Good (o : ℕ × Fmt.Shape × ℕ × ℕ) : Prop :=
  ∃ (y : ℕ × ℕ) (r : Fmt.Round × List Fmt.Stored),
    o.1 = Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y ∧ o.2.1 = Sh y ∧ o.2.2.1 ≤ 2 ∧
    y.1 ≤ o.2.2.1 ∧ (Sh y).tree = firstOf (Three.rootsIn R₁) y.1 + y.2 ∧
    y.2 < treesIn R₁ R₂ R₃ y.1 ∧ (fits34_of_opens_list R₁ R₂ R₃ o.2.2.1)[o.2.2.2]? = some r ∧
    (y.1 = o.2.2.1 →
      y.2 < (Three.sentBefore (fits34_of_opens_list R₁ R₂ R₃ o.2.2.1)).getD o.2.2.2 0 +
        r.1.items.countP (· == .root))

/-- The openings of one chain. -/
theorem fits34_of_opens_good_chain (c : ℕ) (hc : c ≤ 2)
    (H : OpensFit R₁ R₂ R₃ Sh c (fits34_of_opens_list R₁ R₂ R₃ c)) :
    ∀ o ∈ Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) c (fits34_of_opens_list R₁ R₂ R₃ c),
      fits34_of_opens_Good R₁ R₂ R₃ Sh o := by
  intro o ho
  unfold Three.opensOf at ho
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 ho
  obtain ⟨q, hq, e⟩ := List.mem_filterMap.1 hx
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 e
  have hr' := List.mem_zipIdx_iff_getElem?.1 hr
  obtain ⟨a1, a2, a3, a4, a5⟩ := H r.2 r.1 hr' q hq y hy
  subst ey
  exact ⟨y, r.1, rfl, a2, hc, a1, a3, a4, hr', a5⟩

/-- All openings of the file. -/
theorem fits34_of_opens_good (H₁ : OpensFit R₁ R₂ R₃ Sh 0 R₁) (H₂ : OpensFit R₁ R₂ R₃ Sh 1 R₂)
    (H₃ : OpensFit R₁ R₂ R₃ Sh 2 R₃) :
    ∀ o ∈ (Three.Whole.of R₁ R₂ R₃).opens, fits34_of_opens_Good R₁ R₂ R₃ Sh o := by
  intro o ho
  have ho' : o ∈ Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 0 R₁ ++
      (Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 1 R₂ ++
        Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 2 R₃) := ho
  rcases List.mem_append.1 ho' with h | h
  · exact fits34_of_opens_good_chain R₁ R₂ R₃ Sh 0 (by decide) H₁ o h
  · rcases List.mem_append.1 h with h | h
    · exact fits34_of_opens_good_chain R₁ R₂ R₃ Sh 1 (by decide) H₂ o h
    · exact fits34_of_opens_good_chain R₁ R₂ R₃ Sh 2 (by decide) H₃ o h

/-- The shape in the table of a tree that is opened is the one shape of the tree. -/
theorem fits34_of_opens_shape (all : List (ℕ × Fmt.Shape × ℕ × ℕ))
    (G : ∀ o ∈ all, fits34_of_opens_Good R₁ R₂ R₃ Sh o) (y : ℕ × ℕ) (hy : y.1 ≤ 2)
    (ly : y.2 < treesIn R₁ R₂ R₃ y.1) (x : ℕ × Fmt.Shape × ℕ × ℕ) (hx : x ∈ all)
    (ex : x.1 = Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y) (dflt : Fmt.Shape) :
    Three.shapeAt all (Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y) dflt = Sh y := by
  unfold Three.shapeAt
  cases h : all.find? (·.1 == Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y) with
  | none => exact absurd (by simpa using ex) (List.find?_eq_none.1 h x hx)
  | some z =>
    obtain ⟨y', r, e1, e2, c2, yc, -, lt', -, -⟩ := G z (List.mem_of_find?_eq_some h)
    have hz : z.1 = Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y := by
      simpa using List.find?_some h
    have e : y' = y := fits34_of_opens_inj R₁ R₂ R₃ y' y (le_trans yc c2) hy lt' ly
      (e1.symm.trans hz)
    rw [Option.map_some, Option.getD_some, e2, e]

/-- The third clause. -/
theorem fits34_of_opens_three
    (G : ∀ o ∈ (Three.Whole.of R₁ R₂ R₃).opens, fits34_of_opens_Good R₁ R₂ R₃ Sh o) :
    fits3 R₁ R₂ R₃ = true := by
  unfold fits3
  rw [List.all_eq_true]
  intro o ho
  obtain ⟨y, r, e1, e2, c2, yc, -, lt, hr, own⟩ := G o ho
  obtain ⟨i, k, e, m⟩ := fits34_of_opens_table_get R₁ R₂ R₃ y (le_trans yc c2) lt
  rw [e1, e]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · unfold Three.Whole.notLater
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
    rcases Nat.lt_or_eq_of_le yc with h | h
    · exact Or.inl h
    · rw [h] at m
      exact Or.inr ⟨h, m _ r hr (own h)⟩
  · rw [e2]
    exact fits34_of_opens_shape R₁ R₂ R₃ Sh _ G y (le_trans yc c2) lt o ho e1 _

/-- The clause on the number in an opened tree's label. -/
theorem fits34_of_opens_four
    (G : ∀ o ∈ (Three.Whole.of R₁ R₂ R₃).opens, fits34_of_opens_Good R₁ R₂ R₃ Sh o) :
    fits4 R₁ R₂ R₃ = true := by
  unfold fits4
  rw [List.all_eq_true]
  intro t ht
  have ht' := List.mem_zipIdx_iff_getElem?.1 ht
  obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 ht'
  rw [fits34_of_opens_table_length] at hl
  obtain ⟨y, hy, ly, ey⟩ := fits34_of_opens_place R₁ R₂ R₃ t.2 hl
  obtain ⟨i, k, e, -⟩ := fits34_of_opens_table_get R₁ R₂ R₃ y hy ly
  rw [ey, ht'] at e
  have et := Option.some.inj e
  rw [et]
  simp only [Bool.or_eq_true, beq_iff_eq]
  cases hf : (Three.Whole.of R₁ R₂ R₃).opens.filter (·.1 == t.2) with
  | nil => left; simp
  | cons x l =>
    right
    have hx : x ∈ (Three.Whole.of R₁ R₂ R₃).opens.filter (·.1 == t.2) := by
      rw [hf]; exact List.mem_cons_self
    obtain ⟨hx₁, hx₂⟩ := List.mem_filter.1 hx
    have ex : x.1 = Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) y := by
      rw [ey]; simpa using hx₂
    obtain ⟨y', r, e1, e2, c2, yc, tr, lt', -, -⟩ := G x hx₁
    have e' : y' = y := fits34_of_opens_inj R₁ R₂ R₃ y' y (le_trans yc c2) hy lt' ly
      (e1.symm.trans ex)
    rw [← ey, fits34_of_opens_shape R₁ R₂ R₃ Sh _ G y hy ly x hx₁ ex, ← e', tr, e']
    exact fits34_of_opens_label _ _ y hy

end Whole

/-- **The two clauses of the makers' test on opened trees, from what is asked of the openings of
the three lists.** -/
theorem fits34_of_opens : Rows.row_fits34_of_opens := fun R₁ R₂ R₃ Sh H₁ H₂ H₃ =>
  ⟨fits34_of_opens_three R₁ R₂ R₃ Sh (fits34_of_opens_good R₁ R₂ R₃ Sh H₁ H₂ H₃),
    fits34_of_opens_four R₁ R₂ R₃ Sh (fits34_of_opens_good R₁ R₂ R₃ Sh H₁ H₂ H₃)⟩

end OnBytes.Tie.Pv.Keeps.OkOf.Proved
