-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RowsPush.lean: THE TABLE's TESTS ON THE OPEN ROWS' LISTS AND ON THE
GROUPS' MEMBERS (`rowsHeld`, `membersHeld`, Johnson/Desc/First/Borders.lean), BEHIND A BLOCK THAT
OPENS THE CLASS «equation» OF A SEGMENT AND PUSHES ONE PLAIN ROW AT THE END OF THAT SEGMENT's
GROUP's LIST. Theorems over the table's own definitions; no block is named.

What is said.
  `mem_rowSegs`: a segment is among those of which a class of rows is open if and only if some class
    of it is open. `rowsDue_snoc`: what one more open item adds to the count. `rowsHeld_push`: **if
    the test on the rows holds in front at the open set O, the groups behind are those in front with
    a plain row pushed on the group of segment m, that group is no other open segment's, a class of
    m is open already, and the plan lays the class «equation» of m at the list's end, one row: the
    test holds behind at O with that class opened.** `membersHeld_push`: the like for the members,
    where the book's places are as they were. `stepOpen_row`: the table's step at a row that closes
    items which are no classes of rows and opens one class that is not open: the open classes are
    those in front and the new one, behind them; `stepOpen_pins`: the open pins are as they were.

Limits. Rules over letters. The premises on the plan's numbers (which group; where the class lies)
are tests on public data, shown here of no numbers. Nothing on soundness.

-/
import Johnson.Desc.First.PromiseRides
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Item RowClass BlockRow Numbers stepOpen rowSegs rowsDue
  rowsHeld membersHeld sameMembers)

/-- A segment is among those of which a class of rows is open iff some class of it is open. -/
theorem mem_rowSegs (O : List Item) (m : Nat) : m ∈ rowSegs O ↔ ∃ c, Item.row m c ∈ O := by
  unfold rowSegs
  rw [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, e⟩
    cases i with
    | row m' c =>
      obtain rfl : m' = m := Option.some.inj e
      exact ⟨c, hi⟩
    | _ => exact nomatch e
  · rintro ⟨c, hc⟩
    exact ⟨_, hc, rfl⟩

variable (N : Numbers)

/-- What one more open class adds to the count. -/
theorem rowsDue_snoc (O : List Item) (m m' : Nat) (c : RowClass) :
    rowsDue N (O ++ [.row m c]) m' =
      if (m == m' && c.inList) = true then rowsDue N O m' + (N.rowsAt m' c).2
      else rowsDue N O m' := by
  unfold rowsDue
  rw [List.foldl_append]
  rfl

/-- The test on one open item, at segment m and its group G. -/
def itemOk (m : Nat) (G : Group) : Item → Bool
  | .row m' c =>
    !(m' == m && c.inList) ||
      (List.range (N.rowsAt m c).2).all fun j =>
        (G.rows[(N.rowsAt m c).1 + j]?).any fun r => r.kind == c.kind
  | _ => true

theorem itemOk_row (m : Nat) (G : Group) (m' : Nat) (c : RowClass) :
    itemOk N m G (.row m' c) = (!(m' == m && c.inList) ||
      (List.range (N.rowsAt m c).2).all fun j =>
        (G.rows[(N.rowsAt m c).1 + j]?).any fun r => r.kind == c.kind) := rfl

/-- The test on one segment. -/
def segOk (O : List Item) (s : S) (m : Nat) : Bool :=
  match s.st.groups[N.groupAt m]? with
  | none => rowsDue N O m == 0
  | some G => !G.inRun && G.rows.size == rowsDue N O m && O.all (itemOk N m G)

theorem rowsHeld_eq (O : List Item) (s : S) : rowsHeld N O s = (rowSegs O).all (segOk N O s) := by
  unfold rowsHeld segOk
  congr 1

/-- A row more at the list's end leaves the test on an open item. -/
theorem itemOk_push (m : Nat) (G : Group) (row : OnBytes.Row) (i : Item)
    (h : itemOk N m G i = true) : itemOk N m { G with rows := G.rows.push row } i = true := by
  cases i with
  | row m' c =>
    rw [itemOk_row] at h ⊢
    rcases Bool.or_eq_true_iff.1 h with h1 | h1
    · rw [h1]
      rfl
    · refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      rw [List.all_eq_true] at h1 ⊢
      intro j hj
      have h2 := h1 j hj
      cases hx : G.rows[(N.rowsAt m c).1 + j]? with
      | none =>
        rw [hx] at h2
        exact nomatch h2
      | some r =>
        rw [hx] at h2
        have hlt : (N.rowsAt m c).1 + j < G.rows.size := (Array.getElem?_eq_some_iff.1 hx).1
        have e : (G.rows.push row)[(N.rowsAt m c).1 + j]? = some r := by
          rw [Array.getElem?_push_lt hlt, ← hx, Array.getElem?_eq_getElem hlt]
        show ((G.rows.push row)[(N.rowsAt m c).1 + j]?).any _ = true
        rw [e]
        exact h2
  | _ => rfl

/-- **THE TEST ON THE OPEN ROWS, BEHIND A PUSH OF THE EQUATION's ROW.** -/
theorem rowsHeld_push (O : List Item) (m g : Nat) (G : Group) (row : OnBytes.Row) (s s' : S)
    (hg : N.groupAt m = g) (hG : s.st.groups[g]? = some G)
    (hgr : s'.st.groups = s.st.groups.modify g fun G => { G with rows := G.rows.push row })
    (hinj : ∀ m' ∈ rowSegs O, m' ≠ m → N.groupAt m' ≠ g) (hm : m ∈ rowSegs O)
    (hat : N.rowsAt m .equation = (G.rows.size, 1)) (hk : row.kind = .plain)
    (h : rowsHeld N O s = true) : rowsHeld N (O ++ [.row m .equation]) s' = true := by
  rw [rowsHeld_eq, List.all_eq_true] at h ⊢
  intro m' hm'
  have hseg : m' ∈ rowSegs O := by
    obtain ⟨c, hc⟩ := (mem_rowSegs _ _).1 hm'
    rcases List.mem_append.1 hc with hc | hc
    · exact (mem_rowSegs _ _).2 ⟨c, hc⟩
    · obtain ⟨rfl, _⟩ := Item.row.inj (List.mem_singleton.1 hc)
      exact hm
  have h0 := h m' hseg
  unfold segOk at h0 ⊢
  by_cases e : m' = m
  · subst e
    have eg : s'.st.groups[N.groupAt m']? = some { G with rows := G.rows.push row } := by
      rw [hgr, hg, Array.getElem?_modify, if_pos rfl, hG]
      rfl
    rw [hg, hG] at h0
    rw [eg]
    simp only [] at h0 ⊢
    obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 h0
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
    have h2' : G.rows.size = rowsDue N O m' := by simpa using h2
    have d : rowsDue N (O ++ [.row m' .equation]) m' = rowsDue N O m' + 1 := by
      rw [rowsDue_snoc, hat]
      simp [RowClass.inList]
    have e2 : ((G.rows.push row).size == rowsDue N (O ++ [.row m' .equation]) m') = true := by
      rw [d, Array.size_push, h2']
      simp
    have e3 : (O ++ [Item.row m' .equation]).all
        (itemOk N m' { G with rows := G.rows.push row }) = true := by
      rw [List.all_append, Bool.and_eq_true_iff]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true] at h3 ⊢
        exact fun i hi => itemOk_push N m' G row i (h3 i hi)
      · have e4 : (G.rows.push row)[G.rows.size + 0]? = some row := by simp
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [itemOk_row, hat]
        refine Bool.or_eq_true_iff.2 (Or.inr ?_)
        show (List.range 1).all _ = true
        rw [List.all_eq_true]
        intro j hj
        obtain rfl : j = 0 := by
          have := List.mem_range.1 hj
          omega
        show ((G.rows.push row)[G.rows.size + 0]?).any _ = true
        rw [e4]
        show (row.kind == RowClass.kind .equation) = true
        rw [hk]
        rfl
    rw [h1, e2, e3]
    rfl
  · have eg : s'.st.groups[N.groupAt m']? = s.st.groups[N.groupAt m']? := by
      rw [hgr, Array.getElem?_modify, if_neg (fun x => hinj m' hseg e x.symm)]
    have d : rowsDue N (O ++ [.row m .equation]) m' = rowsDue N O m' := by
      rw [rowsDue_snoc]
      have : (m == m') = false := by simpa using fun x : m = m' => e x.symm
      simp [this]
    rw [eg, d]
    cases hx : s.st.groups[N.groupAt m']? with
    | none =>
      rw [hx] at h0
      exact h0
    | some G' =>
      rw [hx] at h0
      simp only [] at h0 ⊢
      obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 h0
      rw [h12, List.all_append, h3]
      have : (m == m') = false := by simpa using fun x : m = m' => e x.symm
      simp [itemOk, this]

/-- The test on one segment's members. -/
def memOk (O : List Item) (s : S) (m : Nat) : Bool :=
  match s.st.groups[N.groupAt m]? with
  | none => true
  | some G =>
    G.members.toList.all (fun o => (s.book.place[o]?).isSome) &&
      sameMembers (G.members.toList.filterMap fun o => s.book.place[o]?)
        ((List.range 3).flatMap fun t => if O.contains (.pin m t) then N.sent m t else [])

theorem membersHeld_eq (O : List Item) (s : S) :
    membersHeld N O s = (rowSegs O).all (memOk N O s) := by
  unfold membersHeld memOk
  congr 1

/-- **THE TEST ON THE MEMBERS, BEHIND A PUSH OF THE EQUATION's ROW.** -/
theorem membersHeld_push (O : List Item) (m g : Nat) (row : OnBytes.Row) (s s' : S)
    (hgr : s'.st.groups = s.st.groups.modify g fun G => { G with rows := G.rows.push row })
    (hb : s'.book.place = s.book.place) (hm : m ∈ rowSegs O)
    (h : membersHeld N O s = true) : membersHeld N (O ++ [.row m .equation]) s' = true := by
  rw [membersHeld_eq, List.all_eq_true] at h ⊢
  intro m' hm'
  have hseg : m' ∈ rowSegs O := by
    obtain ⟨c, hc⟩ := (mem_rowSegs _ _).1 hm'
    rcases List.mem_append.1 hc with hc | hc
    · exact (mem_rowSegs _ _).2 ⟨c, hc⟩
    · obtain ⟨rfl, _⟩ := Item.row.inj (List.mem_singleton.1 hc)
      exact hm
  have h0 := h m' hseg
  have hc : ∀ t, (O ++ [Item.row m .equation]).contains (.pin m' t) = O.contains (.pin m' t) := by
    intro t
    simp
  unfold memOk at h0 ⊢
  rw [hgr, Array.getElem?_modify, hb]
  simp only [hc]
  cases hx : s.st.groups[N.groupAt m']? with
  | none => by_cases e : g = N.groupAt m' <;> simp [e]
  | some G' =>
    rw [hx] at h0
    by_cases e : g = N.groupAt m'
    · simp only [e, if_true, Option.map_some]
      exact h0
    · simp only [e, if_false]
      exact h0

/-- The table's step at a row that closes no class of rows and opens one class that is not open. -/
theorem stepOpen_row (O : List Item) (r : BlockRow) (i₀ : Item)
    (hi : ∀ i ∈ r.ins, i.isRow = false) (ho : r.outs = [i₀]) (hn : i₀ ∉ O) :
    (stepOpen O r).filter Item.isRow = (O ++ [i₀]).filter Item.isRow := by
  unfold stepOpen
  simp only []
  rw [List.filter_append, First.filter_ins Item.isRow r.ins O hi, ho, List.filter_append]
  congr 1
  simp [List.filter_cons, hn]

/-- The open pins are as they were. -/
theorem stepOpen_pins (O : List Item) (r : BlockRow) (i₀ : Item)
    (hi : ∀ i ∈ r.ins, i.isPin = false) (ho : r.outs = [i₀]) (hp : i₀.isPin = false) :
    (stepOpen O r).filter Item.isPin = (O ++ [i₀]).filter Item.isPin := by
  rw [First.stepOpen_filter Item.isPin O r hi (by rw [ho]; simpa using hp), List.filter_append]
  simp [hp]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mem_rowSegs
#print axioms VerifiableInference.Desc.LinkJoin.rowsHeld_eq
#print axioms VerifiableInference.Desc.LinkJoin.rowsHeld_push
#print axioms VerifiableInference.Desc.LinkJoin.membersHeld_push
#print axioms VerifiableInference.Desc.LinkJoin.stepOpen_row
#print axioms VerifiableInference.Desc.LinkJoin.stepOpen_pins
