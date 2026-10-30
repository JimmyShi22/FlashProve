-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/LeftTables.lean: two descriptions of a group's tables agree.

What is proved. Two definitions say which row of a group's table holds which member's row. `tableRow`
(Johnson/Desc/K2/Honest/FoldEnd.lean) is used by the honest prover of the code switch; it places a member's real rows.
`tablesOf` (Johnson/Desc/Means/Says.lean) is used by the library's laws on rows; it places a member's whole block of
2 ^ rowBits rows. `main_is` and `mask_is` show that both give the same entry at every row and place of the group's main
table and of its mask table, for words that are 0 on the rows beyond a member's real rows. Theorems only; no definition.

A seat is a position, counted from 0, in the layout's list of members (for `tableRow`: in the list of first rows).

  `findSome_one`, `findSome_congr`   `List.findSome?` where only one member of the list answers; it reads the function
                   only at the list's members
  `seat_some`       what `tableRow` asks of one seat that has a first row, as a proposition
  `tableRow_in`, `tableRow_off`   `tableRow` at a row inside a seat's block: that seat and the row's number in it if the
                   row is real, nothing if it lies beyond the real rows; at a row in no block: nothing
  `tableRow_lt`, `tableRow_congr`   the seat that it returns is one of the list's; it reads the numbers of rows only at
                   the list's seats
  `find_seat`       if no member occurs twice, the member at a seat is found at that seat
  `real_le`         a member's table has at most 2 ^ rowBits real rows
  **`main_is`**, **`mask_is`**   the entry at row ρ and place j, read off the words through `tableRow` (0 where it
                   returns nothing), equals `tablesOf`'s entry at the index ρ + 2 ^ k * j, or ρ + 2 ^ h * j for the mask
                   table

The premises. `LayFacts S G L` (Johnson/Desc/Means/Layout.lean): the blocks are aligned, inside the table and disjoint.
No member occurs twice: `L.find` returns the first seat, so for a number that occurred twice `tablesOf` would place one
block and `tableRow` two. The list of first rows is as long as the list of members. `Padded S w`: the words are 0 on the
rows beyond the real ones; this is where the two definitions differ, because `tableRow` places nothing there and
`tablesOf` places the words. The row ρ lies below 2 ^ k (2 ^ h for the mask table). The words are over the extension
field.

Limits. No bound is asked of the place j. Nothing is said of the kept members' own tables (see LeftIs.lean). Nothing is
said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K2.Honest.FoldEnd
import Johnson.Desc.Means.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice
open VerifiableInference.Desc.K2.Honest (tableRow)

/-- Where one member of a list alone answers, `findSome?` yields its answer. -/
theorem findSome_one {α β : Type} (g : α → Option β) (i : α) (v : β) (hg : g i = some v) :
    ∀ (l : List α), i ∈ l → (∀ x ∈ l, x ≠ i → g x = none) → l.findSome? g = some v
  | [], hi, _ => by cases hi
  | x :: t, hi, ho => by
    rw [List.findSome?_cons]
    by_cases hx : x = i
    · rw [hx, hg]
    · rw [ho x (List.mem_cons_self ..) hx]
      exact findSome_one g i v hg t ((List.mem_cons.1 hi).resolve_left fun e => hx e.symm)
        fun y hy => ho y (List.mem_cons_of_mem _ hy)

/-- `findSome?` reads the function at the list's members alone. -/
theorem findSome_congr {α β : Type} {g g' : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, g x = g' x) → l.findSome? g = l.findSome? g'
  | [], _ => rfl
  | x :: t, h => by
    rw [List.findSome?_cons, List.findSome?_cons, h x (List.mem_cons_self ..),
      findSome_congr t fun y hy => h y (List.mem_cons_of_mem _ hy)]

section
variable (first : Array (Option Nat)) (rows bits : Nat → Nat)

/-- What `tableRow` asks of one seat that has a first row: the test with `decide`, as a proposition. -/
theorem seat_some {ρ i f : Nat} (hf : first.getD i none = some f) :
    ((first.getD i none).bind fun f =>
      if decide (f ≤ ρ) && decide (ρ < f + rows i) then some (i, ρ - f) else none) =
      if f ≤ ρ ∧ ρ < f + rows i then some (i, ρ - f) else none := by
  rw [hf, Option.bind_some]
  by_cases h : f ≤ ρ ∧ ρ < f + rows i
  · rw [if_pos h, decide_eq_true h.1, decide_eq_true h.2]
    rfl
  · rw [if_neg h]
    by_cases h1 : f ≤ ρ
    · have h2 : ¬ ρ < f + rows i := fun c => h ⟨h1, c⟩
      rw [decide_eq_true h1, decide_eq_false h2]
      rfl
    · rw [decide_eq_false h1]
      rfl

/-- **At a row inside a seat's block** `tableRow` returns that seat and the row's number in the block if the row is
real, and nothing otherwise. hr: a seat's rows fit its block. hap: the blocks are disjoint. -/
theorem tableRow_in (hr : ∀ i, rows i ≤ 2 ^ bits i)
    (hap : ∀ i i' f f', i ≠ i' → first.getD i none = some f → first.getD i' none = some f' →
      f + 2 ^ bits i ≤ f' ∨ f' + 2 ^ bits i' ≤ f)
    {ρ i f : Nat} (hi : i < first.size) (hf : first.getD i none = some f) (h1 : f ≤ ρ)
    (h2 : ρ < f + 2 ^ bits i) :
    tableRow first rows ρ = if ρ - f < rows i then some (i, ρ - f) else none := by
  have others : ∀ x, x ≠ i → ((first.getD x none).bind fun f' =>
      if decide (f' ≤ ρ) && decide (ρ < f' + rows x) then some (x, ρ - f') else none) = none := by
    intro x hx
    cases hx' : first.getD x none with
    | none => rfl
    | some f' =>
      have e := seat_some first rows (ρ := ρ) hx'
      rw [hx'] at e
      rw [e, if_neg]
      intro c
      have := hr x
      rcases hap x i f' f hx hx' hf with a | a <;> omega
  unfold tableRow
  by_cases hb : ρ - f < rows i
  · rw [if_pos hb]
    refine findSome_one _ i (i, ρ - f) ?_ _ (List.mem_range.2 hi) fun x _ hx => others x hx
    rw [seat_some first rows hf, if_pos ⟨h1, by omega⟩]
  · rw [if_neg hb, List.findSome?_eq_none_iff]
    intro x _
    by_cases hx : x = i
    · rw [hx, seat_some first rows hf, if_neg]
      intro c
      omega
    · exact others x hx

/-- **At a row in no block** `tableRow` returns nothing. hr: a seat's rows fit its block. -/
theorem tableRow_off (hr : ∀ i, rows i ≤ 2 ^ bits i) {ρ : Nat}
    (h : ∀ i f, first.getD i none = some f → ¬ (f ≤ ρ ∧ ρ < f + 2 ^ bits i)) :
    tableRow first rows ρ = none := by
  unfold tableRow
  rw [List.findSome?_eq_none_iff]
  intro x _
  cases hx : first.getD x none with
  | none => rfl
  | some f =>
    have e := seat_some first rows (ρ := ρ) hx
    rw [hx] at e
    rw [e, if_neg]
    intro c
    have := hr x
    exact h x f hx ⟨c.1, by omega⟩

end

/-- The seat that `tableRow` yields is one of the list's. -/
theorem tableRow_lt {first : Array (Option Nat)} {rows : Nat → Nat} {ρ i b : Nat}
    (h : tableRow first rows ρ = some (i, b)) : i < first.size := by
  unfold tableRow at h
  obtain ⟨a, ha, e⟩ := List.exists_of_findSome?_eq_some h
  cases hf : first.getD a none with
  | none =>
    rw [hf] at e
    cases e
  | some f =>
    rw [hf, Option.bind_some] at e
    split at e
    · cases e
      exact List.mem_range.1 ha
    · cases e

/-- `tableRow` reads the numbers of rows at the list's seats alone. -/
theorem tableRow_congr (first : Array (Option Nat)) (rows rows' : Nat → Nat) (ρ : Nat)
    (h : ∀ i, i < first.size → rows i = rows' i) : tableRow first rows ρ = tableRow first rows' ρ := by
  unfold tableRow
  refine findSome_congr _ fun i hi => ?_
  rw [h i (List.mem_range.1 hi)]

/-- **If no member occurs twice, the member at a seat is found at that seat.** -/
theorem find_seat {L : GroupLayout} (h : L.members.toList.Nodup) {i : Nat}
    (hi : i < L.members.size) : L.find (L.members.getD i noId) = some i := by
  have hg : L.members.getD i noId = L.members[i] := by simp [Array.getD, hi]
  have hm : L.members.getD i noId ∈ L.members.toList := by
    rw [hg]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
  obtain ⟨i', hf⟩ := find_of_mem hm
  obtain ⟨hi', e⟩ := find_some hf
  have hg' : L.members.getD i' noId = L.members[i'] := by simp [Array.getD, hi']
  have e' : L.members.toList[i']'(by simpa using hi') = L.members.toList[i]'(by simpa using hi) := by
    show L.members[i'] = L.members[i]
    rw [← hg', ← hg]
    exact e
  rw [hf, (List.Nodup.getElem_inj_iff h).1 e']

/-- A member's table has at most 2 ^ rowBits real rows. -/
theorem real_le (S : Statement) (o : Nat) (part : Part) : realRows S o part ≤ 2 ^ S.rowBits o part := by
  unfold realRows Statement.rowBits
  cases S.oracles[o]? with
  | none => exact Nat.zero_le _
  | some x => exact le_two_pow_ceilLog2 _

variable {S : Statement} {G : Group} {L : GroupLayout}

/-- **The main table**: read through `tableRow`, it is `tablesOf`'s. -/
theorem main_is (F : LayFacts S G L) (once : L.members.toList.Nodup)
    (hn : L.mainFirst.size = L.members.size) (w : Words GE) (hp : Padded S w) (ρ j : Nat)
    (hρ : ρ < 2 ^ L.k) :
    (match tableRow L.mainFirst (fun i => realRows S (L.members.getD i noId) .main) ρ with
      | some (i, b) =>
        w (L.members.getD i noId) .main (b + j * 2 ^ S.rowBits (L.members.getD i noId) .main)
      | none => 0) = (tablesOf S L w).main (ρ + 2 ^ L.k * j) := by
  have hmod : (ρ + 2 ^ L.k * j) % 2 ^ L.k = ρ := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]
  have seat : ∀ i f, L.mainFirst.getD i none = some f → i < L.members.size := by
    intro i f hf
    by_contra c
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hf
    cases hf
  have hr : ∀ i, realRows S (L.members.getD i noId) .main ≤
      2 ^ S.rowBits (L.members.getD i noId) .main := fun i => real_le S _ _
  have hap : ∀ i i' f f', i ≠ i' → L.mainFirst.getD i none = some f →
      L.mainFirst.getD i' none = some f' →
      f + 2 ^ S.rowBits (L.members.getD i noId) .main ≤ f' ∨
        f' + 2 ^ S.rowBits (L.members.getD i' noId) .main ≤ f := by
    intro i i' f f' hne hf hf'
    have a := find_seat once (seat i f hf)
    have a' := find_seat once (seat i' f' hf')
    refine F.main_apart _ _ i i' f f' ?_ a a' hf hf'
    intro e
    rw [e, a'] at a
    exact hne (Option.some.inj a).symm
  by_cases hoff : OffMain S L (ρ + 2 ^ L.k * j)
  · rw [tablesOf_main_else F w _ hoff,
      tableRow_off L.mainFirst _ (fun i => S.rowBits (L.members.getD i noId) .main) hr]
    intro i f hf c
    have a := find_seat once (seat i f hf)
    have hk := (F.main_block _ i f a hf).2.1
    refine hoff _ i f a hk hf ?_
    unfold InBlock
    rw [hmod]
    exact c
  · have hex : ∃ o i f, L.find o = some i ∧ L.kept.getD i false = false ∧
        L.mainFirst.getD i none = some f ∧ InBlock (ρ + 2 ^ L.k * j) (S.rowBits o .main) f L.k := by
      by_contra c
      exact hoff fun o i f hf hk hm hin => c ⟨o, i, f, hf, hk, hm, hin⟩
    obtain ⟨o, i, f, hf, _, hm, hin⟩ := hex
    unfold InBlock at hin
    rw [hmod] at hin
    obtain ⟨hi, ho⟩ := find_some hf
    have hpos := Nat.two_pow_pos (S.rowBits o .main)
    have e1 : (ρ - f + j * 2 ^ S.rowBits o .main) % 2 ^ S.rowBits o .main = ρ - f := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (ρ - f + j * 2 ^ S.rowBits o .main) / 2 ^ S.rowBits o .main = j := by
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have eJ : ρ + 2 ^ L.k * j =
        groupIndex (ρ - f + j * 2 ^ S.rowBits o .main) (S.rowBits o .main) f L.k := by
      unfold groupIndex
      rw [e1, e2, Nat.mul_comm]
      omega
    have h2 : ρ < f + 2 ^ S.rowBits (L.members.getD i noId) .main := by rw [ho]; exact hin.2
    rw [eJ, tablesOf_main_at F w hf hm,
      tableRow_in L.mainFirst _ (fun i => S.rowBits (L.members.getD i noId) .main) hr hap
        (by omega) hm hin.1 h2, ho]
    by_cases hreal : ρ - f < realRows S o .main
    · rw [if_pos hreal]
      show w (L.members.getD i noId) .main (ρ - f + j * 2 ^ S.rowBits (L.members.getD i noId) .main) = _
      rw [ho]
    · rw [if_neg hreal]
      exact (hp o .main _ (by rw [e1]; omega)).symm

/-- **The mask table**: read through `tableRow`, it is `tablesOf`'s. -/
theorem mask_is (F : LayFacts S G L) (once : L.members.toList.Nodup)
    (hn : L.maskFirst.size = L.members.size) (w : Words GE) (hp : Padded S w) (ρ j : Nat)
    (hρ : ρ < 2 ^ L.h) :
    (match tableRow L.maskFirst (fun i => realRows S (L.members.getD i noId) .mask) ρ with
      | some (i, b) =>
        w (L.members.getD i noId) .mask (b + j * 2 ^ S.rowBits (L.members.getD i noId) .mask)
      | none => 0) = (tablesOf S L w).mask (ρ + 2 ^ L.h * j) := by
  have hmod : (ρ + 2 ^ L.h * j) % 2 ^ L.h = ρ := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]
  have seat : ∀ i f, L.maskFirst.getD i none = some f → i < L.members.size := by
    intro i f hf
    by_contra c
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hf
    cases hf
  have hr : ∀ i, realRows S (L.members.getD i noId) .mask ≤
      2 ^ S.rowBits (L.members.getD i noId) .mask := fun i => real_le S _ _
  have hap : ∀ i i' f f', i ≠ i' → L.maskFirst.getD i none = some f →
      L.maskFirst.getD i' none = some f' →
      f + 2 ^ S.rowBits (L.members.getD i noId) .mask ≤ f' ∨
        f' + 2 ^ S.rowBits (L.members.getD i' noId) .mask ≤ f := by
    intro i i' f f' hne hf hf'
    have a := find_seat once (seat i f hf)
    have a' := find_seat once (seat i' f' hf')
    refine F.mask_apart _ _ i i' f f' ?_ a a' hf hf'
    intro e
    rw [e, a'] at a
    exact hne (Option.some.inj a).symm
  by_cases hoff : OffMask S L (ρ + 2 ^ L.h * j)
  · rw [tablesOf_mask_else F w _ hoff,
      tableRow_off L.maskFirst _ (fun i => S.rowBits (L.members.getD i noId) .mask) hr]
    intro i f hf c
    have a := find_seat once (seat i f hf)
    refine hoff _ i f a hf ?_
    unfold InBlock
    rw [hmod]
    exact c
  · have hex : ∃ o i f, L.find o = some i ∧ L.maskFirst.getD i none = some f ∧
        InBlock (ρ + 2 ^ L.h * j) (S.rowBits o .mask) f L.h := by
      by_contra c
      exact hoff fun o i f hf hm hin => c ⟨o, i, f, hf, hm, hin⟩
    obtain ⟨o, i, f, hf, hm, hin⟩ := hex
    unfold InBlock at hin
    rw [hmod] at hin
    obtain ⟨hi, ho⟩ := find_some hf
    have hpos := Nat.two_pow_pos (S.rowBits o .mask)
    have e1 : (ρ - f + j * 2 ^ S.rowBits o .mask) % 2 ^ S.rowBits o .mask = ρ - f := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (ρ - f + j * 2 ^ S.rowBits o .mask) / 2 ^ S.rowBits o .mask = j := by
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have eJ : ρ + 2 ^ L.h * j =
        groupIndex (ρ - f + j * 2 ^ S.rowBits o .mask) (S.rowBits o .mask) f L.h := by
      unfold groupIndex
      rw [e1, e2, Nat.mul_comm]
      omega
    have h2 : ρ < f + 2 ^ S.rowBits (L.members.getD i noId) .mask := by rw [ho]; exact hin.2
    rw [eJ, tablesOf_mask_at F w hf hm,
      tableRow_in L.maskFirst _ (fun i => S.rowBits (L.members.getD i noId) .mask) hr hap
        (by omega) hm hin.1 h2, ho]
    by_cases hreal : ρ - f < realRows S o .mask
    · rw [if_pos hreal]
      show w (L.members.getD i noId) .mask (ρ - f + j * 2 ^ S.rowBits (L.members.getD i noId) .mask) = _
      rw [ho]
    · rw [if_neg hreal]
      exact (hp o .mask _ (by rw [e1]; omega)).symm

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.findSome_one
#print axioms ProofFile.Honest.K10.LeftIs.findSome_congr
#print axioms ProofFile.Honest.K10.LeftIs.seat_some
#print axioms ProofFile.Honest.K10.LeftIs.tableRow_in
#print axioms ProofFile.Honest.K10.LeftIs.tableRow_off
#print axioms ProofFile.Honest.K10.LeftIs.tableRow_lt
#print axioms ProofFile.Honest.K10.LeftIs.tableRow_congr
#print axioms ProofFile.Honest.K10.LeftIs.find_seat
#print axioms ProofFile.Honest.K10.LeftIs.real_le
#print axioms ProofFile.Honest.K10.LeftIs.main_is
#print axioms ProofFile.Honest.K10.LeftIs.mask_is
