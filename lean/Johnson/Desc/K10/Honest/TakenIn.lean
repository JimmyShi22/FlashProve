-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/TakenIn.lean: every row that the proximity test on a segment's group takes in lies in one of
that segment's classes of rows. This is the converse of the library's `listClass_taken` and `sampleClass_taken`
(Johnson/Desc/First/Close/Law/FillRow.lean; its head says that the converse is not typed there). The lemmas speak of
the statement and of the tests in the table of joints (Johnson/Desc/First/Borders.lean). They name no honest side's
frame and none of the library's goals.

The words used below.
  The test: the proximity test on a group G of the statement. The rows that it takes in are `Slice.runRows`: the plain
      rows and the generator rows in G's list of open rows, and the sample rows of G's members.
  A class: a `RowClass` of a segment m. Three classes lie in the group's list of open rows (`RowClass.inList`):
      carried, position, equation; each is called a class of the list. The class `sample t` holds the sample rows of
      the oracle messages that the segment sends at moment t. `classRows N m c s` lists the rows of class c as they
      lie in the state s.
  O: a list of the table's items, read as the items that are open at a border. `Item.row m c` is the item of class c;
      `Item.pin m t` is the pin of moment t.
  N: the table's numbers (`Numbers`): the group's number, each class's first place and count, the tenants sent.

What is proved.
  `sample_of_fold`, `taken_split`: a row that the test takes in is an open row of the group, or a sample row of a
      member that the statement has. By the text of `runRows`.
  `mem_listClass`, `mem_sampleClass`: two ways to show that a row is a row of a class. By the text of `classRows`.
  `open_in_class`: every open row of the group is a row of a class of the list whose item is in O.
  `sample_in_class`: every sample row of a member is a row of a class `sample t` with t < 3 and the pin of t in O.
  `taken_in_class`: the two together, for every row that the test takes in. This is the converse.
  `taken_in_open`: the same, ending in a class whose item is in O; it asks hS.
  `taken_in_rows`: the same, ending in a class whose item is in the table's list `First.rowsOf m`, the rows in front of
      the closing; it asks hOnly.
  `sample_mem_rowsOf`, `equation_mem_rowsOf`, `list_mem_rowsOf`: which items `First.rowsOf` holds.
  `only_of_listed`: hOnly from the library's list of the classes of the list with an item in O (`listedOf`).
  `allSay_of_open`, `allSay_of_rows`: if the sentence `rowSays` holds at each of these classes, every row that the test
      takes in says its claim of the words (`AllSay`). The reader of the witness, `words`, is any function.
  `held_of_onAt`: the table's promise at a border (`onAt`), at a state without a mark of failure, gives hR and hM.
  `allSay_at_base`: `allSay_of_rows` at the reader `wordsFirst`, at the record that `K9.recOf` reads off a state of the
      first chain and at the group that `CloseBase` names (Johnson/Desc/K10/Honest/Base.lean).

By: `held_at` and the closed test `coveredB` (Johnson/Desc/First/Link/Law/CountsOfHeld.lean); `clsOf_row`
(Johnson/Desc/First/Link/Law/EqNumbersOf.lean); the texts of `runRows`, `classRows`, `membersHeld`, `First.rowsOf`,
`onAt`.

Why `coveredB` is asked. Take numbers at which the segment sends no tenant and the equation, with one row at place 0,
is the only class of the list with a row; an O that holds the equation's item twice and no other item; and, at the
table's number for the segment, a group whose test has not begun, without members, whose list holds two different
plain rows. Then `rowsHeld` and `membersHeld` say yes (`rowsDue` counts the item twice, so two rows are due, and the
row at place 0 is plain), the test takes the second row in, and that row lies in no class.

Limits. Every premise, by name.
  hR, hM: `rowsHeld N O s` and `membersHeld N O s`. Both stand in the table's promise at a state without a mark.
  hm: `m ∈ rowSegs O`: some class of segment m has its item in O.
  hC: `coveredB N O m`: every place below the count of rows that are due lies in the run of places of a class of the
      list whose item is in O.
  hG: the statement has the group G at the table's number for segment m.
  hS: (`taken_in_open`, `allSay_of_open`) where O holds the pin of a moment t < 3, it holds the item of `sample t`.
  hOnly: (`taken_in_rows`, `allSay_of_rows`, `allSay_at_base`) a class of the list with its item in O has its item in
      `First.rowsOf m`. At m ≠ 0 this holds outright (`list_mem_rowsOf`).
  hL: (`only_of_listed`) the classes of the list with an item in O are the equation alone at m = 0, and carried,
      position, equation elsewhere.
  hf: (`held_of_onAt`) the state bears no mark of failure.
  H, hGrp: (`allSay_at_base`) `CloseBase`, of which the field `there` alone is read; and that the group which the
      record's frame names is the table's number for segment m. hGrp is shown of no state here.
  h: (the three laws on `AllSay`) `rowSays` at each class. What a class's rows say is not shown here.
None of these premises is shown of any state or run here. The library holds hm, hC and hL at the table's open sets at
the 25 closings, at the full size, hC under that file's own premises (`hm_at`, Johnson/LPFE1R/K10Small.lean;
`covered_laid`, `listed_at_k10`, Johnson/LPFE1R/RowsDueAt.lean); these are not called here. Not asked: the table's
test `rowsAtFit`; `PlacesApart`; that every member is among the statement's oracle messages (one that is not gives no
row). The statements on the rows that the test takes in are idle at a group that has no open row and whose members
hold no sample row: there the test takes nothing in.
No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.First.Link.Law.CountsOfHeld
import Johnson.Desc.First.Link.Law.EqNumbersOf
import Johnson.Desc.K10.Honest.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.TakenIn
open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Numbers Item RowClass rowSegs rowsDue rowsHeld membersHeld sameMembers
  onAt classRows rowSays wordsAtFirst)
open VerifiableInference.Desc.LinkJoin (covers coveredB held_at clsOf clsOf_row listedOf)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-! ## What the test takes in, by the text of `runRows` -/

/-- `runRows` appends each listed message's sample rows to an array: a row of the result was in the array at the start,
or is a sample row of a listed message that the statement has. -/
theorem sample_of_fold (T : OnBytes.Statement) (r : OnBytes.Row) :
    ∀ (l : List Nat) (a : Array OnBytes.Row),
      r ∈ (l.foldl (fun a o => a ++ ((T.oracles[o]?).map (·.sampleRows)).getD #[]) a).toList →
      r ∈ a.toList ∨ ∃ o, o ∈ l ∧ ∃ x, T.oracles[o]? = some x ∧ r ∈ x.sampleRows.toList := by
  intro l
  induction l with
  | nil =>
    intro a h
    exact Or.inl h
  | cons o l ih =>
    intro a h
    rw [List.foldl_cons] at h
    rcases ih _ h with c | ⟨o', ho', x, hx, hr⟩
    · rw [Array.toList_append, List.mem_append] at c
      rcases c with c | c
      · exact Or.inl c
      · cases hx : T.oracles[o]? with
        | none =>
          rw [hx] at c
          have c' : r ∈ ([] : List OnBytes.Row) := c
          cases c'
        | some x =>
          rw [hx] at c
          exact Or.inr ⟨o, List.mem_cons.2 (Or.inl rfl), x, hx, c⟩
    · exact Or.inr ⟨o', List.mem_cons.2 (Or.inr ho'), x, hx, hr⟩

/-- A row that the test takes in is an open row of the group, or a sample row of a member that the statement has. -/
theorem taken_split (T : OnBytes.Statement) (G : OnBytes.Group) (r : OnBytes.Row)
    (h : r ∈ (Slice.runRows T G).toList) :
    r ∈ G.rows.toList ∨
      ∃ o, o ∈ G.members.toList ∧ ∃ x, T.oracles[o]? = some x ∧ r ∈ x.sampleRows.toList := by
  unfold Slice.runRows at h
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at h
  rcases h with (h | h) | h
  · exact Or.inl h.1
  · rw [← Array.foldl_toList] at h
    rcases sample_of_fold T r _ _ h with c | c
    · have c' : r ∈ ([] : List OnBytes.Row) := c
      cases c'
    · exact Or.inr c
  · exact Or.inl h.1

/-! ## When a row is a row of a class, by the text of `classRows` -/

variable {N : Numbers} {O : List Item} {s : S} {m : Nat} {G : OnBytes.Group}

/-- If place i lies in the run of places that the numbers give to a class of the list, the row at place i of the group's
list is a row of that class. -/
theorem mem_listClass (hG : s.st.groups[N.groupAt m]? = some G) {c : RowClass} (hc : c.inList = true)
    {i : Nat} (h1 : (N.rowsAt m c).1 ≤ i) (h2 : i < (N.rowsAt m c).1 + (N.rowsAt m c).2)
    {r : OnBytes.Row} (e : G.rows[i]? = some r) : r ∈ classRows N m c s := by
  have h : r ∈ (List.range (N.rowsAt m c).2).filterMap fun j => G.rows[(N.rowsAt m c).1 + j]? := by
    refine List.mem_filterMap.2 ⟨i - (N.rowsAt m c).1, List.mem_range.2 (by omega), ?_⟩
    show G.rows[(N.rowsAt m c).1 + (i - (N.rowsAt m c).1)]? = some r
    rw [show (N.rowsAt m c).1 + (i - (N.rowsAt m c).1) = i by omega]
    exact e
  cases c with
  | sample t => cases hc
  | carried => simpa [classRows, hG] using h
  | position => simpa [classRows, hG] using h
  | equation => simpa [classRows, hG] using h

/-- If the book places message o at a tenant that the segment sends at moment t, each sample row of o is a row of the
class `sample t`. -/
theorem mem_sampleClass {t o : Nat} {p : Nat × Nat} (hp : s.book.place[o]? = some p)
    (hin : p ∈ N.sent m t) {x : OnBytes.Oracle} (hx : s.st.oracles[o]? = some x) {r : OnBytes.Row}
    (hr : r ∈ x.sampleRows.toList) : r ∈ classRows N m (.sample t) s := by
  have ho : o < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  have hc : ((some p : Option (Nat × Nat)).any fun q => (N.sent m t).contains q) = true :=
    List.contains_iff_mem.2 hin
  show r ∈ (List.range s.st.oracles.size).flatMap fun o =>
    if (s.book.place[o]?).any fun q => (N.sent m t).contains q then
      ((s.st.oracles[o]?).map fun q => q.sampleRows.toList).getD []
    else []
  refine List.mem_flatMap.2 ⟨o, List.mem_range.2 ho, ?_⟩
  show r ∈ if (s.book.place[o]?).any fun q => (N.sent m t).contains q then
      ((s.st.oracles[o]?).map fun q => q.sampleRows.toList).getD []
    else []
  rw [hp, hx, if_pos hc]
  exact hr

/-! ## The converse -/

/-- Every open row of the group is a row of a class of the list whose item is in O. -/
theorem open_in_class (hR : rowsHeld N O s = true) (hm : m ∈ rowSegs O) (hC : coveredB N O m = true)
    (hG : s.st.groups[N.groupAt m]? = some G) (r : OnBytes.Row) (hr : r ∈ G.rows.toList) :
    ∃ c : RowClass, c.inList = true ∧ Item.row m c ∈ O ∧ r ∈ classRows N m c s := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hr)
  have e' : G.rows[i]? = some r := by rw [Array.getElem?_eq_getElem hi, e]
  have hd : i < rowsDue N O m := by
    rw [← (held_at hR hm hG).1]
    exact hi
  have hs := List.all_eq_true.1 hC i (List.mem_range.2 hd)
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨it, hit, hcv⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? hk)
  cases it with
  | row m' c =>
    have hcv' : (if (m' == m && c.inList &&
        decide ((N.rowsAt m c).1 ≤ i ∧ i < (N.rowsAt m c).1 + (N.rowsAt m c).2)) = true
        then some c.kind else none) = some k := hcv
    by_cases hc : (m' == m && c.inList &&
        decide ((N.rowsAt m c).1 ≤ i ∧ i < (N.rowsAt m c).1 + (N.rowsAt m c).2)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨c1, c2⟩, c3, c4⟩ := hc
      have em : m' = m := eq_of_beq c1
      have hit' : Item.row m c ∈ O := by
        rw [← em]
        exact hit
      exact ⟨c, c2, hit', mem_listClass hG c2 c3 c4 e'⟩
    · rw [if_neg hc] at hcv'
      cases hcv'
  | _ => cases hcv

/-- Every sample row of a member is a row of a class `sample t` with t < 3 and the pin of moment t in O. -/
theorem sample_in_class (hM : membersHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) {o : Nat} (ho : o ∈ G.members.toList)
    {x : OnBytes.Oracle} (hx : s.st.oracles[o]? = some x) (r : OnBytes.Row)
    (hr : r ∈ x.sampleRows.toList) :
    ∃ t, t < 3 ∧ Item.pin m t ∈ O ∧ r ∈ classRows N m (.sample t) s := by
  have h1 := List.all_eq_true.1 hM m hm
  rw [hG] at h1
  simp only [Bool.and_eq_true, sameMembers] at h1
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 h1.1 o ho)
  have hA : p ∈ G.members.toList.filterMap fun o => s.book.place[o]? :=
    List.mem_filterMap.2 ⟨o, ho, hp⟩
  have hB := List.contains_iff_mem.1 (List.all_eq_true.1 h1.2.1 p hA)
  obtain ⟨t, ht, hin⟩ := List.mem_flatMap.1 hB
  have hin' : p ∈ if O.contains (Item.pin m t) then N.sent m t else [] := hin
  by_cases hc : O.contains (Item.pin m t) = true
  · rw [if_pos hc] at hin'
    exact ⟨t, List.mem_range.1 ht, List.contains_iff_mem.1 hc, mem_sampleClass hp hin' hx hr⟩
  · rw [if_neg hc] at hin'
    cases hin'

/-- **The converse.** Every row that the test takes in is a row of a class of the list whose item is in O, or of a class
`sample t` with t < 3 and the pin of moment t in O. -/
theorem taken_in_class (hR : rowsHeld N O s = true) (hM : membersHeld N O s = true) (hm : m ∈ rowSegs O)
    (hC : coveredB N O m = true) (hG : s.st.groups[N.groupAt m]? = some G) :
    ∀ r ∈ (Slice.runRows s.st G).toList,
      (∃ c : RowClass, c.inList = true ∧ Item.row m c ∈ O ∧ r ∈ classRows N m c s) ∨
        ∃ t, t < 3 ∧ Item.pin m t ∈ O ∧ r ∈ classRows N m (.sample t) s := by
  intro r hr
  rcases taken_split s.st G r hr with h | ⟨o, ho, x, hx, h⟩
  · exact Or.inl (open_in_class hR hm hC hG r h)
  · exact Or.inr (sample_in_class hM hm hG ho hx r h)

/-- **The converse, at the items in O.** If O holds the item of `sample t` wherever it holds the pin of a moment t < 3,
every row that the test takes in is a row of a class whose item is in O. -/
theorem taken_in_open (hR : rowsHeld N O s = true) (hM : membersHeld N O s = true) (hm : m ∈ rowSegs O)
    (hC : coveredB N O m = true)
    (hS : ∀ t, t < 3 → Item.pin m t ∈ O → Item.row m (.sample t) ∈ O)
    (hG : s.st.groups[N.groupAt m]? = some G) :
    ∀ r ∈ (Slice.runRows s.st G).toList, ∃ c : RowClass, Item.row m c ∈ O ∧ r ∈ classRows N m c s := by
  intro r hr
  rcases taken_in_class hR hM hm hC hG r hr with ⟨c, -, hO, h⟩ | ⟨t, ht, hP, h⟩
  · exact ⟨c, hO, h⟩
  · exact ⟨.sample t, hS t ht hP, h⟩

/-! ## At `First.rowsOf`, the table's list of the rows in front of the closing -/

/-- `First.rowsOf n` holds the item of `sample t` for each t < 3. -/
theorem sample_mem_rowsOf (n : Nat) {t : Nat} (ht : t < 3) : Item.row n (.sample t) ∈ First.rowsOf n := by
  have h : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  unfold First.rowsOf
  refine List.mem_append.2 (Or.inr ?_)
  rcases h with e | e | e
  · rw [e]
    exact List.mem_cons.2 (Or.inl rfl)
  · rw [e]
    exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  · rw [e]
    exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))

/-- `First.rowsOf n` holds the item of the class equation. -/
theorem equation_mem_rowsOf (n : Nat) : Item.row n .equation ∈ First.rowsOf n := by
  unfold First.rowsOf
  exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))

/-- At n ≠ 0, `First.rowsOf n` holds the item of every class of the list. -/
theorem list_mem_rowsOf {n : Nat} (h0 : n ≠ 0) {c : RowClass} (hc : c.inList = true) :
    Item.row n c ∈ First.rowsOf n := by
  have hb : ¬ ((n == 0) = true) := fun e => h0 (eq_of_beq e)
  cases c with
  | sample t => cases hc
  | equation => exact equation_mem_rowsOf n
  | carried =>
    unfold First.rowsOf
    rw [if_neg hb]
    exact List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inl rfl)))
  | position =>
    unfold First.rowsOf
    rw [if_neg hb]
    exact List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))

/-- If the classes of the list with an item in O are the equation alone at m = 0, and carried, position and equation
elsewhere, `First.rowsOf m` holds each of these items. -/
theorem only_of_listed
    (hL : listedOf O m = if m = 0 then [RowClass.equation]
      else [RowClass.carried, RowClass.position, RowClass.equation]) :
    ∀ c : RowClass, c.inList = true → Item.row m c ∈ O → Item.row m c ∈ First.rowsOf m := by
  intro c hc hO
  by_cases h0 : m = 0
  · have hb : (m == m && c.inList) = true := by simp [hc]
    have h1 : c ∈ listedOf O m := by
      show c ∈ O.filterMap (clsOf m)
      refine List.mem_filterMap.2 ⟨Item.row m c, hO, ?_⟩
      rw [clsOf_row, if_pos hb]
    rw [hL, if_pos h0] at h1
    rw [List.mem_singleton.1 h1]
    exact equation_mem_rowsOf m
  · exact list_mem_rowsOf h0 hc

/-- **The converse, at the table's list.** Every row that the test takes in is a row of a class whose item is in
`First.rowsOf m`. -/
theorem taken_in_rows (hR : rowsHeld N O s = true) (hM : membersHeld N O s = true) (hm : m ∈ rowSegs O)
    (hC : coveredB N O m = true)
    (hOnly : ∀ c : RowClass, c.inList = true → Item.row m c ∈ O → Item.row m c ∈ First.rowsOf m)
    (hG : s.st.groups[N.groupAt m]? = some G) :
    ∀ r ∈ (Slice.runRows s.st G).toList,
      ∃ c : RowClass, Item.row m c ∈ First.rowsOf m ∧ r ∈ classRows N m c s := by
  intro r hr
  rcases taken_in_class hR hM hm hC hG r hr with ⟨c, hc, hO, h⟩ | ⟨t, ht, -, h⟩
  · exact ⟨c, hOnly c hc hO, h⟩
  · exact ⟨.sample t, sample_mem_rowsOf m ht, h⟩

/-! ## From the classes' sentences to all rows that the test takes in -/

/-- **If `rowSays` holds at every class whose item is in O, every row that the test takes in says its claim of the
words.** -/
theorem allSay_of_open {Pz W : Type} (words : Pz × S → Strs → W → Words GE) (a : Pz × S) (y : Strs) (w : W)
    (hR : rowsHeld N O a.2 = true) (hM : membersHeld N O a.2 = true) (hm : m ∈ rowSegs O)
    (hC : coveredB N O m = true)
    (hS : ∀ t, t < 3 → Item.pin m t ∈ O → Item.row m (.sample t) ∈ O)
    (hG : a.2.st.groups[N.groupAt m]? = some G)
    (h : ∀ c : RowClass, Item.row m c ∈ O → rowSays N words m c a y w) :
    AllSay rdE a.2.st (Slice.runRows a.2.st G).toList (words a y w) := by
  intro r hr
  obtain ⟨c, hc, hin⟩ := taken_in_open hR hM hm hC hS hG r hr
  exact h c hc r hin

/-- **If `rowSays` holds at every class whose item is in `First.rowsOf m`, every row that the test takes in says its
claim of the words.** -/
theorem allSay_of_rows {Pz W : Type} (words : Pz × S → Strs → W → Words GE) (a : Pz × S) (y : Strs) (w : W)
    (hR : rowsHeld N O a.2 = true) (hM : membersHeld N O a.2 = true) (hm : m ∈ rowSegs O)
    (hC : coveredB N O m = true)
    (hOnly : ∀ c : RowClass, c.inList = true → Item.row m c ∈ O → Item.row m c ∈ First.rowsOf m)
    (hG : a.2.st.groups[N.groupAt m]? = some G)
    (h : ∀ c : RowClass, Item.row m c ∈ First.rowsOf m → rowSays N words m c a y w) :
    AllSay rdE a.2.st (Slice.runRows a.2.st G).toList (words a y w) := by
  intro r hr
  obtain ⟨c, hc, hin⟩ := taken_in_rows hR hM hm hC hOnly hG r hr
  exact h c hc r hin

/-- The table's promise at a border (`onAt`), at a state without a mark of failure, gives `rowsHeld` and
`membersHeld`. -/
theorem held_of_onAt {Pz W : Type} {Mg : First.Meaning Pz W} {links : List First.ModelPart}
    {p : Option VerifiableInference.Desc.Place} {Q : List First.Pub} {a : Pz × S} {y : Strs}
    (h : onAt N Mg links p O Q a y) (hf : a.2.failed = none) :
    rowsHeld N O a.2 = true ∧ membersHeld N O a.2 = true := by
  rcases h.2 with c | c
  · exact absurd hf c
  · have e := c.1
    simp only [Bool.and_eq_true] at e
    exact ⟨e.1.1.1.1.2, e.1.1.1.2⟩

/-- **`allSay_of_rows` at the reader `wordsFirst`**, at the record that `K9.recOf` reads off the state t₀ and at the
group D.G that `CloseBase` names. -/
theorem allSay_at_base {Pz Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (z : Pz) (t₀ : S) (y : Strs)
    (v : Wit Cells Tok MsgT) {Q : First.Close.Par} {D : BaseData} (H : CloseBase Q (K9.recOf t₀) D)
    (hGrp : (K9.recOf t₀).frame.group = N.groupAt m)
    (hR : rowsHeld N O t₀ = true) (hM : membersHeld N O t₀ = true) (hm : m ∈ rowSegs O)
    (hC : coveredB N O m = true)
    (hOnly : ∀ c : RowClass, c.inList = true → Item.row m c ∈ O → Item.row m c ∈ First.rowsOf m)
    (h : ∀ c : RowClass, Item.row m c ∈ First.rowsOf m → rowSays N (wordsAtFirst arr) m c (z, t₀) y v) :
    AllSay rdE (K9.recOf t₀).st (Slice.runRows (K9.recOf t₀).st D.G).toList
      (wordsFirst arr t₀.st t₀.book v) := by
  have hG : t₀.st.groups[N.groupAt m]? = some D.G := by
    rw [← hGrp]
    exact H.there
  exact allSay_of_rows (wordsAtFirst arr) (z, t₀) y v hR hM hm hC hOnly hG h

end ProofFile.Honest.K10.TakenIn

#print axioms ProofFile.Honest.K10.TakenIn.sample_of_fold
#print axioms ProofFile.Honest.K10.TakenIn.taken_split
#print axioms ProofFile.Honest.K10.TakenIn.mem_listClass
#print axioms ProofFile.Honest.K10.TakenIn.mem_sampleClass
#print axioms ProofFile.Honest.K10.TakenIn.open_in_class
#print axioms ProofFile.Honest.K10.TakenIn.sample_in_class
#print axioms ProofFile.Honest.K10.TakenIn.taken_in_class
#print axioms ProofFile.Honest.K10.TakenIn.taken_in_open
#print axioms ProofFile.Honest.K10.TakenIn.sample_mem_rowsOf
#print axioms ProofFile.Honest.K10.TakenIn.equation_mem_rowsOf
#print axioms ProofFile.Honest.K10.TakenIn.list_mem_rowsOf
#print axioms ProofFile.Honest.K10.TakenIn.only_of_listed
#print axioms ProofFile.Honest.K10.TakenIn.taken_in_rows
#print axioms ProofFile.Honest.K10.TakenIn.allSay_of_open
#print axioms ProofFile.Honest.K10.TakenIn.allSay_of_rows
#print axioms ProofFile.Honest.K10.TakenIn.held_of_onAt
#print axioms ProofFile.Honest.K10.TakenIn.allSay_at_base
