-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FillRow.lean: THE LAYER OF THE TABLE's FILLING THAT LAYS THE LETTER
`row`: what the item "the rows of class c of segment m hold" says of the state and the witness.
Definitions, statements and proofs. A file BESIDE the table of joints
(Johnson/Desc/First/Borders.lean): it turns nothing of it. After the form of
Johnson/Desc/First/FillKeeper.lean.

Why. `Meaning.row` is a letter. By the table's rule an item's sentence is its closer's:
the kinds K10 (a segment's closing) and K12 (a proximity test) close `row`; both kinds' files name
one sentence: the library's own "what a row says of words" (`OnBytes.Means.Says`, `AllSay`,
Johnson/Desc/Means/Says.lean): a sum over the members' OWN tables. It reads no layout: so a class
says one thing at every border at which it is open.
  `classRows N m c s`: the class's rows as they lie in the state, in the table's own numbers: at
    carried, position, equation: the rows of the group `N.groupAt m` at the places `N.rowsAt m c`;
    at `sample t`: the sample rows of the oracle messages whose place in the state's book is a
    tenant of `N.sent m t`.
  `rowSays N words m c a y w` := `AllSay rdE a.2.st (classRows N m c a.2) (words a y w)`. `fillRow N
    words Mg`: the layer. `fillRow_row`: what it lays; `fillRow_pub`, `_pubP`, `_more`, `_inOrder`,
    `_decodes`, `_pin`, `_carry`: seven of the letters that it leaves: by the make.
  `rowSays_list`: what the item says at a class in the list, unfolded: by the make: for a law that
    speaks of the group's list by places.
  `listClass_taken`, `sampleClass_taken`: under the promise's own `rowsHeld` and `membersHeld`, at
    an open class (and, for a moment's samples, that moment's open pin): every row of the class is
    among the rows that the group's test takes in (`Slice.runRows`).
  `rowSays_of_taken`: A CLOSER's WORDS PAY EVERY OPEN CLASS AT ONCE: from `AllSay rdE st (runRows st
    G).toList words`: what a closer's law ends in, and the premise ht of `Holds.of_begun`
    (Johnson/Desc/Means/Holds.lean).
  `classRows_in`, `says_congr`, `rowSays_back`: IT RIDES, BACKWARDS, under `Means.InOrder` of the
    statement in front (`says_extends`), where the reader gives the same words AT THE MESSAGES OF
    THE STATEMENT IN FRONT, BELOW THEIR TABLES' SIZES: what a row says reads the words there alone
    (`says_congr`: by `value`'s own text). (At EVERY index the equation would ask more
    than the sums read, and would be false of two witnesses that part beyond a table's end.)
Limits. (1) words IS A LETTER OF THIS FILE: the table's files fix the one reader of the
witness: it is laid in by FillRowFirst.lean, beside this file. (2) THE SENTENCE SAYS SOMETHING ONLY
BESIDE THE PROMISE: where the group is not there a class in the list is empty, a place beyond the
list's end is skipped, and a tenant at which no message sits has no row: there `rowSays` holds of
everything. `rowsHeld` and `membersHeld`, which stand in the promise at every border, say how many
rows lie there and who the members are. AT A MARKED STATE the promise gives neither: there the item
"no mark" stands among the open items and fails, so the relation holds of nobody. A member whose
list of sample rows is empty gives no row: that it holds its sample is the letter `held`'s to say.
(3) `PlacesApart` (no two oracle messages have one place in the book) is a premise of the samples'
lemma: shown of no state here; by report, not shown here, it follows from the named item
"K12.seatsCarried" with one test on the plan (the plan's list of places has no member twice). (4)
The converse (every row that the test takes in lies in some open class) is not typed: an opener does
not need it; a closer's law ends in all of them anyway. (5) No kind's law is laid against the
sentence here: K10's law's end gives `AllSay .. (runRows ..)` by EndSays.lean, beside this file,
under a premise that ties the typed message to the words. Nothing on soundness.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.Means.Holds
import OnBytes.Slice.BlkRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE)

/-- **The rows of a class of segment m, as they lie in the state.** A class in the list: the rows
of the segment's group's list of open rows at the class's places. A moment's samples: the sample
rows of the oracle messages whose place in the state's book is a tenant that the segment sends at
that moment. -/
def classRows (N : Numbers) (m : Nat) (c : RowClass) (s : S) : List OnBytes.Row :=
  match c with
  | .sample t =>
    (List.range s.st.oracles.size).flatMap fun o =>
      if (s.book.place[o]?).any fun x => (N.sent m t).contains x then
        ((s.st.oracles[o]?).map fun x => x.sampleRows.toList).getD []
      else []
  | c =>
    match s.st.groups[N.groupAt m]? with
    | none => []
    | some G => (List.range (N.rowsAt m c).2).filterMap fun j => G.rows[(N.rowsAt m c).1 + j]?

variable {P W : Type}

/-- **What the item "row m c" says**: every row of the class says its claim of the witness's words:
the library's own "what a row says of words". words: the one reader of the witness. -/
def rowSays (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (c : RowClass)
    (a : P × S) (y : Strs) (w : W) : Prop :=
  AllSay rdE a.2.st (classRows N m c a.2) (words a y w)

/-- **The layer**: the letter `row` is laid; every other letter is left as it was. -/
def fillRow (N : Numbers) (words : P × S → Strs → W → Words GE) (Mg : Meaning P W) :
    Meaning P W :=
  { Mg with row := rowSays N words }

theorem fillRow_row (N : Numbers) (words : P × S → Strs → W → Words GE) (Mg : Meaning P W) :
    (fillRow N words Mg).row = rowSays N words := rfl

/-- **What the item says at a class in the list, unfolded**: by the make. (For an opener's or a
closer's law that speaks of the group's list by places.) -/
theorem rowSays_list (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (c : RowClass)
    (hc : c.inList = true) (a : P × S) (y : Strs) (w : W) :
    rowSays N words m c a y w ↔
      AllSay rdE a.2.st
        (match a.2.st.groups[N.groupAt m]? with
          | none => []
          | some G => (List.range (N.rowsAt m c).2).filterMap fun j =>
              G.rows[(N.rowsAt m c).1 + j]?) (words a y w) := by
  cases c with
  | sample t => cases hc
  | carried => exact Iff.rfl
  | position => exact Iff.rfl
  | equation => exact Iff.rfl

/-- An open row that is no sample row is among the rows that the test takes in. -/
theorem mem_runRows_of_open (T : Statement) (G : Group) (r : OnBytes.Row) (hr : r ∈ G.rows.toList)
    (hk : r.kind ≠ .sample) : r ∈ (Slice.runRows T G).toList := by
  unfold Slice.runRows
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter]
  cases hkind : r.kind with
  | plain => exact Or.inl (Or.inl ⟨hr, rfl⟩)
  | sample => exact absurd hkind hk
  | generator => exact Or.inr ⟨hr, rfl⟩

theorem mem_rowSegs {O : List Item} {m : Nat} {c : RowClass} (h : Item.row m c ∈ O) :
    m ∈ rowSegs O := by
  unfold rowSegs
  rw [List.mem_eraseDups]
  exact List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- **A class in the list lies in what the test takes in**, where the promise's `rowsHeld` holds and
the class is open. -/
theorem listClass_taken (N : Numbers) (O : List Item) (s : S) (hR : rowsHeld N O s = true)
    (m : Nat) (c : RowClass) (hc : c.inList = true) (hO : Item.row m c ∈ O) (G : Group)
    (hG : s.st.groups[N.groupAt m]? = some G) :
    ∀ r ∈ classRows N m c s, r ∈ (Slice.runRows s.st G).toList := by
  intro r hr
  have h1 := List.all_eq_true.1 hR m (mem_rowSegs hO)
  rw [hG] at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := List.all_eq_true.1 h1.2 _ hO
  simp only [beq_self_eq_true, hc, Bool.and_self, Bool.not_true, Bool.false_or] at h2
  have hr' : r ∈ (List.range (N.rowsAt m c).2).filterMap fun j =>
      G.rows[(N.rowsAt m c).1 + j]? := by
    cases c with
    | sample t => cases hc
    | carried => simpa [classRows, hG] using hr
    | position => simpa [classRows, hG] using hr
    | equation => simpa [classRows, hG] using hr
  obtain ⟨j, hj, e⟩ := List.mem_filterMap.1 hr'
  have h3 := List.all_eq_true.1 h2 j hj
  rw [e] at h3
  have hk : r.kind = c.kind := by simpa using h3
  refine mem_runRows_of_open s.st G r (Array.mem_toList_iff.2 (Array.mem_of_getElem? e)) ?_
  rw [hk]
  cases c with
  | sample t => cases hc
  | carried => exact fun h => by cases h
  | position => exact fun h => by cases h
  | equation => exact fun h => by cases h

/-- No two oracle messages have one place in the book. -/
def PlacesApart (s : S) : Prop :=
  ∀ (o o' : Nat) (x : Nat × Nat), s.book.place[o]? = some x → s.book.place[o']? = some x → o = o'

/-- **A moment's samples lie in what the test takes in**, where the promise's `membersHeld` holds,
the class and the moment's pin are open, and no two messages have one place in the book. -/
theorem sampleClass_taken (N : Numbers) (O : List Item) (s : S) (hM : membersHeld N O s = true)
    (hA : PlacesApart s) (m t : Nat) (ht : t < 3) (hO : Item.row m (.sample t) ∈ O)
    (hP : Item.pin m t ∈ O) (G : Group) (hG : s.st.groups[N.groupAt m]? = some G) :
    ∀ r ∈ classRows N m (.sample t) s, r ∈ (Slice.runRows s.st G).toList := by
  intro r hr
  have h1 := List.all_eq_true.1 hM m (mem_rowSegs hO)
  rw [hG] at h1
  simp only [Bool.and_eq_true, sameMembers] at h1
  obtain ⟨o, -, ho⟩ := List.mem_flatMap.1 hr
  split at ho
  · rename_i hpl
    obtain ⟨x, hx, hin⟩ : ∃ x, s.book.place[o]? = some x ∧ (N.sent m t).contains x = true := by
      cases hq : s.book.place[o]? with
      | none => rw [hq] at hpl; cases hpl
      | some x => rw [hq] at hpl; exact ⟨x, rfl, hpl⟩
    cases hor : s.st.oracles[o]? with
    | none => rw [hor] at ho; cases ho
    | some X =>
      rw [hor] at ho
      have hr2 : r ∈ X.sampleRows.toList := ho
      -- the place is among the open pins' tenants: so a member sits there
      have hin2 : x ∈ (List.range 3).flatMap fun t' =>
          if O.contains (Item.pin m t') then N.sent m t' else [] := by
        refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, ?_⟩
        rw [if_pos (List.contains_iff_mem.2 hP)]
        exact List.contains_iff_mem.1 hin
      have h3 := List.contains_iff_mem.1 (List.all_eq_true.1 h1.2.2 x hin2)
      obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 h3
      obtain rfl := hA o o' x hx e'
      exact samples_taken s.st G ho' hor r hr2
  · cases ho

/-- **A CLOSER's WORDS PAY EVERY OPEN CLASS AT ONCE**: where all rows that the test takes in say
their claims of the words, so does every class of the segment that is open at the border. -/
theorem rowSays_of_taken (N : Numbers) (words : P × S → Strs → W → Words GE) (O : List Item)
    (a : P × S) (y : Strs) (w : W) (hR : rowsHeld N O a.2 = true)
    (hM : membersHeld N O a.2 = true) (hA : PlacesApart a.2) (m : Nat) (G : Group)
    (hG : a.2.st.groups[N.groupAt m]? = some G)
    (hP : ∀ t, Item.row m (.sample t) ∈ O → t < 3 ∧ Item.pin m t ∈ O)
    (h : AllSay rdE a.2.st (Slice.runRows a.2.st G).toList (words a y w)) :
    ∀ c, Item.row m c ∈ O → rowSays N words m c a y w := by
  intro c hc r hr
  cases hl : c.inList with
  | true => exact h r (listClass_taken N O a.2 hR m c hl hc G hG r hr)
  | false =>
    cases c with
    | sample t =>
      exact h r (sampleClass_taken N O a.2 hM hA m t (hP t hc).1 hc (hP t hc).2 G hG r hr)
    | carried => cases hl
    | position => cases hl
    | equation => cases hl

/-- At a statement in order every row of a class has passed the tests of the adding, at some group.
-/
theorem classRows_in (N : Numbers) (m : Nat) (c : RowClass) (s : S) (hI : InOrder s.st) :
    ∀ r ∈ classRows N m c s, ∃ G, RowIn s.st G r := by
  intro r hr
  have list : ∀ a n : Nat, (r ∈ match s.st.groups[N.groupAt m]? with
      | none => []
      | some G => (List.range n).filterMap fun j => G.rows[a + j]?) → ∃ G, RowIn s.st G r := by
    intro a n h
    cases hG : s.st.groups[N.groupAt m]? with
    | none => rw [hG] at h; cases h
    | some G =>
      rw [hG] at h
      obtain ⟨j, -, e⟩ := List.mem_filterMap.1 h
      exact ⟨G, hI.rows _ G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? e))⟩
  cases c with
  | carried => exact list _ _ hr
  | position => exact list _ _ hr
  | equation => exact list _ _ hr
  | sample t =>
    obtain ⟨o, -, ho⟩ := List.mem_flatMap.1 hr
    split at ho
    · cases hor : s.st.oracles[o]? with
      | none => rw [hor] at ho; cases ho
      | some X =>
        rw [hor] at ho
        exact ⟨_, hI.samples o X hor r ho⟩
    · cases ho

/-- What a row says of words reads the words at the statement's own messages, BELOW THE TABLES'
SIZES, alone. -/
theorem says_congr (T : Statement) (r : OnBytes.Row) (m m' : Words GE)
    (h : ∀ o, o < T.oracles.size → ∀ part i, i < tableSize T o part →
      m' o part i = m o part i) :
    Says rdE T r m' ↔ Says rdE T r m := by
  have e : value rdE T r m' = value rdE T r m := by
    unfold value onTable
    refine Finset.sum_congr rfl fun o ho => ?_
    have ho' := Finset.mem_range.1 ho
    congr 1 <;> exact Finset.sum_congr rfl fun i hi => by rw [h o ho' _ i (Finset.mem_range.1 hi)]
  unfold Says
  rw [e]

/-- **IT RIDES, BACKWARDS**: where the statement in front is in order, the statement behind extends
it, the class's rows in front are still among the class's rows behind, and the reader gives, AT THE
MESSAGES OF THE STATEMENT IN FRONT, the same words: what the item says behind, it says in front.
(A reader that reads the statement and the book gives other words at a message that is sent between
the two borders: so the words are asked to agree below the number of the messages in front alone;
and a witness's table may hold anything beyond a message's table's end: so they are asked to agree
BELOW THE TABLE's SIZE alone.) -/
theorem rowSays_back (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (c : RowClass)
    (a b : P × S) (y y' : Strs) (w w' : W) (hI : InOrder a.2.st) (hE : Extends a.2.st b.2.st)
    (hsub : ∀ r ∈ classRows N m c a.2, r ∈ classRows N m c b.2)
    (hw : ∀ o, o < a.2.st.oracles.size → ∀ part i, i < tableSize a.2.st o part →
      words b y' w' o part i = words a y w o part i)
    (h : rowSays N words m c b y' w') : rowSays N words m c a y w := by
  intro r hr
  obtain ⟨G, hG⟩ := classRows_in N m c a.2 hI r hr
  exact (says_congr a.2.st r _ _ hw).1 ((says_extends rdE hE hG _).1 (h r (hsub r hr)))

section
variable (N : Numbers) (words : P × S → Strs → W → Words GE) (Mg : Meaning P W)

/-! What the layer leaves: every other letter, by the make. -/

theorem fillRow_pub : (fillRow N words Mg).pub = Mg.pub := rfl
theorem fillRow_pubP : (fillRow N words Mg).pubP = Mg.pubP := rfl
theorem fillRow_more : (fillRow N words Mg).more = Mg.more := rfl
theorem fillRow_inOrder : (fillRow N words Mg).inOrder = Mg.inOrder := rfl
theorem fillRow_decodes : (fillRow N words Mg).decodes = Mg.decodes := rfl
theorem fillRow_pin : (fillRow N words Mg).pin = Mg.pin := rfl
theorem fillRow_carry : (fillRow N words Mg).carry = Mg.carry := rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.rowSays_list
#print axioms VerifiableInference.Desc.First.listClass_taken
#print axioms VerifiableInference.Desc.First.sampleClass_taken
#print axioms VerifiableInference.Desc.First.rowSays_of_taken
#print axioms VerifiableInference.Desc.First.classRows_in
#print axioms VerifiableInference.Desc.First.says_congr
#print axioms VerifiableInference.Desc.First.rowSays_back
