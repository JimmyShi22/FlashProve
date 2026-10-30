-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsItemRow.lean: THE ITEM row m c: ITS SENTENCE READS ONLY WHAT THE TABLE
BOOKS. Three theorems.

Why. An item `row m c` rides past 226 of the first chain's 358 sub-protocols; each one's fifth tie
asks `ReadsItemQR` of it (Johnson/Desc/Sound/ReadsItems.lean). Its sentence (`rowSays`,
Johnson/Desc/First/Close/Law/FillRow.lean) says of every row of a class that it holds of the
witness's words; the words of an oracle message are read at that message's place in the state's own
book. So the law is not unconditional: it wants that the class's rows name the group's members
alone, and that these sit at the segment's listed seats.

What is said. `wordsFirst_same`: at a state with three of the four facts of the pending rows' law
(msgShapes, bookInOrder, seatsCarried), the book as long as the statement, and the list's bound:
two witnesses that agree on the message and the pad at an oracle message's place give it the same
words. `members_listed`: inside the promise at a
border where a class of rows of segment m is open, without a mark, every member of the segment's
group has a place,
and it is one of the segment's listed seats. `readsItem_row`: `ReadsItemQR … k (.row m c)`.

The premises of the last: the meaning's sentence is `rowSays` at the ruled reader (at `mgAll`:
`mgAll_row`) · the two public items' texts, the index masks' listed seat, the list's bound, the
index masks' pin open at k (as in Johnson/Desc/K13/Law/ReadsK13R.lean) · the item itself open at k
(these two "open at k": closed tests on the written lists: typed by nobody yet) · the four facts and
"the statement is tidy" at reached states (FoldFacts' msgShapes, bookInOrder, seatsCarried,
pileMasks, tidy) · a moment's seats are the group's (by `Numbers.group`'s text at moments 0, 1, 2).

Limits. Nothing on soundness. It reaches the borders at which the index masks' pin is open.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsItemWo
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.Means.ItemsLen
import Johnson.Desc.Means.TestsBack
import Johnson.Desc.Sound.EvalKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open OnBytes.Means (Words wordsOn tableSize InOrder RowIn RowOn AllSay Says says_agree_in tidy4B
  tidy4B_iff)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers Comp RowClass classRows)
open VerifiableInference.Desc.Sound (MsgT Frame onQ meansQ sameQ ReadsItemQR wordsFirst
  wordsFirst_is wordsOn_congr tabFirst_at_door tab_congr)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB)

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- Two witnesses that agree at an oracle message's place give it the same words. -/
theorem wordsFirst_same (M : List OracleShape) (L : Laid) (s : S)
    (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true) (o : ℕ)
    (ho : o < s.st.oracles.size) (q : ℕ × ℕ) (hq : s.book.place[o]? = some q)
    (w w' : Desc.Wit Cells Tok MsgT) (hm : w.msg (arr q.1 q.2) = w'.msg (arr q.1 q.2))
    (hp : w.pad q.1 q.2 = w'.pad q.1 q.2) (part : OnBytes.Part) (i : ℕ) :
    wordsFirst arr s.st s.book w o part i = wordsFirst arr s.st s.book w' o part i := by
  obtain ⟨sh, q1, a1, a2, a3⟩ := tabFirst_at_door arr M L s.st s.book s.roots h₁ h₂ h₃ hs hb w o ho
  obtain ⟨sh', q2, b1, b2, b3⟩ :=
    tabFirst_at_door arr M L s.st s.book s.roots h₁ h₂ h₃ hs hb w' o ho
  obtain rfl : sh = sh' := Option.some.inj (a1.symm.trans b1)
  obtain rfl : q1 = q := Option.some.inj (a2.symm.trans hq)
  obtain rfl : q2 = q1 := Option.some.inj (b2.symm.trans hq)
  rw [wordsFirst_is, wordsFirst_is]
  refine wordsOn_congr s.st s.st _ _ o o rfl ?_ part i
  rw [a3, b3]
  exact (tab_congr w w' s.st.codes sh _ _ _ hm.symm hp.symm).symm

end

section
variable {A Pp Cells Tok : Type} {Fr : Frame}

/-- Inside the promise, the members of a segment's group sit at the segment's listed seats. -/
theorem members_listed (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Place) (get : A → Pp × S) (k m : ℕ) (c : RowClass)
    (hO : Item.row m c ∈ openAt links ps k) (a : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) (G : Group)
    (hG : (get a.1).2.st.groups[N.groupAt m]? = some G) (o : ℕ) (ho : o ∈ G.members.toList) :
    ∃ q, (get a.1).2.book.place[o]? = some q ∧ q ∈ N.group m := by
  obtain ⟨_, hr⟩ := ha
  obtain ⟨hB, _, _, _⟩ := hr.resolve_left (fun h => h hm)
  simp only [Bool.and_eq_true] at hB
  have hMH := hB.1.1.1.2
  unfold First.membersHeld at hMH
  have hseg : m ∈ First.rowSegs (openAt links ps k) :=
    List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨.row m c, hO, rfl⟩)
  have h1 := List.all_eq_true.1 hMH m hseg
  rw [hG] at h1
  simp only [Bool.and_eq_true] at h1
  have hsome := List.all_eq_true.1 h1.1 o ho
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨q, hq, ?_⟩
  have h2 := h1.2
  unfold First.sameMembers at h2
  simp only [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.1 h2.1 q (List.mem_filterMap.2 ⟨o, ho, hq⟩)
  have h4 : q ∈ (List.range 3).flatMap fun t =>
      if (openAt links ps k).contains (.pin m t) then N.sent m t else [] := by
    simpa using h3
  obtain ⟨t, ht, hqt⟩ := List.mem_flatMap.1 h4
  have ht3 : t < 3 := List.mem_range.1 ht
  have hqs : q ∈ N.sent m t := by
    split at hqt
    · exact hqt
    · exact absurd hqt (List.not_mem_nil)
  unfold Numbers.group
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · exact List.mem_append_left _ (List.mem_append_left _ hqs)
  · exact List.mem_append_left _ (List.mem_append_right _ hqs)
  · exact List.mem_append_right _ hqs

/-- **The item row m c.** -/
theorem readsItem_row (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (arr : ℕ → ℕ → ℕ)
    (M : List OracleShape) (L : Laid)
    (hII : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = indexThereC x.2)
    (hbelow : PlanBelow L N) (links : List ModelPart)
    (ps : List Place) (get : A → Pp × S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)
    (hpin : Item.pinI ∈ openAt links ps k) (m : ℕ) (c : RowClass)
    (hO : Item.row m c ∈ openAt links ps k)
    (hRow : ∀ x y w, Mg.row m c x y w ↔
      AllSay rdE x.2.st (classRows N m c x.2) (wordsFirst arr x.2.st x.2.book w))
    (hFacts : ∀ a, Rch k a → (get a.1).2.failed = none → FactsR13 M L (get a.1).2)
    (hTidy : ∀ a, Rch k a → (get a.1).2.failed = none → tidy4B (get a.1).2.st = true)
    (hSub : ∀ t, c = .sample t → ∀ x ∈ N.sent m t, x ∈ N.group m) :
    ReadsItemQR arr N Mg links ps get Rch k (.row m c) := by
  intro a w w' ha hr hm hop hnin hc hw
  clear hop hnin
  obtain ⟨_, _, hbk, _⟩ := promise_index N Mg links ps get k hpin a ha hm
  have hFa := hFacts a hr hm
  have hI : InOrder (get a.1).2.st := (tidy4B_iff.1 (hTidy a hr hm)).inOrder
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hb := below_of_plan hbelow (get a.1) ps[k]? hbk hFa.seats
  have hS : ∀ x ∈ N.group m, w.msg (arr x.1 x.2) = w'.msg (arr x.1 x.2) ∧
      w.pad x.1 x.2 = w'.pad x.1 x.2 := by
    intro x hx
    have hmem : ∀ d ∈ [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2],
        d ∈ (Item.row m c).reads arr N links :=
      fun d hd => List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hx, hd⟩)
    exact ⟨hc (.msg _) (hmem _ (by simp)), hc (.pad _ _) (hmem _ (by simp))⟩
  have W : ∀ o q, o < (get a.1).2.st.oracles.size → (get a.1).2.book.place[o]? = some q →
      q ∈ N.group m → ∀ part i,
      wordsFirst arr (get a.1).2.st (get a.1).2.book w o part i =
        wordsFirst arr (get a.1).2.st (get a.1).2.book w' o part i :=
    fun o q ho hq hqg part i =>
      wordsFirst_same arr M L (get a.1).2 hFa.shapes hFa.book hFa.seats hbk'.1.2 hb o ho q hq w w'
        (hS q hqg).1 (hS q hqg).2 part i
  have hw0 : Mg.row m c (get a.1) (Sound.strsOf Fr a.2) w := hw
  show Mg.row m c (get a.1) (Sound.strsOf Fr a.2) w'
  refine (hRow _ _ _).2 fun r hrm => ?_
  have hr0 := (hRow _ _ _).1 hw0 r hrm
  have hlt : ∀ o q, (get a.1).2.book.place[o]? = some q → o < (get a.1).2.st.oracles.size := by
    intro o q hq
    rw [← hbk'.1.2]
    exact (Array.getElem?_eq_some_iff.1 hq).1
  unfold classRows at hrm
  split at hrm
  · rename_i t
    obtain ⟨o, _, hro⟩ := List.mem_flatMap.1 hrm
    split at hro
    · rename_i hany
      cases hq : (get a.1).2.book.place[o]? with
      | none => simp [hq] at hany
      | some q =>
        have hqs : q ∈ N.sent m t := by simpa [hq] using hany
        cases hx : (get a.1).2.st.oracles[o]? with
        | none => simp [hx] at hro
        | some x =>
          have hrx : r ∈ x.sampleRows.toList := by simpa [hx] using hro
          have hOn : RowIn (get a.1).2.st { code := 0, members := #[o] } r :=
            hI.samples o x hx r hrx
          refine (says_agree_in rdE hOn fun o' ho' part i _ => ?_).1 hr0
          have e : o' = o := by simpa using ho'
          subst e
          exact W o' q (hlt o' q hq) hq (hSub t rfl q hqs) part i
    · exact absurd hro (List.not_mem_nil)
  · split at hrm
    · exact absurd hrm (List.not_mem_nil)
    · rename_i G hG
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 hrm
      have hrG : r ∈ G.rows.toList := by
        rw [Array.mem_toList_iff]
        exact Array.mem_of_getElem? hj
      refine (says_agree_in rdE (hI.rows _ G hG r hrG) fun o ho part i _ => ?_).1 hr0
      obtain ⟨q, hq, hqg⟩ := members_listed N Mg links ps get k m c hO a ha hm G hG o ho
      exact W o q (hlt o q hq) hq hqg part i

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.wordsFirst_same
#print axioms VerifiableInference.Desc.K13.Law.members_listed
#print axioms VerifiableInference.Desc.K13.Law.readsItem_row
