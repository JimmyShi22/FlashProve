-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Holds.lean: all that a statement claims, as one proposition on words, from joint
to joint.

Holds says of a statement and words: every open row of every group and every sample row of every
oracle message holds of the words. This file shows how it goes backwards along a chain: if it holds
of a later statement that still has the rows, it held of the earlier one (Holds.back); behind the
beginning of a proximity test it held before if it holds behind and the rows that the test takes in
hold (Holds.of_begun); and so, for words of which the statement in front of a test does not hold,
either the statement behind does not hold, or the batched row holds at few multipliers
(begin_catches).

A limit of Holds. It counts a message's sample rows at every statement, also behind the test that
has taken them in. So words of which a member's sample row fails make "the statement behind does not
hold" true for nothing, and begin_catches says something of the group's open rows alone. The
proposition that lets a test take both sorts of rows off the statement is Claims
(Johnson/Desc/Means/Claims.lean), which spends this file's OpenKinds, open_taken and samples_taken.

A proximity test takes in the open rows by their marks, plain rows and generator rows: an open row
that were marked as a sample row would be left out, and its claim lost. OpenKinds says that there is
none; the adding of a row tests it.

Main definitions: Holds, OpenKinds.
Main theorems: Holds.back, open_taken, samples_taken, Holds.of_begun, begin_catches; kind_of_rowL,
OpenKinds.start, OpenKinds.sameGroups, OpenKinds.oneGroup, OpenKinds.withGroup, OpenKinds.withRow,
OpenKinds.withMessageInGroup, OpenKinds.begun, addRowP_kinds.

What is not claimed. That every plain function of the page keeps OpenKinds: it is shown of the
effects on groups and of the adding; the others leave the groups as they are
(OpenKinds.sameGroups). No chance is named. Nothing on soundness.

-/
import Johnson.Desc.Means.Page
import Johnson.Desc.Means.Catches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc.Ground Desc.Plain

variable {S S' : Statement} {G : Group}

/-! ## No open row is marked as a sample row -/

/-- No open row is marked as a sample row. -/
def OpenKinds (S : Statement) : Prop :=
  ∀ (g : Nat) (G : Group), S.groups[g]? = some G → ∀ r ∈ G.rows.toList, r.kind ≠ .sample

theorem OpenKinds.start (codes : Codes) :
    OpenKinds { codes := codes, oracles := #[], groups := #[] } :=
  fun g G h => by simp at h

theorem OpenKinds.sameGroups (h : OpenKinds S) (hg : S'.groups = S.groups) : OpenKinds S' :=
  fun g G hG => h g G (hg ▸ hG)

theorem OpenKinds.oneGroup (h : OpenKinds S) (g : Nat) (f : Group → Group)
    (hg : S'.groups = S.groups.modify g f)
    (hf : ∀ G, S.groups[g]? = some G → ∀ r ∈ (f G).rows.toList, r.kind ≠ .sample) :
    OpenKinds S' := by
  intro g' G' hG'
  rw [hg, Array.getElem?_modify] at hG'
  by_cases c : g = g'
  · rw [if_pos c] at hG'
    obtain ⟨G, h1, rfl⟩ := Option.map_eq_some_iff.1 hG'
    exact hf G (by rw [c]; exact h1)
  · rw [if_neg c] at hG'
    exact h g' G' hG'

theorem OpenKinds.withGroup (h : OpenKinds S) (a b : Nat) : OpenKinds (Slice.withGroup S a b) := by
  intro g G hG
  have hG' : (S.groups.push { code := a, maskCode := b })[g]? = some G := hG
  rw [Array.getElem?_push] at hG'
  by_cases c : g = S.groups.size
  · rw [if_pos c] at hG'
    obtain rfl := Option.some.inj hG'
    intro r hr
    simp at hr
  · rw [if_neg c] at hG'
    exact h g G hG'

theorem OpenKinds.withRow (h : OpenKinds S) (g : Nat) (row : Row) (hk : row.kind ≠ .sample) :
    OpenKinds (Slice.withRow S g row) := by
  refine h.oneGroup g (fun G => { G with rows := G.rows.push row }) rfl fun G hG r hr => ?_
  have hr' : r ∈ (G.rows.push row).toList := hr
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr'
  rcases hr' with c | rfl
  · exact h g G hG r c
  · exact hk

theorem OpenKinds.withMessageInGroup (h : OpenKinds S) (g o : Nat) (k : Bool) (G : Group) :
    OpenKinds (Slice.withMessageInGroup S g o k G) :=
  h.oneGroup g (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k }) rfl
    fun G' hG' r hr => h g G' hG' r hr

theorem begun_groups (S : Statement) (g : Nat) (G : Group) : (Slice.begun S g G).groups =
    S.groups.modify g fun G => { G with inRun := true, rows := #[] } := by
  have e : (Slice.begun S g G).groups = (Slice.closeLedgers S G.members.toList).groups.modify g
      fun G => { G with inRun := true, rows := #[] } := rfl
  rw [e, closeLedgers_groups]

theorem OpenKinds.begun (h : OpenKinds S) (g : Nat) (G : Group) :
    OpenKinds (Slice.begun S g G) :=
  h.oneGroup g _ (begun_groups S g G) fun G' _ r hr => by simp at hr

/-- A row that passes the clauses of the adding is not marked as a sample row. -/
theorem kind_of_rowL {g : Nat} {row : Row} (h : ok (rowL S g row) = true) :
    row.kind ≠ .sample := by
  simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simpa using h.2.2.1

/-- The adding of a row keeps it. -/
theorem addRowP_kinds {Lc : Type} {d d' : DState Lc} {g : Nat} {row : Row}
    (h : addRowP d g row = some d') (hK : OpenKinds d.st) : OpenKinds d'.st := by
  unfold addRowP at h
  by_cases c : ok (rowL d.st g row) = true
  · rw [if_pos c] at h
    obtain rfl := Option.some.inj h
    exact hK.withRow g row (kind_of_rowL c)
  · rw [if_neg c] at h
    cases h

/-! ## What a proximity test takes in -/

/-- **Every open row of the group is among the rows that its proximity test takes in.** -/
theorem open_taken (hK : OpenKinds S) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    ∀ r ∈ G.rows.toList, r ∈ (Slice.runRows S G).toList := by
  intro r hr
  have hk := hK g G hG r hr
  unfold Slice.runRows
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter]
  cases hkind : r.kind with
  | plain => exact Or.inl (Or.inl ⟨hr, rfl⟩)
  | sample => exact absurd hkind hk
  | generator => exact Or.inr ⟨hr, rfl⟩

/-- Every sample row of a member is among them too. -/
theorem samples_taken (S : Statement) (G : Group) {o : Nat} {x : Oracle}
    (ho : o ∈ G.members.toList) (hx : S.oracles[o]? = some x) :
    ∀ r ∈ x.sampleRows.toList, r ∈ (Slice.runRows S G).toList := by
  intro r hr
  have gen : ∀ (l : List Nat) (a : Array Row), (r ∈ a.toList ∨ o ∈ l) →
      r ∈ (l.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) a).toList := by
    intro l
    induction l with
    | nil =>
      intro a h
      rcases h with c | c
      · exact c
      · cases c
    | cons o' l ih =>
      intro a h
      rw [List.foldl_cons]
      apply ih
      rcases h with c | c
      · exact Or.inl (by simp [c])
      · rcases List.mem_cons.1 c with e | e
        · subst e
          exact Or.inl (by simp [hx, hr])
        · exact Or.inr e
  unfold Slice.runRows
  simp only [Array.toList_append, List.mem_append]
  refine Or.inl (Or.inr ?_)
  rw [← Array.foldl_toList]
  exact gen _ _ (Or.inr ho)

/-! ## All that a statement claims -/

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Every open row of every group and every sample row of every oracle message holds of the
words. -/
structure Holds (S : Statement) (m : Words K) : Prop where
  rows : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → AllSay ρ S G.rows.toList m
  samples : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x → AllSay ρ S x.sampleRows.toList m

/-- **Backwards along a chain**: if all that a later statement claims holds, and the later statement
still has every open row and every sample row of the earlier one, all that the earlier one claimed
held. -/
theorem Holds.back {m : Words K} (hI : InOrder S) (hE : Extends S S')
    (hr : ∀ (g : Nat) (G : Group), S.groups[g]? = some G →
      ∃ G', S'.groups[g]? = some G' ∧ ∀ r ∈ G.rows.toList, r ∈ G'.rows.toList)
    (hs : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x →
      ∃ x' : Oracle, S'.oracles[o]? = some x' ∧ ∀ r ∈ x.sampleRows.toList, r ∈ x'.sampleRows.toList)
    (h : Holds ρ S' m) : Holds ρ S m := by
  refine ⟨fun g G hG r hr' => ?_, fun o x hx r hr' => ?_⟩
  · obtain ⟨G', hG', hsub⟩ := hr g G hG
    exact (says_extends ρ hE (hI.rows g G hG r hr') m).1 (h.rows g G' hG' r (hsub r hr'))
  · obtain ⟨x', hx', hsub⟩ := hs o x hx
    exact (says_extends ρ hE (hI.samples o x hx r hr') m).1 (h.samples o x' hx' r (hsub r hr'))

/-- **Backwards over the beginning of a test**: if all that the statement behind claims holds, and
the rows that the test takes in hold, all that the statement in front claimed held. -/
theorem Holds.of_begun {m : Words K} (hI : InOrder S) (hK : OpenKinds S) (g : Nat) (G : Group)
    (hG : S.groups[g]? = some G) (h : Holds ρ (Slice.begun S g G) m)
    (ht : AllSay ρ S (Slice.runRows S G).toList m) : Holds ρ S m := by
  have hE := extends_begun S g G
  refine ⟨fun g' G' hG' r hr' => ?_, fun o x hx r hr' => ?_⟩
  · by_cases c : g = g'
    · subst c
      rw [hG] at hG'
      obtain rfl := Option.some.inj hG'
      exact ht r (open_taken hK g G hG r hr')
    · have e : (Slice.begun S g G).groups[g']? = some G' := by
        rw [begun_groups, Array.getElem?_modify, if_neg c]
        exact hG'
      exact (says_extends ρ hE (hI.rows g' G' hG' r hr') m).1 (h.rows g' G' e r hr')
  · have e := closeLedgers_sampleRows G.members.toList S o
    rw [hx] at e
    have e' : ((Slice.begun S g G).oracles[o]?).map (fun x : Oracle => x.sampleRows) =
        some x.sampleRows := e
    obtain ⟨x', hx', hsame⟩ := Option.map_eq_some_iff.1 e'
    have hr'' : r ∈ x'.sampleRows.toList := by
      rw [hsame]
      exact hr'
    exact (says_extends ρ hE (hI.samples o x hx r hr') m).1 (h.samples o x' hx' r hr'')

/-- **A batching, for the group's open rows.** For words of which not all holds that the statement
in front of a proximity test claims: either not all holds that the statement behind claims, or the
elements of K as which x reads, for some x at which the batched row holds of tables that hold the
words on the blocks, are fewer than the rows that the test takes in. Where a member's sample row
fails, the first alternative is true for nothing, since the statement behind keeps the row: for both
sorts of rows see claims_catches (Johnson/Desc/Means/Claims.lean). -/
theorem begin_catches [IsDomain K] [Finite K] {m : Words K} (hI : InOrder S) (hK : OpenKinds S)
    (g : Nat) (G : Group) (hG : S.groups[g]? = some G) (hbad : ¬ Holds ρ S m) :
    ¬ Holds ρ (Slice.begun S g G) m ∨
    Nat.card {y : K // ∃ (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
      Bat.combine (Slice.begun S g G) g ⟨layoutOf S G, Slice.runRows S G⟩ x = some out ∧
      LaidOn (Slice.begun S g G) (layoutOf S G) m T ∧
      GroupSays ρ (Slice.begun S g G) (layoutOf S G) out T} ≤ (Slice.runRows S G).size - 1 := by
  by_cases hb : Holds ρ (Slice.begun S g G) m
  · right
    have hE := extends_begun S g G
    have hOk := hI.groups g G hG
    have hrows := hI.runRows g G hG
    have hG' := begun_group S g G hG
    have hOk' : GroupOk (Slice.begun S g G) { G with inRun := true, rows := #[] } :=
      hOk.extends hE rfl rfl rfl rfl
    have hL' : (Slice.begun S g G).layout g = some (layoutOf S G) := by
      rw [layout_eq _ g _ hG',
        layoutOf_extends (G' := { G with inRun := true, rows := #[] }) hE hOk rfl rfl rfl rfl]
    have hnot : ¬ AllSay ρ (Slice.begun S g G) (Slice.runRows S G).toList m := by
      intro c
      exact hbad (Holds.of_begun ρ hI hK g G hG hb
        fun r hr => (says_extends ρ hE (hrows r hr) m).1 (c r hr))
    exact combine_catches ρ (Slice.begun S g G) g _ (layoutOf S G) (Slice.runRows S G) hG' hL' hOk'
      (fun r h => RowIn.extends (G := G) hE (fun _ c => c) (hrows r h)) m hnot
  · exact Or.inl hb

end OnBytes.Means
