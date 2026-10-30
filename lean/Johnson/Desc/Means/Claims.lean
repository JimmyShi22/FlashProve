-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Claims.lean: what a statement still claims, so that a proximity test takes the
claims off it.

Holds (Johnson/Desc/Means/Holds.lean) counts every sample row of every oracle message, at every
statement. But the beginning of a proximity test hands the members' sample rows to the batching and
leaves them where they lie. So a false sample row would make Holds false for ever, and no joint
would be made to catch it. Claims counts a message's sample rows only as long as the message is
pending: a member of no group whose test has begun. Then the beginning of a test takes off the
statement both the group's open rows and the members' sample rows, and hands them to the batching.

This file shows: backwards over the beginning of a test (Claims.of_begun); the joint at a batching,
for open rows and sample rows alike (claims_catches); backwards over every other effect (Claims.back
and its cases); and that a statement whose groups are all in their tests, hold no open row, and have
every message with a sample row as a member, claims nothing (claims_end).
So along a chain from a statement of which Claims is false to an end that meets claims_end, Claims
turns from false to true at some step; of the effects shown here none but the beginning of a test
can do that; and there the batched row holds at few multipliers.

Beside this file. The same of the plain functions: Johnson/Desc/Means/ClaimsP.lean. That a message
is pending when its sample rows are written, so that a false sample row makes Claims false at once:
Johnson/Desc/Means/Entry.lean. The joint as one count: Johnson/Desc/Means/Joint.lean. Along a chain:
over the beginnings of its tests the argument above is stated as a theorem nowhere in this folder:
Johnson/Desc/Means/Walk.lean carries tidiness alone (see LIMIT there).

Main definitions: Pending, Claims.
Main theorems: Claims.of_begun, claims_catches, Claims.back, Claims.of_withRow, Claims.of_withGroup,
Claims.of_joined, Claims.of_stSent, Claims.of_admitted, Claims.of_onOracle, Claims.of_closeLedgers,
claims_end.

What is not claimed. That the end of a chain meets the conditions of claims_end. No chance is named.
Nothing on soundness.

-/
import Johnson.Desc.Means.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {S S' : Statement} {G : Group}

/-- The oracle message o is a member of no group whose proximity test has begun. -/
def Pending (S : Statement) (o : Nat) : Prop :=
  ∀ (g : Nat) (G : Group), S.groups[g]? = some G → o ∈ G.members.toList → G.inRun = false

/-- Pending goes on to a later statement in which each group that has o either is in no test or was
there before, with o and with the same mark. -/
theorem Pending.later {o : Nat} (h : Pending S o)
    (hg : ∀ (g : Nat) (G' : Group), S'.groups[g]? = some G' → o ∈ G'.members.toList →
      G'.inRun = false ∨ ∃ G, S.groups[g]? = some G ∧ o ∈ G.members.toList ∧ G'.inRun = G.inRun) :
    Pending S' o := by
  intro g G' hG' ho
  rcases hg g G' hG' ho with c | ⟨G, hG, hm, e⟩
  · exact c
  · rw [e]
    exact h g G hG hm

theorem Pending.sameGroups {o : Nat} (h : Pending S o) (hg : S'.groups = S.groups) :
    Pending S' o :=
  fun g G hG => h g G (hg ▸ hG)

/-- A change of one group that leaves its members and its mark. -/
theorem Pending.oneGroup {o : Nat} (h : Pending S o) (g : Nat) (f : Group → Group)
    (hg : S'.groups = S.groups.modify g f) (h1 : ∀ G, (f G).members = G.members)
    (h2 : ∀ G, (f G).inRun = G.inRun) : Pending S' o := by
  refine h.later fun g' G' hG' ho => Or.inr ?_
  rw [hg, Array.getElem?_modify] at hG'
  by_cases c : g = g'
  · rw [if_pos c] at hG'
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hG'
    exact ⟨G, hG, by rw [← h1]; exact ho, h2 G⟩
  · rw [if_neg c] at hG'
    exact ⟨G', hG', ho, rfl⟩

variable {K : Type} [CommRing K] (ρ : Reading K) {m : Words K}

/-- What the statement still claims holds of the words: every open row of every group, and every
sample row of every oracle message that is pending. -/
structure Claims (S : Statement) (m : Words K) : Prop where
  rows : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → AllSay ρ S G.rows.toList m
  samples : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x → Pending S o →
    AllSay ρ S x.sampleRows.toList m

/-- All that a statement claims includes what it still claims. -/
theorem Holds.claims (h : Holds ρ S m) : Claims ρ S m :=
  ⟨h.rows, fun o x hx _ => h.samples o x hx⟩

/-! ## The beginning of a test -/

/-- What is no member of the group stays pending over the beginning of its test. -/
theorem Pending.begun {o : Nat} (h : Pending S o) (g : Nat) (G : Group)
    (hG : S.groups[g]? = some G) (ho : o ∉ G.members.toList) : Pending (Slice.begun S g G) o := by
  refine h.later fun g' G' hG' hm => Or.inr ?_
  rw [begun_groups, Array.getElem?_modify] at hG'
  by_cases c : g = g'
  · subst c
    rw [if_pos rfl, hG] at hG'
    obtain rfl := Option.some.inj hG'
    exact absurd hm ho
  · rw [if_neg c] at hG'
    exact ⟨G', hG', hm, rfl⟩

/-- **Backwards over the beginning of a test**: if what the statement behind still claims holds, and
the rows that the test takes in hold, what the statement in front claimed held. -/
theorem Claims.of_begun (hI : InOrder S) (hK : OpenKinds S) (g : Nat) (G : Group)
    (hG : S.groups[g]? = some G) (h : Claims ρ (Slice.begun S g G) m)
    (ht : AllSay ρ S (Slice.runRows S G).toList m) : Claims ρ S m := by
  have hE := extends_begun S g G
  refine ⟨fun g' G' hG' r hr' => ?_, fun o x hx hp r hr' => ?_⟩
  · by_cases c : g = g'
    · subst c
      rw [hG] at hG'
      obtain rfl := Option.some.inj hG'
      exact ht r (open_taken hK g G hG r hr')
    · have e : (Slice.begun S g G).groups[g']? = some G' := by
        rw [begun_groups, Array.getElem?_modify, if_neg c]
        exact hG'
      exact (says_extends ρ hE (hI.rows g' G' hG' r hr') m).1 (h.rows g' G' e r hr')
  · by_cases ho : o ∈ G.members.toList
    · exact ht r (samples_taken S G ho hx r hr')
    · have e := closeLedgers_sampleRows G.members.toList S o
      rw [hx] at e
      have e' : ((Slice.begun S g G).oracles[o]?).map (fun x : Oracle => x.sampleRows) =
          some x.sampleRows := e
      obtain ⟨x', hx', hsame⟩ := Option.map_eq_some_iff.1 e'
      have hr'' : r ∈ x'.sampleRows.toList := by
        rw [hsame]
        exact hr'
      exact (says_extends ρ hE (hI.samples o x hx r hr') m).1
        (h.samples o x' hx' (hp.begun g G hG ho) r hr'')

/-- **The joint at a batching, for open rows and sample rows alike.** For words of which not all
holds that the statement in front of a proximity test still claims: either not all holds that the
statement behind still claims, or the elements of K as which x reads, for some x at which the
batched row holds of tables that hold the words on the blocks, are fewer than the rows that the test
takes in. A member's sample rows are no longer among what the statement behind claims. -/
theorem claims_catches [IsDomain K] [Finite K] (hI : InOrder S) (hK : OpenKinds S)
    (g : Nat) (G : Group) (hG : S.groups[g]? = some G) (hbad : ¬ Claims ρ S m) :
    ¬ Claims ρ (Slice.begun S g G) m ∨
    Nat.card {y : K // ∃ (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
      Bat.combine (Slice.begun S g G) g ⟨layoutOf S G, Slice.runRows S G⟩ x = some out ∧
      LaidOn (Slice.begun S g G) (layoutOf S G) m T ∧
      GroupSays ρ (Slice.begun S g G) (layoutOf S G) out T} ≤ (Slice.runRows S G).size - 1 := by
  by_cases hb : Claims ρ (Slice.begun S g G) m
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
      exact hbad (Claims.of_begun ρ hI hK g G hG hb
        fun r hr => (says_extends ρ hE (hrows r hr) m).1 (c r hr))
    exact combine_catches ρ (Slice.begun S g G) g _ (layoutOf S G) (Slice.runRows S G) hG' hL' hOk'
      (fun r h => RowIn.extends (G := G) hE (fun _ c => c) (hrows r h)) m hnot
  · exact Or.inl hb

/-! ## Every other effect -/

/-- **Backwards along a chain**: the later statement still has the rows, and what was pending is
pending. -/
theorem Claims.back (hI : InOrder S) (hE : Extends S S')
    (hr : ∀ (g : Nat) (G : Group), S.groups[g]? = some G →
      ∃ G', S'.groups[g]? = some G' ∧ ∀ r ∈ G.rows.toList, r ∈ G'.rows.toList)
    (hs : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x →
      ∃ x' : Oracle, S'.oracles[o]? = some x' ∧ ∀ r ∈ x.sampleRows.toList, r ∈ x'.sampleRows.toList)
    (hp : ∀ o, Pending S o → Pending S' o) (h : Claims ρ S' m) : Claims ρ S m := by
  refine ⟨fun g G hG r hr' => ?_, fun o x hx hpo r hr' => ?_⟩
  · obtain ⟨G', hG', hsub⟩ := hr g G hG
    exact (says_extends ρ hE (hI.rows g G hG r hr') m).1 (h.rows g G' hG' r (hsub r hr'))
  · obtain ⟨x', hx', hsub⟩ := hs o x hx
    exact (says_extends ρ hE (hI.samples o x hx r hr') m).1
      (h.samples o x' hx' (hp o hpo) r (hsub r hr'))

theorem Claims.of_withRow (hI : InOrder S) (g : Nat) (row : Row) (hG : S.groups[g]? = some G)
    (h : Claims ρ (Slice.withRow S g row) m) : Claims ρ S m ∧ Says ρ S row m := by
  refine ⟨Claims.back ρ hI (extends_withRow S g row)
    (rows_modify (f := fun G => { G with rows := G.rows.push row }) fun G r hr => by
      show r ∈ (G.rows.push row).toList
      simp [hr])
    (fun o x hx => ⟨x, hx, fun _ c => c⟩)
    (fun o hp => hp.oneGroup g (fun G => { G with rows := G.rows.push row }) rfl (fun _ => rfl)
      (fun _ => rfl)) h, ?_⟩
  have e := h.rows g _ (Slice.withRow_group S g row G hG) row (by simp)
  unfold Says at e ⊢
  rw [value_congr ρ (S := S) (S' := Slice.withRow S g row) rfl rfl] at e
  exact e

theorem Claims.of_withGroup (hI : InOrder S) (a b : Nat)
    (h : Claims ρ (Slice.withGroup S a b) m) : Claims ρ S m := by
  refine Claims.back ρ hI (extends_withGroup S a b) (fun g G hG => ⟨G, ?_, fun _ c => c⟩)
    (fun o x hx => ⟨x, hx, fun _ c => c⟩) (fun o hp => hp.later fun g G' hG' ho => ?_) h
  · show (S.groups.push { code := a, maskCode := b })[g]? = some G
    have hg : g < S.groups.size := by
      by_contra c
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hG
      cases hG
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hg)]
    exact hG
  · have hG'' : (S.groups.push { code := a, maskCode := b })[g]? = some G' := hG'
    rw [Array.getElem?_push] at hG''
    by_cases c : g = S.groups.size
    · rw [if_pos c] at hG''
      obtain rfl := Option.some.inj hG''
      exact Or.inl rfl
    · rw [if_neg c] at hG''
      exact Or.inr ⟨G', hG'', ho, rfl⟩

/-- A message joins a group whose test has not begun. -/
theorem Claims.of_joined (hI : InOrder S) (g o : Nat) (k : Bool) (G : Group)
    (hG : S.groups[g]? = some G) (hrun : G.inRun = false)
    (h : Claims ρ (Slice.withMessageInGroup S g o k G) m) : Claims ρ S m := by
  refine Claims.back ρ hI (extends_withMessageInGroup S g o k G)
    (rows_modify (f := fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k })
      fun _ _ c => c)
    (samples_modify (f := fun x => { x with groups := x.groups ++ [g] }) fun _ _ _ c => c)
    (fun o' hp => hp.later fun g' G' hG' ho' => ?_) h
  have hG'' : (S.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k })[g']? = some G' :=
    hG'
  rw [Array.getElem?_modify] at hG''
  by_cases c : g = g'
  · subst c
    rw [if_pos rfl, hG] at hG''
    obtain rfl := Option.some.inj hG''
    exact Or.inl hrun
  · rw [if_neg c] at hG''
    exact Or.inr ⟨G', hG'', ho', rfl⟩

theorem Claims.of_stSent (hI : InOrder S) (sent : Array OracleNotice)
    (h : Claims ρ (Slice.stSent S sent) m) : Claims ρ S m := by
  refine Claims.back ρ hI (extends_stSent S sent) (fun g G hG => ⟨G, hG, fun _ c => c⟩)
    (fun o x hx => ⟨x, ?_, fun _ c => c⟩) (fun o hp => hp.sameGroups rfl) h
  have ho : o < S.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  rw [Slice.stSent_old S sent o ho]
  exact hx

theorem Claims.of_admitted (hI : InOrder S) (hN : NoneYet S) (o : Nat) (s : OracleShape)
    (p : List PadPlace) (rows : Array Row)
    (hs : ∀ x : Oracle, S.oracles[o]? = some x → x.sampled = false)
    (h : Claims ρ (Slice.admitted S o s p rows) m) : Claims ρ S m :=
  Claims.back ρ hI (extends_admitted S o s p rows) (fun g G hG => ⟨G, hG, fun _ c => c⟩)
    (samples_modify (f := fun x => { x with
      sampled := true, sampleRows := rows, pad := p.map fun q => (q.part, q.index),
      ledger := Slice.freshLedger S.codes s }) fun x hx r hr => by
        rw [hN o x hx (hs x hx)] at hr
        simp at hr) (fun o' hp => hp.sameGroups rfl) h

theorem Claims.of_onOracle (hI : InOrder S) (o : Nat) (f : Oracle → Oracle)
    (h1 : ∀ x, (f x).shape = x.shape) (h2 : ∀ x, (f x).sampleRows = x.sampleRows)
    (h : Claims ρ { S with oracles := S.oracles.modify o f } m) : Claims ρ S m :=
  Claims.back (S' := { S with oracles := S.oracles.modify o f }) ρ hI
    (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ h1)
    (fun g G hG => ⟨G, hG, fun _ c => c⟩)
    (samples_modify (f := f) fun x _ r hr => by rw [h2]; exact hr)
    (fun o' hp => hp.sameGroups rfl) h

theorem Claims.of_closeLedgers (hI : InOrder S) (l : List Nat)
    (h : Claims ρ (Slice.closeLedgers S l) m) : Claims ρ S m := by
  refine Claims.back ρ hI (extends_closeLedgers S l)
    (fun g G hG => ⟨G, by rw [closeLedgers_groups]; exact hG, fun _ c => c⟩)
    (fun o x hx => ?_) (fun o hp => hp.sameGroups (closeLedgers_groups l S)) h
  have e := closeLedgers_sampleRows l S o
  rw [hx] at e
  obtain ⟨x', hx', hsame⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', hx', fun r hr => by rw [hsame]; exact hr⟩

/-! ## The end of a chain -/

/-- **A statement that claims nothing any more.** If every group's test has begun, no group holds an
open row, and every oracle message that has a sample row is a member of a group, then what the
statement still claims holds of all words. -/
theorem claims_end (hall : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → G.inRun = true)
    (hnone : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → G.rows = #[])
    (hmem : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x → x.sampleRows ≠ #[] →
      ∃ (g : Nat) (G : Group), S.groups[g]? = some G ∧ o ∈ G.members.toList) (m : Words K) :
    Claims ρ S m := by
  refine ⟨fun g G hG r hr => ?_, fun o x hx hp r hr => ?_⟩
  · rw [hnone g G hG] at hr
    simp at hr
  · have hne : x.sampleRows ≠ #[] := by
      intro c
      rw [c] at hr
      simp at hr
    obtain ⟨g, G, hG, ho⟩ := hmem o x hx hne
    have c := hp g G hG ho
    rw [hall g G hG] at c
    cases c

end OnBytes.Means
