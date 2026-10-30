-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Entry.lean: a sample row enters what the statement claims at the moment at which
it is written.

Claims (Johnson/Desc/Means/Claims.lean) counts a message's sample rows as long as the message is
pending: a member of no group whose test has begun. So a false sample row makes Claims false only if
its message is pending when the row is written. This file shows that it is: every member of a group
is marked as sampled (SampledMembers: the joining tests the mark, and no effect takes a mark back),
and the writing of sample rows tests that the message is not marked; so the message is in no group
at all. With that: if Claims holds behind the admitting, it held in front, and the rows that were
written hold (Claims.of_admitted_rows, admitP_enters). That Claims drops a message's sample rows for
good rests on the same two facts: a member of a group is marked, and both functions that write
sample rows test that the message is not marked. No theorem here says that in one sentence.

Main definitions: SampledMembers. Main theorems: pending_of_unsampled, Claims.of_admitted_rows,
admitP_enters; SampledMembers.start, SampledMembers.later, and ‹f›_members for the plain functions
of Johnson/Desc/First/Base/Ground.lean.

What is not claimed. The like of admitP_enters for the copying of sample rows from another
statement. That a block changes the statement by these functions alone. Nothing on soundness.

-/
import Johnson.Desc.Means.ClaimsP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc.Ground Desc.Plain

variable {S S' : Statement} {G : Group}

/-- Every member of a group is an oracle message that is there and is marked as sampled. -/
def SampledMembers (S : Statement) : Prop :=
  ∀ (g : Nat) (G : Group), S.groups[g]? = some G → ∀ o ∈ G.members.toList,
    ∃ x : Oracle, S.oracles[o]? = some x ∧ x.sampled = true

theorem SampledMembers.start (codes : Codes) :
    SampledMembers { codes := codes, oracles := #[], groups := #[] } :=
  fun g G h => by simp at h

/-- It goes on to a later statement in which no mark is taken back, and each member of a group
either was a member of the group at that number or is marked. -/
theorem SampledMembers.later (h : SampledMembers S)
    (hm : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x → x.sampled = true →
      ∃ x' : Oracle, S'.oracles[o]? = some x' ∧ x'.sampled = true)
    (hg : ∀ (g : Nat) (G' : Group), S'.groups[g]? = some G' → ∀ o ∈ G'.members.toList,
      (∃ G, S.groups[g]? = some G ∧ o ∈ G.members.toList) ∨
        ∃ x' : Oracle, S'.oracles[o]? = some x' ∧ x'.sampled = true) : SampledMembers S' := by
  intro g G' hG' o ho
  rcases hg g G' hG' o ho with ⟨G, hG, hmem⟩ | c
  · obtain ⟨x, hx, hs⟩ := h g G hG o hmem
    exact hm o x hx hs
  · exact c

/-- No mark is taken back by a change of one oracle message that keeps or sets the mark. -/
theorem marks_modify {A : Array Oracle} {o : Nat} {f : Oracle → Oracle}
    (hf : ∀ x : Oracle, x.sampled = true → (f x).sampled = true) (o' : Nat) (x : Oracle)
    (h : A[o']? = some x) (hs : x.sampled = true) :
    ∃ x' : Oracle, (A.modify o f)[o']? = some x' ∧ x'.sampled = true := by
  rw [Array.getElem?_modify]
  by_cases c : o = o'
  · rw [if_pos c, h]
    exact ⟨f x, rfl, hf x hs⟩
  · rw [if_neg c]
    exact ⟨x, h, hs⟩

/-- The members behind a change of one group that leaves its members. -/
theorem members_modify {A : Array Group} {g : Nat} {f : Group → Group}
    (hf : ∀ G : Group, (f G).members = G.members) (g' : Nat) (G' : Group)
    (h : (A.modify g f)[g']? = some G') (o : Nat) (ho : o ∈ G'.members.toList) :
    ∃ G, A[g']? = some G ∧ o ∈ G.members.toList := by
  rw [Array.getElem?_modify] at h
  by_cases c : g = g'
  · rw [if_pos c] at h
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨G, hG, by rw [← hf]; exact ho⟩
  · rw [if_neg c] at h
    exact ⟨G', h, ho⟩

/-- An effect on one oracle message that keeps or sets the mark, and leaves the groups. -/
theorem SampledMembers.onOracle (h : SampledMembers S) (o : Nat) (f : Oracle → Oracle)
    (ho : S'.oracles = S.oracles.modify o f) (hg : S'.groups = S.groups)
    (hf : ∀ x : Oracle, x.sampled = true → (f x).sampled = true) : SampledMembers S' :=
  h.later (fun o' x hx hs => by rw [ho]; exact marks_modify hf o' x hx hs)
    (fun g G' hG' o' ho' => Or.inl ⟨G', hg ▸ hG', ho'⟩)

theorem SampledMembers.withGroup (h : SampledMembers S) (a b : Nat) :
    SampledMembers (Slice.withGroup S a b) := by
  refine h.later (fun o x hx hs => ⟨x, hx, hs⟩) fun g G' hG' o ho => ?_
  have hG'' : (S.groups.push { code := a, maskCode := b })[g]? = some G' := hG'
  rw [Array.getElem?_push] at hG''
  by_cases c : g = S.groups.size
  · rw [if_pos c] at hG''
    obtain rfl := Option.some.inj hG''
    simp at ho
  · rw [if_neg c] at hG''
    exact Or.inl ⟨G', hG'', ho⟩

theorem SampledMembers.withRow (h : SampledMembers S) (g : Nat) (row : Row) :
    SampledMembers (Slice.withRow S g row) :=
  h.later (fun o x hx hs => ⟨x, hx, hs⟩) fun g' G' hG' o ho =>
    Or.inl (members_modify (f := fun G => { G with rows := G.rows.push row }) (fun _ => rfl)
      g' G' hG' o ho)

theorem SampledMembers.stSent (h : SampledMembers S) (sent : Array OracleNotice) :
    SampledMembers (Slice.stSent S sent) := by
  refine h.later (fun o x hx hs => ⟨x, ?_, hs⟩) fun g G' hG' o ho => Or.inl ⟨G', hG', ho⟩
  have ho : o < S.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  rw [Slice.stSent_old S sent o ho]
  exact hx

theorem SampledMembers.closeLedgers (h : SampledMembers S) (l : List Nat) :
    SampledMembers (Slice.closeLedgers S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons a l ih =>
    have h1 : SampledMembers { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } :=
      h.onOracle a (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
        rfl rfl (fun _ hs => hs)
    exact ih h1

/-- A message that is marked as sampled joins a group. -/
theorem SampledMembers.withMessageInGroup (h : SampledMembers S) (g o : Nat) (k : Bool) (G : Group) (x : Oracle)
    (hG : S.groups[g]? = some G) (hx : S.oracles[o]? = some x) (hs : x.sampled = true) :
    SampledMembers (Slice.withMessageInGroup S g o k G) := by
  have hm : ∀ (o' : Nat) (x' : Oracle), S.oracles[o']? = some x' → x'.sampled = true →
      ∃ x'' : Oracle, (Slice.withMessageInGroup S g o k G).oracles[o']? = some x'' ∧ x''.sampled = true :=
    fun o' x' hx' hs' => marks_modify (f := fun x => { x with groups := x.groups ++ [g] })
      (fun _ c => c) o' x' hx' hs'
  refine h.later hm fun g' G' hG' o' ho' => ?_
  have hG'' : (S.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k })[g']? = some G' :=
    hG'
  rw [Array.getElem?_modify] at hG''
  by_cases c : g = g'
  · subst c
    rw [if_pos rfl, hG] at hG''
    obtain rfl := Option.some.inj hG''
    have ho'' : o' ∈ (G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o).toList :=
      ho'
    rw [toList_insertIdxIfInBounds] at ho''
    have hpos : (G.members.filter (· < o)).size ≤ G.members.toList.length := by
      rw [Array.length_toList]
      exact Array.size_filter_le
    rcases (List.mem_insertIdx hpos).1 ho'' with e | e
    · rw [e]
      exact Or.inr (hm o x hx hs)
    · exact Or.inl ⟨G, hG, e⟩
  · rw [if_neg c] at hG''
    exact Or.inl ⟨G', hG'', ho'⟩

theorem SampledMembers.begun (h : SampledMembers S) (g : Nat) (G : Group) :
    SampledMembers (Slice.begun S g G) := by
  have h1 := h.closeLedgers G.members.toList
  refine h1.later (fun o x hx hs => ⟨x, hx, hs⟩) fun g' G' hG' o ho => Or.inl ?_
  have e : (Slice.begun S g G).groups = (Slice.closeLedgers S G.members.toList).groups.modify g
      fun G => { G with inRun := true, rows := #[] } := rfl
  rw [e] at hG'
  exact members_modify (f := fun G => { G with inRun := true, rows := #[] }) (fun _ => rfl)
    g' G' hG' o ho

/-! ## A message that is not marked is in no group -/

/-- A message that is not marked as sampled is pending: it is a member of no group. -/
theorem pending_of_unsampled (h : SampledMembers S) {o : Nat} {x : Oracle}
    (hx : S.oracles[o]? = some x) (hs : x.sampled = false) : Pending S o := by
  intro g G hG ho
  obtain ⟨x', hx', hs'⟩ := h g G hG o ho
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  rw [hs] at hs'
  cases hs'

variable {K : Type} [CommRing K] (ρ : Reading K) {m : Words K}

/-- **The sample rows enter.** If what the statement behind the admitting still claims holds, what
the statement in front claimed held, and the rows that were written hold. -/
theorem Claims.of_admitted_rows (hI : InOrder S) (hN : NoneYet S) (hM : SampledMembers S) (o : Nat)
    (x : Oracle) (s : OracleShape) (p : List PadPlace) (rows : Array Row)
    (hx : S.oracles[o]? = some x) (hs : x.sampled = false)
    (hr : ∀ r ∈ rows.toList, RowOn S o r) (h : Claims ρ (Slice.admitted S o s p rows) m) :
    Claims ρ S m ∧ AllSay ρ S rows.toList m := by
  refine ⟨Claims.of_admitted ρ hI hN o s p rows (fun x' hx' => ?_) h, fun r hr' => ?_⟩
  · rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    exact hs
  · have hp : Pending (Slice.admitted S o s p rows) o :=
      (pending_of_unsampled hM hx hs).sameGroups rfl
    exact (says_extends ρ (extends_admitted S o s p rows) (hr r hr') m).1
      (h.samples o _ (Slice.admitted_same S o s p rows x hx) hp r hr')

/-! ## The plain functions -/

variable {Lc : Type}

theorem newGroupP_members {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact hM.withGroup a b
  · cases h

theorem recvP_members {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice}
    {ids : Array Nat} (h : recvP first d sent = some (ids, d')) (hM : SampledMembers d.st) :
    SampledMembers d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hM.stSent sent
  · cases h

theorem adoptP_members {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hM : SampledMembers d.st) :
    SampledMembers d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hM.stSent sent
  · cases h

theorem admitP_members {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    exact hM.onOracle o (fun y => { y with
      sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
      ledger := Slice.freshLedger d.st.codes x.shape }) rfl rfl fun _ _ => rfl
  · cases h

/-- A message joins a group: the clause "sampled" keeps the invariant. -/
theorem joinP_members {d d' : DState Lc} {g o : Nat} {kept : Bool}
    (h : joinP d g o kept = some d') (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold joinP at h
  by_cases c : ok (joinL d.st g o kept) = true
  · rw [if_pos c] at h
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    obtain ⟨_, c2, c3, _⟩ := c
    cases hx : d.st.oracles[o]? with
    | none =>
      rw [hx] at c2
      cases c2
    | some x =>
      rw [hx, has_some] at c3
      exact hM.withMessageInGroup g o kept G x hG hx c3
  · rw [if_neg c] at h
    cases h

theorem addRowP_members {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold addRowP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hM.withRow g row
  · cases h

theorem takeMaskP_members {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hM.onOracle o (fun x => { x with ledger := some { l with
      next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } })
      rfl rfl fun _ hs => hs
  · cases h

theorem closeLedgerP_members {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hM.closeLedgers [o]
  · cases h

theorem spendAsMaskP_members {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hM : SampledMembers d.st) : SampledMembers d'.st := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hM.onOracle o (fun x => { x with spentAsMask := true }) rfl rfl fun _ hs => hs
  · cases h

theorem elsewhereP_members {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hM : SampledMembers d.st) :
    SampledMembers d'.st := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hM.onOracle mine (fun x => { x with
      sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad }) rfl rfl
      fun _ _ => rfl
  · cases h

theorem beginRunP_members {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hM : SampledMembers d.st) : SampledMembers d'.st := by
  obtain ⟨G, _, _, e⟩ := beginRunP_inv h
  rw [e]
  exact hM.begun g G

/-- **The sample rows enter, at the plain function.** -/
theorem admitP_enters {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hI : InOrder d.st) (hN : NoneYet d.st)
    (hM : SampledMembers d.st) (hr : ∀ r ∈ rows.toList, RowOn d.st o r)
    (hH : Claims ρ d'.st m) : Claims ρ d.st m ∧ AllSay ρ d.st rows.toList m := by
  unfold admitP at h
  by_cases c : ok (admitL d.st o rows) = true
  · rw [if_pos c] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, places, _, rfl⟩ := h
    simp only [ok, admitL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    have c3 := c.2.2.1
    rw [hx, has_some] at c3
    exact Claims.of_admitted_rows ρ hI hN hM o x x.shape places rows hx (by simpa using c3) hr hH
  · rw [if_neg c] at h
    cases h

end OnBytes.Means
