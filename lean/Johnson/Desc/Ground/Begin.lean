-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Begin.lean: the step that lays a group's mark, at the ground's own function
beginRunP; the relation "a sampled message's sample rows stay"; and that a member's sample rows are
among the rows which the beginning of its group's test hands on. Theorems.

  sample_in_runRows  the rows that a test takes in hold every sample row of every member.
  SampleKept T T'    a message that is sampled in T stands in T' with the same sample rows.
  groundKeeps_kept   the ground's ten plain functions keep it; admitP's and elsewhereP's proofs READ
                     their own clause "not sampled before | here".
  beginRun_takes     beginRunP's yes at g: the group stood there WITHOUT the mark; what is handed to
                     the test is runRows of the statement IN FRONT; the statement behind is "begun".
  begun_at           behind it the group bears the mark, has the same members and no open row.
  beginRun_frozen · beginRun_kept     it keeps Frozen and SampleKept.
  rows_entered       **the sample rows entered the test**: let A be a statement in which the message
                     i is sampled, with the sample rows R; B, behind A along SampleKept, the
                     statement in front of a beginRunP at g that says yes; E the end, behind that
                     step along Frozen, with i a member of g at E. Then every row of R is among the
                     rows that beginRunP handed to the test.
What is not claimed. THAT A MEMBER WAS SAMPLED IN FRONT OF THE STEP: rows_entered asks a statement A
in front of it in which the message is sampled. A message that is made a member unsampled, and
sampled only behind the step, is not reached: its sample rows enter no test, and all the relations
here and in Johnson/Desc/Ground/Linked.lean are kept. joinP's clause "sampled" excludes it; no law
here reads that clause: THAT MEMBERS ARE SAMPLED IS A FURTHER PROPERTY, stated and kept elsewhere
(SampledMembers, Johnson/Desc/Means/Entry.lean). That beginRunP keeps Linked. That the OPEN rows in
front of the step enter the test: runRows takes those of the kinds plain and generator; an open row
of the kind sample would be dropped; addRowP's clause "no sample row" excludes it; no law here reads
that clause (OpenKinds, Johnson/Desc/Means/Holds.lean). That a
proximity test's block calls beginRunP once, at its own group, and tests what it is handed: that is
owed by the laws of the proximity test's own files.

-/
import Johnson.Desc.Ground.LinkedKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Slice

theorem mem_foldl_append {α β : Type} (f : β → Array α) (a : α) :
    ∀ (l : List β) (acc : Array α), (a ∈ acc ∨ ∃ b ∈ l, a ∈ f b) →
      a ∈ l.foldl (fun s b => s ++ f b) acc := by
  intro l
  induction l with
  | nil =>
    intro acc h
    rcases h with h | ⟨b, hb, _⟩
    · exact h
    · cases hb
  | cons c l ih =>
    intro acc h
    apply ih
    rcases h with h | ⟨b, hb, hab⟩
    · exact Or.inl (Array.mem_append.2 (Or.inl h))
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl (Array.mem_append.2 (Or.inr hab))
      · exact Or.inr ⟨b, hb, hab⟩

/-- The rows that a test takes in hold every sample row of every member. -/
theorem sample_in_runRows (S : Statement) (G : Group) (o : Nat) (x : OnBytes.Oracle)
    (row : OnBytes.Row) (ho : o ∈ G.members) (hx : S.oracles[o]? = some x)
    (hr : row ∈ x.sampleRows) : row ∈ runRows S G := by
  unfold runRows
  refine Array.mem_append.2 (Or.inl (Array.mem_append.2 (Or.inr ?_)))
  rw [← Array.foldl_toList]
  exact mem_foldl_append _ row _ _ (Or.inr ⟨o, Array.mem_toList_iff.2 ho, by simpa [hx] using hr⟩)

/-- A message that is sampled stands behind with the same sample rows. -/
def SampleKept (T T' : Statement) : Prop :=
  ∀ (i : Nat) x, T.oracles[i]? = some x → x.sampled = true →
    ∃ x', T'.oracles[i]? = some x' ∧ x'.sampled = true ∧ x'.sampleRows = x.sampleRows

theorem SampleKept.refl (T : Statement) : SampleKept T T := fun _ x h s => ⟨x, h, s, rfl⟩

theorem SampleKept.trans {A B C : Statement} (h : SampleKept A B) (k : SampleKept B C) :
    SampleKept A C := by
  intro i x hx s
  obtain ⟨y, hy, sy, ry⟩ := h i x hx s
  obtain ⟨z, hz, sz, rz⟩ := k i y hy sy
  exact ⟨z, hz, sz, rz.trans ry⟩

/-- A change of the groups alone. -/
theorem kept_groups (T : Statement) (gs : Array Group) : SampleKept T { T with groups := gs } :=
  fun _ x h s => ⟨x, h, s, rfl⟩

/-- A change of one message that leaves the flag and the rows of a sampled one. -/
theorem kept_modOracle (T : Statement) (k : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, T.oracles[k]? = some x → x.sampled = true →
      (f x).sampled = true ∧ (f x).sampleRows = x.sampleRows) :
    SampleKept T { T with oracles := T.oracles.modify k f } := by
  intro i x hx s
  show ∃ x', (T.oracles.modify k f)[i]? = some x' ∧ _
  rw [Array.getElem?_modify]
  split
  · rename_i hk
    subst hk
    exact ⟨f x, by simp [hx], (hf x hx s).1, (hf x hx s).2⟩
  · exact ⟨x, hx, s, rfl⟩

theorem kept_stSent (T : Statement) (sent : Array OracleNotice) : SampleKept T (stSent T sent) := by
  intro i x hx s
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 hx
  refine ⟨x, ?_, s, rfl⟩
  show (T.oracles ++ _)[i]? = some x
  rw [Array.getElem?_append, if_pos hi, hx]

theorem kept_closeLedgers (l : List Nat) : ∀ T : Statement, SampleKept T (closeLedgers T l) := by
  induction l with
  | nil => exact SampleKept.refl
  | cons o l ih =>
    intro T
    exact (kept_modOracle T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun _ _ s => ⟨s, rfl⟩).trans (ih _)

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- admitP's yes: the message was not sampled. -/
theorem admit_unsampled (S : Statement) (o : Nat) (rows : Array OnBytes.Row)
    (h : ok (admitL S o rows) = true) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x) :
    x.sampled = false := by
  have := clause_of_ok _ h ("admit: not sampled before", has S.oracles[o]? fun x => !x.sampled)
    (by simp [admitL])
  simpa [has, hx] using this

/-- elsewhereP's yes: the message here was not sampled. -/
theorem elsewhere_unsampled (S : Statement) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : ok (elsewhereL S mine other theirs) = true) (x : OnBytes.Oracle)
    (hx : S.oracles[mine]? = some x) : x.sampled = false := by
  have := clause_of_ok _ h
    ("elsewhere: not sampled here", has S.oracles[mine]? (!·.sampled)) (by simp [elsewhereL])
  simpa [has, hx] using this

/-- "A sampled message's sample rows stay" is such a relation. -/
theorem groundKeeps_kept : GroundKeeps SampleKept where
  refl := SampleKept.refl
  trans := SampleKept.trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact kept_groups d.st _
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold recvP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact kept_stSent d.st sent
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · rename_i hok
      cases hx : d.st.oracles[o]? with
      | none => simp [hx] at h
      | some x =>
        cases hp : Own.padMade d.st.codes x.shape with
        | none => simp [hx, hp] at h
        | some places =>
          simp only [hx, hp, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          refine kept_modOracle d.st o _ fun y hy s => ?_
          rw [admit_unsampled d.st o rows hok y hy] at s
          cases s
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · cases hg : d.st.groups[g]? with
      | none => simp [hg] at h
      | some G =>
        simp only [hg, Option.map_some, Option.some.injEq] at h
        subst h
        exact (kept_groups d.st _).trans
          (kept_modOracle _ o (fun x => { x with groups := x.groups ++ [g] })
            fun _ _ s => ⟨s, rfl⟩)
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact kept_groups d.st _
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
      | none => simp [hl] at h
      | some l =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact kept_modOracle d.st o _ fun _ _ s => ⟨s, rfl⟩
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact kept_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact kept_modOracle d.st o _ fun _ _ s => ⟨s, rfl⟩
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold adoptP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact kept_stSent d.st sent
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · rename_i hok
      cases hy : other.oracles[theirs]? with
      | none => simp [hy] at h
      | some y =>
        simp only [hy, Option.map_some, Option.some.injEq] at h
        subst h
        refine kept_modOracle d.st mine _ fun z hz s => ?_
        rw [elsewhere_unsampled d.st mine other theirs hok z hz] at s
        cases s
    · cases h

variable {L : Type}

/-- **What the beginning of a test takes in, and what it leaves.** -/
theorem beginRun_takes (d d' : DState L) (g : Nat) (inp : RunInput)
    (h : beginRunP d g = some (inp, d')) :
    ∃ G, d.st.groups[g]? = some G ∧ G.inRun = false ∧ inp.rows = runRows d.st G ∧
      d'.st = begun d.st g G := by
  unfold beginRunP at h
  split at h
  · rename_i hok
    cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := clause_of_ok _ hok
        ("beginRun: no test has begun", has d.st.groups[g]? (!·.inRun)) (by simp [beginRunL])
      exact ⟨G, rfl, by simpa [has, hg] using this, rfl, rfl⟩
  · cases h

theorem closeLedgers_groups (l : List Nat) : ∀ S : Statement,
    (closeLedgers S l).groups = S.groups := by
  induction l with
  | nil => intro S; rfl
  | cons o l ih =>
    intro S
    exact ih _

/-- The group at g behind the beginning of its test. -/
theorem begun_at (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    (begun S g G).groups[g]? = some { G with inRun := true, rows := #[] } := by
  show ((closeLedgers S G.members.toList).groups.modify g _)[g]? = _
  rw [closeLedgers_groups, Array.getElem?_modify]
  simp [hG]

/-- The beginning of a test on a group without the mark keeps Frozen. -/
theorem frozen_begun (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G)
    (hm : G.inRun = false) : Frozen S (begun S g G) :=
  (frozen_closeLedgers G.members.toList S).trans
    (frozen_modGroup _ g (fun G => { G with inRun := true, rows := #[] }) fun A hA => by
      rw [closeLedgers_groups, hG] at hA
      cases hA
      exact hm)

/-- It keeps SampleKept. -/
theorem kept_begun (S : Statement) (g : Nat) (G : Group) : SampleKept S (begun S g G) :=
  (kept_closeLedgers G.members.toList S).trans (kept_groups _ _)

theorem beginRun_frozen (d d' : DState L) (g : Nat) (inp : RunInput)
    (h : beginRunP d g = some (inp, d')) : Frozen d.st d'.st := by
  obtain ⟨G, hG, hm, -, he⟩ := beginRun_takes d d' g inp h
  rw [he]
  exact frozen_begun d.st g G hG hm

theorem beginRun_kept (d d' : DState L) (g : Nat) (inp : RunInput)
    (h : beginRunP d g = some (inp, d')) : SampleKept d.st d'.st := by
  obtain ⟨G, -, -, -, he⟩ := beginRun_takes d d' g inp h
  rw [he]
  exact kept_begun d.st g G

/-- **The sample rows entered the test.** A: a statement in which the message
i is sampled; d: the state in front of a beginning of the test on g that says yes, behind A along
SampleKept; E: the end, behind that step along Frozen, at which i is a member of g. -/
theorem rows_entered (A E : Statement) (d d' : DState L) (g : Nat) (inp : RunInput)
    (hb : beginRunP d g = some (inp, d')) (hk : SampleKept A d.st) (hf : Frozen d'.st E) (i : Nat)
    (x : OnBytes.Oracle) (hx : A.oracles[i]? = some x) (hs : x.sampled = true) (GE : Group)
    (hGE : E.groups[g]? = some GE) (hi : i ∈ GE.members) :
    ∀ row ∈ x.sampleRows, row ∈ inp.rows := by
  intro row hr
  obtain ⟨G, hG, -, hrows, he⟩ := beginRun_takes d d' g inp hb
  obtain ⟨y, hy, -, ry⟩ := hk i x hx hs
  have hat : d'.st.groups[g]? = some { G with inRun := true, rows := #[] } := by
    rw [he]
    exact begun_at d.st g G hG
  obtain ⟨G2, h2, -, hm, -⟩ := hf g _ hat rfl
  rw [hGE] at h2
  cases h2
  rw [hrows]
  exact sample_in_runRows d.st G i y row (by rw [hm] at hi; exact hi) hy (by rw [ry]; exact hr)

end VerifiableInference.Desc.Ground
