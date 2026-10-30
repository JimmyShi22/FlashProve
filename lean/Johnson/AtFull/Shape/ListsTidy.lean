-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ListsTidy.lean: A MESSAGE's LIST OF GROUPS AND THE GROUPS' LISTS OF MEMBERS:
TWO PROPERTIES OF A STATEMENT THAT THE GROUND's ROUTINES KEEP (StKeeps), AND WHAT THEY GIVE
TOGETHER: a member of the last group whose number is not below N has just that group in its list; so
the test "what shares a leaf" (leafOk, Johnson/Top/H0/Tw/K2C/Asks.lean) accepts at a tree whose
sampled parts are such members. General laws on statements; no head; no state; nothing is evaluated
but in the controls.

Why. The library ties the two sides one way (Linked, Johnson/Desc/Ground/Linked.lean: a list names
only groups that hold the message). The code switch's test reads the lists; the library's laws along
the chain speak of the members.

  listAt T o, membersAt T g, markAt T g: what is read of a statement: a message's list; a group's
    members; a group's mark "its proximity test has begun".
  Tidy T: a list names only groups that hold the message (what the library's Linked says; no law
    here ties the two) · a member of group g is there and has g in its list · no list names a group
    twice.
  Shut k N T: each group g < k bears the mark, and its members are below N.
  Stays P, PlainKeeps P, stKeeps_of: a property that the five plain changes of a statement keep (a
    message's change that leaves its list · a group's that leaves its members and takes off no
    mark · messages sent · a new group · a joining, under the look-up of its group and three of the
    joining's own clauses) meets StKeeps (Johnson/Desc/K13/Law/StatementCalls.lean).
  plain_tidy, plain_shut: the two are such. stKeeps_tidy, stKeeps_shut.
  tidy_start: a statement without a message and without a group is tidy.
  list_one: Tidy T · Shut k N T · T has k + 1 groups · o is a member of group k · N ≤ o: the list of
    o is [k].
  leafOk_of_lists: where each sampled part of a tree has the list [k], leafOk accepts.
  tidy_can_fail, tidy_can_fail_listed, tidy_can_fail_once (one a clause), shut_can_fail,
    shut_can_fail_below (one a clause), list_one_wants_shut, leafOk_can_fail: CONTROLS at small
    made-up statements.

Limits. That Tidy or Shut holds of any state of a chain is not said here. Tidy is another thing than
the library's OnBytes.Means.Tidy (Johnson/Desc/Means/Walk.lean), which is also a structure over a
statement. The controls state "not Tidy" or "not Shut": that each breaks one clause alone is said by
reading the made-up statements, not by Lean. Shut is kept because the joining's own clause refuses a
marked group: that a group bears the mark is nowhere shown here. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.K13.Law.StatementCalls
import Johnson.Desc.Ground.LinkedKeeps
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (mem_insertIfIn mem_insertSelf)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K13.Law (StKeeps)
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_iff)
open _root_.Tw.K2 (leafOk leafGroups)

/-! ## 1 What is read of a statement -/

/-- A message's list of groups. -/
def listAt (T : Statement) (o : Nat) : Option (List Nat) := (T.oracles[o]?).map (·.groups)

/-- A group's members. -/
def membersAt (T : Statement) (g : Nat) : Option (Array Nat) := (T.groups[g]?).map (·.members)

/-- A group's mark "its proximity test has begun". -/
def markAt (T : Statement) (g : Nat) : Option Bool := (T.groups[g]?).map (·.inRun)

/-- **The two sides say the same, and no list says it twice.** -/
structure Tidy (T : Statement) : Prop where
  linked : ∀ o l g, listAt T o = some l → g ∈ l → ∃ M, membersAt T g = some M ∧ o ∈ M
  listed : ∀ g M o, membersAt T g = some M → o ∈ M → ∃ l, listAt T o = some l ∧ g ∈ l
  once : ∀ o l, listAt T o = some l → l.Nodup

/-- **Each group below k bears the mark, and its members are below N.** -/
def Shut (k N : Nat) (T : Statement) : Prop :=
  ∀ g, g < k → markAt T g = some true ∧ ∃ M, membersAt T g = some M ∧ ∀ o ∈ M, o < N

/-- Tidy reads the lists and the members alone. -/
theorem Tidy.congr {T T' : Statement} (hl : ∀ o, listAt T' o = listAt T o)
    (hm : ∀ g, membersAt T' g = membersAt T g) (h : Tidy T) : Tidy T' :=
  ⟨fun o l g a b => by rw [hl] at a; rw [hm]; exact h.linked o l g a b,
    fun g M o a b => by rw [hm] at a; rw [hl]; exact h.listed g M o a b,
    fun o l a => by rw [hl] at a; exact h.once o l a⟩

/-- Shut reads the members and the marks alone, and a mark more does no harm. -/
theorem Shut.congr {k N : Nat} {T T' : Statement} (hm : ∀ g, membersAt T' g = membersAt T g)
    (hk : ∀ g, markAt T g = some true → markAt T' g = some true) (h : Shut k N T) : Shut k N T' :=
  fun g hg => ⟨hk g (h g hg).1, by rw [hm]; exact (h g hg).2⟩

/-! ## 2 The plain changes, on what is read -/

/-- A message's change that leaves its list leaves every list. -/
theorem listAt_modify (T : Statement) (k : Nat) (f : Oracle → Oracle)
    (hf : ∀ x, (f x).groups = x.groups) (o : Nat) :
    listAt { T with oracles := T.oracles.modify k f } o = listAt T o := by
  unfold listAt
  show ((T.oracles.modify k f)[o]?).map (·.groups) = _
  rw [Array.getElem?_modify]
  split
  · cases T.oracles[o]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

/-- A group's change that leaves its members leaves every group's members. -/
theorem membersAt_modify (T : Statement) (k : Nat) (f : Group → Group)
    (hf : ∀ G, (f G).members = G.members) (g : Nat) :
    membersAt { T with groups := T.groups.modify k f } g = membersAt T g := by
  unfold membersAt
  show ((T.groups.modify k f)[g]?).map (·.members) = _
  rw [Array.getElem?_modify]
  split
  · cases T.groups[g]? with
    | none => rfl
    | some G => exact congrArg some (hf G)
  · rfl

/-- A group's change that takes off no mark leaves a mark that is borne. -/
theorem markAt_modify (T : Statement) (k : Nat) (f : Group → Group)
    (hf : ∀ G, G.inRun = true → (f G).inRun = true) (g : Nat) (h : markAt T g = some true) :
    markAt { T with groups := T.groups.modify k f } g = some true := by
  unfold markAt at h ⊢
  show ((T.groups.modify k f)[g]?).map (·.inRun) = some true
  rw [Array.getElem?_modify]
  split
  · cases hG : T.groups[g]? with
    | none => rw [hG] at h; cases h
    | some G =>
      rw [hG] at h
      exact congrArg some (hf G (Option.some.inj h))
  · exact h

/-- Behind a sending a list is one of those in front, or empty. -/
theorem listAt_sent_of {T : Statement} {sent : Array OracleNotice} {o : Nat} {l : List Nat}
    (h : listAt (stSent T sent) o = some l) : listAt T o = some l ∨ l = [] := by
  unfold listAt at h ⊢
  have h' : ((T.oracles ++ sent.map fun n => ({ shape := n.shape } : Oracle))[o]?).map
      (·.groups) = some l := h
  rw [Array.getElem?_append] at h'
  split at h'
  · exact Or.inl h'
  · rw [Array.getElem?_map] at h'
    cases hs : sent[o - T.oracles.size]? with
    | none => rw [hs] at h'; cases h'
    | some n =>
      rw [hs] at h'
      exact Or.inr (Option.some.inj h').symm

/-- A sending leaves the lists in front. -/
theorem listAt_sent_old {T : Statement} (sent : Array OracleNotice) {o : Nat} {l : List Nat}
    (h : listAt T o = some l) : listAt (stSent T sent) o = some l := by
  unfold listAt at h ⊢
  show ((T.oracles ++ sent.map fun n => ({ shape := n.shape } : Oracle))[o]?).map
      (·.groups) = some l
  have ho : o < T.oracles.size := by
    cases hx : T.oracles[o]? with
    | none => rw [hx] at h; cases h
    | some x => exact (Array.getElem?_eq_some_iff.1 hx).1
  rw [Array.getElem?_append, if_pos ho]
  exact h

/-- Behind a new group a group's members are those in front, or none. -/
theorem membersAt_new_of {T : Statement} {a b g : Nat} {M : Array Nat}
    (h : membersAt (Slice.withGroup T a b) g = some M) : membersAt T g = some M ∨ M = #[] := by
  unfold membersAt at h ⊢
  have h' : ((T.groups.push { code := a, maskCode := b })[g]?).map (·.members) = some M := h
  rw [Array.getElem?_push] at h'
  split at h'
  · exact Or.inr (Option.some.inj h').symm
  · exact Or.inl h'

/-- A new group leaves what is read of the groups in front. -/
theorem group_new_old {α : Type} (T : Statement) (a b : Nat) (φ : Group → α) {g : Nat} {v : α}
    (h : (T.groups[g]?).map φ = some v) : ((Slice.withGroup T a b).groups[g]?).map φ = some v := by
  show ((T.groups.push { code := a, maskCode := b })[g]?).map φ = some v
  have hg : g < T.groups.size := by
    cases hx : T.groups[g]? with
    | none => rw [hx] at h; cases h
    | some x => exact (Array.getElem?_eq_some_iff.1 hx).1
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hg)]
  exact h

/-- The joining lays g behind the list of o and leaves every other list. -/
theorem listAt_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group) (o' : Nat) :
    listAt (withMessageInGroup T g o kept G) o' =
      if o = o' then (listAt T o').map (· ++ [g]) else listAt T o' := by
  unfold listAt
  show ((T.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[o']?).map
    (·.groups) = _
  rw [Array.getElem?_modify]
  split
  · cases T.oracles[o']? <;> rfl
  · rfl

/-- The joining inserts o among the members of g and leaves every other group's. -/
theorem membersAt_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group) (g' : Nat) :
    membersAt (withMessageInGroup T g o kept G) g' =
      if g = g' then (membersAt T g').map
        (·.insertIdxIfInBounds (G.members.filter (· < o)).size o) else membersAt T g' := by
  unfold membersAt
  show ((T.groups.modify g fun G' => { G' with
    members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
    kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })[g']?).map
    (·.members) = _
  rw [Array.getElem?_modify]
  split
  · cases T.groups[g']? <;> rfl
  · rfl

/-- The joining leaves every mark. -/
theorem markAt_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group) (g' : Nat) :
    markAt (withMessageInGroup T g o kept G) g' = markAt T g' := by
  unfold markAt
  show ((T.groups.modify g fun G' => { G' with
    members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
    kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })[g']?).map
    (·.inRun) = _
  rw [Array.getElem?_modify]
  split
  · cases T.groups[g']? <;> rfl
  · rfl

/-- What is in an array behind an insertion was in it, or is what was inserted. -/
theorem mem_of_insertIfIn {α : Type} {xs : Array α} {i : Nat} {a b : α}
    (h : b ∈ xs.insertIdxIfInBounds i a) : b = a ∨ b ∈ xs := by
  unfold Array.insertIdxIfInBounds at h
  split at h
  · exact Array.mem_insertIdx.1 h
  · exact Or.inr h

/-! ## 3 A property that the plain changes keep meets StKeeps -/

/-- The relation of an invariant. -/
def Stays (P : Statement → Prop) (T T' : Statement) : Prop := P T → P T'

/-- **The five plain changes of a statement.** -/
structure PlainKeeps (P : Statement → Prop) : Prop where
  oracle : ∀ (T : Statement) (k : Nat) (f : Oracle → Oracle), (∀ x, (f x).groups = x.groups) →
    Stays P T { T with oracles := T.oracles.modify k f }
  group : ∀ (T : Statement) (k : Nat) (f : Group → Group),
    (∀ G, (f G).members = G.members ∧ (G.inRun = true → (f G).inRun = true)) →
    Stays P T { T with groups := T.groups.modify k f }
  sent : ∀ (T : Statement) (sent : Array OracleNotice), Stays P T (stSent T sent)
  fresh : ∀ (T : Statement) (a b : Nat), Stays P T (Slice.withGroup T a b)
  joined : ∀ (T : Statement) (g o : Nat) (kept : Bool) (G : Group), T.groups[g]? = some G →
    (T.oracles[o]?).isSome = true → G.inRun = false → o ∉ G.members →
    Stays P T (withMessageInGroup T g o kept G)

variable {P : Statement → Prop}

/-- Closing ledgers is a run of messages' changes that leave their lists. -/
theorem PlainKeeps.ledgers (K : PlainKeeps P) (l : List Nat) :
    ∀ T : Statement, Stays P T (closeLedgers T l) := by
  induction l with
  | nil => exact fun _ h => h
  | cons o l ih =>
    intro T h
    exact ih _ (K.oracle T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      (fun _ => rfl) h)

/-- The ground's twelve fields, each from the plain change that the routine's text makes. -/
theorem groundKeeps_of (K : PlainKeeps P) : GroundKeeps (Stays P) where
  refl := fun _ h => h
  trans := fun a b h => b (a h)
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact K.fresh d.st code maskCode
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold recvP at h
    split at h
    · cases hl : VerifiableInference.Desc.Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact K.sent d.st sent
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · cases hx : d.st.oracles[o]? with
      | none => simp [hx] at h
      | some x =>
        cases hp : VerifiableInference.Desc.Own.padMade d.st.codes x.shape with
        | none => simp [hx, hp] at h
        | some places =>
          simp only [hx, hp, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          exact K.oracle d.st o _ fun _ => rfl
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · rename_i hok
      cases hg : d.st.groups[g]? with
      | none => simp [hg] at h
      | some G =>
        simp only [hg, Option.map_some, Option.some.injEq] at h
        subst h
        have h1 : (d.st.oracles[o]?).isSome = true :=
          clause_of_ok _ hok ("join: the message is there", (d.st.oracles[o]?).isSome)
            (by simp [joinL])
        have h2 := clause_of_ok _ hok
          ("join: no member twice", has d.st.groups[g]? (!·.members.contains o)) (by simp [joinL])
        have h3 : o ∉ G.members := by
          intro hm
          simp [has, hg, hm] at h2
        exact K.joined d.st g o kept G hg h1 (join_unmarked d.st g o kept hok G hg) h3
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact K.group d.st g (fun G => { G with rows := G.rows.push row }) fun _ => ⟨rfl, id⟩
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
        exact K.oracle d.st o _ fun _ => rfl
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact K.ledgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact K.oracle d.st o _ fun _ => rfl
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold adoptP at h
    split at h
    · cases hl : VerifiableInference.Desc.Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact K.sent d.st sent
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · cases hy : other.oracles[theirs]? with
      | none => simp [hy] at h
      | some y =>
        simp only [hy, Option.map_some, Option.some.injEq] at h
        subst h
        exact K.oracle d.st mine _ fun _ => rfl
    · cases h

/-- **Such a property meets StKeeps**: a record on the ground's routines. The step from there to the
chain's sub-protocols is taken elsewhere (ListsReached.lean). -/
theorem stKeeps_of (K : PlainKeeps P) : StKeeps (Stays P) where
  ground := groundKeeps_of K
  begun := fun T g G h =>
    K.group (closeLedgers T G.members.toList) g (fun G' => { G' with inRun := true, rows := #[] })
      (fun _ => ⟨rfl, fun _ => rfl⟩) (K.ledgers _ T h)
  row := fun lay im o n lin T r os' h => by
    obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, _, -, _, l', -, -, rfl⟩ :=
      (pendingRowO_iff lay im o n lin T.oracles os' r).1 h
    exact K.oracle T im _ fun _ => rfl

/-! ## 4 The two properties -/

/-- **The plain changes keep Tidy.** -/
theorem plain_tidy : PlainKeeps Tidy where
  oracle := fun T k f hf h => h.congr (listAt_modify T k f hf) fun _ => rfl
  group := fun T k f hf h =>
    Tidy.congr (T := T) (fun _ => rfl) (membersAt_modify T k f fun G => (hf G).1) h
  sent := fun T sent h => by
    refine ⟨fun o l g a b => ?_, fun g M o a b => ?_, fun o l a => ?_⟩
    · rcases listAt_sent_of a with a | rfl
      · exact h.linked o l g a b
      · cases b
    · obtain ⟨l, hl, hg⟩ := h.listed g M o a b
      exact ⟨l, listAt_sent_old sent hl, hg⟩
    · rcases listAt_sent_of a with a | rfl
      · exact h.once o l a
      · exact List.nodup_nil
  fresh := fun T a b h => by
    refine ⟨fun o l g x y => ?_, fun g M o x y => ?_, fun o l x => h.once o l x⟩
    · obtain ⟨M, hM, ho⟩ := h.linked o l g x y
      exact ⟨M, group_new_old T a b (·.members) hM, ho⟩
    · rcases membersAt_new_of x with x | rfl
      · exact h.listed g M o x y
      · simp at y
  joined := fun T g o kept G hG hx _ hno h => by
    have hMg : membersAt T g = some G.members := by
      unfold membersAt
      rw [hG]
      rfl
    obtain ⟨l0, hl0⟩ : ∃ l0, listAt T o = some l0 := by
      unfold listAt
      cases hy : T.oracles[o]? with
      | none => rw [hy] at hx; cases hx
      | some y => exact ⟨y.groups, rfl⟩
    have memKeep : ∀ g' M b, membersAt T g' = some M → b ∈ M →
        ∃ M', membersAt (withMessageInGroup T g o kept G) g' = some M' ∧ b ∈ M' := by
      intro g' M b hM hb
      rw [membersAt_joined]
      split
      · rw [hM]
        exact ⟨_, rfl, mem_insertIfIn _ _ _ _ hb⟩
      · exact ⟨M, hM, hb⟩
    have listKeep : ∀ o' l g', listAt T o' = some l → g' ∈ l →
        ∃ l', listAt (withMessageInGroup T g o kept G) o' = some l' ∧ g' ∈ l' := by
      intro o' l g' hl hg
      rw [listAt_joined]
      split
      · rw [hl]
        exact ⟨_, rfl, List.mem_append_left _ hg⟩
      · exact ⟨l, hl, hg⟩
    refine ⟨fun o' l g' a b => ?_, fun g' M' o' a b => ?_, fun o' l a => ?_⟩
    · rw [listAt_joined] at a
      split at a
      · rename_i e
        subst e
        rw [hl0] at a
        obtain rfl : l0 ++ [g] = l := Option.some.inj a
        rcases List.mem_append.1 b with b | b
        · obtain ⟨M, hM, ho⟩ := h.linked o l0 g' hl0 b
          exact memKeep g' M o hM ho
        · obtain rfl := List.mem_singleton.1 b
          rw [membersAt_joined, if_pos rfl, hMg]
          exact ⟨_, rfl, mem_insertSelf _ _ _ Array.size_filter_le⟩
      · obtain ⟨M, hM, ho⟩ := h.linked o' l g' a b
        exact memKeep g' M o' hM ho
    · rw [membersAt_joined] at a
      split at a
      · rename_i e
        subst e
        rw [hMg] at a
        obtain rfl := Option.some.inj a
        rcases mem_of_insertIfIn b with rfl | b
        · rw [listAt_joined, if_pos rfl, hl0]
          exact ⟨_, rfl, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩
        · obtain ⟨l, hl, hg⟩ := h.listed g G.members o' hMg b
          exact listKeep o' l g hl hg
      · obtain ⟨l, hl, hg⟩ := h.listed g' M' o' a b
        exact listKeep o' l g' hl hg
    · rw [listAt_joined] at a
      split at a
      · rename_i e
        subst e
        rw [hl0] at a
        obtain rfl : l0 ++ [g] = l := Option.some.inj a
        refine List.Nodup.append (h.once o l0 hl0) (List.nodup_singleton g) fun c h1 h2 => ?_
        obtain rfl := List.mem_singleton.1 h2
        obtain ⟨M, hM, ho⟩ := h.linked o l0 c hl0 h1
        rw [hMg] at hM
        obtain rfl := Option.some.inj hM
        exact hno ho
      · exact h.once o' l a

/-- **The plain changes keep Shut**: the joining's clause "no test has begun" keeps it out of a
marked group. -/
theorem plain_shut (k N : Nat) : PlainKeeps (Shut k N) where
  oracle := fun _ _ _ _ h => h.congr (fun _ => rfl) fun _ m => m
  group := fun T j f hf h =>
    h.congr (membersAt_modify T j f fun G => (hf G).1) (markAt_modify T j f fun G => (hf G).2)
  sent := fun _ _ h => h.congr (fun _ => rfl) fun _ m => m
  fresh := fun T a b h g hg => by
    obtain ⟨m, M, hM, hb⟩ := h g hg
    exact ⟨group_new_old T a b (·.inRun) m, M, group_new_old T a b (·.members) hM, hb⟩
  joined := fun T g o kept G hG _ hun _ h g' hg' => by
    obtain ⟨m, M, hM, hb⟩ := h g' hg'
    have hne : ¬ g = g' := by
      rintro rfl
      unfold markAt at m
      rw [hG] at m
      have : G.inRun = true := Option.some.inj m
      rw [hun] at this
      cases this
    refine ⟨by rw [markAt_joined]; exact m, M, ?_, hb⟩
    rw [membersAt_joined, if_neg hne]
    exact hM

/-- So Tidy meets StKeeps. -/
theorem stKeeps_tidy : StKeeps (Stays Tidy) := stKeeps_of plain_tidy

/-- So Shut meets StKeeps. -/
theorem stKeeps_shut (k N : Nat) : StKeeps (Stays (Shut k N)) := stKeeps_of (plain_shut k N)

/-- A statement without a message and without a group is tidy. -/
theorem tidy_start {T : Statement} (h1 : T.oracles = #[]) (h2 : T.groups = #[]) : Tidy T :=
  ⟨fun o l g a _ => by unfold listAt at a; rw [h1] at a; simp at a,
    fun g M o a _ => by unfold membersAt at a; rw [h2] at a; simp at a,
    fun o l a => by unfold listAt at a; rw [h1] at a; simp at a⟩

/-! ## 5 What the two give together -/

/-- A list without a repeat, all of whose entries are k, and which holds k, is [k]. -/
theorem eq_single {l : List Nat} {k : Nat} (hn : l.Nodup) (ha : ∀ g ∈ l, g = k) (hk : k ∈ l) :
    l = [k] := by
  match l, hn, ha, hk with
  | [], _, _, hk => cases hk
  | [a], _, ha, _ => rw [ha a (List.mem_singleton.2 rfl)]
  | a :: b :: t, hn, ha, _ =>
    have e1 := ha a (by simp)
    have e2 := ha b (by simp)
    rw [List.nodup_cons] at hn
    exact absurd (by rw [e1, e2]; simp) hn.1

/-- **A member of the last group whose number is not below N has just that group in its list.** -/
theorem list_one {T : Statement} {k N o : Nat} {M : Array Nat} (hT : Tidy T) (hS : Shut k N T)
    (hn : T.groups.size = k + 1) (hM : membersAt T k = some M) (ho : o ∈ M) (hN : N ≤ o) :
    listAt T o = some [k] := by
  obtain ⟨l, hl, hk⟩ := hT.listed k M o hM ho
  have hall : ∀ g ∈ l, g = k := by
    intro g hg
    obtain ⟨M', hM', ho'⟩ := hT.linked o l g hl hg
    have hlt : g < k + 1 := by
      rw [← hn]
      unfold membersAt at hM'
      cases hG : T.groups[g]? with
      | none => rw [hG] at hM'; cases hM'
      | some G => exact (Array.getElem?_eq_some_iff.1 hG).1
    by_contra hne
    obtain ⟨-, M'', hM'', hb⟩ := hS g (by omega)
    rw [hM'] at hM''
    obtain rfl := Option.some.inj hM''
    exact absurd (hb o ho') (by omega)
  rw [hl, eq_single (hT.once o l hl) hall hk]

/-- **Where each sampled part of a tree has the list [k], "what shares a leaf" accepts.** -/
theorem leafOk_of_lists (S : Statement) (tree : Tree) (k : Nat)
    (h : ∀ o ∈ tree.parts.toList, ∀ x, S.oracles[o]? = some x → x.shape.answers ≠ 0 →
      x.groups = [k]) : leafOk S tree = true := by
  have hall : ∀ a ∈ leafGroups S tree, a = [k] := by
    intro a ha
    unfold leafGroups at ha
    obtain ⟨o, ho, hb⟩ := List.mem_filterMap.1 ha
    cases hx : S.oracles[o]? with
    | none => rw [hx] at hb; cases hb
    | some x =>
      rw [hx] at hb
      have hb' : (if x.shape.answers == 0 then none else some x.groups) = some a := hb
      split at hb'
      · cases hb'
      · rename_i hne
        rw [← Option.some.inj hb']
        exact h o ho x hx fun e => hne (by rw [e]; rfl)
  unfold leafOk
  cases hg : leafGroups S tree with
  | nil => rfl
  | cons a l =>
    have ea : a = [k] := hall a (by rw [hg]; simp)
    have el : ∀ b ∈ l, b = [k] := fun b hb => hall b (by rw [hg]; simp [hb])
    show (l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1))) = true
    rw [Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro b hb
      rw [el b hb, ea]
      exact beq_self_eq_true _
    · rw [ea]
      simp

/-! ## 6 Controls -/

/-- A message that lists a group which is not there: not tidy. -/
theorem tidy_can_fail :
    ¬ Tidy { oracles := #[{ shape := default, groups := [0] }] } := by
  intro h
  obtain ⟨M, hM, -⟩ := h.linked 0 [0] 0 rfl (by simp)
  simp [membersAt] at hM

/-- A member that does not list its group: not tidy. -/
theorem tidy_can_fail_listed :
    ¬ Tidy { oracles := #[{ shape := default }], groups := #[{ code := 0, members := #[0] }] } := by
  intro h
  obtain ⟨l, hl, hg⟩ := h.listed 0 #[0] 0 rfl (by simp)
  obtain rfl : [] = l := Option.some.inj hl
  cases hg

/-- A list that names a group twice: not tidy. -/
theorem tidy_can_fail_once :
    ¬ Tidy { oracles := #[{ shape := default, groups := [0, 0] }],
             groups := #[{ code := 0, members := #[0] }] } := by
  intro h
  have := h.once 0 [0, 0] rfl
  simp at this

/-- A marked group with a member that is not below N: not shut. -/
theorem shut_can_fail_below :
    ¬ Shut 1 0 { groups := #[{ code := 0, members := #[0], inRun := true }] } := by
  intro h
  obtain ⟨-, M, hM, hb⟩ := h 0 (by omega)
  obtain rfl : #[0] = M := Option.some.inj hM
  exact absurd (hb 0 (by simp)) (by omega)

/-- A group without the mark: not shut. -/
theorem shut_can_fail : ¬ Shut 1 0 { groups := #[{ code := 0 }] } := by
  intro h
  have := (h 0 (by omega)).1
  simp [markAt] at this

/-- Without Shut the conclusion of list_one can fail: a tidy statement of two groups, both of which
hold the message 0. -/
theorem list_one_wants_shut :
    ∃ T : Statement, Tidy T ∧ T.groups.size = 2 ∧ membersAt T 1 = some #[0] ∧
      listAt T 0 ≠ some [1] := by
  refine ⟨{ oracles := #[{ shape := default, groups := [0, 1] }],
            groups := #[{ code := 0, members := #[0] }, { code := 0, members := #[0] }] },
    ⟨fun o l g a b => ?_, fun g M o a b => ?_, fun o l a => ?_⟩, rfl, rfl, by simp [listAt]⟩
  · match o with
    | 0 =>
      obtain rfl : [0, 1] = l := Option.some.inj a
      simp only [List.mem_cons, List.not_mem_nil, or_false] at b
      rcases b with rfl | rfl
      · exact ⟨#[0], rfl, by simp⟩
      · exact ⟨#[0], rfl, by simp⟩
    | o + 1 => simp [listAt] at a
  · match g with
    | 0 =>
      obtain rfl : #[0] = M := Option.some.inj a
      obtain rfl : o = 0 := by simpa using b
      exact ⟨[0, 1], rfl, by simp⟩
    | 1 =>
      obtain rfl : #[0] = M := Option.some.inj a
      obtain rfl : o = 0 := by simpa using b
      exact ⟨[0, 1], rfl, by simp⟩
    | g + 2 => simp [membersAt] at a
  · match o with
    | 0 =>
      obtain rfl : [0, 1] = l := Option.some.inj a
      simp
    | o + 1 => simp [listAt] at a

/-- The test itself can fail: two sampled parts of one tree with different lists. -/
theorem leafOk_can_fail :
    leafOk { oracles := #[{ shape := { answers := 1 }, groups := [0] },
        { shape := { answers := 1 }, groups := [1] }] }
      { shape := default, parts := #[0, 1] } = false := by decide

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.listAt
#print axioms Johnson.AtFull.Shape.membersAt
#print axioms Johnson.AtFull.Shape.markAt
#print axioms Johnson.AtFull.Shape.Tidy
#print axioms Johnson.AtFull.Shape.Shut
#print axioms Johnson.AtFull.Shape.Tidy.congr
#print axioms Johnson.AtFull.Shape.Shut.congr
#print axioms Johnson.AtFull.Shape.listAt_modify
#print axioms Johnson.AtFull.Shape.membersAt_modify
#print axioms Johnson.AtFull.Shape.markAt_modify
#print axioms Johnson.AtFull.Shape.listAt_sent_of
#print axioms Johnson.AtFull.Shape.listAt_sent_old
#print axioms Johnson.AtFull.Shape.membersAt_new_of
#print axioms Johnson.AtFull.Shape.group_new_old
#print axioms Johnson.AtFull.Shape.listAt_joined
#print axioms Johnson.AtFull.Shape.membersAt_joined
#print axioms Johnson.AtFull.Shape.markAt_joined
#print axioms Johnson.AtFull.Shape.mem_of_insertIfIn
#print axioms Johnson.AtFull.Shape.Stays
#print axioms Johnson.AtFull.Shape.PlainKeeps
#print axioms Johnson.AtFull.Shape.PlainKeeps.ledgers
#print axioms Johnson.AtFull.Shape.groundKeeps_of
#print axioms Johnson.AtFull.Shape.stKeeps_of
#print axioms Johnson.AtFull.Shape.plain_tidy
#print axioms Johnson.AtFull.Shape.plain_shut
#print axioms Johnson.AtFull.Shape.stKeeps_tidy
#print axioms Johnson.AtFull.Shape.stKeeps_shut
#print axioms Johnson.AtFull.Shape.tidy_start
#print axioms Johnson.AtFull.Shape.eq_single
#print axioms Johnson.AtFull.Shape.list_one
#print axioms Johnson.AtFull.Shape.leafOk_of_lists
#print axioms Johnson.AtFull.Shape.tidy_can_fail
#print axioms Johnson.AtFull.Shape.tidy_can_fail_listed
#print axioms Johnson.AtFull.Shape.tidy_can_fail_once
#print axioms Johnson.AtFull.Shape.shut_can_fail_below
#print axioms Johnson.AtFull.Shape.shut_can_fail
#print axioms Johnson.AtFull.Shape.list_one_wants_shut
#print axioms Johnson.AtFull.Shape.leafOk_can_fail
