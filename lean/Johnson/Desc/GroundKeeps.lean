-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/GroundKeeps.lean: what a relation R on statements owes so that every step which writes
the statement through the ground's plain functions keeps it: R is reflexive and transitive, and each
of these functions, BUT FOR THE BEGINNING OF A PROXIMITY TEST, keeps it. A kind's step is then
proved once, for every such R. Theorems.

  GroundKeeps R        the record of what is owed: ten functions.
  GroundKeeps.addRowsFrom · addRows · takeMasksInto · takeMasks   the four that are made of these.
  GroundKeeps.and      two such relations together are one.
  groundKeeps_grows    "a statement only grows" is such a relation.
  groundKeeps_noNew    "no new mark" is such a relation.
  By R st              the relation on records: R at the statements that st reads.
What is not claimed. beginRunP is left out on purpose: it lays the mark. Nothing on a step that
writes the statement by another road than these functions.

-/
import Johnson.Desc.GrowsGround
import Johnson.Desc.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- What a relation on statements owes. -/
structure GroundKeeps (R : Statement → Statement → Prop) : Prop where
  refl : ∀ T, R T T
  trans : ∀ {A B C}, R A B → R B C → R A C
  newGroup : ∀ {L : Type} (d d' : DState L) (code maskCode n : Nat),
    newGroupP d code maskCode = some (n, d') → R d.st d'.st
  recv : ∀ {L : Type} (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat),
    recvP ft d sent = some (ids, d') → R d.st d'.st
  admit : ∀ {L : Type} (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row),
    admitP d o rows = some d' → R d.st d'.st
  join : ∀ {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool),
    joinP d g o kept = some d' → R d.st d'.st
  addRow : ∀ {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row),
    addRowP d g row = some d' → R d.st d'.st
  takeMask : ∀ {L : Type} (d d' : DState L) (o n : Nat),
    takeMaskP d o = some (n, d') → R d.st d'.st
  closeLedger : ∀ {L : Type} (d d' : DState L) (o : Nat), closeLedgerP d o = some d' → R d.st d'.st
  spendAsMask : ∀ {L : Type} (d d' : DState L) (o : Nat), spendAsMaskP d o = some d' → R d.st d'.st
  adopt : ∀ {L : Type} (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat),
    adoptP d sent given = some (ids, d') → R d.st d'.st
  elsewhere : ∀ {L : Type} (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat),
    elsewhereP d mine other theirs = some d' → R d.st d'.st

variable {R : Statement → Statement → Prop} {L : Type}

/-- Rows added one behind the other keep R. -/
theorem GroundKeeps.addRowsFrom (H : GroundKeeps R) (g : Nat) (rows : List OnBytes.Row) :
    ∀ (d d' : DState L), addRowsFrom g rows d = some d' → R d.st d'.st := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [Ground.addRowsFrom, Option.some.injEq] at h
    subst h
    exact H.refl _
  | cons row l ih =>
    intro d d' h
    simp only [Ground.addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact H.trans (H.addRow d e g row h1) (ih e d' h)

/-- Rows added to a group keep R. -/
theorem GroundKeeps.addRows (H : GroundKeeps R) (d d' : DState L) (g : Nat)
    (rows : List OnBytes.Row) (h : addRowsP d g rows = some d') : R d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact H.addRowsFrom g rows d d' h
  · cases h

/-- Entries of a mask taken one behind the other keep R. -/
theorem GroundKeeps.takeMasksInto (H : GroundKeeps R) (o : Nat) (count : Nat) :
    ∀ (d d' : DState L) (acc : Array Nat) (r : List Nat),
      takeMasksInto o count d acc = some (r, d') → R d.st d'.st := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [Ground.takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact H.refl _
  | succ n ih =>
    intro d d' acc r h
    simp only [Ground.takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact H.trans (H.takeMask d e o i h1) (ih e d' _ r h)

/-- So many entries of a mask taken keep R. -/
theorem GroundKeeps.takeMasks (H : GroundKeeps R) (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : R d.st d'.st :=
  H.takeMasksInto o count d d' #[] r h

/-- Two such relations together are one. -/
theorem GroundKeeps.and {R' : Statement → Statement → Prop} (H : GroundKeeps R)
    (K : GroundKeeps R') : GroundKeeps fun a b => R a b ∧ R' a b where
  refl := fun T => ⟨H.refl T, K.refl T⟩
  trans := fun a b => ⟨H.trans a.1 b.1, K.trans a.2 b.2⟩
  newGroup := fun d d' c m n h => ⟨H.newGroup d d' c m n h, K.newGroup d d' c m n h⟩
  recv := fun f d d' s i h => ⟨H.recv f d d' s i h, K.recv f d d' s i h⟩
  admit := fun d d' o r h => ⟨H.admit d d' o r h, K.admit d d' o r h⟩
  join := fun d d' g o k h => ⟨H.join d d' g o k h, K.join d d' g o k h⟩
  addRow := fun d d' g r h => ⟨H.addRow d d' g r h, K.addRow d d' g r h⟩
  takeMask := fun d d' o n h => ⟨H.takeMask d d' o n h, K.takeMask d d' o n h⟩
  closeLedger := fun d d' o h => ⟨H.closeLedger d d' o h, K.closeLedger d d' o h⟩
  spendAsMask := fun d d' o h => ⟨H.spendAsMask d d' o h, K.spendAsMask d d' o h⟩
  adopt := fun d d' s g i h => ⟨H.adopt d d' s g i h, K.adopt d d' s g i h⟩
  elsewhere := fun d d' m o t h => ⟨H.elsewhere d d' m o t h, K.elsewhere d d' m o t h⟩

/-- "A statement only grows" is such a relation. -/
theorem groundKeeps_grows : GroundKeeps Grows where
  refl := Grows.refl
  trans := Grows.trans
  newGroup := fun d d' c m n h => newGroupP_grows d d' c m n h
  recv := fun f d d' s i h => recvP_grows f d d' s i h
  admit := fun d d' o r h => admitP_grows d d' o r h
  join := fun d d' g o k h => joinP_grows d d' g o k h
  addRow := fun d d' g r h => addRowP_grows d d' g r h
  takeMask := fun d d' o n h => takeMaskP_grows d d' o n h
  closeLedger := fun d d' o h => closeLedgerP_grows d d' o h
  spendAsMask := fun d d' o h => spendAsMaskP_grows d d' o h
  adopt := fun d d' s g i h => adoptP_grows d d' s g i h
  elsewhere := fun d d' m o t h => elsewhereP_grows d d' m o t h

/-- "No new mark" is such a relation. -/
theorem groundKeeps_noNew : GroundKeeps NoNewMark where
  refl := NoNewMark.refl
  trans := NoNewMark.trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact noNew_withGroup d.st code maskCode
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact noNew_stSent d.st sent
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, -, places, -, rfl⟩ := h
      exact noNew_admitted d.st o x.shape places rows
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
        exact noNew_joined d.st g o kept G
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact noNew_withRow d.st g row
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
        exact noNew_oracles d.st _
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact noNew_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact noNew_oracles d.st _
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold adoptP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact noNew_stSent d.st sent
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
        exact noNew_oracles d.st _
    · cases h

/-- The relation on records: R at the statements that st reads. -/
def By {S : Type} (R : Statement → Statement → Prop) (st : S → Statement) : S → S → Prop :=
  fun s s' => R (st s) (st s')

/-- The relation on records is reflexive. -/
theorem GroundKeeps.by_refl {S : Type} (H : GroundKeeps R) (st : S → Statement) (s : S) :
    By R st s s := H.refl _

/-- The relation on records is transitive. -/
theorem GroundKeeps.by_trans {S : Type} (H : GroundKeeps R) (st : S → Statement) (a b c : S)
    (h : By R st a b) (k : By R st b c) : By R st a c := H.trans h k

end VerifiableInference.Desc.Ground
