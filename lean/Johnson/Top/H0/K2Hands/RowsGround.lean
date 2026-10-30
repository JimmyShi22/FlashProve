-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/RowsGround.lean: what the plain functions by which a step of the description
changes the statement (Johnson/Desc/First/Base/Ground.lean) do to the messages' shapes and stored
sample rows. One theorem for each function, general in the state's own part L. A law file; no
running text imports it.

The twin in form of Johnson/Desc/GrowsGround.lean, which says of the same functions that no group or
message is dropped and no mark taken back, and says nothing on rows. Here, in SampleChain.lean's
words:
  SameRows (the codes, and every message's shape and stored rows, stay):
     newGroupP · joinP · addRowP · addRowsFrom · addRowsP · takeMaskP · takeMasksInto · takeMasksP ·
     closeLedgerP · spendAsMaskP · beginRunP: each name with _rows behind it.
  recvP_rows, adoptP_rows: OldRows, and a new message has no stored row (NoNewRows); so
     recvP_inv, adoptP_inv: they keep RowsInv Q at every Q.
  admitP_rows: the one function of these that writes stored rows: every other message stays; the
     message o keeps its shape and has just the rows that were handed in.
  admitP_inv: so it keeps RowsInv Q if Q holds of these rows.
Tools: sameRows_groups, sameRows_modOracle, sameRows_closeLedgers.
No proof reads a function's test: the theorems hold whatever the named clauses ask.
Limits. elsewhereP (a message is marked as sampled on another chain: it copies that chain's stored
rows) is not treated: no block of the first chain calls it, by grep. sendP and the loop over the
messages to sample (Johnson/Desc/Ground/Calls.lean) are not treated: K2Hears/SentRows.lean has them.
Nothing on a step that writes the statement by another road than these functions. Nothing on
soundness.

-/
import Johnson.Top.H0.K2Hands.SampleChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## Tools -/

theorem sameRows_groups (S : Statement) (G : Array Group) : SameRows S { S with groups := G } :=
  ⟨rfl, fun _ => rfl⟩

theorem sameRows_modOracle (S : Statement) (o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).shape = x.shape ∧ (f x).sampleRows = x.sampleRows) :
    SameRows S { S with oracles := S.oracles.modify o f } := by
  refine ⟨rfl, fun j => ?_⟩
  show ((S.oracles.modify o f)[j]?).map _ = _
  rw [Array.getElem?_modify]
  split
  · cases S.oracles[j]? with
    | none => rfl
    | some x => simp [(hf x).1, (hf x).2]
  · rfl

theorem sameRows_closeLedgers : ∀ (l : List Nat) (S : Statement), SameRows S (closeLedgers S l)
  | [], S => SameRows.refl S
  | o :: l, S => by
    have h1 := sameRows_modOracle S o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun _ => ⟨rfl, rfl⟩
    exact h1.trans (sameRows_closeLedgers l _)

/-! ## The functions that leave the stored rows -/

theorem newGroupP_rows (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : SameRows d.st d'.st := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact sameRows_groups d.st _
  · cases h

theorem joinP_rows (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : SameRows d.st d'.st := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      exact (sameRows_modOracle d.st o (fun x => { x with groups := x.groups ++ [g] })
        fun _ => ⟨rfl, rfl⟩).trans (sameRows_groups _ _)
  · cases h

theorem addRowP_rows (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : SameRows d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact sameRows_groups d.st _
  · cases h

theorem addRowsFrom_rows (g : Nat) (rows : List OnBytes.Row) : ∀ (d d' : DState L),
    addRowsFrom g rows d = some d' → SameRows d.st d'.st := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact SameRows.refl _
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact (addRowP_rows d e g row h1).trans (ih e d' h)

theorem addRowsP_rows (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') : SameRows d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_rows g rows d d' h
  · cases h

theorem takeMaskP_rows (d d' : DState L) (o n : Nat)
    (h : takeMaskP d o = some (n, d')) : SameRows d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact sameRows_modOracle d.st o _ fun _ => ⟨rfl, rfl⟩
  · cases h

theorem takeMasksInto_rows (o : Nat) (count : Nat) : ∀ (d d' : DState L) (acc : Array Nat)
    (r : List Nat), takeMasksInto o count d acc = some (r, d') → SameRows d.st d'.st := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact SameRows.refl _
  | succ n ih =>
    intro d d' acc r h
    simp only [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact (takeMaskP_rows d e o i h1).trans (ih e d' _ r h)

theorem takeMasksP_rows (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : SameRows d.st d'.st :=
  takeMasksInto_rows o count d d' #[] r h

theorem closeLedgerP_rows (d d' : DState L) (o : Nat)
    (h : closeLedgerP d o = some d') : SameRows d.st d'.st := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact sameRows_closeLedgers [o] d.st
  · cases h

theorem spendAsMaskP_rows (d d' : DState L) (o : Nat)
    (h : spendAsMaskP d o = some d') : SameRows d.st d'.st := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact sameRows_modOracle d.st o _ fun _ => ⟨rfl, rfl⟩
  · cases h

theorem beginRunP_rows (d d' : DState L) (g : Nat) (r : RunInput)
    (h : beginRunP d g = some (r, d')) : SameRows d.st d'.st := by
  unfold beginRunP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨G, -, -, rfl⟩ := h
    exact (sameRows_closeLedgers G.members.toList d.st).trans (sameRows_groups _ _)
  · cases h

/-! ## New messages without a stored row -/

/-- No message from number n on has a stored row. -/
def NoNewRows (n : Nat) (St : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), n ≤ o → St.oracles[o]? = some x → x.sampleRows.size = 0

theorem newInv_of_none {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {n : Nat}
    {St : Statement} (h : NoNewRows n St) : NewInv Q n St :=
  fun o x ho hx hs => absurd (h o x ho hx) hs

theorem stSent_rows (S : Statement) (sent : Array OracleNotice) :
    OldRows S (stSent S sent) ∧ NoNewRows S.oracles.size (stSent S sent) := by
  refine ⟨⟨rfl, fun j hj => by rw [stSent_old S sent j hj]⟩, fun o x ho hx => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, o = S.oracles.size + i := ⟨o - S.oracles.size, by omega⟩
  rw [stSent_new] at hx
  obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  rfl

theorem recvP_rows (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) :
    OldRows d.st d'.st ∧ NoNewRows d.st.oracles.size d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact stSent_rows d.st sent
  · cases h

theorem adoptP_rows (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) :
    OldRows d.st d'.st ∧ NoNewRows d.st.oracles.size d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact stSent_rows d.st sent
  · cases h

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop}

theorem recvP_inv (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) (hd : RowsInv Q d.st) :
    RowsInv Q d'.st :=
  rowsInv_oldRows (recvP_rows firstTree d d' sent ids h).1
    (newInv_of_none (recvP_rows firstTree d d' sent ids h).2) hd

theorem adoptP_inv (d d' : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (ids : Array Nat) (h : adoptP d sent given = some (ids, d')) (hd : RowsInv Q d.st) :
    RowsInv Q d'.st :=
  rowsInv_oldRows (adoptP_rows d d' sent given ids h).1
    (newInv_of_none (adoptP_rows d d' sent given ids h).2) hd

/-! ## The function that writes stored rows -/

theorem admitP_rows (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') :
    d'.st.codes = d.st.codes ∧ (∀ j, j ≠ o → d'.st.oracles[j]? = d.st.oracles[j]?) ∧
      ∃ x x', d.st.oracles[o]? = some x ∧ d'.st.oracles[o]? = some x' ∧ x'.shape = x.shape ∧
        x'.sampleRows = rows := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, places, -, rfl⟩ := h
    refine ⟨rfl, fun j hj => ?_, x, { x with
      sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
      ledger := freshLedger d.st.codes x.shape }, hx, ?_, rfl, rfl⟩
    · show ((d.st.oracles.modify o _)[j]?) = _
      rw [Array.getElem?_modify, if_neg (fun e => hj e.symm)]
    · show ((d.st.oracles.modify o _)[o]?) = _
      rw [Array.getElem?_modify, if_pos rfl, hx]
      rfl
  · cases h

theorem admitP_inv (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') (hd : RowsInv Q d.st)
    (hq : ∀ x, d.st.oracles[o]? = some x → Q d.st.codes x.shape o rows) : RowsInv Q d'.st := by
  obtain ⟨hc, hj, x, x', hx, hx', e1, e2⟩ := admitP_rows d d' o rows h
  intro j y hy hs
  rw [hc]
  by_cases e : j = o
  · subst e
    rw [hx'] at hy
    obtain rfl := Option.some.inj hy
    rw [e1, e2]
    exact hq x hx
  · rw [hj j e] at hy
    exact hd j y hy hs

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.beginRunP_rows
#print axioms VerifiableInference.Desc.First.K2.joinP_rows
#print axioms VerifiableInference.Desc.First.K2.recvP_inv
#print axioms VerifiableInference.Desc.First.K2.admitP_inv
