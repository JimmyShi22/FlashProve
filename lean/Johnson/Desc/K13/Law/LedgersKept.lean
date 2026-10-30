-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersKept.lean: THE PROOF OF THE STATEMENT THAT
Johnson/Desc/K13/Law/OwedLedgers.lean WRITES AS OWED: every routine of the ground keeps "every
ledger in the statement is in order" (LedgersFit).

  NoNewLedger T T'   no ledger comes from nowhere: a ledger in T' was a ledger in T, or is that of
                     no take.
  ..._noNew          of each routine: messages that are received or taken over come without a
                     ledger; a message marked as sampled on another chain gets none; THE ADMITTING
                     IS THE ONE MAKER, and what it lays is the ledger of no take (a mask row: by the
                     maker's own test; an answer: by the admitting's fifth clause).
  fit_of             with OkStays (Johnson/Desc/K13/Law/LedgerOk.lean) that gives LedgersFit behind.
  ledgersKept        the owed statement.
  ledgersFit_none    a statement without a message is in order: the chain's start.

What is not claimed. Of a text that writes a statement's messages and is no routine of the ground
(the pending row's take: takeEntry_inside, LedgerOk.lean, has its core). Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.LedgerOk
import Johnson.Desc.K13.Law.OwedLedgers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground

/-! ## 1 No ledger comes from nowhere -/

/-- A ledger behind was a ledger in front, or is that of no take. -/
def NoNewLedger (T T' : Statement) : Prop :=
  ∀ (o : ℕ) (x' : OnBytes.Oracle), T'.oracles[o]? = some x' → x'.ledger.isSome = true →
    (∃ x : OnBytes.Oracle, T.oracles[o]? = some x ∧ x.ledger.isSome = true) ∨ LedgerAt T' o 0

theorem fit_of {T T' : Statement} (hO : OkStays T T') (hB : NoNewLedger T T')
    (h : LedgersFit T) : LedgersFit T' := fun o x' hx' hl =>
  (hB o x' hx' hl).elim (fun ⟨x, hx, hs⟩ => hO o (h o x hx hs)) fun h0 => ⟨0, h0⟩

theorem noNew_modify {T T' : Statement} (j : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (ho : T'.oracles = T.oracles.modify j f)
    (hf : ∀ x, T.oracles[j]? = some x → (f x).ledger.isSome = true → x.ledger.isSome = true) :
    NoNewLedger T T' := by
  intro o x' h hl
  rw [ho, Array.getElem?_modify] at h
  by_cases e : j = o
  · subst e
    rw [if_pos rfl] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inl ⟨x, hx, hf x hx hl⟩
  · rw [if_neg e] at h
    exact Or.inl ⟨x', h, hl⟩

theorem noNew_modify₀ (T : Statement) (j : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, T.oracles[j]? = some x → (f x).ledger.isSome = true → x.ledger.isSome = true) :
    NoNewLedger T { T with oracles := T.oracles.modify j f } :=
  noNew_modify (T := T) (T' := { T with oracles := T.oracles.modify j f }) j f rfl hf

theorem noNew_sent (T : Statement) (sent : Array OracleNotice) :
    NoNewLedger T (stSent T sent) := by
  intro o x' hx' hl
  have h : (T.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? =
      some x' := hx'
  by_cases ho : o < T.oracles.size
  · rw [Array.getElem?_append_left ho] at h
    exact Or.inl ⟨x', h, hl⟩
  · rw [Array.getElem?_append_right (Nat.le_of_not_lt ho), Array.getElem?_map] at h
    obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 h
    cases hl

variable {L : Type}

theorem newGroupP_noNew (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : NoNewLedger d.st d'.st := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun o x' hx' hl => Or.inl ⟨x', hx', hl⟩
  · cases h

theorem recvP_noNew (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) : NoNewLedger d.st d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact noNew_sent d.st sent
  · cases h

/-- **The one maker**: the ledger that the admitting lays is that of no take. -/
theorem admitP_noNew (d d' : DState L) (j : Nat) (rows : Array OnBytes.Row)
    (h : admitP d j rows = some d') : NoNewLedger d.st d'.st := by
  unfold admitP at h
  split at h
  · rename_i hok
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, places, -, rfl⟩ := h
    intro o x' hx' hl
    have hx : (d.st.oracles.modify j fun x => { x with
        sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes y.shape })[o]? = some x' := hx'
    rw [Array.getElem?_modify] at hx
    by_cases e : j = o
    · subst e
      rw [if_pos rfl, hy] at hx
      obtain rfl := Option.some.inj hx
      have hm : 0 < y.shape.maskRows := by
        have hl' : (freshLedger d.st.codes y.shape).isSome = true := hl
        unfold freshLedger at hl'
        by_cases hm : 0 < y.shape.maskRows
        · exact hm
        · rw [if_neg hm] at hl'
          cases hl'
      have ha : 1 ≤ y.shape.answers := by
        simp only [ok, admitL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          hy] at hok
        exact of_decide_eq_true hok.2.2.2.2
      refine Or.inr (ledgerAt_made hx' hm ha ?_)
      show freshLedger d.st.codes y.shape = _
      unfold freshLedger
      rw [if_pos hm]
      rfl
    · rw [if_neg e] at hx
      exact Or.inl ⟨x', hx, hl⟩
  · cases h

theorem joinP_noNew (d d' : DState L) (g j : Nat) (kept : Bool)
    (h : joinP d g j kept = some d') : NoNewLedger d.st d'.st := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      exact noNew_modify (T := d.st) (T' := withMessageInGroup d.st g j kept G) j
        (fun x => { x with groups := x.groups ++ [g] }) rfl fun _ _ hl => hl
  · cases h

theorem addRowP_noNew (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : NoNewLedger d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact fun o x' hx' hl => Or.inl ⟨x', hx', hl⟩
  · cases h

theorem takeMaskP_noNew (d d' : DState L) (j n : Nat)
    (h : takeMaskP d j = some (n, d')) : NoNewLedger d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[j]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine noNew_modify₀ d.st j _ ?_
      intro x hx _
      rw [hx] at hl
      have hl' : x.ledger = some l := hl
      rw [hl']
      rfl
  · cases h

theorem closeLedgerP_noNew (d d' : DState L) (j : Nat)
    (h : closeLedgerP d j = some d') : NoNewLedger d.st d'.st := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine noNew_modify (T := d.st) j
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } }) ?_ ?_
    · rfl
    · intro x _ hl
      have hl' : (x.ledger.map fun l => { l with closed := true }).isSome = true := hl
      rw [Option.isSome_map] at hl'
      exact hl'
  · cases h

theorem spendAsMaskP_noNew (d d' : DState L) (j : Nat)
    (h : spendAsMaskP d j = some d') : NoNewLedger d.st d'.st := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine noNew_modify₀ d.st j _ ?_
    exact fun _ _ hl => hl
  · cases h

theorem adoptP_noNew (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) : NoNewLedger d.st d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact noNew_sent d.st sent
  · cases h

theorem elsewhereP_noNew (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : NoNewLedger d.st d'.st := by
  unfold elsewhereP at h
  split at h
  · cases hy : other.oracles[theirs]? with
    | none => simp [hy] at h
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at h
      subst h
      refine noNew_modify₀ d.st mine _ ?_
      exact fun _ _ hl => hl
  · cases h

/-! ## 2 The owed statement -/

/-- **EVERY ROUTINE OF THE GROUND KEEPS «every ledger in the statement is in order».** -/
theorem ledgersKept : OwedLedgersKept where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun d d' c m n h => fit_of (newGroupP_ok d d' c m n h) (newGroupP_noNew d d' c m n h)
  recv := fun f d d' s i h => fit_of (recvP_ok f d d' s i h) (recvP_noNew f d d' s i h)
  admit := fun d d' o r h => fit_of (admitP_ok d d' o r h) (admitP_noNew d d' o r h)
  join := fun d d' g o k h => fit_of (joinP_ok d d' g o k h) (joinP_noNew d d' g o k h)
  addRow := fun d d' g r h => fit_of (addRowP_ok d d' g r h) (addRowP_noNew d d' g r h)
  takeMask := fun d d' o n h => fit_of (takeMaskP_ok d d' o n h) (takeMaskP_noNew d d' o n h)
  closeLedger := fun d d' o h => fit_of (closeLedgerP_ok d d' o h) (closeLedgerP_noNew d d' o h)
  spendAsMask := fun d d' o h => fit_of (spendAsMaskP_ok d d' o h) (spendAsMaskP_noNew d d' o h)
  adopt := fun d d' s g i h => fit_of (adoptP_ok d d' s g i h) (adoptP_noNew d d' s g i h)
  elsewhere := fun d d' m o t h =>
    fit_of (elsewhereP_ok d d' m o t h) (elsewhereP_noNew d d' m o t h)

/-- A statement without a message is in order: the chain's start. -/
theorem ledgersFit_none (st : Statement) (h : st.oracles = #[]) : LedgersFit st := by
  intro o x hx
  rw [h] at hx
  simp at hx

end VerifiableInference.Desc.K13.Law
