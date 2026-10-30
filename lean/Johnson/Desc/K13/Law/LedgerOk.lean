-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgerOk.lean: EVERY ROUTINE OF THE GROUND KEEPS A LEDGER IN ORDER, message by
message.

A sampled oracle message with mask rows has a ledger, the verifier's own counter, which hands out
the free entries of its mask table one by one. LedgerAt st o k
(Johnson/Desc/K13/Law/LedgerWithin.lean) says: the ledger of message o is that of k takes since it
was made.

  LedSame, ledgerAt_same   what that sentence reads of a message: its shape and the ledger's four
                    numbers (not whether it is shut); with the code table: where these stay, it
                    stays.
  LedgerOk st o     the ledger of o is in order: that of SOME number of takes. What is left fixes
                    the number.
  OkStays T T'      every ledger in order in T is in order in T'.
  groundKeeps_ledgerOk   GroundKeeps OkStays (Johnson/Desc/GroundKeeps.lean): a take at o goes from
                    k to k + 1; the admitting of o lays the ledger of no take; the shutting turns
                    "closed" alone; every other routine leaves what the sentence reads.
  sendAtS_ledgerOk, commitAtS_ledgerOk, firstAtS_ledgerOk, atM3_ledgerOk, atM4_ledgerOk   so K1's
                    and K13's blocks of the first chain keep it, by their laws.
  takeMasksP_inside, takeEntry_inside   what it buys: where the ledger is in order, an entry that is
                    given lies within its mask table, and the ledger behind is in order.

WHY "SOME NUMBER". "The ledger of o stays" is no GroundKeeps relation: that structure has a field
for a take at any message. "In order" is one, and needs no number of the plan.

What is not claimed. That any ledger of a chain's state is in order at the chain's start or at its
making (ledgerAt_made, LedgerWithin.lean; the first sending's law is another file's). The number of
takes at a border. That an entry given is no entry of the pad. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K13.Law.LedgerWithin
import Johnson.Desc.GroundKeeps
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (takeEntry pendingRowO)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Keeps (Decides)

/-! ## 1 What the sentence reads of a message -/

/-- The shape, and the ledger's four numbers: not whether it is shut. -/
def LedSame (x x' : OnBytes.Oracle) : Prop :=
  x'.shape = x.shape ∧ ∀ l, x.ledger = some l → ∃ l', x'.ledger = some l' ∧ l'.next = l.next ∧
    l'.left = l.left ∧ l'.rows = l.rows ∧ l'.logRows = l.logRows

theorem LedSame.refl (x : OnBytes.Oracle) : LedSame x x :=
  ⟨rfl, fun l h => ⟨l, h, rfl, rfl, rfl, rfl⟩⟩

/-- The sentence goes on where the code table, the message's shape and these four numbers stay. -/
theorem ledgerAt_same {T T' : Statement} {o k : ℕ} (hc : T'.codes = T.codes)
    (h : ∀ x, T.oracles[o]? = some x → ∃ x', T'.oracles[o]? = some x' ∧ LedSame x x')
    (hk : LedgerAt T o k) : LedgerAt T' o k := by
  obtain ⟨x, l, hx, hl, hm, ha, hr, hq, hleft, hnext⟩ := hk
  obtain ⟨x', hx', hs, hL⟩ := h x hx
  obtain ⟨l', hl', e1, e2, e3, e4⟩ := hL l hl
  refine ⟨x', l', hx', hl', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact hm
  · rw [hs]; exact ha
  · rw [hs, e3]; exact hr
  · rw [hs, e4]; exact hq
  · rw [hs, hc, e2]; exact hleft
  · rw [hs, e1]; exact hnext

/-- One message is turned, by a change that leaves what the sentence reads. -/
theorem ledgerAt_modify {T T' : Statement} (j : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hc : T'.codes = T.codes) (ho : T'.oracles = T.oracles.modify j f)
    (hf : ∀ x, LedSame x (f x)) {o k : ℕ} (hk : LedgerAt T o k) : LedgerAt T' o k := by
  refine ledgerAt_same hc (fun x hx => ?_) hk
  rw [ho, Array.getElem?_modify]
  by_cases e : j = o
  · rw [if_pos e, hx]
    exact ⟨f x, rfl, hf x⟩
  · rw [if_neg e]
    exact ⟨x, hx, LedSame.refl x⟩

/-- Another message is turned. -/
theorem ledgerAt_other {T T' : Statement} (j : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hc : T'.codes = T.codes) (ho : T'.oracles = T.oracles.modify j f) {o k : ℕ} (hne : j ≠ o)
    (hk : LedgerAt T o k) : LedgerAt T' o k := by
  refine ledgerAt_same hc (fun x hx => ?_) hk
  rw [ho, Array.getElem?_modify, if_neg hne]
  exact ⟨x, hx, LedSame.refl x⟩

/-- The two, where nothing but the messages is turned. -/
theorem ledgerAt_modify₀ (T : Statement) (j : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, LedSame x (f x)) {o k : ℕ} (hk : LedgerAt T o k) :
    LedgerAt { T with oracles := T.oracles.modify j f } o k :=
  ledgerAt_modify (T := T) (T' := { T with oracles := T.oracles.modify j f }) j f rfl rfl hf hk

theorem ledgerAt_other₀ (T : Statement) (j : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle) {o k : ℕ}
    (hne : j ≠ o) (hk : LedgerAt T o k) :
    LedgerAt { T with oracles := T.oracles.modify j f } o k :=
  ledgerAt_other (T := T) (T' := { T with oracles := T.oracles.modify j f }) j f rfl rfl hne hk

/-- Messages come behind. -/
theorem ledgerAt_sent (T : Statement) (sent : Array OracleNotice) {o k : ℕ}
    (hk : LedgerAt T o k) : LedgerAt (stSent T sent) o k := by
  refine ledgerAt_same (T := T) rfl (fun x hx => ⟨x, ?_, LedSame.refl x⟩) hk
  have ho : o < T.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  show (T.oracles ++ _)[o]? = some x
  rw [Array.getElem?_append_left ho]
  exact hx

/-! ## 2 In order -/

/-- **The ledger of message o is in order**: it is that of some number of takes since it was made.
The number is fixed by what is left. -/
def LedgerOk (st : Statement) (o : ℕ) : Prop := ∃ k, LedgerAt st o k

/-- Every ledger that is in order in front is in order behind. -/
def OkStays (T T' : Statement) : Prop := ∀ o, LedgerOk T o → LedgerOk T' o

variable {L : Type}

theorem newGroupP_ok (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : OkStays d.st d'.st := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun o ⟨k, hk⟩ => ⟨k, hk⟩
  · cases h

theorem recvP_ok (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) : OkStays d.st d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact fun o ⟨k, hk⟩ => ⟨k, ledgerAt_sent d.st sent hk⟩
  · cases h

/-- At the message that is admitted the ledger is made anew: that of no take. -/
theorem admitP_ok (d d' : DState L) (j : Nat) (rows : Array OnBytes.Row)
    (h : admitP d j rows = some d') : OkStays d.st d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, places, -, rfl⟩ := h
    intro o ⟨k, hk⟩
    by_cases e : j = o
    · subst e
      obtain ⟨x, l, hx, -, hm, ha, -⟩ := hk
      obtain rfl : y = x := Option.some.inj (hy.symm.trans hx)
      refine ⟨0, ledgerAt_made (x := { y with
        sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes y.shape }) ?_ hm ha ?_⟩
      · show (d.st.oracles.modify j _)[j]? = _
        rw [Array.getElem?_modify, if_pos rfl, hx]
        rfl
      · show freshLedger d.st.codes y.shape = _
        unfold freshLedger
        rw [if_pos hm]
        rfl
    · exact ⟨k, ledgerAt_other (T := d.st) (T' := admitted d.st j y.shape places rows) j
        (fun x => { x with
          sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
          ledger := freshLedger d.st.codes y.shape }) rfl rfl e hk⟩
  · cases h

theorem joinP_ok (d d' : DState L) (g j : Nat) (kept : Bool)
    (h : joinP d g j kept = some d') : OkStays d.st d'.st := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      rintro o ⟨k, hk⟩
      refine ⟨k, ?_⟩
      exact ledgerAt_modify (T := d.st) (T' := withMessageInGroup d.st g j kept G) j
        (fun x => { x with groups := x.groups ++ [g] }) rfl rfl
        (fun x => ⟨rfl, fun l hl => ⟨l, hl, rfl, rfl, rfl, rfl⟩⟩) hk
  · cases h

theorem addRowP_ok (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : OkStays d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact fun o ⟨k, hk⟩ => ⟨k, hk⟩
  · cases h

/-- **A take**: at the message itself one take more; elsewhere nothing. -/
theorem takeMaskP_ok (d d' : DState L) (j n : Nat)
    (h : takeMaskP d j = some (n, d')) : OkStays d.st d'.st := by
  intro o ⟨k, hk⟩
  by_cases e : j = o
  · subst e
    exact ⟨k + 1, (takeMaskP_within hk h).2.2⟩
  · unfold takeMaskP at h
    split at h
    · cases hl : (d.st.oracles[j]?).bind (·.ledger) with
      | none => simp [hl] at h
      | some l =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨k, ?_⟩
        exact ledgerAt_other₀ d.st j _ e hk
    · cases h

theorem closeLedgerP_ok (d d' : DState L) (j : Nat)
    (h : closeLedgerP d j = some d') : OkStays d.st d'.st := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rintro o ⟨k, hk⟩
    refine ⟨k, ?_⟩
    refine ledgerAt_modify (T := d.st) j
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } }) ?_ ?_ ?_ hk
    · rfl
    · rfl
    · exact fun x => ⟨rfl, fun l hl =>
        ⟨{ l with closed := true }, by simp [hl], rfl, rfl, rfl, rfl⟩⟩
  · cases h

theorem spendAsMaskP_ok (d d' : DState L) (j : Nat)
    (h : spendAsMaskP d j = some d') : OkStays d.st d'.st := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rintro o ⟨k, hk⟩
    refine ⟨k, ?_⟩
    refine ledgerAt_modify₀ d.st j _ ?_ hk
    exact fun x => ⟨rfl, fun l hl => ⟨l, hl, rfl, rfl, rfl, rfl⟩⟩
  · cases h

theorem adoptP_ok (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) : OkStays d.st d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact fun o ⟨k, hk⟩ => ⟨k, ledgerAt_sent d.st sent hk⟩
  · cases h

theorem elsewhereP_ok (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : OkStays d.st d'.st := by
  unfold elsewhereP at h
  split at h
  · cases hy : other.oracles[theirs]? with
    | none => simp [hy] at h
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at h
      subst h
      rintro o ⟨k, hk⟩
      refine ⟨k, ?_⟩
      refine ledgerAt_modify₀ d.st mine _ ?_ hk
      exact fun x => ⟨rfl, fun l hl => ⟨l, hl, rfl, rfl, rfl, rfl⟩⟩
  · cases h

/-- **EVERY ROUTINE OF THE GROUND KEEPS THE LEDGERS IN ORDER.** -/
theorem groundKeeps_ledgerOk : GroundKeeps OkStays where
  refl := fun _ _ h => h
  trans := fun h k o x => k o (h o x)
  newGroup := newGroupP_ok
  recv := recvP_ok
  admit := admitP_ok
  join := joinP_ok
  addRow := addRowP_ok
  takeMask := takeMaskP_ok
  closeLedger := closeLedgerP_ok
  spendAsMask := spendAsMaskP_ok
  adopt := adoptP_ok
  elsewhere := elsewhereP_ok

/-! ## 3 So K1's and K13's blocks of the first chain do -/

variable {Cl : Type}

theorem sendAtS_ledgerOk (P : K1.Par) :
    Decides (By OkStays fun s : S => s.st) (K1.sendAtS (Cl := Cl) P) :=
  K1.Rel.sendAtS_keeps groundKeeps_ledgerOk P

theorem commitAtS_ledgerOk (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides (By OkStays fun s : S => s.st) (K1.commitAtS (Cl := Cl) P link moment arrays) :=
  K1.Rel.commitAtS_keeps groundKeeps_ledgerOk P link moment arrays

theorem firstAtS_ledgerOk (q : Params.First) (gp : GPar) :
    Decides (By OkStays fun s : S => s.st) (K1.firstSegmentOpening (Cl := Cl) q gp) :=
  K1.Rel.firstAtS_keeps groundKeeps_ledgerOk q gp

theorem atM3_ledgerOk (p : K13.Where) :
    Decides (By OkStays fun s : S => s.st) (K13.atM3 (Cl := Cl) p) :=
  K13.atM3_keeps groundKeeps_ledgerOk.quiet p

theorem atM4_ledgerOk (p : K13.Where) (commitW : Block S Cl)
    (hW : Decides (By OkStays fun s : S => s.st) commitW) :
    Decides (By OkStays fun s : S => s.st) (K13.atM4 p commitW) :=
  K13.atM4_keeps groundKeeps_ledgerOk.quiet p commitW hW

/-! ## 4 What it buys at a take -/

/-- **Where the ledger is in order, an entry that the ground gives lies within its table.** -/
theorem takeMasksP_inside {d : DState L} {o n : ℕ} {t : List ℕ × DState L}
    (h : LedgerOk d.st o) (ht : takeMasksP d o n = some t) :
    (∀ i ∈ t.1, i < OnBytes.Means.tableSize d.st o .mask) ∧ LedgerOk t.2.st o := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨a, -, c⟩ := takeMasksP_within hk ht
  exact ⟨a, _, c⟩

/-- The like at the pending row's take. -/
theorem takeEntry_inside {st : Statement} {o : ℕ} (h : LedgerOk st o) {l l' : Ledger} {c : ℕ}
    (hl : (st.oracles[o]?).bind (·.ledger) = some l) (ht : takeEntry l = some (c, l')) :
    c < OnBytes.Means.tableSize st o .mask ∧ LedgerOk (layLedger st o l') o := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨a, -, b⟩ := takeEntry_within hk hl ht
  exact ⟨a, _, b⟩

end VerifiableInference.Desc.K13.Law
