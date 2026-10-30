-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgerWithin.lean: AN ENTRY THAT THE LEDGER GIVES LIES WITHIN ITS TABLE.
Definitions, and statements with their proofs. It names no block and no filling.
IN PLAIN WORDS. A sampled oracle message with mask rows has a ledger, which hands out the free
entries of its mask table one by one. `LedgerAt st o k` says: the ledger of message o is that of k
takes since it was made. From it: the next entry that is taken has a number below the size of o's
mask table, and behind the take the ledger is that of k + 1 takes.
Main names:
  `nextAt m k`: where the search begins in front of take k: 0, then the number behind the last one.
  `LedgerAt st o k`: the message is there, has a ledger, a mask row and an answer; the ledger's rows
    and row bits are the shape's; what is left and k make the count of free entries
    (`Send.freeMaskEntries`); the search begins at `nextAt`. It does not read `closed`.
  `ledgerAt_made`: **a member**: the ledger that `Send.admit` lays (OnBytes/Iop/Send.lean: next 0,
    left the count, rows max maskRows 1, logRows ceilLog2 maskRows) is that of 0 takes.
  `nextOf l`, `taken l`, `layLedger st o l'`: the number given; the ledger behind; the statement
    with a ledger laid back: the text that `takeEntry`'s caller and `takeMaskP` share.
  `nextEntry_is`: `Pend.nextEntry` is `Blk.nextRealRow`.
  `ledgerAt_take`: **THE LEMMA**, at that shared text.
  `takeEntry_within`: at `takeEntry` (Johnson/Desc/First/Pend/Row.lean).
  `takeMaskP_within`, `takeMasksInto_within`, `takeMasksP_within`: at the ground's calls
    (Johnson/Desc/First/Base/Ground.lean): every index given lies within the table, the table's size
    stays, and behind n takes the ledger is that of k + n.
CALLED: `takenNo_eq` (OnBytes/Iop/LedgerPlaces.lean), `entryNo_lt`, `freeAt_row_lt`,
`freeAt_entry_lt`, `le_two_pow_logUp` (Fmt/PlacesLaws.lean).
NOT ASKED: that the codes' lengths are powers of two, or that the mask code is in the list: a place
in a row is below the row's length ell, and ell ≤ 2 ^ ceilLog2 ell, the table's places, whatever
ell is.
The corners. One mask row: no row bits; the entries are the places 0, 1, … below ell - answers. As
many answers as places: the count is maskRows - 1: place 0 of all rows but the last. More answers
than places: the count is 0: nothing is left, nothing is taken.

What is not claimed. That a record's ledger has `LedgerAt` at any k: that no other text writes
`next`, `left`, `rows` or `logRows` between the making and a take is shown here of no block. That
an entry given is no entry of the pad (Fmt/PlacesLaws.lean has it of `freeAt`). Nothing on soundness
or on hiding.

-/
import OnBytes.Iop.LedgerPlaces
import OnBytes.Iop.Send
import Johnson.Desc.Means.Says
import Johnson.Desc.First.Pend.Row
import Johnson.Desc.First.Base.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open Fmt.Places (logUp entryNo freeAt freeCount entryNo_lt freeAt_row_lt freeAt_entry_lt
  le_two_pow_logUp)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.First.Pend (nextEntry takeEntry)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP takeMaskL ok has)
open Desc.Plain (DState)

/-- Where the search begins in front of take k. -/
def nextAt (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => takenNo m k + 1

/-- **The ledger of message o is that of k takes since it was made.** -/
def LedgerAt (st : Statement) (o k : ℕ) : Prop :=
  ∃ (x : Oracle) (l : Ledger), st.oracles[o]? = some x ∧ x.ledger = some l ∧
    0 < x.shape.maskRows ∧ 1 ≤ x.shape.answers ∧ l.rows = x.shape.maskRows ∧
    l.logRows = ceilLog2 x.shape.maskRows ∧
    l.left + k = Send.freeMaskEntries x.shape.maskRows
      (st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers ∧
    l.next = nextAt x.shape.maskRows k

/-- **A member**: the ledger that `Send.admit` lays is that of 0 takes. -/
theorem ledgerAt_made {st : Statement} {o : ℕ} {x : Oracle} (hx : st.oracles[o]? = some x)
    (hm : 0 < x.shape.maskRows) (ha : 1 ≤ x.shape.answers)
    (hl : x.ledger = some
      { next := 0
        left := Send.freeMaskEntries x.shape.maskRows
          (st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers
        rows := max x.shape.maskRows 1, logRows := ceilLog2 x.shape.maskRows }) :
    LedgerAt st o 0 :=
  ⟨x, _, hx, hl, hm, ha, Nat.max_eq_left hm, rfl, rfl, rfl⟩

/-- The number that a ledger gives next. -/
def nextOf (l : Ledger) : ℕ := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next

/-- The ledger behind a take. -/
def taken (l : Ledger) : Ledger := { l with next := nextOf l + 1, left := l.left - 1 }

/-- The statement with a ledger laid back at message o. -/
def layLedger (st : Statement) (o : ℕ) (l' : Ledger) : Statement :=
  { st with oracles := st.oracles.modify o fun x => { x with ledger := some l' } }

/-- The pending row's search is the ground's. -/
theorem nextEntry_is (rows q : ℕ) : ∀ fuel n : ℕ,
    nextEntry rows q fuel n = Blk.nextRealRow rows q fuel n
  | 0, _ => rfl
  | fuel + 1, n => by
    rw [nextEntry, Blk.nextRealRow, nextEntry_is rows q fuel (n + 1)]

/-- From `nextAt m k` the search ends at the k-th number given. -/
theorem takenNo_at (m : ℕ) : ∀ k,
    Blk.nextRealRow m (logUp m) (2 ^ logUp m) (nextAt m k) = takenNo m k
  | 0 => rfl
  | _ + 1 => rfl

/-- The program's count of free entries is the format page's. -/
theorem free_is (m e s : ℕ) : Send.freeMaskEntries m e s = freeCount m e s := by
  unfold Send.freeMaskEntries freeCount
  by_cases h : m = 0 ∨ e < s
  · rw [if_pos h, if_pos (by simpa using h)]
  · rw [if_neg h, if_neg (by simpa using h)]

/-- The k-th number given, k below the count, is below 2 ^ (row bits + place bits). -/
theorem takenNo_lt {m e s k : ℕ} (hm : 0 < m) (h1 : 1 ≤ s) (hk : k < freeCount m e s) :
    takenNo m k < 2 ^ (logUp m + logUp e) := by
  have hs : s ≤ e := by
    by_contra hn
    unfold freeCount at hk
    rw [if_pos (Or.inr (by omega))] at hk
    exact absurd hk (Nat.not_lt_zero _)
  rw [takenNo_eq hm k]
  exact entryNo_lt (freeAt_row_lt hm k)
    (Nat.lt_of_lt_of_le (freeAt_entry_lt hm h1 hs hk) (le_two_pow_logUp e))

/-- The size of the mask table of a message with a mask row. -/
theorem tableSize_mask {st : Statement} {o : ℕ} {x : Oracle} (hx : st.oracles[o]? = some x)
    (hm : 0 < x.shape.maskRows) :
    tableSize st o .mask = 2 ^ (logUp x.shape.maskRows +
      logUp (st.codes.mask.getD x.shape.maskCode default).ell) := by
  have h0 : (x.shape.rows .mask == 0) = false := by
    show (x.shape.maskRows == 0) = false
    exact beq_false_of_ne (by omega)
  unfold tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  simp only [hx, h0]
  have hm' : 0 < x.shape.rows .mask := hm
  rw [if_pos (decide_eq_true hm'), if_neg Bool.false_ne_true]
  rfl

/-- The message o of the statement with a ledger laid back. -/
theorem layLedger_at {st : Statement} {o : ℕ} {x : Oracle} (hx : st.oracles[o]? = some x)
    (l' : Ledger) : (layLedger st o l').oracles[o]? = some { x with ledger := some l' } := by
  show (st.oracles.modify o _)[o]? = _
  rw [Array.getElem?_modify, if_pos rfl, hx]
  rfl

/-- **THE LEMMA**: where an entry is left, the number given lies within the mask table; the table's
size stays; behind the take the ledger is that of k + 1 takes. -/
theorem ledgerAt_take {st : Statement} {o k : ℕ} (h : LedgerAt st o k) {l : Ledger}
    (hl : (st.oracles[o]?).bind (·.ledger) = some l) (h0 : 0 < l.left) :
    nextOf l < tableSize st o .mask ∧
      tableSize (layLedger st o (taken l)) o .mask = tableSize st o .mask ∧
      LedgerAt (layLedger st o (taken l)) o (k + 1) := by
  obtain ⟨x, l₀, hx, hl₀, hm, ha, hr, hq, hleft, hnext⟩ := h
  rw [hx] at hl
  have hl' : x.ledger = some l := hl
  obtain rfl := Option.some.inj (hl₀.symm.trans hl')
  have hn : nextOf l₀ = takenNo x.shape.maskRows k := by
    unfold nextOf
    rw [hr, hq, hnext]
    exact takenNo_at x.shape.maskRows k
  rw [free_is] at hleft
  refine ⟨?_, ?_, ?_⟩
  · rw [hn, tableSize_mask hx hm]
    exact takenNo_lt hm ha (by omega)
  · rw [tableSize_mask hx hm, tableSize_mask (layLedger_at hx (taken l₀)) hm]
    rfl
  · refine ⟨_, taken l₀, layLedger_at hx (taken l₀), rfl, hm, ha, hr, hq, ?_, ?_⟩
    · show l₀.left - 1 + (k + 1) = Send.freeMaskEntries _ _ _
      rw [free_is]
      show l₀.left - 1 + (k + 1) = freeCount x.shape.maskRows
        (st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers
      omega
    · show nextOf l₀ + 1 = takenNo x.shape.maskRows k + 1
      rw [hn]

/-- What a yes of `takeEntry` is. -/
theorem takeEntry_is {l l' : Ledger} {c : ℕ} (h : takeEntry l = some (c, l')) :
    0 < l.left ∧ c = nextOf l ∧ l' = taken l := by
  unfold takeEntry at h
  split at h
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    have e := Prod.mk.inj (Option.some.inj h)
    refine ⟨of_decide_eq_true hc.2, ?_, ?_⟩
    · rw [← e.1, nextEntry_is]
      rfl
    · rw [← e.2, nextEntry_is]
      rfl
  · cases h

/-- **At the pending row's take.** -/
theorem takeEntry_within {st : Statement} {o k : ℕ} (h : LedgerAt st o k) {l l' : Ledger} {c : ℕ}
    (hl : (st.oracles[o]?).bind (·.ledger) = some l) (ht : takeEntry l = some (c, l')) :
    c < tableSize st o .mask ∧ tableSize (layLedger st o l') o .mask = tableSize st o .mask ∧
      LedgerAt (layLedger st o l') o (k + 1) := by
  obtain ⟨h0, rfl, rfl⟩ := takeEntry_is ht
  exact ledgerAt_take h hl h0

section
variable {L : Type}

/-- **At the ground's take of one entry.** -/
theorem takeMaskP_within {d d' : DState L} {o k n : ℕ} (h : LedgerAt d.st o k)
    (ht : takeMaskP d o = some (n, d')) :
    n < tableSize d.st o .mask ∧ tableSize d'.st o .mask = tableSize d.st o .mask ∧
      LedgerAt d'.st o (k + 1) := by
  unfold takeMaskP at ht
  split at ht
  · rename_i hok
    cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none =>
      rw [hl] at ht
      cases ht
    | some l =>
      rw [hl] at ht
      have e : (nextOf l, { d with st := layLedger d.st o (taken l) }) = (n, d') :=
        Option.some.inj ht
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      have h0 : 0 < l.left := by
        simp only [ok, takeMaskL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          hl] at hok
        exact of_decide_eq_true hok.2.2.2
      exact ledgerAt_take h hl h0
  · cases ht

/-- At the taking of several, with what was taken before. -/
theorem takeMasksInto_within (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ)
    (t : List ℕ × DState L) (k : ℕ), LedgerAt d.st o k →
    (∀ i ∈ acc.toList, i < tableSize d.st o .mask) → takeMasksInto o n d acc = some t →
    (∀ i ∈ t.1, i < tableSize d.st o .mask) ∧
      tableSize t.2.st o .mask = tableSize d.st o .mask ∧ LedgerAt t.2.st o (k + n)
  | 0, d, acc, t, k, h, ha, ht => by
    have e : some (acc.toList, d) = some t := ht
    rw [← Option.some.inj e]
    exact ⟨ha, rfl, h⟩
  | n + 1, d, acc, t, k, h, ha, ht => by
    unfold takeMasksInto at ht
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at ht
      cases ht
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at ht
      obtain ⟨h1, h2, h3⟩ := takeMaskP_within h hm
      obtain ⟨g1, g2, g3⟩ := takeMasksInto_within o n d' (acc.push i) t (k + 1) h3
        (fun j hj => by
          rw [h2]
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hj
          rcases hj with hj | rfl
          · exact ha j hj
          · exact h1) ht
      refine ⟨fun j hj => ?_, g2.trans h2, ?_⟩
      · rw [← h2]
        exact g1 j hj
      · rw [show k + (n + 1) = k + 1 + n by omega]
        exact g3

/-- **At the ground's take of n entries**: every index given lies within the table. -/
theorem takeMasksP_within {d : DState L} {o k n : ℕ} {t : List ℕ × DState L}
    (h : LedgerAt d.st o k) (ht : takeMasksP d o n = some t) :
    (∀ i ∈ t.1, i < tableSize d.st o .mask) ∧
      tableSize t.2.st o .mask = tableSize d.st o .mask ∧ LedgerAt t.2.st o (k + n) :=
  takeMasksInto_within o n d #[] t k h (fun _ hi => by cases hi) ht

end

end VerifiableInference.Desc.K13.Law
