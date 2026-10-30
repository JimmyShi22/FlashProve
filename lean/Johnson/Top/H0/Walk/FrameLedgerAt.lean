-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameLedgerAt.lean: THE LINK's FRAME's STEPS CARRY "every ledger in the
statement is that of so many takes since it was made" AND "every mask entry that a pending row names
lies within its table": the two halves of the public item "K13.pileWithin", in the words of their
laws (Johnson/Desc/K13/Law/LedgerWithin.lean: LedgerAt; OwedLedgers.lean: LedgersFit).

Why. That item is open across all 25 "cleared". Thirteen of them take an entry off the index-mask
message's ledger and lay a pending row that names it: not by the ground's functions, but by
pendingRowO: so the keeping is the frame's own to show.

  cleared_st        where the link leaves a row: THE STATEMENT BEHIND, TO THE LETTER: layLedger at
                    the index-mask message, with the ledger that takeEntry hands back; and the row
                    that is laid
  lay_other, lay_codes, tableSize_lay   layLedger turns one message's ledger and nothing else
  ledgerAt_lay_other   so LedgerAt at another message is as it was
  cleared_ledgerAt  LedgerAt at the index-mask message: k takes in front, k + 1 behind; the entry
                    that the row names lies within the mask table
  cleared_ledgersFit   LedgersFit in front gives LedgersFit behind (whichever the flag)
  RowsWithin, cleared_rowsWithin   the pending rows' mask entries lie within their tables: in front,
                    with LedgersFit: so behind

Limits. In the laws' words, not at the item's Bool: that ledgersFitC says LedgersFit is owed by its
own authors (OwedWithin.lean: OwedLedgersC). "laid" hands the verifier's state on; the three
"opened" leave the statement and the pending rows (OpenedLeaves; t.out's pending rows:
FrameGives.lean). No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTiedRec
import Johnson.Desc.K13.Law.OwedLedgers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO takeEntry)
open VerifiableInference.Desc.K13.Law (LedgerAt LedgersFit layLedger takeEntry_within)

section
variable {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut} {lay : WsLay}
  {lin : Params.LinShape} {s t : S}

/-- **The statement behind, to the letter**, where the link leaves a row. -/
theorem cleared_st
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) :
    ∃ l c l' r β, (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l ∧
      takeEntry l = some (c, l') ∧ t.st = layLedger s.st s.out.indexMasks l' ∧
      t.out.pending = s.out.pending ++ [r] ∧ r.masks = [(⟨s.out.indexMasks, c⟩, β)] ∧
      t.out.indexMasks = s.out.indexMasks := by
  obtain ⟨C, F, _, _, _, _, _, _, _, _, _, _, hrow⟩ := Law.clearWith_ok h
  obtain ⟨w, r, os, _, hr, hout, hst⟩ := hrow hv
  obtain ⟨l, c, l', hl, ht, hm, hos⟩ := Law.pendingRowO_spec hr
  refine ⟨l, c, l', r, w.beta, hl, ht, ?_, ?_, hm, ?_⟩
  · rw [hst, hos]
    rfl
  · rw [hout]
    rfl
  · rw [hout]
    rfl

end

theorem lay_other {st : Statement} {o o' : Nat} (l' : Ledger) (h : o ≠ o') :
    (layLedger st o l').oracles[o']? = st.oracles[o']? := by
  show (st.oracles.modify o _)[o']? = _
  rw [Array.getElem?_modify, if_neg h]

theorem lay_codes (st : Statement) (o : Nat) (l' : Ledger) : (layLedger st o l').codes = st.codes :=
  rfl

/-- What layLedger leaves of every message: all but the ledger. -/
theorem lay_at {st : Statement} {o o' : Nat} (l' : Ledger) :
    (layLedger st o l').oracles[o']? =
      (st.oracles[o']?).map fun x => if o = o' then { x with ledger := some l' } else x := by
  show (st.oracles.modify o _)[o']? = _
  rw [Array.getElem?_modify]
  by_cases h : o = o'
  · simp [h]
  · simp [h]

theorem tableSize_lay (st : Statement) (o o' : Nat) (l' : Ledger) (part : Part) :
    tableSize (layLedger st o l') o' part = tableSize st o' part := by
  unfold tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  rw [lay_at, lay_codes]
  cases hx : st.oracles[o']? with
  | none => rfl
  | some x =>
    by_cases h : o = o'
    · simp [h]
    · simp [h]

theorem ledgerAt_lay_other {st : Statement} {o o' k : Nat} (l' : Ledger) (h : o ≠ o')
    (hk : LedgerAt st o' k) : LedgerAt (layLedger st o l') o' k := by
  obtain ⟨x, l, h1, h2⟩ := hk
  exact ⟨x, l, by rw [lay_other l' h]; exact h1, h2⟩

section
variable {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut} {lay : WsLay}
  {lin : Params.LinShape} {s t : S}

/-- **At the index-mask message: one take more; and the entry named lies within the table.** -/
theorem cleared_ledgerAt {k : Nat}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) (hk : LedgerAt s.st s.out.indexMasks k) :
    LedgerAt t.st t.out.indexMasks (k + 1) ∧
      ∃ r c β, t.out.pending = s.out.pending ++ [r] ∧ r.masks = [(⟨s.out.indexMasks, c⟩, β)] ∧
        c < tableSize t.st s.out.indexMasks .mask := by
  obtain ⟨l, c, l', r, β, hl, ht, hst, hp, hm, him⟩ := cleared_st h hv
  obtain ⟨g1, g2, g3⟩ := takeEntry_within hk hl ht
  rw [hst, him]
  exact ⟨g3, r, c, β, hp, hm, by rw [g2]; exact g1⟩

/-- **Every ledger fits, behind as in front.** -/
theorem cleared_ledgersFit
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hF : LedgersFit s.st) : LedgersFit t.st := by
  cases hv : X.fv with
  | false =>
    rw [((clearedGives X counts left lay lin s t h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hv).2]
    exact hF
  | true =>
    obtain ⟨l, c, l', r, β, hl, ht, hst, _, _, _⟩ := cleared_st h hv
    rw [hst]
    intro o x hx hs
    by_cases ho : s.out.indexMasks = o
    · subst ho
      cases hx0 : s.st.oracles[s.out.indexMasks]? with
      | none => rw [hx0] at hl; cases hl
      | some x0 =>
        have hl0 : x0.ledger = some l := by rw [hx0] at hl; exact hl
        obtain ⟨k, hk⟩ := hF _ x0 hx0 (by rw [hl0]; rfl)
        exact ⟨k + 1, (takeEntry_within hk hl ht).2.2⟩
    · rw [lay_other l' ho] at hx
      obtain ⟨k, hk⟩ := hF o x hx hs
      exact ⟨k, ledgerAt_lay_other l' ho hk⟩

/-- Every mask entry that a pending row names lies within its table. -/
def RowsWithin (s : S) : Prop :=
  ∀ r ∈ s.out.pending, ∀ e ∈ r.masks, e.1.index < tableSize s.st e.1.oracle .mask

/-- **The pending rows' entries lie within, behind as in front.** -/
theorem cleared_rowsWithin
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hF : LedgersFit s.st) (hR : RowsWithin s) : RowsWithin t := by
  cases hv : X.fv with
  | false =>
    obtain ⟨h1, h2⟩ := (clearedGives X counts left lay lin s t h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hv
    unfold RowsWithin
    rw [h1, h2]
    exact hR
  | true =>
    obtain ⟨l, c, l', r, β, hl, ht, hst, hp, hm, _⟩ := cleared_st h hv
    intro r' hr' e he
    rw [hst, tableSize_lay]
    rw [hp] at hr'
    rcases List.mem_append.1 hr' with h1 | h1
    · exact hR r' h1 e he
    · obtain rfl : r' = r := by simpa using h1
      rw [hm] at he
      obtain rfl : e = (⟨s.out.indexMasks, c⟩, β) := by simpa using he
      cases hx0 : s.st.oracles[s.out.indexMasks]? with
      | none => rw [hx0] at hl; cases hl
      | some x0 =>
        have hl0 : x0.ledger = some l := by rw [hx0] at hl; exact hl
        obtain ⟨k, hk⟩ := hF _ x0 hx0 (by rw [hl0]; rfl)
        exact (takeEntry_within hk hl ht).1

end

#print axioms cleared_st
#print axioms cleared_ledgerAt
#print axioms cleared_ledgersFit
#print axioms cleared_rowsWithin

end Johnson.Desc.First.Walk.Tied
