-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameEntries.lean: THE FREE ENTRIES OF THE INDEX-MASK MESSAGE's LEDGER, ALONG
THE FRAME's STEPS: made at link 0, spent one a row.

Why. A pending row takes one entry off that ledger ("cleared", where the link leaves a row). That
the row can be made at all (hasRow) wants an entry free. "link 0: opened" tests once, for the whole
request, that the ledger has room for all rows to come (guard I4). Here that test is carried along.

  (freeOf, endTakes, rowsFrom, roomB: the definitions with code: FrameEntriesDefs.lean)
  le_freeOf_iff     at n > 0: n ≤ freeOf s says: the ledger is there, not closed, n ≤ left
  RoomAt fvs e m s  rowsFrom fvs m + e is at most freeOf s; roomB_iff: roomB says just that
  openedZero_room   MADE: behind a yes of openLayZero: RoomAt at link 0, at e := endTakes fvs kCol;
                    room_mono: so at every smaller e, 0 among them
  laid_free, openedAtt_free, openedLay_free, cleared_free_none   KEPT: freeOf is unturned
  cleared_free_row  SPENT: where the link leaves a row: freeOf in front is freeOf behind and one
  cleared_ledger    there: the ledger behind, to the letter, and the entry that the row bears
  ledger_same       the whole ledger is kept where st and out are
  leftIsB_iff, leftIs_free, leftIsB_same, cleared_leftIs, cleared_leftIs_none, rowsBefore_succ,
  roomIs_step       THE ITEM "pile.room" AS AN EQUATION (roomIsB): kept where st and out are; the
                    taker: one less; from segment m to m + 1 across "cleared"
  cleared_room      so RoomAt at link m in front of "cleared" gives RoomAt at link m + 1 behind it,
                    where the link's planned flag is the list's entry at m
  room_pos          where link m leaves a row, RoomAt at m gives a free entry

Limits. What the blocks between the frame's steps do to that ledger is their laws' to say. fvs,
kCol, e are letters. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTiedRec
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO takeEntry)

/-- At a number that is not 0: "n free entries" says: there is such a ledger, it is not closed, and
at least n entries are left. (At 0 it says nothing.) -/
theorem le_freeOf_iff {n : Nat} {s : S} (hn : 0 < n) :
    n ≤ freeOf s ↔ ∃ l, Law.ledgerAt s = some l ∧ l.closed = false ∧ n ≤ l.left := by
  unfold freeOf
  cases h : Law.ledgerAt s with
  | none => simp; omega
  | some l =>
    cases hc : l.closed with
    | true => simp [hc]; omega
    | false => simp [hc]

theorem rowsFrom_zero (fvs : List Bool) (kCol : Nat) :
    rowsFrom fvs 0 + endTakes fvs kCol = roomOf fvs kCol := rfl

theorem rowsFrom_succ {fvs : List Bool} {m : Nat} {v : Bool} (h : fvs[m]? = some v) :
    rowsFrom fvs m = rowsFrom fvs (m + 1) + (if v then 1 else 0) := by
  unfold rowsFrom
  have e : fvs.drop m = v :: fvs.drop (m + 1) := by
    obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.1 h
    exact List.drop_eq_getElem_cons hm
  rw [e]
  cases v <;> simp [List.filter_cons]

def RoomAt (fvs : List Bool) (e m : Nat) (s : S) : Prop := rowsFrom fvs m + e ≤ freeOf s

theorem roomB_iff {fvs : List Bool} {e m : Nat} {s : S} :
    roomB fvs e m s = true ↔ RoomAt fvs e m s := by
  unfold roomB RoomAt
  exact decide_eq_true_iff

theorem room_mono {fvs : List Bool} {e e' m : Nat} {s : S} (h : e' ≤ e)
    (hr : RoomAt fvs e m s) : RoomAt fvs e' m s := by
  unfold RoomAt at hr ⊢
  omega

/-- The whole ledger is kept where the statement and what is handed out are. -/
theorem ledger_same {s t : S} (h1 : t.st = s.st) (h2 : t.out = s.out) :
    Law.ledgerAt t = Law.ledgerAt s := by
  unfold Law.ledgerAt
  rw [h1, h2]

theorem freeOf_same {s t : S} (h1 : t.st = s.st) (h2 : t.out = s.out) : freeOf t = freeOf s := by
  unfold freeOf Law.ledgerAt
  rw [h1, h2]

/-- **MADE at link 0.** -/
theorem openedZero_room {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : RoomAt fvs (endTakes fvs kCol) 0 t := by
  obtain ⟨_, _, hL, ⟨im, ⟨_, _, x, l, h3, h4, h5⟩, ho⟩, _⟩ := openedZeroGives P fvs kCol s t h
  unfold RoomAt
  rw [rowsFrom_zero]
  have e : Law.ledgerAt t = some l := by
    unfold Law.ledgerAt
    rw [hL.2.2.1, ho]
    show (s.st.oracles[im]?).bind (·.ledger) = some l
    rw [h3]
    exact h4
  unfold freeOf
  rw [e]
  exact h5

theorem laid_free {m : Nat} {s t : S} (h : layFront m s = .ok t) : freeOf t = freeOf s := by
  rw [(Law.layFront_ok h).1]

theorem openedAtt_free {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : freeOf t = freeOf s := by
  obtain ⟨_, _, hL, ho, _⟩ := openedAttGives P s t h
  exact freeOf_same hL.2.2.1 ho

theorem openedLay_free {P : LayPar} {s t : S} (h : openLay P s = .ok t) : freeOf t = freeOf s := by
  obtain ⟨_, _, hL, ho, _⟩ := openedLayGives P s t h
  exact freeOf_same hL.2.2.1 ho

section
variable {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut} {lay : WsLay}
  {lin : Params.LinShape} {s t : S}

theorem cleared_free_none
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = false) : freeOf t = freeOf s := by
  obtain ⟨h1, h2⟩ := (clearedGives X counts left lay lin s t h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hv
  exact freeOf_same h2 h1

/-- **SPENT: one a row.** -/
theorem cleared_free_row
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) : freeOf s = freeOf t + 1 := by
  obtain ⟨l, c, l', _, _, h1, h2, _, _, _, _, h3⟩ := Law.clear_row h hv
  unfold freeOf
  rw [h1, h3]
  unfold takeEntry at h2
  by_cases hc : (!l.closed && decide (0 < l.left)) = true
  · rw [if_pos hc] at h2
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    simp only [hc.1, Bool.false_eq_true, if_false]
    omega
  · rw [if_neg hc] at h2
    cases h2

/-- **THE LEDGER BEHIND, TO THE LETTER**, where the link leaves a row: n: the entry that the row
bears: the next free one by nextEntry; behind, "next" stands one past it and "left" one lower; the
ledger's rows, logRows and "closed" are unturned. -/
theorem cleared_ledger
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) :
    ∃ l, Law.ledgerAt s = some l ∧ l.closed = false ∧ 0 < l.left ∧
      Law.ledgerAt t = some { l with
        next := VerifiableInference.Desc.First.Pend.nextEntry l.rows l.logRows (2 ^ l.logRows)
          l.next + 1
        left := l.left - 1 } ∧
      ∃ r w, t.out.pending = s.out.pending ++ [r] ∧ r.masks = [(⟨s.out.indexMasks,
        VerifiableInference.Desc.First.Pend.nextEntry l.rows l.logRows (2 ^ l.logRows) l.next⟩,
        w)] := by
  obtain ⟨l, c, l', w, r, h1, h2, _, h4, h5, _, h3⟩ := Law.clear_row h hv
  unfold takeEntry at h2
  by_cases hc : (!l.closed && decide (0 < l.left)) = true
  · rw [if_pos hc] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    exact ⟨l, h1, hc.1, hc.2, h3, r, w.beta, h4, h5⟩
  · rw [if_neg hc] at h2
    cases h2

/-! ### The item "pile.room" as an equation -/

theorem leftIsB_iff {n : Nat} {s : S} :
    leftIsB n s = true ↔ ∃ l, Law.ledgerAt s = some l ∧ l.closed = false ∧ l.left = n := by
  unfold leftIsB
  cases h : Law.ledgerAt s with
  | none => simp
  | some l => simp

theorem leftIs_free {n : Nat} {s : S} (h : leftIsB n s = true) : freeOf s = n := by
  obtain ⟨l, h1, h2, h3⟩ := leftIsB_iff.1 h
  unfold freeOf
  rw [h1]
  simp [h2, h3]

/-- KEPT where the statement and what is handed out are. -/
theorem leftIsB_same {n : Nat} {s t : S} (h1 : t.st = s.st) (h2 : t.out = s.out) :
    leftIsB n t = leftIsB n s := by
  unfold leftIsB
  rw [ledger_same h1 h2]

/-- **THE TAKER**: at a link that leaves a row. -/
theorem cleared_leftIs {n : Nat}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) (hn : leftIsB n s = true) : 0 < n ∧ leftIsB (n - 1) t = true := by
  obtain ⟨l, h1, hc, hp, h3, _⟩ := cleared_ledger h hv
  obtain ⟨l', h1', _, h3'⟩ := leftIsB_iff.1 hn
  rw [h1] at h1'
  obtain rfl : l = l' := Option.some.inj h1'
  subst h3'
  exact ⟨hp, leftIsB_iff.2 ⟨_, h3, hc, rfl⟩⟩

theorem cleared_leftIs_none {n : Nat}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = false) : leftIsB n t = leftIsB n s := by
  obtain ⟨h1, h2⟩ := (clearedGives X counts left lay lin s t h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hv
  exact leftIsB_same h2 h1

theorem rowsBefore_succ {fvs : List Bool} {m : Nat} {v : Bool} (h : fvs[m]? = some v) :
    rowsBefore fvs (m + 1) = rowsBefore fvs m + (if v then 1 else 0) := by
  unfold rowsBefore
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.take_succ_eq_append_getElem hm, List.filter_append, List.length_append]
  cases fvs[m] <;> simp

/-- **The item from segment m to segment m + 1, across "cleared".** -/
theorem roomIs_step {free0 : Nat} {fvs : List Bool} {m : Nat}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hm : fvs[m]? = some X.fv) (hr : roomIsB free0 fvs m s = true) :
    roomIsB free0 fvs (m + 1) t = true := by
  unfold roomIsB at hr ⊢
  rw [rowsBefore_succ hm]
  cases hv : X.fv with
  | false =>
    rw [cleared_leftIs_none h hv]
    simpa using hr
  | true =>
    have h2 := (cleared_leftIs h hv hr).2
    simpa [Nat.sub_sub] using h2

/-- **From link m to link m + 1.** -/
theorem cleared_room {fvs : List Bool} {e m : Nat}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hm : fvs[m]? = some X.fv) (hr : RoomAt fvs e m s) : RoomAt fvs e (m + 1) t := by
  unfold RoomAt at hr ⊢
  rw [rowsFrom_succ hm] at hr
  cases hv : X.fv with
  | false =>
    rw [hv] at hr
    rw [cleared_free_none h hv]
    simpa using hr
  | true =>
    rw [hv] at hr
    have e1 := cleared_free_row h hv
    simp only [if_true] at hr
    omega

end

/-- Where link m leaves a row, room at m gives a free entry. -/
theorem room_pos {fvs : List Bool} {e m : Nat} {s : S} (hm : fvs[m]? = some true)
    (hr : RoomAt fvs e m s) : 0 < freeOf s := by
  unfold RoomAt at hr
  rw [rowsFrom_succ hm] at hr
  simp only [if_true] at hr
  omega

#print axioms le_freeOf_iff
#print axioms openedZero_room
#print axioms cleared_free_row
#print axioms cleared_ledger
#print axioms cleared_leftIs
#print axioms roomIs_step
#print axioms cleared_room
#print axioms room_pos

end Johnson.Desc.First.Walk.Tied
