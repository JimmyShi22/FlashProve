-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/Seat.lean: a caller of the lookup verifier over any context of the program: its contexts,
and what the program's primitives do at them. The caller itself, what is asked of the context, and
the laws of OnBytes/G4/AnyCaller.lean are in OnBytes/G4/SeatLaws.lean.

A `Seat` is a context of the program (`base`) together with what Lkp.verify is told at a call: the
public inputs, where the bits are read, the two messages that give mask entries, and the group.
`Seat.caller` (OnBytes/G4/SeatLaws.lean) makes a Caller of it. Its contexts are the base context
with these parts replaced: in the channel the entries left, the open round, the rounds left and the
entry closed last; in the statement the ledgers of the two messages and the rows of the group. Three
marks are set: it is no dry run, no intermediate values are kept, and no block has yet asked for the
last round's number of rows. Nothing else of the base is turned. So a context of the program is one
of these contexts only if its own three marks are so (`Seat.ctx_self`, in that file). The state of
the ledgers is the pair of the two ledgers themselves.

Main definitions: Seat, stepLedger, takesOf, Seat.st, Seat.ctx, Seat.fix, Seat.slotsAt.
Main theorems: Seat.recv, Seat.close, Seat.note, Seat.takesOf_add, Seat.takeSlots_first,
Seat.takeSlots_second.
Not claimed. That a given context of the program is good.


-/
import OnBytes.G4.AnyRun

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-- A context of the program, and what Lkp.verify is told at a call. -/
structure Seat where
  /-- the context -/
  base : Ctx
  /-- the lookup's public inputs -/
  S : Lkp.Public
  /-- where the bits of the multiplicities are read -/
  planesAt : Row → Tensor → Row
  /-- the message that gives the mask entries -/
  masks : Nat
  /-- the message that gives the two mask entries of each part's last key level -/
  keyMasks : Nat
  /-- the group to which the rows are added -/
  group : Nat

/-- One take from a ledger: the entry's index, and the ledger after it (Blk.takeMask). -/
def stepLedger (l : Ledger) : Nat × Ledger :=
  (nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next,
    { l with next := nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 })

/-- n takes from a ledger: the entries' indices, and the ledger after them. -/
def takesOf (l : Ledger) : Nat → List Nat × Ledger
  | 0 => ([], l)
  | n + 1 => ((stepLedger l).1 :: (takesOf (stepLedger l).2 n).1, (takesOf (stepLedger l).2 n).2)

namespace Seat

/-- The statement with the two ledgers and the group's rows replaced. -/
def st (Z : Seat) (σ : Ledger × Ledger) (rows : Array Row) : Statement :=
  { Z.base.st with
    oracles := (Z.base.st.oracles.modify Z.masks fun x => { x with ledger := some σ.1 }).modify
      Z.keyMasks fun x => { x with ledger := some σ.2 }
    groups := Z.base.st.groups.modify Z.group fun G => { G with rows := rows } }

/-- The context with the channel's moving parts, the two ledgers and the group's rows replaced. -/
def ctx (Z : Seat) (es : List Fmt.Entry) (cur : Option Fmt.RoundView) (rs : List Fmt.RoundView)
    (last : Option Fmt.Entry) (σ : Ledger × Ledger) (rows : Array Row) : Ctx :=
  { Z.base with
    ch := { Z.base.ch with
      dry := false, entries := es, left := rs, cur := cur, last := last, askedRows := false }
    st := Z.st σ rows
    keepNotes := false }

theorem settled (Z : Seat) {es cur rs last σ rows} (h : NoRows last) :
    (Z.ctx es cur rs last σ rows).ch.settled = true := by
  unfold Chan.settled ctx
  cases last with
  | none => rfl
  | some e => simp [h e rfl]

/-- Receiving elements from a message that is open. -/
theorem recvEsInto_open (Z : Seat) (es rs last σ rows) (d : Fmt.Drawn) :
    ∀ (xs : List E) (rest : List Fmt.ItemValue) (acc : Array E),
      Blk.recvEsInto xs.length acc
          (Z.ctx es (some ⟨xs.map (fun x => Fmt.ItemValue.e x.triple) ++ rest, d⟩) rs last σ rows) =
        .ok (acc ++ xs.toArray, Z.ctx es (some ⟨rest, d⟩) rs last σ rows)
  | [], rest, acc => by simp [Blk.recvEsInto, pure_ok]
  | x :: xs, rest, acc => by
    have h1 : Blk.recvE
        (Z.ctx es (some ⟨(x :: xs).map (fun x => Fmt.ItemValue.e x.triple) ++ rest, d⟩) rs last σ rows) =
        .ok (x, Z.ctx es (some ⟨xs.map (fun x => Fmt.ItemValue.e x.triple) ++ rest, d⟩) rs last σ rows) :=
            rfl
    show (Blk.recvE >>= fun y => Blk.recvEsInto xs.length (acc.push y)) _ = _
    rw [bind_ok h1, recvEsInto_open Z es rs last σ rows d xs rest (acc.push x)]
    simp

/-- Receiving all elements of a round that is not yet begun. -/
theorem recv (Z : Seat) (es rs last σ rows) (r : FlatRound) :
    (Blk.recvEs r.sent.length) (Z.ctx es none (r.rv :: rs) last σ rows) =
      .ok (r.sent, Z.ctx es (openedCur r) (openedLeft r rs) last σ rows) := by
  obtain ⟨sent, drawn⟩ := r
  cases sent with
  | nil => rfl
  | cons x xs =>
    have h1 : Blk.recvE (Z.ctx es none ((⟨x :: xs, drawn⟩ : FlatRound).rv :: rs) last σ rows) =
        .ok (x, Z.ctx es (some ⟨xs.map (fun x => Fmt.ItemValue.e x.triple) ++ [],
          (⟨x :: xs, drawn⟩ : FlatRound).rv.drawn⟩) rs last σ rows) := by
      simp only [List.append_nil]
      rfl
    show ((Blk.recvE >>= fun y => Blk.recvEsInto xs.length ((#[] : Array E).push y)) >>=
      fun a => pure a.toList) _ = _
    have h2 : (Blk.recvE >>= fun y => Blk.recvEsInto xs.length ((#[] : Array E).push y))
        (Z.ctx es none ((⟨x :: xs, drawn⟩ : FlatRound).rv :: rs) last σ rows) =
        .ok ((#[] : Array E).push x ++ xs.toArray,
          Z.ctx es (some ⟨[], (⟨x :: xs, drawn⟩ : FlatRound).rv.drawn⟩) rs last σ rows) := by
      rw [bind_ok h1]
      exact recvEsInto_open Z es rs last σ rows _ xs [] _
    rw [bind_ok h2]
    simp [pure_ok, openedCur, openedLeft]

/-- Closing a round whose elements are received. -/
theorem close (Z : Seat) (e : Fmt.Entry) (es rs last σ rows) (r : FlatRound)
    (name : String) (kind : Fmt.Kind) (nz : Nat) (hn : e.name = name) (hz : e.drawNZ = nz)
    (hq : NoRows last) (hd : r.drawn.length = e.drawE) (hp : e.poss = 0) (ht : e.trits = 0) :
    (Blk.close name kind nz) (Z.ctx (e :: es) (openedCur r) (openedLeft r rs) last σ rows) =
      .ok (r.rv.drawn, Z.ctx es none rs (some e) σ rows) := by
  have hs := Z.settled (es := e :: es) (cur := openedCur r) (rs := openedLeft r rs) (σ := σ)
    (rows := rows) hq
  obtain ⟨sent, drawn⟩ := r
  cases sent with
  | nil =>
    unfold Blk.close
    simp [ctx, openedCur, openedLeft, FlatRound.rv, hn, hz, hp, ht] at hs hd ⊢
    simp [hs, hd]
  | cons x xs =>
    unfold Blk.close
    simp [ctx, openedCur, openedLeft, FlatRound.rv, hn, hz, hp, ht] at hs hd ⊢
    simp [hs, hd]

theorem note (Z : Seat) (es cur rs last σ rows) (what : String) (x : E) :
    (Blk.note what x) (Z.ctx es cur rs last σ rows) = .ok ((), Z.ctx es cur rs last σ rows) := rfl

/-! ## The statement -/

/-- What the replacing of the ledgers makes of the message number o. -/
def fix (Z : Seat) (σ : Ledger × Ledger) (o : Nat) (x : Oracle) : Oracle :=
  if Z.keyMasks = o then
    { (if Z.masks = o then { x with ledger := some σ.1 } else x) with ledger := some σ.2 }
  else if Z.masks = o then { x with ledger := some σ.1 } else x

theorem oracleAt (Z : Seat) (σ rows) (o : Nat) :
    (Z.st σ rows).oracles[o]? = (Z.base.st.oracles[o]?).map (Z.fix σ o) := by
  simp only [st, Array.getElem?_modify]
  by_cases h1 : Z.keyMasks = o <;> by_cases h2 : Z.masks = o <;>
    cases Z.base.st.oracles[o]? <;> simp [h1, h2, fix]

theorem fix_shape (Z : Seat) (σ o x) : (Z.fix σ o x).shape = x.shape := by
  unfold fix
  split
  · split <;> rfl
  · split <;> rfl

theorem fix_pad (Z : Seat) (σ o x) : (Z.fix σ o x).pad = x.pad := by
  unfold fix
  split
  · split <;> rfl
  · split <;> rfl

theorem fix_sampled (Z : Seat) (σ o x) : (Z.fix σ o x).sampled = x.sampled := by
  unfold fix
  split
  · split <;> rfl
  · split <;> rfl

theorem has_st (Z : Seat) (σ rows o part) : (Z.st σ rows).has o part = Z.base.st.has o part := by
  unfold Statement.has
  rw [oracleAt]
  cases Z.base.st.oracles[o]? <;> simp [fix_shape]

theorem tableBits_st (Z : Seat) (σ rows o part) :
    (Z.st σ rows).tableBits o part = Z.base.st.tableBits o part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [oracleAt]
  cases Z.base.st.oracles[o]? <;> simp [fix_shape, st]

theorem pad_st (Z : Seat) (σ rows) (o : Nat) :
    (((Z.st σ rows).oracles[o]?).map Oracle.pad).getD [] =
      ((Z.base.st.oracles[o]?).map Oracle.pad).getD [] := by
  rw [oracleAt]
  cases Z.base.st.oracles[o]? <;> simp [fix_pad]

theorem placeOk_st (Z : Seat) (σ rows) (G : Group) (rows' : Array Row) (o part vars index) :
    placeOk (Z.st σ rows) { G with rows := rows' } o part vars index =
      placeOk Z.base.st G o part vars index := by
  simp [placeOk, has_st, tableBits_st]

/-! ## The ledgers -/

theorem oracles_setFirst (Z : Seat) (h : Z.masks ≠ Z.keyMasks) (σ : Ledger × Ledger) (rows)
    (l : Ledger) :
    ((Z.st σ rows).oracles.modify Z.masks fun x => { x with ledger := some l }) =
      (Z.st (l, σ.2) rows).oracles := by
  apply Array.ext_getElem?
  intro i
  simp only [st, Array.getElem?_modify]
  by_cases h1 : Z.masks = i <;> by_cases h2 : Z.keyMasks = i <;>
    cases Z.base.st.oracles[i]? <;> simp_all

theorem oracles_setSecond (Z : Seat) (σ : Ledger × Ledger) (rows) (l : Ledger) :
    ((Z.st σ rows).oracles.modify Z.keyMasks fun x => { x with ledger := some l }) =
      (Z.st (σ.1, l) rows).oracles := by
  apply Array.ext_getElem?
  intro i
  simp only [st, Array.getElem?_modify]
  by_cases h1 : Z.masks = i <;> by_cases h2 : Z.keyMasks = i <;>
    cases Z.base.st.oracles[i]? <;> simp_all

theorem size_st (Z : Seat) (σ rows) : (Z.st σ rows).oracles.size = Z.base.st.oracles.size := by
  simp [st]

/-- One take from the first ledger. -/
theorem takeMask_first (Z : Seat) (h : Z.masks ≠ Z.keyMasks) (x : Oracle)
    (hx : Z.base.st.oracles[Z.masks]? = some x) (es rs last) (σ : Ledger × Ledger) (rows)
    (hc : σ.1.closed = false) (hl : 0 < σ.1.left) :
    (Blk.takeMask Z.masks) (Z.ctx es none rs last σ rows) =
      .ok ((stepLedger σ.1).1, Z.ctx es none rs last ((stepLedger σ.1).2, σ.2) rows) := by
  have ho : (Blk.oracle Z.masks) (Z.ctx es none rs last σ rows) =
      .ok (Z.fix σ Z.masks x, Z.ctx es none rs last σ rows) := by
    show (Blk.get ((Z.st σ rows).oracles[Z.masks]?)) _ = _
    rw [oracleAt, hx]
    rfl
  have hled : (Z.fix σ Z.masks x).ledger = some σ.1 := by
    simp [fix, Ne.symm h]
  have hsize : Z.masks < (Z.st σ rows).oracles.size := by
    rw [size_st]
    exact (Array.getElem?_eq_some_iff.1 hx).1
  unfold Blk.takeMask
  rw [bind_ok ho, hled, bind_ok (get_ok _ _), bind_ok (must_ok (by simp [hc, hl]) _)]
  have hon : (Blk.onOracle Z.masks fun x => { x with ledger := some (stepLedger σ.1).2 })
      (Z.ctx es none rs last σ rows) =
      .ok ((), Z.ctx es none rs last ((stepLedger σ.1).2, σ.2) rows) := by
    unfold Blk.onOracle
    rw [if_pos (show Z.masks < (Z.ctx es none rs last σ rows).st.oracles.size from hsize)]
    have e : ((Z.ctx es none rs last σ rows).st.oracles.modify Z.masks fun x =>
        { x with ledger := some (stepLedger σ.1).2 }) =
        (Z.st ((stepLedger σ.1).2, σ.2) rows).oracles := oracles_setFirst Z h σ rows _
    simp only [e]
    rfl
  refine (bind_ok hon).trans ?_
  rfl

/-- One take from the second ledger. -/
theorem takeMask_second (Z : Seat) (x : Oracle)
    (hx : Z.base.st.oracles[Z.keyMasks]? = some x) (es rs last) (σ : Ledger × Ledger) (rows)
    (hc : σ.2.closed = false) (hl : 0 < σ.2.left) :
    (Blk.takeMask Z.keyMasks) (Z.ctx es none rs last σ rows) =
      .ok ((stepLedger σ.2).1, Z.ctx es none rs last (σ.1, (stepLedger σ.2).2) rows) := by
  have ho : (Blk.oracle Z.keyMasks) (Z.ctx es none rs last σ rows) =
      .ok (Z.fix σ Z.keyMasks x, Z.ctx es none rs last σ rows) := by
    show (Blk.get ((Z.st σ rows).oracles[Z.keyMasks]?)) _ = _
    rw [oracleAt, hx]
    rfl
  have hled : (Z.fix σ Z.keyMasks x).ledger = some σ.2 := by
    simp [fix]
  have hsize : Z.keyMasks < (Z.st σ rows).oracles.size := by
    rw [size_st]
    exact (Array.getElem?_eq_some_iff.1 hx).1
  unfold Blk.takeMask
  rw [bind_ok ho, hled, bind_ok (get_ok _ _), bind_ok (must_ok (by simp [hc, hl]) _)]
  have hon : (Blk.onOracle Z.keyMasks fun x => { x with ledger := some (stepLedger σ.2).2 })
      (Z.ctx es none rs last σ rows) =
      .ok ((), Z.ctx es none rs last (σ.1, (stepLedger σ.2).2) rows) := by
    unfold Blk.onOracle
    rw [if_pos (show Z.keyMasks < (Z.ctx es none rs last σ rows).st.oracles.size from hsize)]
    have e : ((Z.ctx es none rs last σ rows).st.oracles.modify Z.keyMasks fun x =>
        { x with ledger := some (stepLedger σ.2).2 }) =
        (Z.st (σ.1, (stepLedger σ.2).2) rows).oracles := oracles_setSecond Z σ rows _
    simp only [e]
    rfl
  refine (bind_ok hon).trans ?_
  rfl

theorem stepLedger_closed (l : Ledger) : (stepLedger l).2.closed = l.closed := rfl

theorem stepLedger_left (l : Ledger) : (stepLedger l).2.left = l.left - 1 := rfl

theorem takesOf_length : ∀ (n : Nat) (l : Ledger), (takesOf l n).1.length = n
  | 0, _ => rfl
  | n + 1, l => by simp [takesOf, takesOf_length n]

theorem takesOf_closed : ∀ (n : Nat) (l : Ledger), (takesOf l n).2.closed = l.closed
  | 0, _ => rfl
  | n + 1, l => by rw [takesOf, takesOf_closed n, stepLedger_closed]

theorem takesOf_left : ∀ (n : Nat) (l : Ledger), (takesOf l n).2.left = l.left - n
  | 0, _ => rfl
  | n + 1, l => by
    rw [takesOf, takesOf_left n, stepLedger_left]
    omega

/-- Takes in two goes are takes in one. -/
theorem takesOf_add : ∀ (a b : Nat) (l : Ledger),
    (takesOf l (a + b)).1 = (takesOf l a).1 ++ (takesOf (takesOf l a).2 b).1
  | 0, b, l => by simp [takesOf]
  | a + 1, b, l => by
    rw [show a + 1 + b = (a + b) + 1 from by omega]
    simp [takesOf, takesOf_add a b]

/-- n takes from the first ledger. -/
theorem takeInto_first (Z : Seat) (h : Z.masks ≠ Z.keyMasks) (x : Oracle)
    (hx : Z.base.st.oracles[Z.masks]? = some x) (es rs last rows) :
    ∀ (n : Nat) (σ : Ledger × Ledger) (acc : Array Nat), σ.1.closed = false → n ≤ σ.1.left →
      (Blk.takeMasksInto Z.masks n acc) (Z.ctx es none rs last σ rows) =
        .ok (acc ++ (takesOf σ.1 n).1.toArray, Z.ctx es none rs last ((takesOf σ.1 n).2, σ.2) rows)
  | 0, σ, acc, _, _ => by simp [Blk.takeMasksInto, takesOf, pure_ok]
  | n + 1, σ, acc, hc, hl => by
    show ((Blk.takeMask Z.masks) >>= fun a => Blk.takeMasksInto Z.masks n (acc.push a)) _ = _
    rw [bind_ok (takeMask_first Z h x hx es rs last σ rows hc (by omega)),
      takeInto_first Z h x hx es rs last rows n ((stepLedger σ.1).2, σ.2) _ hc
        (by show n ≤ σ.1.left - 1; omega)]
    simp [takesOf]

/-- n takes from the second ledger. -/
theorem takeInto_second (Z : Seat) (x : Oracle)
    (hx : Z.base.st.oracles[Z.keyMasks]? = some x) (es rs last rows) :
    ∀ (n : Nat) (σ : Ledger × Ledger) (acc : Array Nat), σ.2.closed = false → n ≤ σ.2.left →
      (Blk.takeMasksInto Z.keyMasks n acc) (Z.ctx es none rs last σ rows) =
        .ok (acc ++ (takesOf σ.2 n).1.toArray, Z.ctx es none rs last (σ.1, (takesOf σ.2 n).2) rows)
  | 0, σ, acc, _, _ => by simp [Blk.takeMasksInto, takesOf, pure_ok]
  | n + 1, σ, acc, hc, hl => by
    show ((Blk.takeMask Z.keyMasks) >>= fun a => Blk.takeMasksInto Z.keyMasks n (acc.push a)) _ = _
    rw [bind_ok (takeMask_second Z x hx es rs last σ rows hc (by omega)),
      takeInto_second Z x hx es rs last rows n (σ.1, (stepLedger σ.2).2) _ hc
        (by show n ≤ σ.2.left - 1; omega)]
    simp [takesOf]

/-- The entries of message o with the given indices. -/
def slotsAt (o : Nat) (l : List Nat) : List Slot := l.map fun i => ⟨o, i⟩

theorem takeSlots_first (Z : Seat) (h : Z.masks ≠ Z.keyMasks) (x : Oracle)
    (hx : Z.base.st.oracles[Z.masks]? = some x) (es rs last rows) (n : Nat) (σ : Ledger × Ledger)
    (hc : σ.1.closed = false) (hl : n ≤ σ.1.left) :
    (takeSlots Z.masks n) (Z.ctx es none rs last σ rows) =
      .ok (slotsAt Z.masks (takesOf σ.1 n).1, Z.ctx es none rs last ((takesOf σ.1 n).2, σ.2)
          rows) := by
  show (((Blk.takeMasksInto Z.masks n #[]) >>= fun a => pure a.toList) >>= fun l =>
    pure (l.map fun i => (⟨Z.masks, i⟩ : Slot))) _ = _
  rw [bind_ok (bind_ok (takeInto_first Z h x hx es rs last rows n σ #[] hc hl))]
  simp [pure_ok, slotsAt]

theorem takeSlots_second (Z : Seat) (x : Oracle)
    (hx : Z.base.st.oracles[Z.keyMasks]? = some x) (es rs last rows) (n : Nat) (σ : Ledger × Ledger)
    (hc : σ.2.closed = false) (hl : n ≤ σ.2.left) :
    (takeSlots Z.keyMasks n) (Z.ctx es none rs last σ rows) =
      .ok (slotsAt Z.keyMasks (takesOf σ.2 n).1,
        Z.ctx es none rs last (σ.1, (takesOf σ.2 n).2) rows) := by
  show (((Blk.takeMasksInto Z.keyMasks n #[]) >>= fun a => pure a.toList) >>= fun l =>
    pure (l.map fun i => (⟨Z.keyMasks, i⟩ : Slot))) _ = _
  rw [bind_ok (bind_ok (takeInto_second Z x hx es rs last rows n σ #[] hc hl))]
  simp [pure_ok, slotsAt]

end Seat

end OnBytes.G4
