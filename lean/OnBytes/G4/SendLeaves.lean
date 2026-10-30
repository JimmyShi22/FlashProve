-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/SendLeaves.lean: what the port's SEND leaves of a context, if it goes through.

Every statement here is an inversion: if a call gave a value and a context, then that context has
these properties. Nothing is said on whether a call goes through.

Main names:
  `bind_inv`, `get_inv`, `must_inv`, `oracle_inv`, `onOracle_inv`: the steps of a block.
  `admitAs`: the update of an oracle message that `Send.admit` makes, as a function of the codes,
  the message's shape, the sample rows and the places of the pad.
  `admit_inv`: what `Send.admit` leaves.
  `close_inv`, `closeEmpty_inv`: what closing a round leaves, on a view.
  `forIn_keeps`: a loop keeps a reflexive and transitive relation that every step keeps.
  `receiveOracles_inv`: the new messages are appended with their shapes; their numbers; the parts
  of the channel that a lookup reads stay (`SameChan`).
  `Steady`, `AdmittedOrSame`: what the steps of SEND keep: codes, groups, the number of messages;
  each message is untouched, or was not sampled and has been updated as `Send.admit` does.
  `sendVerifyIds_inv`: what `Send.verify` leaves, on a view.
  `sendVerify_inv`, `sendVerify_sampled`: what `sendVerify` leaves, on a view. A new message that is
  sampled afterwards has the pad and the ledger that `admitAs` gives at its shape.
  `Flow`, `sendVerifyIds_flow`, `sendVerify_flow`: with a round of its own, SEND takes the plan's
  next two entries, "SEND seed" and "SEND answer", and the rounds left are a tail of those that were
  left.
  `sendVerifyIds_parts`: the course of `Send.verify`, so that a relation is followed through its
  loops once for all.
  `Loads`, `sendVerifyIds_rounds`, `sendVerify_rounds`: with a round of its own, and no round open
  at the start, SEND takes exactly two rounds.
Limits: no statement says that a call goes through. The loops are followed by a relation, not by
  values: that every message with answers IS sampled at the end is not shown
  (`sendVerify_sampled` takes it as a premise); which sample rows are stored is not said.
The library has laws of the same kind: OnBytes/Iop/GroundLaws.lean (the steps of a block, an item,
  closing a round), OnBytes/Slice/BlkCalls.lean (what Send.admit leaves) and
  OnBytes/Slice/BlkSendRun.lean (receiving oracles; the course of Send.verify, by values). Part of
  this file says again what they say: the steps of a block, `admit_inv`, `close_inv`,
  `receiveOracles_inv`, the unfolding in `sendVerifyIds_parts`. Not found there: the relations
  `Steady`, `Flow` and `Loads`, that SEND takes exactly two rounds, that an old sampled message
  stays, and `sendVerify_sampled`.


-/
import OnBytes.Iop.Send

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-! ## The steps of a block -/

theorem bind_inv {α β : Type} {x : Blk α} {f : α → Blk β} {c c' : Ctx} {b : β}
    (h : (x >>= f) c = .ok (b, c')) : ∃ a c1, x c = .ok (a, c1) ∧ f a c1 = .ok (b, c') := by
  have e : (x >>= f) c = (x c >>= fun p => f p.1 p.2) := rfl
  rw [e] at h
  cases hx : x c with
  | error err =>
    rw [hx] at h
    cases h
  | ok p =>
    rw [hx] at h
    exact ⟨p.1, p.2, rfl, h⟩

theorem ok_inj {α : Type} {a a' : α} {c c' : Ctx}
    (h : (Except.ok (a, c) : Except Failure (α × Ctx)) = .ok (a', c')) : a = a' ∧ c = c' := by
  injection h with h
  injection h with h1 h2
  exact ⟨h1, h2⟩

theorem pure_inv {α : Type} {a b : α} {c c' : Ctx} (h : (pure a : Blk α) c = .ok (b, c')) :
    b = a ∧ c' = c := by
  have e : (pure a : Blk α) c = .ok (a, c) := rfl
  rw [e] at h
  injection h with h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

theorem get_inv {α : Type} {x : Option α} {name : String} {a : α} {c c' : Ctx}
    (h : (Blk.get x name) c = .ok (a, c')) : x = some a ∧ c' = c := by
  cases x with
  | none => cases h
  | some v =>
    have e : (Blk.get (some v) name) c = .ok (v, c) := rfl
    rw [e] at h
    injection h with h
    injection h with h1 h2
    exact ⟨congrArg some h1, h2.symm⟩

theorem must_inv {b : Bool} {name : String} {u : Unit} {c c' : Ctx}
    (h : (Blk.must b name) c = .ok (u, c')) : b = true ∧ c' = c := by
  cases b with
  | false => cases h
  | true =>
    have e : (Blk.must true name) c = .ok ((), c) := rfl
    rw [e] at h
    injection h with h
    injection h with _ h2
    exact ⟨rfl, h2.symm⟩

theorem statement_inv {S : Statement} {c c' : Ctx} (h : Blk.statement c = .ok (S, c')) :
    S = c.st ∧ c' = c := by
  have e : Blk.statement c = .ok (c.st, c) := rfl
  rw [e] at h
  injection h with h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

theorem oracle_inv {o : Nat} {y : Oracle} {c c' : Ctx} (h : (Blk.oracle o) c = .ok (y, c')) :
    c.st.oracles[o]? = some y ∧ c' = c := by
  obtain ⟨S, c1, h1, h2⟩ := bind_inv (x := Blk.statement)
    (f := fun S => Blk.get (S.oracles[o]?)) h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  exact get_inv h2

theorem onOracle_inv {o : Nat} {f : Oracle → Oracle} {u : Unit} {c c' : Ctx}
    (h : (Blk.onOracle o f) c = .ok (u, c')) :
    o < c.st.oracles.size ∧
      c' = { c with st := { c.st with oracles := c.st.oracles.modify o f } } := by
  unfold Blk.onOracle at h
  split at h
  · rename_i hlt
    injection h with h
    injection h with _ h2
    exact ⟨hlt, h2.symm⟩
  · cases h

/-! ## `Send.admit` -/

/-- The update of an oracle message that `Send.admit` makes. s: the message's shape. -/
def admitAs (codes : Codes) (s : OracleShape) (rows : Array Row) (places : List PadPlace)
    (x : Oracle) : Oracle :=
  { x with
    sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
    ledger :=
      if 0 < s.maskRows then
        some { next := 0,
               left := Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell
                 s.answers,
               rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows }
      else none }

/-- What `Send.admit` leaves. -/
theorem admit_inv {o : Nat} {rows : Array Row} {u : Unit} {c c' : Ctx}
    (h : (Send.admit o rows) c = .ok (u, c')) :
    ∃ y places, c.st.oracles[o]? = some y ∧ Send.pad c.st.codes y.shape = some places ∧
      y.sampled = false ∧ rows.size = y.shape.answers ∧ 1 ≤ y.shape.answers ∧
      c' = { c with st := { c.st with
        oracles := c.st.oracles.modify o (admitAs c.st.codes y.shape rows places) } } := by
  unfold Send.admit at h
  obtain ⟨S, c1, h1, h⟩ := bind_inv h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  obtain ⟨y, c2, h2, h⟩ := bind_inv h
  obtain ⟨hy, rfl⟩ := oracle_inv h2
  obtain ⟨places, c3, h3, h⟩ := bind_inv h
  obtain ⟨hp, rfl⟩ := get_inv h3
  obtain ⟨_, c4, h4, h⟩ := bind_inv h
  obtain ⟨hm, rfl⟩ := must_inv h4
  obtain ⟨_, hc⟩ := onOracle_inv h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨y, places, hy, hp, hm.1.1, hm.1.2, hm.2, hc⟩

/-! ## Closing a round, on a view -/

/-- What closing a round leaves, on a view. -/
theorem close_inv {name : String} {kind : Fmt.Kind} {nz : Nat} {d : Fmt.Drawn} {c c' : Ctx}
    (h : (Blk.close name kind nz) c = .ok (d, c')) (hv : c.ch.dry = false) :
    ∃ e es, c.ch.entries = e :: es ∧ e.name = name ∧ e.drawNZ = nz ∧ c'.ch.entries = es ∧
      c'.ch.last = some e ∧ c'.ch.cur = none ∧ c'.ch.askedRows = false ∧ c'.ch.dry = false ∧
      c'.st = c.st ∧ c'.keepNotes = c.keepNotes := by
  unfold Blk.close at h
  split at h
  · cases h
  · rename_i e es he
    split at h
    · cases h
    · rename_i hn
      simp only [hv, Bool.false_eq_true, if_false] at h
      split at h
      · cases h
      · split at h
        · injection h with h
          injection h with _ h2
          subst h2
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
            Decidable.not_not] at hn
          exact ⟨e, es, he, hn.1.1, hn.1.2, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · cases h

/-- What closing a round in which the verifier says nothing leaves, on a view. -/
theorem closeEmpty_inv {name : String} {u : Unit} {c c' : Ctx}
    (h : (Blk.closeEmpty name) c = .ok (u, c')) (hv : c.ch.dry = false) :
    ∃ e es, c.ch.entries = e :: es ∧ e.name = name ∧ c'.ch.entries = es ∧
      c'.ch.last = some e ∧ c'.ch.cur = none ∧ c'.ch.askedRows = false ∧ c'.ch.dry = false ∧
      c'.st = c.st ∧ c'.keepNotes = c.keepNotes := by
  unfold Blk.closeEmpty at h
  obtain ⟨d, c1, h1, h2⟩ := bind_inv h
  obtain ⟨_, rfl⟩ := pure_inv h2
  obtain ⟨e, es, a1, a2, _, a4, a5, a6, a7, a8, a9, a10⟩ := close_inv h1 hv
  exact ⟨e, es, a1, a2, a4, a5, a6, a7, a8, a9, a10⟩

/-! ## Loops -/

/-- A loop over a list keeps a relation on contexts that is reflexive and transitive and that every
step keeps. -/
theorem forIn_keeps {α β : Type} (R : Ctx → Ctx → Prop) (hr : ∀ c, R c c)
    (ht : ∀ a b c, R a b → R b c → R a c) (f : α → β → Blk (ForInStep β))
    (hf : ∀ a b c r c', f a b c = .ok (r, c') → R c c') :
    ∀ (l : List α) (b : β) (c : Ctx) (r : β) (c' : Ctx), (forIn l b f) c = .ok (r, c') → R c c'
  | [], b, c, r, c', h => by
    rw [List.forIn_nil] at h
    obtain ⟨_, rfl⟩ := pure_inv h
    exact hr _
  | a :: l, b, c, r, c', h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, c1, h1, h2⟩ := bind_inv h
    cases s with
    | done b' =>
      obtain ⟨_, rfl⟩ := pure_inv h2
      exact hf _ _ _ _ _ h1
    | yield b' => exact ht _ _ _ (hf _ _ _ _ _ h1) (forIn_keeps R hr ht f hf l b' c1 r c' h2)

/-- The parts of a context that a run of the lookup reads beside the statement stay. -/
structure SameChan (c c' : Ctx) : Prop where
  dry : c'.ch.dry = c.ch.dry
  entries : c'.ch.entries = c.ch.entries
  cur : c'.ch.cur = c.ch.cur
  left : c'.ch.left = c.ch.left
  last : c'.ch.last = c.ch.last
  askedRows : c'.ch.askedRows = c.ch.askedRows
  keepNotes : c'.keepNotes = c.keepNotes

theorem SameChan.refl (c : Ctx) : SameChan c c := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameChan.trans {a b c : Ctx} (h : SameChan a b) (k : SameChan b c) : SameChan a c :=
  ⟨k.dry.trans h.dry, k.entries.trans h.entries, k.cur.trans h.cur, k.left.trans h.left,
    k.last.trans h.last, k.askedRows.trans h.askedRows, k.keepNotes.trans h.keepNotes⟩

theorem recvRoot_inv {n : Nat} {c c' : Ctx} (h : Blk.recvRoot c = .ok (n, c')) :
    SameChan c c' ∧ c'.st = c.st := by
  unfold Blk.recvRoot at h
  injection h with h
  injection h with _ h2
  subst h2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩, rfl⟩ <;> (simp only []; split <;> rfl)

/-! ## Receiving the roots of oracle messages -/

/-- What `Blk.receiveOracles` leaves. -/
theorem receiveOracles_inv {sent : Array OracleNotice} {ids : Array Nat} {c c' : Ctx}
    (h : (Blk.receiveOracles sent) c = .ok (ids, c')) :
    ids = (Array.range sent.size).map (· + c.st.oracles.size) ∧
      c'.st = { c.st with oracles := c.st.oracles ++ sent.map fun n => { shape := n.shape } } ∧
      SameChan c c' := by
  unfold Blk.receiveOracles at h
  obtain ⟨S, c1, h1, h⟩ := bind_inv h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  obtain ⟨B, c2, h2, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := ok_inj (show Except.ok (_, _) = _ from h2)
  obtain ⟨first, c3, h3, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := ok_inj (show Except.ok (_, _) = _ from h3)
  obtain ⟨_, c4, h4, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := must_inv h4
  obtain ⟨_, c5, h5, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := must_inv h5
  obtain ⟨lay, c6, h6, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := get_inv h6
  dsimp only at h
  obtain ⟨t1, c7, h7, h⟩ := bind_inv h
  obtain ⟨t2, c8, h8, h⟩ := bind_inv h
  obtain ⟨_, c9, h9, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := ok_inj (show Except.ok (_, _) = _ from h9)
  obtain ⟨_, c10, h10, h⟩ := bind_inv h
  obtain ⟨-, rfl⟩ := ok_inj (show Except.ok (_, _) = _ from h10)
  obtain ⟨rfl, rfl⟩ := pure_inv h
  have k7 : SameChan c6 c7 ∧ c7.st = c6.st := by
    rw [← Array.forIn_toList] at h7
    refine forIn_keeps (fun a b => SameChan a b ∧ b.st = a.st) (fun a => ⟨SameChan.refl a, rfl⟩)
      (fun a b c x y => ⟨x.1.trans y.1, y.2.trans x.2⟩) _ ?_ _ _ _ _ _ h7
    intro s r a q a' hs
    obtain ⟨n, a1, e1, e2⟩ := bind_inv hs
    obtain ⟨_, a2, e3, e4⟩ := bind_inv e2
    obtain ⟨-, rfl⟩ := pure_inv e3
    obtain ⟨-, rfl⟩ := pure_inv e4
    exact recvRoot_inv e1
  have k8 : SameChan c7 c8 ∧ c8.st = c7.st := by
    refine forIn_keeps (fun a b => SameChan a b ∧ b.st = a.st) (fun a => ⟨SameChan.refl a, rfl⟩)
      (fun a b c x y => ⟨x.1.trans y.1, y.2.trans x.2⟩) _ ?_ _ _ _ _ _ h8
    intro s r a q a' hs
    obtain ⟨_, a2, e3, e4⟩ := bind_inv hs
    obtain ⟨-, rfl⟩ := pure_inv e3
    obtain ⟨-, rfl⟩ := pure_inv e4
    exact ⟨SameChan.refl _, rfl⟩
  have k := k7.1.trans k8.1
  exact ⟨rfl, rfl, ⟨k.dry, k.entries, k.cur, k.left, k.last, k.askedRows, k.keepNotes⟩⟩

/-! ## `Send.verify` -/

/-- From c to c', oracle message o is untouched, or it was not sampled and has been updated as
`Send.admit` does. -/
def AdmittedOrSame (c c' : Ctx) (o : Nat) : Prop :=
  c'.st.oracles[o]? = c.st.oracles[o]? ∨
    ∃ y rows places, c.st.oracles[o]? = some y ∧ y.sampled = false ∧
      Send.pad c.st.codes y.shape = some places ∧
      c'.st.oracles[o]? = some (admitAs c.st.codes y.shape rows places y)

/-- What the steps of SEND keep. -/
structure Steady (c c' : Ctx) : Prop where
  codes : c'.st.codes = c.st.codes
  groups : c'.st.groups = c.st.groups
  size : c'.st.oracles.size = c.st.oracles.size
  dry : c'.ch.dry = c.ch.dry
  keepNotes : c'.keepNotes = c.keepNotes
  each : ∀ o, AdmittedOrSame c c' o

theorem Steady.of_st {c c' : Ctx} (h1 : c'.st = c.st) (h2 : c'.ch.dry = c.ch.dry)
    (h3 : c'.keepNotes = c.keepNotes) : Steady c c' :=
  ⟨by rw [h1], by rw [h1], by rw [h1], h2, h3, fun _ => Or.inl (by rw [h1])⟩

theorem Steady.refl (c : Ctx) : Steady c c := Steady.of_st rfl rfl rfl

theorem Steady.trans {a b c : Ctx} (h : Steady a b) (k : Steady b c) : Steady a c := by
  refine ⟨k.codes.trans h.codes, k.groups.trans h.groups, k.size.trans h.size,
    k.dry.trans h.dry, k.keepNotes.trans h.keepNotes, fun o => ?_⟩
  rcases h.each o with h1 | ⟨y, rows, places, e1, e2, e3, e4⟩
  · rcases k.each o with k1 | ⟨y, rows, places, e1, e2, e3, e4⟩
    · exact Or.inl (k1.trans h1)
    · exact Or.inr ⟨y, rows, places, h1 ▸ e1, e2, h.codes ▸ e3, h.codes ▸ e4⟩
  · rcases k.each o with k1 | ⟨y', rows', places', f1, f2, f3, f4⟩
    · exact Or.inr ⟨y, rows, places, e1, e2, e3, k1.trans e4⟩
    · rw [e4] at f1
      have : y' = admitAs a.st.codes y.shape rows places y := (Option.some.inj f1).symm
      rw [this] at f2
      cases f2

/-- `Send.admit` is such a step. -/
theorem steady_admit {o : Nat} {rows : Array Row} {u : Unit} {c c' : Ctx}
    (h : (Send.admit o rows) c = .ok (u, c')) : Steady c c' := by
  obtain ⟨y, places, hy, hp, hs, -, -, rfl⟩ := admit_inv h
  refine ⟨rfl, rfl, by simp, rfl, rfl, fun o' => ?_⟩
  by_cases e : o = o'
  · subst e
    refine Or.inr ⟨y, rows, places, hy, hs, hp, ?_⟩
    simp [Array.getElem?_modify, hy]
  · exact Or.inl (by simp [Array.getElem?_modify, e])

/-- Taking an item of the open message touches the channel alone. -/
theorem item_inv {i : Fmt.Item} {d g : Fmt.ItemValue} {c c' : Ctx}
    (h : (Blk.item i d) c = .ok (g, c')) :
    c'.st = c.st ∧ c'.ch.dry = c.ch.dry ∧ c'.keepNotes = c.keepNotes := by
  unfold Blk.item at h
  repeat' split at h
  all_goals try dsimp only at h
  all_goals repeat' split at h
  all_goals first
    | (cases h; done)
    | (obtain ⟨-, rfl⟩ := ok_inj h
       exact ⟨rfl, rfl, rfl⟩)

theorem steady_recvAnswer {y : E} {c c' : Ctx} (h : Blk.recvAnswer c = .ok (y, c')) :
    Steady c c' := by
  unfold Blk.recvAnswer at h
  obtain ⟨g, c1, h1, h2⟩ := bind_inv h
  obtain ⟨a1, a2, a3⟩ := item_inv h1
  cases g with
  | answer x =>
    obtain ⟨-, rfl⟩ := pure_inv h2
    exact Steady.of_st a1 a2 a3
  | _ => cases h2

theorem test_inv {b : Bool} {name : String} {u : Unit} {c c' : Ctx}
    (h : (Blk.test b name) c = .ok (u, c')) : c' = c := by
  unfold Blk.test at h
  split at h
  · exact (ok_inj h).2.symm
  · cases h

/-- The course of `Send.verify`: it closes the round "SEND seed"; then come steps that are
`Send.admit` or `Blk.recvAnswer` or leave the context, so that every reflexive and transitive
relation that these two keep holds from the context behind the closing to that behind the loops;
then it closes the round "SEND answer", if it has a round of its own. -/
theorem sendVerifyIds_parts {ids : Array Nat} {ownRound : Bool} {u : Unit} {c c' : Ctx}
    (h : (Send.verify ids ownRound) c = .ok (u, c')) :
    ∃ nz drawn c5 c8, (Blk.close "SEND seed" .seeds nz) c = .ok (drawn, c5) ∧
      (∀ R : Ctx → Ctx → Prop, (∀ a, R a a) → (∀ a b d, R a b → R b d → R a d) →
        (∀ o rows v a b, (Send.admit o rows) a = .ok (v, b) → R a b) →
        (∀ y a b, Blk.recvAnswer a = .ok (y, b) → R a b) → R c5 c8) ∧
      (if ownRound = true then Blk.closeEmpty "SEND answer" else pure PUnit.unit) c8 =
        .ok (u, c') := by
  unfold Send.verify at h
  obtain ⟨S, c1, h1, k1⟩ := bind_inv h
  obtain ⟨rfl, rfl⟩ := statement_inv h1
  try dsimp only at k1
  obtain ⟨_, c2, h2, k2⟩ := bind_inv k1
  obtain ⟨-, rfl⟩ := must_inv h2
  obtain ⟨_, c3, h3, k3⟩ := bind_inv k2
  obtain ⟨-, rfl⟩ := must_inv h3
  obtain ⟨shapes, c4, h4, k4⟩ := bind_inv k3
  obtain ⟨-, rfl⟩ := get_inv h4
  try dsimp only at k4
  obtain ⟨drawn, c5, h5, k5⟩ := bind_inv k4
  obtain ⟨seeds, c6, h6, k6⟩ := bind_inv k5
  obtain ⟨-, rfl⟩ := get_inv h6
  obtain ⟨_, c7, h7, k7⟩ := bind_inv k6
  have e7 := test_inv h7
  subst e7
  obtain ⟨_, c8, h8, k8⟩ := bind_inv k7
  refine ⟨_, drawn, _, c8, h5, fun R hr ht hadm hans => ?_, k8⟩
  exact forIn_keeps R hr ht _
    (fun x r a q a' hs => by
      obtain ⟨rows, a1, e1, e2⟩ := bind_inv hs
      obtain ⟨_, a2, e3, e4⟩ := bind_inv e2
      obtain ⟨-, rfl⟩ := pure_inv e4
      refine ht _ _ _ ?_ (hadm _ _ _ _ _ e3)
      exact forIn_keeps R hr ht _
        (fun i r b q b' hi => by
          obtain ⟨_, b1, f1, f2⟩ := bind_inv hi
          obtain ⟨-, rfl⟩ := get_inv f1
          obtain ⟨_, b2, f3, f4⟩ := bind_inv f2
          obtain ⟨-, rfl⟩ := get_inv f3
          obtain ⟨_, b3, f5, f6⟩ := bind_inv f4
          obtain ⟨_, b4, f7, f8⟩ := bind_inv f6
          obtain ⟨-, rfl⟩ := pure_inv f7
          obtain ⟨-, rfl⟩ := pure_inv f8
          exact hans _ _ _ f5) _ _ _ _ _ e1) _ _ _ _ _ h8

/-- What `Send.verify` leaves, on a view. -/
theorem sendVerifyIds_inv {ids : Array Nat} {ownRound : Bool} {u : Unit} {c c' : Ctx}
    (h : (Send.verify ids ownRound) c = .ok (u, c')) (hv : c.ch.dry = false) :
    Steady c c' ∧ (ownRound = true → ∃ e, c'.ch.last = some e ∧ e.name = "SEND answer" ∧
      c'.ch.cur = none ∧ c'.ch.askedRows = false) := by
  obtain ⟨nz, drawn, c5, c8, h5, hR, k8⟩ := sendVerifyIds_parts h
  obtain ⟨e, es, -, -, -, -, -, -, -, d5, s5, n5⟩ := close_inv h5 hv
  have st5 := Steady.of_st s5 (d5.trans hv.symm) n5
  have st8 := hR Steady Steady.refl (fun _ _ _ => Steady.trans) (fun _ _ _ _ _ => steady_admit)
    (fun _ _ _ => steady_recvAnswer)
  have st := st5.trans st8
  cases ownRound with
  | false =>
    obtain ⟨-, rfl⟩ := pure_inv (show (pure PUnit.unit : Blk PUnit) _ = _ from k8)
    exact ⟨st, fun hf => by cases hf⟩
  | true =>
    have k9 : (Blk.closeEmpty "SEND answer") c8 = .ok (u, c') := k8
    obtain ⟨e', es', -, g2, -, g4, g5, g6, g7, g8, g9⟩ := closeEmpty_inv k9 (st.dry.trans hv)
    exact ⟨st.trans (Steady.of_st g8 (g7.trans (st.dry.trans hv).symm) g9),
      fun _ => ⟨e', g4, g2, g5, g6⟩⟩

/-! ## The plan's entries and the rounds that are left -/

/-- The plan's entries stay, and the rounds that are left are a tail of those that were left. -/
structure Flow (c c' : Ctx) : Prop where
  entries : c'.ch.entries = c.ch.entries
  left : ∃ pre, c.ch.left = pre ++ c'.ch.left

theorem Flow.refl (c : Ctx) : Flow c c := ⟨rfl, [], rfl⟩

theorem Flow.trans {a b c : Ctx} (h : Flow a b) (k : Flow b c) : Flow a c := by
  obtain ⟨p, hp⟩ := h.left
  obtain ⟨q, hq⟩ := k.left
  exact ⟨k.entries.trans h.entries, p ++ q, by rw [hp, hq, List.append_assoc]⟩

theorem flow_item {i : Fmt.Item} {d g : Fmt.ItemValue} {c c' : Ctx}
    (h : (Blk.item i d) c = .ok (g, c')) : Flow c c' := by
  unfold Blk.item at h
  split at h
  · obtain ⟨-, rfl⟩ := ok_inj h
    exact ⟨rfl, [], rfl⟩
  · cases hc : c.ch.cur with
    | some r =>
      simp only [hc] at h
      split at h
      · cases h
      · obtain ⟨-, rfl⟩ := ok_inj h
        exact ⟨rfl, [], rfl⟩
    | none =>
      cases hl : c.ch.left with
      | nil =>
        simp only [hc, hl] at h
        cases h
      | cons r t =>
        simp only [hc, hl] at h
        split at h
        · cases h
        · obtain ⟨-, rfl⟩ := ok_inj h
          exact ⟨rfl, [r], hl⟩

theorem flow_recvAnswer {y : E} {c c' : Ctx} (h : Blk.recvAnswer c = .ok (y, c')) :
    Flow c c' := by
  unfold Blk.recvAnswer at h
  obtain ⟨g, c1, h1, h2⟩ := bind_inv h
  have a := flow_item h1
  cases g with
  | answer x =>
    obtain ⟨-, rfl⟩ := pure_inv h2
    exact a
  | _ => cases h2

theorem flow_admit {o : Nat} {rows : Array Row} {u : Unit} {c c' : Ctx}
    (h : (Send.admit o rows) c = .ok (u, c')) : Flow c c' := by
  obtain ⟨_, _, -, -, -, -, -, rfl⟩ := admit_inv h
  exact ⟨rfl, [], rfl⟩

/-- Closing a round, on a view: the rounds that are left are a tail of those that were left. -/
theorem close_left {name : String} {kind : Fmt.Kind} {nz : Nat} {d : Fmt.Drawn} {c c' : Ctx}
    (h : (Blk.close name kind nz) c = .ok (d, c')) (hv : c.ch.dry = false) :
    ∃ pre, c.ch.left = pre ++ c'.ch.left := by
  unfold Blk.close at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [hv, Bool.false_eq_true, if_false] at h
      cases hc : c.ch.cur with
      | some r =>
        simp only [hc] at h
        split at h
        · obtain ⟨-, rfl⟩ := ok_inj h
          exact ⟨[], rfl⟩
        · cases h
      | none =>
        cases hl : c.ch.left with
        | nil =>
          simp only [hc, hl] at h
          cases h
        | cons r t =>
          simp only [hc, hl] at h
          split at h
          · obtain ⟨-, rfl⟩ := ok_inj h
            exact ⟨[r], rfl⟩
          · cases h

/-- The entries and rounds that `Send.verify` with a round of its own leaves, on a view: it takes
the plan's next two entries, "SEND seed" and "SEND answer"; the rounds that are left are a tail of
those that were left. -/
theorem sendVerifyIds_flow {ids : Array Nat} {u : Unit} {c c' : Ctx}
    (h : (Send.verify ids true) c = .ok (u, c')) (hv : c.ch.dry = false) :
    (∃ e1 e2, c.ch.entries = e1 :: e2 :: c'.ch.entries ∧ e1.name = "SEND seed" ∧
      e2.name = "SEND answer" ∧ c'.ch.last = some e2) ∧
      ∃ pre, c.ch.left = pre ++ c'.ch.left := by
  obtain ⟨nz, drawn, c5, c8, h5, hR, k8⟩ := sendVerifyIds_parts h
  obtain ⟨e1, es1, a1, a2, -, a4, -, -, -, d5, -, -⟩ := close_inv h5 hv
  obtain ⟨p5, l5⟩ := close_left h5 hv
  have fl := hR Flow Flow.refl (fun _ _ _ => Flow.trans) (fun _ _ _ _ _ => flow_admit)
    (fun _ _ _ => flow_recvAnswer)
  have st8 := hR Steady Steady.refl (fun _ _ _ => Steady.trans) (fun _ _ _ _ _ => steady_admit)
    (fun _ _ _ => steady_recvAnswer)
  have k9 : (Blk.closeEmpty "SEND answer") c8 = .ok (u, c') := k8
  have d8 : c8.ch.dry = false := st8.dry.trans d5
  obtain ⟨e2, es2, g1, g2, g3, g4, -, -, -, -, -⟩ := closeEmpty_inv k9 d8
  obtain ⟨dd, c9, m1, m2⟩ := bind_inv (show ((Blk.close "SEND answer" .nothing) >>= fun _ =>
    (pure () : Blk Unit)) c8 = _ from k9)
  obtain ⟨-, rfl⟩ := pure_inv m2
  obtain ⟨p9, l9⟩ := close_left m1 d8
  obtain ⟨p8, l8⟩ := fl.left
  refine ⟨⟨e1, e2, ?_, a2, g2, g4⟩, p5 ++ (p8 ++ p9), ?_⟩
  · rw [a1, ← a4, ← fl.entries, g1, g3]
  · rw [l5, l8, l9, List.append_assoc, List.append_assoc]

/-! ## How many rounds are taken -/

/-- From a to b no round is begun, or one: if none is open at a, then none is open at b and the same
rounds are left, or one is open at b and it was the first of those left; if one is open at a, one is
open at b and the same rounds are left. -/
structure Loads (a b : Ctx) : Prop where
  fromNone : a.ch.cur = none → (b.ch.cur = none ∧ b.ch.left = a.ch.left) ∨
    (b.ch.cur ≠ none ∧ ∃ r, a.ch.left = r :: b.ch.left)
  fromSome : a.ch.cur ≠ none → b.ch.cur ≠ none ∧ b.ch.left = a.ch.left

theorem Loads.refl (a : Ctx) : Loads a a := ⟨fun h => Or.inl ⟨h, rfl⟩, fun h => ⟨h, rfl⟩⟩

theorem Loads.trans {a b c : Ctx} (h : Loads a b) (k : Loads b c) : Loads a c := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rcases h.fromNone e with ⟨b1, b2⟩ | ⟨b1, r, b2⟩
    · rcases k.fromNone b1 with ⟨c1, c2⟩ | ⟨c1, r, c2⟩
      · exact Or.inl ⟨c1, c2.trans b2⟩
      · exact Or.inr ⟨c1, r, b2 ▸ c2⟩
    · obtain ⟨c1, c2⟩ := k.fromSome b1
      exact Or.inr ⟨c1, r, c2 ▸ b2⟩
  · obtain ⟨b1, b2⟩ := h.fromSome e
    obtain ⟨c1, c2⟩ := k.fromSome b1
    exact ⟨c1, c2.trans b2⟩

theorem loads_item {i : Fmt.Item} {d g : Fmt.ItemValue} {c c' : Ctx}
    (h : (Blk.item i d) c = .ok (g, c')) : Loads c c' := by
  unfold Blk.item at h
  split at h
  · obtain ⟨-, rfl⟩ := ok_inj h
    exact ⟨fun e => Or.inl ⟨e, rfl⟩, fun e => ⟨e, rfl⟩⟩
  · cases hc : c.ch.cur with
    | some r =>
      simp only [hc] at h
      split at h
      · cases h
      · obtain ⟨-, rfl⟩ := ok_inj h
        exact ⟨fun e => (by rw [hc] at e; cases e), fun _ => ⟨by simp, rfl⟩⟩
    | none =>
      cases hl : c.ch.left with
      | nil =>
        simp only [hc, hl] at h
        cases h
      | cons r t =>
        simp only [hc, hl] at h
        split at h
        · cases h
        · obtain ⟨-, rfl⟩ := ok_inj h
          exact ⟨fun _ => Or.inr ⟨by simp, r, hl⟩, fun e => absurd hc e⟩

theorem loads_recvAnswer {y : E} {c c' : Ctx} (h : Blk.recvAnswer c = .ok (y, c')) :
    Loads c c' := by
  unfold Blk.recvAnswer at h
  obtain ⟨g, c1, h1, h2⟩ := bind_inv h
  have a := loads_item h1
  cases g with
  | answer x =>
    obtain ⟨-, rfl⟩ := pure_inv h2
    exact a
  | _ => cases h2

theorem loads_admit {o : Nat} {rows : Array Row} {u : Unit} {c c' : Ctx}
    (h : (Send.admit o rows) c = .ok (u, c')) : Loads c c' := by
  obtain ⟨_, _, -, -, -, -, -, rfl⟩ := admit_inv h
  exact ⟨fun e => Or.inl ⟨e, rfl⟩, fun e => ⟨e, rfl⟩⟩

/-- Closing a round, on a view: if none is open, the first of the rounds left is taken; if one is
open, the rounds left stay. -/
theorem close_loads {name : String} {kind : Fmt.Kind} {nz : Nat} {d : Fmt.Drawn} {c c' : Ctx}
    (h : (Blk.close name kind nz) c = .ok (d, c')) (hv : c.ch.dry = false) :
    (c.ch.cur = none → ∃ r, c.ch.left = r :: c'.ch.left) ∧
      (c.ch.cur ≠ none → c'.ch.left = c.ch.left) := by
  unfold Blk.close at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [hv, Bool.false_eq_true, if_false] at h
      cases hc : c.ch.cur with
      | some r =>
        simp only [hc] at h
        split at h
        · obtain ⟨-, rfl⟩ := ok_inj h
          exact ⟨fun e => (by cases e), fun _ => rfl⟩
        · cases h
      | none =>
        cases hl : c.ch.left with
        | nil =>
          simp only [hc, hl] at h
          cases h
        | cons r t =>
          simp only [hc, hl] at h
          split at h
          · obtain ⟨-, rfl⟩ := ok_inj h
            exact ⟨fun _ => ⟨r, rfl⟩, fun e => absurd rfl e⟩
          · cases h

/-- `Send.verify` with a round of its own takes exactly two rounds, on a view, if none is open. -/
theorem sendVerifyIds_rounds {ids : Array Nat} {u : Unit} {c c' : Ctx}
    (h : (Send.verify ids true) c = .ok (u, c')) (hv : c.ch.dry = false)
    (hc : c.ch.cur = none) : ∃ r1 r2, c.ch.left = r1 :: r2 :: c'.ch.left := by
  obtain ⟨nz, drawn, c5, c8, h5, hR, k8⟩ := sendVerifyIds_parts h
  obtain ⟨_, _, -, -, -, -, -, cur5, -, d5, -, -⟩ := close_inv h5 hv
  obtain ⟨r1, l1⟩ := (close_loads h5 hv).1 hc
  have ld := hR Loads Loads.refl (fun _ _ _ => Loads.trans) (fun _ _ _ _ _ => loads_admit)
    (fun _ _ _ => loads_recvAnswer)
  have st8 := hR Steady Steady.refl (fun _ _ _ => Steady.trans) (fun _ _ _ _ _ => steady_admit)
    (fun _ _ _ => steady_recvAnswer)
  have d8 : c8.ch.dry = false := st8.dry.trans d5
  obtain ⟨dd, c9, m1, m2⟩ := bind_inv (show ((Blk.close "SEND answer" .nothing) >>= fun _ =>
    (pure () : Blk Unit)) c8 = _ from k8)
  obtain ⟨-, rfl⟩ := pure_inv m2
  obtain ⟨q1, q2⟩ := close_loads m1 d8
  rcases ld.fromNone cur5 with ⟨b1, b2⟩ | ⟨b1, r2, b2⟩
  · obtain ⟨r2, l2⟩ := q1 b1
    exact ⟨r1, r2, by rw [l1, ← b2, l2]⟩
  · exact ⟨r1, r2, by rw [l1, b2, q2 b1]⟩

/-! ## `sendVerify` -/

/-- What SEND for a verifier leaves, on a view: the numbers of the new messages; codes and groups
stay; a message that was there and was sampled stays as it was; a new message is as it was entered,
or updated as `Send.admit` does at its shape; with a round of its own, that round is closed. -/
theorem sendVerify_inv {notices : Array OracleNotice} {ownRound : Bool} {ids : Array Nat}
    {c c' : Ctx} (h : (sendVerify notices ownRound) c = .ok (ids, c')) (hv : c.ch.dry = false) :
    ids = (Array.range notices.size).map (· + c.st.oracles.size) ∧
      c'.st.codes = c.st.codes ∧ c'.st.groups = c.st.groups ∧
      c'.st.oracles.size = c.st.oracles.size + notices.size ∧
      c'.ch.dry = false ∧ c'.keepNotes = c.keepNotes ∧
      (∀ (o : Nat) (y : Oracle), c.st.oracles[o]? = some y → y.sampled = true →
        c'.st.oracles[o]? = some y) ∧
      (∀ (j : Nat) (n : OracleNotice), notices[j]? = some n →
        c'.st.oracles[c.st.oracles.size + j]? = some { shape := n.shape } ∨
          ∃ rows places, Send.pad c.st.codes n.shape = some places ∧
            c'.st.oracles[c.st.oracles.size + j]? =
              some (admitAs c.st.codes n.shape rows places { shape := n.shape })) ∧
      (ownRound = true → ∃ e, c'.ch.last = some e ∧ e.name = "SEND answer" ∧
        c'.ch.cur = none ∧ c'.ch.askedRows = false) := by
  unfold sendVerify at h
  obtain ⟨ids', c1, h1, k1⟩ := bind_inv h
  obtain ⟨_, c2, h2, k2⟩ := bind_inv k1
  obtain ⟨rfl, rfl⟩ := pure_inv k2
  obtain ⟨hids, hst, hch⟩ := receiveOracles_inv h1
  obtain ⟨st, hown⟩ := sendVerifyIds_inv h2 (hch.dry.trans hv)
  have hcodes : c1.st.codes = c.st.codes := by rw [hst]
  have hor : c1.st.oracles = c.st.oracles ++ notices.map fun n => { shape := n.shape } := by
    rw [hst]
  refine ⟨hids, st.codes.trans hcodes, st.groups.trans (by rw [hst]), ?_,
    st.dry.trans (hch.dry.trans hv), st.keepNotes.trans hch.keepNotes, ?_, ?_, hown⟩
  · rw [st.size, hor]
    simp
  · intro o y hy hs
    have hlt : o < c.st.oracles.size := (Array.getElem?_eq_some_iff.1 hy).1
    have e1 : c1.st.oracles[o]? = some y := by
      rw [hor, Array.getElem?_append_left hlt, hy]
    rcases st.each o with e | ⟨y', _, _, f1, f2, _, _⟩
    · rw [e, e1]
    · rw [e1] at f1
      rw [← Option.some.inj f1, hs] at f2
      cases f2
  · intro j n hn
    have e1 : c1.st.oracles[c.st.oracles.size + j]? = some { shape := n.shape } := by
      rw [hor, Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        Array.getElem?_map, hn]
      rfl
    rcases st.each (c.st.oracles.size + j) with e | ⟨y', rows, places, f1, _, f3, f4⟩
    · exact Or.inl (e.trans e1)
    · rw [e1] at f1
      have ey := Option.some.inj f1
      subst ey
      rw [hcodes] at f3 f4
      exact Or.inr ⟨rows, places, f3, f4⟩

/-- The entries and rounds that `sendVerify` with a round of its own leaves, on a view. -/
theorem sendVerify_flow {notices : Array OracleNotice} {ids : Array Nat} {c c' : Ctx}
    (h : (sendVerify notices true) c = .ok (ids, c')) (hv : c.ch.dry = false) :
    (∃ e1 e2, c.ch.entries = e1 :: e2 :: c'.ch.entries ∧ e1.name = "SEND seed" ∧
      e2.name = "SEND answer" ∧ c'.ch.last = some e2) ∧
      ∃ pre, c.ch.left = pre ++ c'.ch.left := by
  unfold sendVerify at h
  obtain ⟨ids', c1, h1, k1⟩ := bind_inv h
  obtain ⟨_, c2, h2, k2⟩ := bind_inv k1
  obtain ⟨rfl, rfl⟩ := pure_inv k2
  obtain ⟨-, -, hch⟩ := receiveOracles_inv h1
  have r := sendVerifyIds_flow h2 (hch.dry.trans hv)
  rw [hch.entries, hch.left] at r
  exact r

/-- `sendVerify` with a round of its own takes exactly two rounds, on a view, if none is open. -/
theorem sendVerify_rounds {notices : Array OracleNotice} {ids : Array Nat} {c c' : Ctx}
    (h : (sendVerify notices true) c = .ok (ids, c')) (hv : c.ch.dry = false)
    (hc : c.ch.cur = none) : ∃ r1 r2, c.ch.left = r1 :: r2 :: c'.ch.left := by
  unfold sendVerify at h
  obtain ⟨ids', c1, h1, k1⟩ := bind_inv h
  obtain ⟨_, c2, h2, k2⟩ := bind_inv k1
  obtain ⟨rfl, rfl⟩ := pure_inv k2
  obtain ⟨-, -, hch⟩ := receiveOracles_inv h1
  have r := sendVerifyIds_rounds h2 (hch.dry.trans hv) (hch.cur.trans hc)
  rw [hch.left] at r
  exact r

/-- A new message that is sampled afterwards has been updated as `Send.admit` does: its pad and its
ledger are functions of the codes and of its shape alone. -/
theorem sendVerify_sampled {notices : Array OracleNotice} {ownRound : Bool} {ids : Array Nat}
    {c c' : Ctx} (h : (sendVerify notices ownRound) c = .ok (ids, c')) (hv : c.ch.dry = false)
    (j : Nat) (n : OracleNotice) (hn : notices[j]? = some n)
    (hs : (c'.st.oracles[c.st.oracles.size + j]?).any Oracle.sampled = true) :
    ∃ rows places, Send.pad c.st.codes n.shape = some places ∧
      c'.st.oracles[c.st.oracles.size + j]? =
        some (admitAs c.st.codes n.shape rows places { shape := n.shape }) := by
  obtain ⟨-, -, -, -, -, -, -, hnew, -⟩ := sendVerify_inv h hv
  rcases hnew j n hn with e | e
  · rw [e] at hs
    cases hs
  · exact e

end OnBytes.G4

#print axioms OnBytes.G4.receiveOracles_inv
#print axioms OnBytes.G4.sendVerifyIds_inv
#print axioms OnBytes.G4.sendVerify_inv
#print axioms OnBytes.G4.sendVerify_sampled
#print axioms OnBytes.G4.sendVerify_flow
#print axioms OnBytes.G4.sendVerify_rounds
#print axioms OnBytes.G4.admit_inv
#print axioms OnBytes.G4.closeEmpty_inv
